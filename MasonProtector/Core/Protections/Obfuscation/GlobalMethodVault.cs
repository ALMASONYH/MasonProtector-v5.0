using System;
using System.Collections.Generic;
using System.Linq;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnFieldAttributes = dnlib.DotNet.FieldAttributes;
using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{

    internal class GlobalMethodVaultProtection
    {
        private readonly Obfuscation engine;
        private readonly Random rng;
        private HashSet<TypeDef> serializableTypes;

        private const int VAULT_HOST_COUNT = 32;

        private const int ENC_ARRAY_POOL = 8;
        private const int ENC_ARRAY_SIZE = 256;
        private TypeDef encContainer;
        private List<FieldDef> encArrayFields;
        private List<int[]> encArrayData;
        private List<int[]> encArrayShuffles;
        private int[] encArrayPtrs;

        private List<FieldDef> xorKeyFields;
        private int[] xorKeyValues;

        internal GlobalMethodVaultProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void Apply(ModuleDef module, TypeDef modType)
        {
            serializableTypes = BuildSerializableSet(module);

            var hosts = new List<TypeDef>(VAULT_HOST_COUNT);
            for (int h = 0; h < VAULT_HOST_COUNT; h++)
            {
                var host = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);

                host.Attributes = PickHostAttribs(h);
                module.Types.Add(host);
                engine.injectedTypes.Add(host);
                hosts.Add(host);
            }

            BuildEncInfrastructure(module);

            var addressTakenInstanceMethods = new HashSet<MethodDef>();
            foreach (TypeDef t in module.GetTypes())
            {
                if (engine.injectedTypes.Contains(t)) continue;
                foreach (MethodDef m in t.Methods)
                {
                    if (m == null || !m.HasBody) continue;
                    foreach (var instr in m.Body.Instructions)
                    {
                        if (instr.OpCode == DnOpCodes.Ldftn ||
                            instr.OpCode == DnOpCodes.Ldvirtftn)
                        {
                            var target = instr.Operand as MethodDef;
                            if (target != null && !target.IsStatic)
                                addressTakenInstanceMethods.Add(target);
                        }
                    }
                }
            }

            var relocMap = new Dictionary<MethodDef, MethodDef>();

            var relocated = new List<(MethodDef orig, MethodDef host, TypeDef origType)>();

            int totalCandidates = 0;

            foreach (TypeDef type in module.GetTypes().ToList())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                if (engine.injectedTypes.Contains(type)) continue;
                if (engine.IsTypeUserExcluded(type)) continue;
                if (type.HasGenericParameters) continue;

                foreach (MethodDef method in type.Methods.ToList())
                {
                    if (!IsVaultCandidate(module, method, type, addressTakenInstanceMethods)) continue;
                    totalCandidates++;

                    var hostType = hosts[rng.Next(hosts.Count)];
                    MethodDef hostMethod = TryRelocate(module, method, type, hostType);
                    if (hostMethod == null) continue;

                    relocMap[method] = hostMethod;
                    relocated.Add((method, hostMethod, type));
                }
            }

            if (relocated.Count == 0)
            {

                foreach (var h in hosts)
                {
                    module.Types.Remove(h);
                    engine.injectedTypes.Remove(h);
                }

                if (encContainer != null)
                {
                    module.Types.Remove(encContainer);
                    engine.injectedTypes.Remove(encContainer);
                }
                return;
            }

            RewriteCallsites(module, relocMap);

            var sealedHostMethods = new HashSet<MethodDef>();
            try
            {
                var hostMethods = new List<MethodDef>(relocated.Count);
                foreach (var (_, hostMethod, _) in relocated)
                    hostMethods.Add(hostMethod);
                var bvp = new BodyVaultProtection(engine);
                bvp.SealExplicitMethods(module, hostMethods);
                foreach (var m in hostMethods)
                    if (engine.bodyVaultedStubs.Contains(m))
                        sealedHostMethods.Add(m);
            }
            catch { }

            foreach (var (_, hostMethod, _) in relocated)
            {
                if (sealedHostMethods.Contains(hostMethod)) continue;
                try { EncryptMethodBody(module, hostMethod); }
                catch { }
            }

            if (encContainer != null)
                BuildEncContainerCctor(module);

            var stillReferenced = BuildResidualRefSet(module, relocated);

            bool indirectRefsActive = engine.cfg != null &&
                (engine.cfg.ProxyCalls || engine.cfg.ReferenceProxy || engine.cfg.CallHiding);

            foreach (var (origMethod, hostMethod, origType) in relocated)
            {
                bool reflPreserved = IsReflectionPreserved(origMethod);
                bool hasResidue   = stillReferenced.Contains(origMethod);

                if (!reflPreserved && !hasResidue && !indirectRefsActive)
                {
                    try { origType.Methods.Remove(origMethod); }
                    catch { }
                }
                else
                {
                    try { ReplaceWithOpaqueThunk(origMethod, hostMethod); }
                    catch
                    {
                        try { ReplaceWithThunk(module, origMethod, hostMethod); }
                        catch { }
                    }
                }
            }

            _ = totalCandidates;
        }

        private DnTypeAttributes PickHostAttribs(int index)
        {

            switch (index % 4)
            {
                case 0:
                    return DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                           DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                case 1:

                    return DnTypeAttributes.NotPublic | DnTypeAttributes.Sealed |
                           DnTypeAttributes.BeforeFieldInit;
                case 2:
                    return DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                           DnTypeAttributes.Sealed;
                default:
                    return DnTypeAttributes.NotPublic | DnTypeAttributes.Sealed;
            }
        }

        private bool IsVaultCandidate(ModuleDef module, MethodDef m, TypeDef declaringType,
            HashSet<MethodDef> addressTakenInstanceMethods)
        {
            if (m == null || !m.HasBody || !m.Body.HasInstructions) return false;
            if (engine.injectedMethods.Contains(m)) return false;
            if (engine.IsMethodUserExcluded(m)) return false;
            if (engine.bodyVaultedStubs.Contains(m)) return false;

            if (m.IsConstructor || m.IsStaticConstructor) return false;

            if (m.IsVirtual || m.IsAbstract) return false;
            if (m.HasOverrides) return false;

            if (m == module.EntryPoint) return false;
            if (m.Name == "Main") return false;

            if (m.IsPinvokeImpl) return false;

            if (m.HasGenericParameters) return false;

            if (declaringType.HasGenericParameters) return false;

            if (!m.IsStatic && declaringType.IsValueType) return false;

            if (engine.MethodHasAsyncOrIteratorAttribute(m)) return false;

            if (m.Name.StartsWith("<")) return false;
            if (m.Name.StartsWith("VB$")) return false;

            if (m.Name == "InitializeComponent" && engine.cfg != null && engine.cfg.HideDesignerCode)
                return false;
            if (m.Name == "Dispose" && m.MethodSig != null &&
                m.MethodSig.Params.Count == 1 &&
                m.MethodSig.Params[0].FullName == "System.Boolean" &&
                engine.IsWinFormsType(declaringType))
                return false;

            if (engine.designerSplitSubMethods.Contains(m)) return false;

            if (!m.IsStatic && addressTakenInstanceMethods.Contains(m)) return false;

            if (m.IsRuntimeSpecialName) return false;

            MethodSig sig = m.MethodSig;
            if (sig == null) return false;
            if (!IsSafeTypeSig(sig.RetType)) return false;
            foreach (var p in sig.Params)
                if (!IsSafeTypeSig(p)) return false;

            if (HasUnpromotableAccess(m, declaringType)) return false;

            foreach (var instr in m.Body.Instructions)
            {
                Code c = instr.OpCode.Code;
                if (c == Code.Calli || c == Code.Localloc || c == Code.Jmp) return false;
                if (instr.OpCode.OperandType == OperandType.InlineSig) return false;
            }

            return true;
        }

        private static bool IsSafeTypeSig(TypeSig ts)
        {
            if (ts == null) return false;
            ts = ts.RemovePinnedAndModifiers();
            if (ts == null) return false;
            if (ts is PtrSig) return false;
            if (ts is GenericSig) return false;
            if (ts is FnPtrSig) return false;
            return true;
        }

        private static HashSet<TypeDef> BuildSerializableSet(ModuleDef module)
        {
            var result = new HashSet<TypeDef>();
            foreach (TypeDef t in module.GetTypes())
            {
                if (t == null) continue;
                if (t.IsSerializable) { result.Add(t); continue; }
                foreach (var iface in t.Interfaces)
                {
                    if (iface.Interface == null) continue;
                    string fn = iface.Interface.FullName;
                    if (fn == "System.Runtime.Serialization.ISerializable" ||
                        fn == "System.Runtime.Serialization.IDeserializationCallback")
                    { result.Add(t); break; }
                }
            }
            return result;
        }

        private static bool MemberHasReflectionOrSerializationAttribute(IHasCustomAttribute member)
        {
            if (member == null || !member.HasCustomAttributes) return false;
            foreach (var ca in member.CustomAttributes)
            {
                if (ca.TypeFullName == null) continue;
                string n = ca.TypeFullName;
                if (n.Contains("Serializ") || n.Contains("NonSerialized") ||
                    n.Contains("DataMember") || n.Contains("DataContract") ||
                    n.Contains("JsonProperty") || n.Contains("XmlElement") ||
                    n.Contains("XmlAttribute") || n.Contains("XmlIgnore") ||
                    n.Contains("EditorBrowsable") || n.Contains("Browsable"))
                    return true;
            }
            return false;
        }

        private bool IsPromotableMember(IMemberDef member, TypeDef ownerType)
        {
            if (member == null) return false;
            if (serializableTypes != null && serializableTypes.Contains(ownerType)) return false;
            if (MemberHasReflectionOrSerializationAttribute(member)) return false;
            if (engine.reflectionNames.Contains(member.Name)) return false;
            if (engine.reflectionNames.Contains(member.FullName)) return false;
            return true;
        }

        private bool HasUnpromotableAccess(MethodDef method, TypeDef declaringType)
        {
            if (!method.HasBody) return false;
            foreach (var instr in method.Body.Instructions)
            {
                if (instr.OpCode == DnOpCodes.Ldfld || instr.OpCode == DnOpCodes.Stfld ||
                    instr.OpCode == DnOpCodes.Ldsfld || instr.OpCode == DnOpCodes.Stsfld ||
                    instr.OpCode == DnOpCodes.Ldflda || instr.OpCode == DnOpCodes.Ldsflda)
                {
                    var fieldRef = instr.Operand as IField;
                    if (fieldRef != null)
                    {
                        var fd = fieldRef.ResolveFieldDef();
                        if (fd != null && fd.DeclaringType == declaringType &&
                            (fd.IsPrivate || fd.IsFamily || fd.IsFamilyAndAssembly))
                        {
                            if (!IsPromotableMember(fd, declaringType)) return true;
                        }
                    }
                }

                if (instr.OpCode == DnOpCodes.Call || instr.OpCode == DnOpCodes.Callvirt ||
                    instr.OpCode == DnOpCodes.Ldftn || instr.OpCode == DnOpCodes.Ldvirtftn)
                {
                    var methodRef = instr.Operand as IMethod;
                    if (methodRef != null)
                    {
                        var md = methodRef.ResolveMethodDef();
                        if (md != null && md.DeclaringType == declaringType &&
                            (md.IsPrivate || md.IsFamily || md.IsFamilyAndAssembly))
                        {
                            if (md.IsConstructor || md.IsStaticConstructor) return true;
                            if (md.IsVirtual || md.IsAbstract || md.HasOverrides) return true;
                            if (!IsPromotableMember(md, declaringType)) return true;
                        }
                    }
                }

                ITypeDefOrRef refType = null;
                var fieldR = instr.Operand as IField;
                if (fieldR != null) refType = fieldR.DeclaringType;
                var methodR = instr.Operand as IMethod;
                if (methodR != null && refType == null) refType = methodR.DeclaringType;
                var typeR = instr.Operand as ITypeDefOrRef;
                if (typeR != null && refType == null) refType = typeR;
                if (refType != null)
                {
                    var td = refType.ResolveTypeDef();
                    if (td != null)
                    {
                        var owner = td.DeclaringType;
                        while (owner != null)
                        {
                            if (owner == declaringType)
                            {
                                bool isNestedPrivate = td.IsNestedPrivate || td.IsNestedFamily ||
                                                       td.IsNestedFamilyAndAssembly;
                                if (isNestedPrivate && !IsPromotableMember(td, declaringType))
                                    return true;
                                break;
                            }
                            owner = owner.DeclaringType;
                        }
                    }
                }
            }
            return false;
        }

        private void PromoteMembersForRelocation(MethodDef method, TypeDef declaringType)
        {
            if (!method.HasBody) return;
            foreach (var instr in method.Body.Instructions)
            {
                if (instr.OpCode == DnOpCodes.Ldfld || instr.OpCode == DnOpCodes.Stfld ||
                    instr.OpCode == DnOpCodes.Ldsfld || instr.OpCode == DnOpCodes.Stsfld ||
                    instr.OpCode == DnOpCodes.Ldflda || instr.OpCode == DnOpCodes.Ldsflda)
                {
                    var fieldRef = instr.Operand as IField;
                    if (fieldRef != null)
                    {
                        var fd = fieldRef.ResolveFieldDef();
                        if (fd != null && fd.DeclaringType == declaringType &&
                            (fd.IsPrivate || fd.IsFamily || fd.IsFamilyAndAssembly) &&
                            IsPromotableMember(fd, declaringType))
                        {
                            try { fd.Access = DnFieldAttributes.Assembly; } catch { }
                        }
                    }
                }

                if (instr.OpCode == DnOpCodes.Call || instr.OpCode == DnOpCodes.Callvirt ||
                    instr.OpCode == DnOpCodes.Ldftn || instr.OpCode == DnOpCodes.Ldvirtftn)
                {
                    var methodRef = instr.Operand as IMethod;
                    if (methodRef != null)
                    {
                        var md = methodRef.ResolveMethodDef();
                        if (md != null && md.DeclaringType == declaringType &&
                            (md.IsPrivate || md.IsFamily || md.IsFamilyAndAssembly) &&
                            !md.IsConstructor && !md.IsStaticConstructor &&
                            !md.IsVirtual && !md.IsAbstract && !md.HasOverrides &&
                            IsPromotableMember(md, declaringType))
                        {
                            try { md.Access = DnMethodAttributes.Assembly; } catch { }
                        }
                    }
                }

                ITypeDefOrRef refType = null;
                var fieldR = instr.Operand as IField;
                if (fieldR != null) refType = fieldR.DeclaringType;
                var methodR = instr.Operand as IMethod;
                if (methodR != null && refType == null) refType = methodR.DeclaringType;
                var typeR = instr.Operand as ITypeDefOrRef;
                if (typeR != null && refType == null) refType = typeR;
                if (refType != null)
                {
                    var td = refType.ResolveTypeDef();
                    if (td != null)
                    {
                        var owner = td.DeclaringType;
                        while (owner != null)
                        {
                            if (owner == declaringType)
                            {
                                if ((td.IsNestedPrivate || td.IsNestedFamily ||
                                     td.IsNestedFamilyAndAssembly) &&
                                    IsPromotableMember(td, declaringType))
                                {
                                    try { td.Attributes = (td.Attributes &
                                        ~DnTypeAttributes.VisibilityMask) |
                                        DnTypeAttributes.NestedAssembly; }
                                    catch { }
                                }
                                break;
                            }
                            owner = owner.DeclaringType;
                        }
                    }
                }
            }
        }

        private bool IsReflectionPreserved(MethodDef m)
        {
            if (m == null) return false;

            if (engine.reflectionNames.Contains(m.Name)) return true;

            if (engine.reflectionNames.Contains(m.FullName)) return true;
            return false;
        }

        private HashSet<MethodDef> BuildResidualRefSet(ModuleDef module,
            List<(MethodDef orig, MethodDef host, TypeDef origType)> relocated)
        {

            var origSet = new HashSet<MethodDef>();
            foreach (var (orig, _, _) in relocated)
                origSet.Add(orig);

            var referenced = new HashSet<MethodDef>();

            foreach (TypeDef t in module.GetTypes())
            {

                foreach (MethodDef m in t.Methods)
                {
                    if (!m.HasBody) continue;
                    foreach (var instr in m.Body.Instructions)
                    {
                        var md = TryResolveMethodDef(instr.Operand);
                        if (md != null && origSet.Contains(md))
                            referenced.Add(md);
                    }
                }

                foreach (var ca in t.CustomAttributes)
                    CheckCustomAttr(ca, origSet, referenced);

                foreach (var f in t.Fields)
                    foreach (var ca in f.CustomAttributes)
                        CheckCustomAttr(ca, origSet, referenced);

                foreach (MethodDef m in t.Methods)
                    foreach (var ca in m.CustomAttributes)
                        CheckCustomAttr(ca, origSet, referenced);
            }

            return referenced;
        }

        private static MethodDef TryResolveMethodDef(object operand)
        {
            var md = operand as MethodDef;
            if (md != null) return md;
            var mref = operand as MemberRef;
            if (mref != null)
            {
                try { return mref.ResolveMethod(); } catch { }
            }
            return null;
        }

        private static void CheckCustomAttr(CustomAttribute ca,
            HashSet<MethodDef> origSet, HashSet<MethodDef> referenced)
        {
            if (ca == null || ca.Constructor == null) return;
            var md = ca.Constructor as MethodDef;
            if (md != null && origSet.Contains(md))
                referenced.Add(md);
        }

        private MethodDef TryRelocate(ModuleDef module, MethodDef orig, TypeDef origType, TypeDef hostType)
        {
            try
            {
                PromoteMembersForRelocation(orig, origType);

                bool wasInstance = !orig.IsStatic;

                var paramTypes = new List<TypeSig>();
                if (wasInstance)
                    paramTypes.Add(origType.ToTypeSig());
                foreach (var p in orig.MethodSig.Params)
                    paramTypes.Add(p);

                TypeSig retType = orig.MethodSig.RetType;
                var newSig = MethodSig.CreateStatic(retType, paramTypes.ToArray());

                var hostMethod = new MethodDefUser(engine.MakeName(),
                    newSig,
                    DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                    DnMethodAttributes.Assembly | DnMethodAttributes.Static |
                    DnMethodAttributes.HideBySig);

                hostMethod.Body = new CilBody();
                hostMethod.Body.InitLocals = orig.Body.InitLocals;

                var localMap = new Dictionary<Local, Local>();
                foreach (var local in orig.Body.Variables)
                {
                    var nl = new Local(local.Type);
                    hostMethod.Body.Variables.Add(nl);
                    localMap[local] = nl;
                }

                var instrMap = new Dictionary<Instruction, Instruction>();
                foreach (var origInstr in orig.Body.Instructions)
                {
                    var clone = new Instruction(origInstr.OpCode);

                    var asLocal = origInstr.Operand as Local;
                    if (asLocal != null && localMap.ContainsKey(asLocal))
                    {
                        clone.Operand = localMap[asLocal];
                    }

                    else if (wasInstance && origInstr.Operand is Parameter)
                    {
                        var origParam = (Parameter)origInstr.Operand;

                        clone.Operand = hostMethod.Parameters[origParam.Index];
                    }
                    else
                    {
                        clone.Operand = origInstr.Operand;
                    }

                    instrMap[origInstr] = clone;
                    hostMethod.Body.Instructions.Add(clone);
                }

                if (wasInstance)
                {
                    foreach (var clone in hostMethod.Body.Instructions)
                    {

                        _ = clone;
                    }
                }

                foreach (var clone in hostMethod.Body.Instructions)
                {
                    var asInstr = clone.Operand as Instruction;
                    if (asInstr != null)
                    {
                        Instruction mapped;
                        if (instrMap.TryGetValue(asInstr, out mapped))
                            clone.Operand = mapped;
                        continue;
                    }
                    var asSwitch = clone.Operand as Instruction[];
                    if (asSwitch != null)
                    {
                        var newTargets = new Instruction[asSwitch.Length];
                        for (int i = 0; i < asSwitch.Length; i++)
                        {
                            Instruction mapped2;
                            newTargets[i] = instrMap.TryGetValue(asSwitch[i], out mapped2)
                                ? mapped2 : asSwitch[i];
                        }
                        clone.Operand = newTargets;
                    }
                }

                foreach (var eh in orig.Body.ExceptionHandlers)
                {
                    var newEh = new ExceptionHandler(eh.HandlerType);
                    if (eh.TryStart != null)
                    {
                        if (!instrMap.ContainsKey(eh.TryStart)) return null;
                        newEh.TryStart = instrMap[eh.TryStart];
                    }
                    if (eh.TryEnd != null)
                    {
                        if (!instrMap.ContainsKey(eh.TryEnd)) return null;
                        newEh.TryEnd = instrMap[eh.TryEnd];
                    }
                    if (eh.HandlerStart != null)
                    {
                        if (!instrMap.ContainsKey(eh.HandlerStart)) return null;
                        newEh.HandlerStart = instrMap[eh.HandlerStart];
                    }
                    if (eh.HandlerEnd != null)
                    {
                        if (!instrMap.ContainsKey(eh.HandlerEnd)) return null;
                        newEh.HandlerEnd = instrMap[eh.HandlerEnd];
                    }
                    if (eh.FilterStart != null)
                    {
                        if (!instrMap.ContainsKey(eh.FilterStart)) return null;
                        newEh.FilterStart = instrMap[eh.FilterStart];
                    }
                    newEh.CatchType = eh.CatchType;
                    hostMethod.Body.ExceptionHandlers.Add(newEh);
                }

                hostType.Methods.Add(hostMethod);
                engine.injectedMethods.Add(hostMethod);

                return hostMethod;
            }
            catch
            {
                return null;
            }
        }

        private void RewriteCallsites(ModuleDef module, Dictionary<MethodDef, MethodDef> relocMap)
        {
            foreach (TypeDef t in module.GetTypes())
            {
                if (engine.injectedTypes.Contains(t)) continue;
                foreach (MethodDef m in t.Methods)
                {
                    if (!m.HasBody) continue;
                    bool changed = false;
                    foreach (var instr in m.Body.Instructions)
                    {
                        Code c = instr.OpCode.Code;
                        if (c != Code.Call && c != Code.Callvirt &&
                            c != Code.Ldftn && c != Code.Ldvirtftn)
                            continue;

                        var operandMethod = instr.Operand as MethodDef;
                        if (operandMethod == null) continue;

                        MethodDef hostMethod;
                        if (!relocMap.TryGetValue(operandMethod, out hostMethod)) continue;

                        instr.Operand = hostMethod;
                        if (instr.OpCode == DnOpCodes.Callvirt)
                            instr.OpCode = DnOpCodes.Call;
                        else if (instr.OpCode == DnOpCodes.Ldvirtftn)
                            instr.OpCode = DnOpCodes.Ldftn;
                        changed = true;
                    }
                    if (changed)
                    {
                        try
                        {
                            m.Body.SimplifyBranches();
                            m.Body.OptimizeBranches();
                        }
                        catch { }
                    }
                }
            }
        }

        private void ReplaceWithThunk(ModuleDef module, MethodDef orig, MethodDef hostMethod)
        {
            orig.Body.Instructions.Clear();
            orig.Body.ExceptionHandlers.Clear();
            orig.Body.Variables.Clear();

            var il = orig.Body.Instructions;
            bool wasInstance = !orig.IsStatic;

            int paramCount = orig.Parameters.Count;
            for (int i = 0; i < paramCount; i++)
            {
                switch (i)
                {
                    case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                    case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                    case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                    case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                    default: il.Add(Instruction.Create(DnOpCodes.Ldarg_S, orig.Parameters[i])); break;
                }
            }
            il.Add(Instruction.Create(DnOpCodes.Call, hostMethod));
            il.Add(Instruction.Create(DnOpCodes.Ret));
        }

        private void ReplaceWithOpaqueThunk(MethodDef orig, MethodDef hostMethod)
        {
            orig.Body.Instructions.Clear();
            orig.Body.ExceptionHandlers.Clear();
            orig.Body.Variables.Clear();

            var int32Sig = encContainer.Module.CorLibTypes.Int32;
            var junkLocal = new Local(int32Sig);
            orig.Body.Variables.Add(junkLocal);
            orig.Body.InitLocals = true;

            var il = orig.Body.Instructions;

            var tickCount = encContainer.Module.Import(typeof(System.Environment).GetProperty("TickCount").GetGetMethod());
            var neverTakenLabel = Instruction.Create(DnOpCodes.Nop);

            il.Add(Instruction.Create(DnOpCodes.Call, tickCount));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, neverTakenLabel));

            int paramCount = orig.Parameters.Count;
            for (int i = 0; i < paramCount; i++)
                EmitLdarg(il, orig, i);
            il.Add(Instruction.Create(DnOpCodes.Call, hostMethod));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(neverTakenLabel);
            for (int i = 0; i < paramCount; i++)
                EmitDummyArg(il, hostMethod, i);
            il.Add(Instruction.Create(DnOpCodes.Call, hostMethod));
            il.Add(Instruction.Create(DnOpCodes.Ret));
        }

        private static void EmitLdarg(IList<Instruction> il, MethodDef m, int i)
        {
            switch (i)
            {
                case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                default: il.Add(Instruction.Create(DnOpCodes.Ldarg_S, m.Parameters[i])); break;
            }
        }

        private static void EmitDummyArg(IList<Instruction> il,
            MethodDef hostMethod, int paramIdx)
        {

            TypeSig ts = null;
            try
            {
                if (paramIdx < hostMethod.Parameters.Count)
                    ts = hostMethod.Parameters[paramIdx].Type;
            }
            catch { }

            if (ts == null || IsRefOrObjectSig(ts))
            {
                il.Add(Instruction.Create(DnOpCodes.Ldnull));
            }
            else
            {

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            }
        }

        private static bool IsRefOrObjectSig(TypeSig ts)
        {
            if (ts == null) return true;
            var et = ts.ElementType;
            return et == ElementType.Object || et == ElementType.String ||
                   et == ElementType.Class || et == ElementType.ValueType;
        }

        private void BuildEncInfrastructure(ModuleDef module)
        {
            encArrayFields = new List<FieldDef>();
            encArrayData = new List<int[]>();
            encArrayShuffles = new List<int[]>();
            encArrayPtrs = new int[ENC_ARRAY_POOL];
            xorKeyFields = new List<FieldDef>();
            xorKeyValues = new int[8];

            encContainer = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            encContainer.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(encContainer);
            engine.injectedTypes.Add(encContainer);

            for (int k = 0; k < 8; k++)
            {
                xorKeyValues[k] = rng.Next(100000, int.MaxValue / 2);
                var kf = new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                encContainer.Fields.Add(kf);
                xorKeyFields.Add(kf);
            }

            for (int a = 0; a < ENC_ARRAY_POOL; a++)
            {
                var arrField = new FieldDefUser(engine.MakeName(),
                    new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                encContainer.Fields.Add(arrField);
                encArrayFields.Add(arrField);

                var data = new int[ENC_ARRAY_SIZE];
                for (int i = 0; i < ENC_ARRAY_SIZE; i++)
                    data[i] = rng.Next(int.MinValue, int.MaxValue);
                encArrayData.Add(data);

                var shuffle = new int[ENC_ARRAY_SIZE];
                for (int i = 0; i < ENC_ARRAY_SIZE; i++) shuffle[i] = i;
                for (int i = ENC_ARRAY_SIZE - 1; i > 0; i--)
                {
                    int j = rng.Next(0, i + 1);
                    int tmp = shuffle[i]; shuffle[i] = shuffle[j]; shuffle[j] = tmp;
                }
                encArrayShuffles.Add(shuffle);
                encArrayPtrs[a] = 0;
            }
        }

        private int AllocSlot(int arrayIdx)
        {
            if (encArrayPtrs[arrayIdx] >= ENC_ARRAY_SIZE) return -1;
            return encArrayShuffles[arrayIdx][encArrayPtrs[arrayIdx]++];
        }

        private void EncryptMethodBody(ModuleDef module, MethodDef method)
        {
            if (!method.HasBody) return;
            var il = method.Body.Instructions;

            for (int i = 0; i < il.Count; i++)
            {
                if (!engine.IsIntLoad(il[i])) continue;
                int val = engine.ExtractInt(il[i]);
                if (val == int.MinValue) continue;
                if (val >= -1 && val <= 8) continue;
                if (rng.Next(0, 3) != 0) continue;

                var replacement = BuildXorRetrieval(val);
                if (replacement == null || replacement.Count == 0) continue;

                il[i].OpCode = replacement[0].OpCode;
                il[i].Operand = replacement[0].Operand;
                for (int j = 1; j < replacement.Count; j++)
                    il.Insert(i + j, replacement[j]);
                i += replacement.Count - 1;
            }
        }

        private List<Instruction> BuildXorRetrieval(int target)
        {
            int a = rng.Next(0, ENC_ARRAY_POOL);
            int s1 = AllocSlot(a);
            int s2 = AllocSlot(a);
            if (s1 < 0 || s2 < 0) return BuildFallback(target);

            encArrayData[a][s2] = encArrayData[a][s1] ^ target;

            var insts = new List<Instruction>();
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, encArrayFields[a]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, s1));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.Ldsfld, encArrayFields[a]));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, s2));
            insts.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private List<Instruction> BuildFallback(int target)
        {
            var insts = new List<Instruction>();
            int k = rng.Next(int.MinValue, int.MaxValue);
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k));
            insts.Add(Instruction.Create(DnOpCodes.Ldc_I4, k ^ target));
            insts.Add(Instruction.Create(DnOpCodes.Xor));
            return insts;
        }

        private void BuildEncContainerCctor(ModuleDef module)
        {
            var cctor = new MethodDefUser(".cctor",
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Private | DnMethodAttributes.Static |
                DnMethodAttributes.HideBySig | DnMethodAttributes.SpecialName |
                DnMethodAttributes.RTSpecialName);

            cctor.Body = new CilBody();
            var il = cctor.Body.Instructions;

            for (int k = 0; k < 8; k++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, xorKeyValues[k]));
                il.Add(Instruction.Create(DnOpCodes.Stsfld, xorKeyFields[k]));
            }

            for (int a = 0; a < ENC_ARRAY_POOL; a++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, ENC_ARRAY_SIZE));
                il.Add(Instruction.Create(DnOpCodes.Newarr,
                    module.CorLibTypes.Int32.TypeDefOrRef));

                for (int i = 0; i < ENC_ARRAY_SIZE; i++)
                {
                    il.Add(Instruction.Create(DnOpCodes.Dup));
                    il.Add(engine.LoadInt(i));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, encArrayData[a][i]));
                    il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
                }

                il.Add(Instruction.Create(DnOpCodes.Stsfld, encArrayFields[a]));
            }

            il.Add(Instruction.Create(DnOpCodes.Ret));
            encContainer.Methods.Add(cctor);
            engine.injectedMethods.Add(cctor);
        }
    }
}
