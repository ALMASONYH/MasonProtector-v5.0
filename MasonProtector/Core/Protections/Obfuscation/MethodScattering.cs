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
    internal class MethodScatteringProtection
    {
        private Obfuscation engine;
        private Random rng;

        private const int SCATTER_HOST_COUNT = 24;
        private const int SCATTER_BRIDGE_COUNT = 36;
        private const int SCATTER_FAKE_COUNT = 32;
        private const int SCATTER_FIELD_NOISE = 48;
        private const int SCATTER_DECOY_TYPE_COUNT = 14;

        private List<TypeDef> scatterHosts;
        private List<MethodDef> bridgeMethods;
        private List<TypeDef> decoyTypes;

        private HashSet<TypeDef> serializableTypes;

        internal MethodScatteringProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyMethodScattering(ModuleDef module, TypeDef modType)
        {
            scatterHosts = new List<TypeDef>();
            bridgeMethods = new List<MethodDef>();
            decoyTypes = new List<TypeDef>();
            serializableTypes = BuildSerializableSet(module);

            CreateScatterHosts(module);
            CreateDecoyTypes(module);
            InjectFieldNoise(module);

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

            foreach (TypeDef type in module.GetTypes().ToList())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                if (engine.injectedTypes.Contains(type)) continue;
                foreach (MethodDef method in type.Methods.ToList())
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    if (method.IsConstructor || method.IsStaticConstructor) continue;
                    if (method == module.EntryPoint) continue;
                    if (method.Parameters.Count > 4) continue;
                    if (method.MethodSig == null) continue;
                    if (method.MethodSig.RetType == null) continue;
                    if (engine.MethodHasAsyncOrIteratorAttribute(method)) continue;

                    if (!method.IsStatic)
                    {
                        if (method.IsVirtual || method.IsAbstract || method.HasOverrides) continue;
                        if (type.IsValueType) continue;
                        if (addressTakenInstanceMethods.Contains(method)) continue;
                    }

                    if (HasUnpromotableAccess(method, type)) continue;

                    if (!IsSafeMethodSig(method.MethodSig)) continue;

                    if (HasUnsafeBodyOps(method)) continue;

                    if (!engine.LevelChance(0.4, 0.7, 1.0)) continue;

                    try
                    {
                        ScatterMethod(module, method, type);
                    }
                    catch { }
                }
            }

            CreateBridgeMethods(module);
            CreateFakeMethods(module);
            InjectDecoyMethodNoise(module);
        }

        private MethodDef ScatterMethod(ModuleDef module, MethodDef method, TypeDef declaringType)
        {
            PromoteMembersForRelocation(method, declaringType);

            bool wasInstance = !method.IsStatic;

            var paramTypes = new List<TypeSig>();
            if (wasInstance)
                paramTypes.Add(declaringType.ToTypeSig());
            foreach (var p in method.MethodSig.Params)
                paramTypes.Add(p);

            var newSig = MethodSig.CreateStatic(method.MethodSig.RetType, paramTypes.ToArray());
            if (newSig == null) return null;

            var host = scatterHosts[rng.Next(scatterHosts.Count)];

            var scattered = new MethodDefUser(engine.MakeName(),
                newSig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            scattered.Body = new CilBody();
            scattered.Body.InitLocals = method.Body.InitLocals;

            var localMap = new Dictionary<Local, Local>();
            foreach (var local in method.Body.Variables)
            {
                var nl = new Local(local.Type);
                scattered.Body.Variables.Add(nl);
                localMap[local] = nl;
            }

            var instrMap = new Dictionary<Instruction, Instruction>();
            foreach (var orig in method.Body.Instructions)
            {
                var clone = new Instruction(orig.OpCode);

                var asLocal = orig.Operand as Local;
                if (asLocal != null && localMap.ContainsKey(asLocal))
                {
                    clone.Operand = localMap[asLocal];
                }
                else if (wasInstance && orig.Operand is Parameter)
                {
                    var origParam = (Parameter)orig.Operand;
                    if (origParam.Index < scattered.Parameters.Count)
                        clone.Operand = scattered.Parameters[origParam.Index];
                    else
                        clone.Operand = orig.Operand;
                }
                else
                {
                    clone.Operand = orig.Operand;
                }

                instrMap[orig] = clone;
                scattered.Body.Instructions.Add(clone);
            }

            foreach (var clone in scattered.Body.Instructions)
            {
                var asInstr = clone.Operand as Instruction;
                if (asInstr != null && instrMap.ContainsKey(asInstr))
                {
                    clone.Operand = instrMap[asInstr];
                }
                else
                {
                    var asInstrArr = clone.Operand as Instruction[];
                    if (asInstrArr != null)
                    {
                        var newTargets = new Instruction[asInstrArr.Length];
                        for (int t = 0; t < asInstrArr.Length; t++)
                        {
                            Instruction mapped;
                            newTargets[t] = instrMap.TryGetValue(asInstrArr[t], out mapped)
                                ? mapped : asInstrArr[t];
                        }
                        clone.Operand = newTargets;
                    }
                }
            }

            foreach (var eh in method.Body.ExceptionHandlers)
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
                scattered.Body.ExceptionHandlers.Add(newEh);
            }

            host.Methods.Add(scattered);
            engine.injectedMethods.Add(scattered);

            method.Body.Instructions.Clear();
            method.Body.ExceptionHandlers.Clear();
            method.Body.Variables.Clear();

            var il = method.Body.Instructions;
            for (int p = 0; p < method.Parameters.Count; p++)
            {
                switch (p)
                {
                    case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                    case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                    case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                    case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                    default: il.Add(Instruction.Create(DnOpCodes.Ldarg_S, method.Parameters[p])); break;
                }
            }
            il.Add(Instruction.Create(DnOpCodes.Call, scattered));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return scattered;
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
                                    try
                                    {
                                        td.Attributes = (td.Attributes &
                                            ~DnTypeAttributes.VisibilityMask) |
                                            DnTypeAttributes.NestedAssembly;
                                    }
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

        private bool IsPromotableMember(IMemberDef member, TypeDef ownerType)
        {
            if (member == null) return false;
            if (serializableTypes != null && serializableTypes.Contains(ownerType)) return false;
            if (MemberHasReflectionOrSerializationAttribute(member)) return false;
            if (engine.reflectionNames.Contains(member.Name)) return false;
            if (engine.reflectionNames.Contains(member.FullName)) return false;
            return true;
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

        private static bool IsSafeMethodSig(MethodSig sig)
        {
            if (sig == null) return false;
            if (!IsSafeTypeSig(sig.RetType)) return false;
            foreach (var p in sig.Params)
                if (!IsSafeTypeSig(p)) return false;
            return true;
        }

        private static bool HasUnsafeBodyOps(MethodDef method)
        {
            if (!method.HasBody) return false;
            foreach (var instr in method.Body.Instructions)
            {
                Code c = instr.OpCode.Code;
                if (c == Code.Calli || c == Code.Localloc || c == Code.Jmp) return true;
                if (instr.OpCode.OperandType == OperandType.InlineSig) return true;
            }
            return false;
        }

        private void CreateScatterHosts(ModuleDef module)
        {
            for (int h = 0; h < SCATTER_HOST_COUNT; h++)
            {
                var host = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                host.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                module.Types.Add(host);
                engine.injectedTypes.Add(host);
                scatterHosts.Add(host);

                for (int f = 0; f < rng.Next(3, 7); f++)
                {
                    TypeSig fieldType;
                    int t = rng.Next(0, 4);
                    if (t == 0) fieldType = module.CorLibTypes.Int32;
                    else if (t == 1) fieldType = module.CorLibTypes.Int64;
                    else if (t == 2) fieldType = module.CorLibTypes.Boolean;
                    else fieldType = module.CorLibTypes.Byte;

                    host.Fields.Add(new FieldDefUser(engine.MakeName(),
                        new FieldSig(fieldType),
                        DnFieldAttributes.Private | DnFieldAttributes.Static));
                }
            }
        }

        private void CreateDecoyTypes(ModuleDef module)
        {
            for (int d = 0; d < SCATTER_DECOY_TYPE_COUNT; d++)
            {
                var decoy = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                decoy.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed;
                module.Types.Add(decoy);
                engine.injectedTypes.Add(decoy);
                decoyTypes.Add(decoy);

                for (int f = 0; f < rng.Next(4, 10); f++)
                {
                    TypeSig ft;
                    int t = rng.Next(0, 5);
                    if (t == 0) ft = module.CorLibTypes.Int32;
                    else if (t == 1) ft = module.CorLibTypes.Int64;
                    else if (t == 2) ft = module.CorLibTypes.String;
                    else if (t == 3) ft = module.CorLibTypes.Boolean;
                    else ft = module.CorLibTypes.Double;

                    decoy.Fields.Add(new FieldDefUser(engine.MakeName(),
                        new FieldSig(ft),
                        DnFieldAttributes.Private | DnFieldAttributes.Static));
                }

                for (int m = 0; m < rng.Next(3, 7); m++)
                {
                    var fakeMethod = BuildDecoyComputeMethod(module);
                    decoy.Methods.Add(fakeMethod);
                    engine.injectedMethods.Add(fakeMethod);
                }
            }
        }

        private void InjectFieldNoise(ModuleDef module)
        {
            var allHosts = new List<TypeDef>();
            allHosts.AddRange(scatterHosts);
            allHosts.AddRange(decoyTypes);

            for (int i = 0; i < SCATTER_FIELD_NOISE; i++)
            {
                var host = allHosts[rng.Next(allHosts.Count)];
                TypeSig ft;
                int t = rng.Next(0, 5);
                if (t == 0) ft = module.CorLibTypes.Int32;
                else if (t == 1) ft = new SZArraySig(module.CorLibTypes.Int32);
                else if (t == 2) ft = module.CorLibTypes.Int64;
                else if (t == 3) ft = module.CorLibTypes.Byte;
                else ft = new SZArraySig(module.CorLibTypes.Byte);

                host.Fields.Add(new FieldDefUser(engine.MakeName(),
                    new FieldSig(ft),
                    DnFieldAttributes.Private | DnFieldAttributes.Static));
            }
        }

        private void CreateBridgeMethods(ModuleDef module)
        {
            for (int b = 0; b < SCATTER_BRIDGE_COUNT; b++)
            {
                var host = scatterHosts[rng.Next(scatterHosts.Count)];
                var bridge = BuildBridgeMethod(module);
                host.Methods.Add(bridge);
                engine.injectedMethods.Add(bridge);
                bridgeMethods.Add(bridge);
            }
        }

        private void CreateFakeMethods(ModuleDef module)
        {
            for (int f = 0; f < SCATTER_FAKE_COUNT; f++)
            {
                var host = scatterHosts[rng.Next(scatterHosts.Count)];
                var fake = BuildFakeScatterMethod(module);
                host.Methods.Add(fake);
                engine.injectedMethods.Add(fake);
            }
        }

        private void InjectDecoyMethodNoise(ModuleDef module)
        {
            for (int i = 0; i < rng.Next(6, 12); i++)
            {
                var host = scatterHosts[rng.Next(scatterHosts.Count)];
                var decoy = BuildDecoyComputeMethod(module);
                host.Methods.Add(decoy);
                engine.injectedMethods.Add(decoy);
            }
        }

        private MethodDef BuildBridgeMethod(ModuleDef module)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            for (int r = 0; r < rng.Next(4, 10); r++)
            {
                int op = rng.Next(0, 6);
                switch (op)
                {
                    case 0:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_2));
                        break;
                    case 1:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Not));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                        break;
                    case 2:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Add));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                        break;
                    case 3:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                        break;
                    case 4:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 16)));
                        il.Add(Instruction.Create(DnOpCodes.Shl));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_2));
                        break;
                    default:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                        break;
                }
            }

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }

        private MethodDef BuildFakeScatterMethod(ModuleDef module)
        {
            int paramCount = rng.Next(1, 4);
            var paramTypes = new List<TypeSig>();
            for (int p = 0; p < paramCount; p++)
                paramTypes.Add(module.CorLibTypes.Int32);

            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32, paramTypes.ToArray()),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            for (int r = 0; r < rng.Next(5, 12); r++)
            {
                int op = rng.Next(0, 5);
                switch (op)
                {
                    case 0:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                        break;
                    case 1:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Not));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                        break;
                    case 2:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Add));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                        break;
                    case 3:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 16)));
                        il.Add(Instruction.Create(DnOpCodes.Shl));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                        break;
                    default:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                        break;
                }
            }

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }

        private MethodDef BuildDecoyComputeMethod(ModuleDef module)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            for (int r = 0; r < rng.Next(6, 14); r++)
            {
                int op = rng.Next(0, 8);
                switch (op)
                {
                    case 0:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_2));
                        break;
                    case 1:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Not));
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                        il.Add(Instruction.Create(DnOpCodes.And));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_2));
                        break;
                    case 2:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Add));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                        break;
                    case 3:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                        break;
                    case 4:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_3));
                        break;
                    case 5:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 16)));
                        il.Add(Instruction.Create(DnOpCodes.Shl));
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                        il.Add(Instruction.Create(DnOpCodes.Or));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_2));
                        break;
                    case 6:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                        il.Add(Instruction.Create(DnOpCodes.Not));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                        break;
                    default:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_3));
                        il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
                        il.Add(Instruction.Create(DnOpCodes.Add));
                        il.Add(Instruction.Create(DnOpCodes.Stloc_3));
                        break;
                }
            }

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }
    }
}
