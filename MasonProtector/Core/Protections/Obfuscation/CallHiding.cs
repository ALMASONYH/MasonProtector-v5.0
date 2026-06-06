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
    internal class CallHidingProtection
    {
        private Obfuscation engine;
        private Random rng;

        private const int TRAMPOLINE_POOL = 18;
        private List<TypeDef> trampolineTypes;
        private Dictionary<string, MethodDef> trampolineCache;
        private int trampolineCount;

        internal CallHidingProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyCallHiding(ModuleDef module)
        {
            trampolineTypes = new List<TypeDef>();
            trampolineCache = new Dictionary<string, MethodDef>();
            trampolineCount = 0;

            for (int i = 0; i < TRAMPOLINE_POOL; i++)
            {
                var trampType = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                trampType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                module.Types.Add(trampType);
                engine.injectedTypes.Add(trampType);

                for (int d = 0; d < rng.Next(6, 14); d++)
                {
                    trampType.Fields.Add(new FieldDefUser(engine.MakeName(),
                        new FieldSig(module.CorLibTypes.Int32),
                        DnFieldAttributes.Private | DnFieldAttributes.Static));
                }

                for (int f = 0; f < rng.Next(4, 10); f++)
                {
                    var fakeMethod = BuildFakeTrampoline(module);
                    trampType.Methods.Add(fakeMethod);
                    engine.injectedMethods.Add(fakeMethod);
                }

                trampolineTypes.Add(trampType);
            }

            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    if (engine.MethodHasAsyncOrIteratorAttribute(method)) continue;
                    try
                    {
                        HideMethodCalls(module, method);
                    }
                    catch { }
                }
            }
        }

        private bool IsInstanceTargetSafe(ModuleDef module, IMethod target, out TypeSig receiverTypeSig)
        {
            receiverTypeSig = null;
            if (target == null) return false;
            var declType = target.DeclaringType;
            if (declType == null) return false;
            TypeDef td = null;
            try { td = declType.ResolveTypeDef(); } catch { }
            if (td != null)
            {
                if (td.IsValueType) return false;
                if (td.HasGenericParameters) return false;
                if (td.Module != null && td.Module != module)
                {
                    string extNs = td.Namespace?.String ?? "";
                    string extNm = td.Name?.String ?? "";
                    if (!IsKnownSafeExternalType(extNs, extNm)) return false;
                }
            }
            else
            {
                var tr = declType as TypeRef;
                if (tr == null) return false;
                string ns = tr.Namespace?.String ?? "";
                string nm = tr.Name?.String ?? "";
                if (nm.Contains("`")) return false;
                if (IsKnownValueType(ns, nm)) return false;
                if (!IsKnownSafeExternalType(ns, nm)) return false;
            }
            try { receiverTypeSig = module.Import(declType.ToTypeSig()); }
            catch { return false; }
            return receiverTypeSig != null;
        }

        private static bool IsKnownSafeExternalType(string ns, string nm)
        {
            if (ns == "System.Text" && (nm == "StringBuilder" || nm == "Encoding" || nm == "UTF8Encoding"))
                return true;
            if (ns == "System.IO" && (nm == "StreamReader" || nm == "StreamWriter" ||
                nm == "MemoryStream" || nm == "StringReader" || nm == "StringWriter" ||
                nm == "BinaryReader" || nm == "BinaryWriter"))
                return true;
            if (ns == "System.Collections.Generic" &&
                (nm == "List`1" || nm == "Dictionary`2" || nm == "HashSet`1" || nm == "Queue`1" || nm == "Stack`1"))
                return true;
            if (ns == "System.Collections" && (nm == "ArrayList" || nm == "Hashtable"))
                return true;
            return false;
        }

        private static bool IsKnownValueType(string ns, string nm)
        {
            if (ns == "System")
            {
                switch (nm)
                {
                    case "Int32": case "Int64": case "Int16": case "Byte": case "SByte":
                    case "UInt32": case "UInt64": case "UInt16": case "Char": case "Boolean":
                    case "Single": case "Double": case "Decimal": case "IntPtr": case "UIntPtr":
                    case "DateTime": case "TimeSpan": case "Guid": case "DateTimeOffset":
                    case "Nullable`1": case "ValueType": case "Enum":
                        return true;
                }
            }
            if (ns == "System.Drawing")
            {
                switch (nm)
                {
                    case "Color": case "Point": case "PointF": case "Size": case "SizeF":
                    case "Rectangle": case "RectangleF":
                        return true;
                }
            }
            if (ns == "System.Windows.Forms")
            {
                switch (nm)
                {
                    case "Padding": case "Message": case "TableLayoutPanelCellPosition":
                        return true;
                }
            }
            return false;
        }

        private void HideMethodCalls(ModuleDef module, MethodDef method)
        {
            var il = method.Body.Instructions;
            for (int i = 0; i < il.Count; i++)
            {
                bool isCall     = il[i].OpCode == DnOpCodes.Call;
                bool isCallvirt = il[i].OpCode == DnOpCodes.Callvirt;
                bool isNewObj   = il[i].OpCode == DnOpCodes.Newobj;
                if (!isCall && !isCallvirt && !isNewObj) continue;

                if (i > 0 && il[i - 1].OpCode == DnOpCodes.Constrained) continue;

                var target = il[i].Operand as IMethod;
                if (target == null) continue;
                if (engine.IsCompilerInfrastructureCall(target)) continue;
                if (engine.IsCompilerGeneratedOwner(target)) continue;

                if (!isNewObj && (target.Name == ".ctor" || target.Name == ".cctor")) continue;

                MethodDef mdTarget = target as MethodDef;
                if (mdTarget != null && engine.injectedMethods.Contains(mdTarget)) continue;

                if (mdTarget != null && !isNewObj)
                {
                    bool isAccessible = mdTarget.IsPublic ||
                        mdTarget.IsAssembly || mdTarget.IsFamilyOrAssembly;
                    if (!isAccessible) continue;
                }

                var sig = target.MethodSig;
                if (sig == null) continue;
                if (sig.GenParamCount > 0) continue;

                bool hasBadParam = false;
                foreach (var p in sig.Params) { if (p == null || p.IsByRef || p.IsPointer) { hasBadParam = true; break; } }
                if (hasBadParam) continue;
                if (!isNewObj && sig.RetType != null && (sig.RetType.IsByRef || sig.RetType.IsPointer)) continue;

                bool hasThis = sig.HasThis && !isNewObj;
                TypeSig receiverTypeSig = null;

                if (isNewObj)
                {
                    if (!engine.IsConfirmedReferenceTypeCtor(target.DeclaringType)) continue;
                    if (sig.Params.Count > 4) continue;
                }
                else if (hasThis)
                {
                    if (!IsInstanceTargetSafe(module, target, out receiverTypeSig)) continue;
                    if (sig.Params.Count + 1 > 4) continue;
                }
                else
                {
                    if (sig.Params.Count > 4) continue;
                }

                if (!engine.LevelChance(0.5, 0.8, 1.0)) continue;

                bool useCallvirt = hasThis && isCallvirt;
                string key = "CH:" + (isNewObj ? "NEW:" : (useCallvirt ? "CV:" : (hasThis ? "CI:" : "S:"))) + target.FullName;
                MethodDef trampoline;
                if (!trampolineCache.TryGetValue(key, out trampoline))
                {
                    trampoline = BuildTrampoline(module, target, hasThis, receiverTypeSig, useCallvirt, isNewObj);
                    if (trampoline == null) continue;

                    var host = trampolineTypes[trampolineCount % TRAMPOLINE_POOL];
                    host.Methods.Add(trampoline);
                    engine.injectedMethods.Add(trampoline);
                    trampolineCache[key] = trampoline;
                    trampolineCount++;
                }

                il[i].OpCode = DnOpCodes.Call;
                il[i].Operand = trampoline;
            }
        }

        private MethodDef BuildTrampoline(ModuleDef module, IMethod target,
            bool hasThis = false, TypeSig receiverTypeSig = null, bool useCallvirt = false,
            bool isNewObj = false)
        {
            var sig = target.MethodSig;
            if (sig == null) return null;

            TypeSig[] trampParams;
            if (hasThis && receiverTypeSig != null)
            {
                trampParams = new TypeSig[1 + sig.Params.Count];
                trampParams[0] = receiverTypeSig;
                for (int pi = 0; pi < sig.Params.Count; pi++)
                    trampParams[pi + 1] = sig.Params[pi];
            }
            else
            {
                trampParams = sig.Params.ToArray();
            }

            TypeSig trampRetType;
            if (isNewObj)
            {
                if (target.DeclaringType == null) return null;
                try
                {
                    var imported = module.Import(target.DeclaringType);
                    var asDefOrRef = imported as ITypeDefOrRef;
                    if (asDefOrRef == null) return null;
                    trampRetType = asDefOrRef.ToTypeSig();
                }
                catch { return null; }
                if (trampRetType == null) return null;
            }
            else
            {
                trampRetType = sig.RetType;
            }

            var trampolineSig = MethodSig.CreateStatic(trampRetType, trampParams);
            var method = new MethodDefUser(engine.MakeName(),
                trampolineSig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            var il = method.Body.Instructions;

            int junkPattern = rng.Next(0, 6);
            switch (junkPattern)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Pop));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Pop));
                    break;
                case 2:
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Pop));
                    break;
                case 3:
                    il.Add(Instruction.Create(DnOpCodes.Nop));
                    il.Add(Instruction.Create(DnOpCodes.Nop));
                    il.Add(Instruction.Create(DnOpCodes.Nop));
                    break;
                case 4:
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Pop));
                    break;
                default:
                    break;
            }

            bool doubleWrap = rng.Next(0, 3) == 0;

            if (doubleWrap)
            {
                var innerTramp = BuildInnerTrampoline(module, target, hasThis, receiverTypeSig, useCallvirt, isNewObj);
                if (innerTramp != null)
                {
                    var host = trampolineTypes[trampolineCount % TRAMPOLINE_POOL];
                    host.Methods.Add(innerTramp);
                    engine.injectedMethods.Add(innerTramp);

                    var tickW = module.Import(typeof(Environment).GetProperty("TickCount").GetGetMethod());
                    Instruction deadW = Instruction.Create(DnOpCodes.Ldnull);
                    il.Add(Instruction.Create(DnOpCodes.Call, tickW));
                    il.Add(Instruction.Create(DnOpCodes.Dup));
                    il.Add(Instruction.Create(DnOpCodes.Dup));
                    il.Add(Instruction.Create(DnOpCodes.Mul));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Brtrue, deadW));

                    for (int p = 0; p < trampParams.Length; p++)
                    {
                        switch (p)
                        {
                            case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                            case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                            case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                            case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                        }
                    }

                    il.Add(Instruction.Create(DnOpCodes.Call, innerTramp));
                    il.Add(Instruction.Create(DnOpCodes.Ret));

                    il.Add(deadW);
                    il.Add(Instruction.Create(DnOpCodes.Throw));
                    return method;
                }
            }

            var tickD = module.Import(typeof(Environment).GetProperty("TickCount").GetGetMethod());
            Instruction deadD = Instruction.Create(DnOpCodes.Ldnull);
            il.Add(Instruction.Create(DnOpCodes.Call, tickD));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, deadD));

            for (int p = 0; p < trampParams.Length; p++)
            {
                switch (p)
                {
                    case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                    case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                    case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                    case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                }
            }

            OpCode finalCallOp;
            if (isNewObj) finalCallOp = DnOpCodes.Newobj;
            else if (hasThis && useCallvirt) finalCallOp = DnOpCodes.Callvirt;
            else finalCallOp = DnOpCodes.Call;
            il.Add(Instruction.Create(finalCallOp, module.Import(target)));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(deadD);
            il.Add(Instruction.Create(DnOpCodes.Throw));
            return method;
        }

        private MethodDef BuildInnerTrampoline(ModuleDef module, IMethod target,
            bool hasThis = false, TypeSig receiverTypeSig = null, bool useCallvirt = false,
            bool isNewObj = false)
        {
            var sig = target.MethodSig;
            if (sig == null) return null;

            TypeSig innerRetType;
            if (isNewObj)
            {
                if (target.DeclaringType == null) return null;
                try
                {
                    var imported = module.Import(target.DeclaringType);
                    var asDefOrRef = imported as ITypeDefOrRef;
                    if (asDefOrRef == null) return null;
                    innerRetType = asDefOrRef.ToTypeSig();
                }
                catch { return null; }
                if (innerRetType == null) return null;
            }
            else
            {
                innerRetType = sig.RetType;
            }

            TypeSig[] innerParams;
            if (hasThis && receiverTypeSig != null)
            {
                innerParams = new TypeSig[1 + sig.Params.Count];
                innerParams[0] = receiverTypeSig;
                for (int pi = 0; pi < sig.Params.Count; pi++)
                    innerParams[pi + 1] = sig.Params[pi];
            }
            else
            {
                innerParams = sig.Params.ToArray();
            }

            var innerSig = MethodSig.CreateStatic(innerRetType, innerParams);
            var method = new MethodDefUser(engine.MakeName(),
                innerSig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Nop));

            var tickI = module.Import(typeof(Environment).GetProperty("TickCount").GetGetMethod());
            Instruction deadI = Instruction.Create(DnOpCodes.Ldnull);
            il.Add(Instruction.Create(DnOpCodes.Call, tickI));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, deadI));

            for (int p = 0; p < innerParams.Length; p++)
            {
                switch (p)
                {
                    case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                    case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                    case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                    case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                }
            }

            OpCode innerCallOp;
            if (isNewObj) innerCallOp = DnOpCodes.Newobj;
            else if (hasThis && useCallvirt) innerCallOp = DnOpCodes.Callvirt;
            else innerCallOp = DnOpCodes.Call;
            il.Add(Instruction.Create(innerCallOp, module.Import(target)));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(deadI);
            il.Add(Instruction.Create(DnOpCodes.Throw));
            return method;
        }

        private MethodDef BuildFakeTrampoline(ModuleDef module)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32, module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }
    }
}

