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
    internal class ReferenceProxyProtection
    {
        private Obfuscation engine;
        private Random rng;

        private const int DELEGATE_POOL_SIZE = 24;
        private List<TypeDef> proxyContainers;
        private Dictionary<string, MethodDef> proxyCache;
        private int totalProxied;

        internal ReferenceProxyProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyReferenceProxy(ModuleDef module)
        {
            proxyContainers = new List<TypeDef>();
            proxyCache = new Dictionary<string, MethodDef>();
            totalProxied = 0;

            for (int c = 0; c < DELEGATE_POOL_SIZE; c++)
            {
                var container = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                container.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                module.Types.Add(container);
                engine.injectedTypes.Add(container);

                for (int d = 0; d < rng.Next(6, 14); d++)
                {
                    container.Fields.Add(new FieldDefUser(engine.MakeName(),
                        new FieldSig(module.CorLibTypes.Int32),
                        DnFieldAttributes.Private | DnFieldAttributes.Static));
                }

                proxyContainers.Add(container);
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
                        ProxyMethodReferences(module, method);
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

        private void ProxyMethodReferences(ModuleDef module, MethodDef method)
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

                MethodDef mdCheck = target as MethodDef;
                if (mdCheck != null && engine.injectedMethods.Contains(mdCheck)) continue;

                if (mdCheck != null && !isNewObj)
                {
                    bool isAccessible = mdCheck.IsPublic ||
                        mdCheck.IsAssembly || mdCheck.IsFamilyOrAssembly;
                    if (!isAccessible) continue;
                }

                var targetSig = target.MethodSig;
                if (targetSig == null) continue;
                if (targetSig.GenParamCount > 0) continue;

                bool hasBadParam = false;
                foreach (var p in targetSig.Params) { if (p == null || p.IsByRef || p.IsPointer) { hasBadParam = true; break; } }
                if (hasBadParam) continue;
                if (!isNewObj && targetSig.RetType != null && (targetSig.RetType.IsByRef || targetSig.RetType.IsPointer)) continue;

                bool hasThis = targetSig.HasThis && !isNewObj;
                TypeSig receiverTypeSig = null;

                if (isNewObj)
                {
                    if (!engine.IsConfirmedReferenceTypeCtor(target.DeclaringType)) continue;
                    if (targetSig.Params.Count > 4) continue;
                }
                else if (hasThis)
                {
                    if (!IsInstanceTargetSafe(module, target, out receiverTypeSig)) continue;
                    if (targetSig.Params.Count + 1 > 4) continue;
                }
                else
                {
                    if (targetSig.Params.Count > 4) continue;
                }

                bool useCallvirt = hasThis && isCallvirt;
                string cacheKey = "RP:" + (isNewObj ? "NEW:" : (useCallvirt ? "CV:" : (hasThis ? "CI:" : "S:"))) + target.FullName;
                MethodDef proxy;
                if (!proxyCache.TryGetValue(cacheKey, out proxy))
                {
                    proxy = BuildStaticProxy(module, target, hasThis, receiverTypeSig, useCallvirt, isNewObj);
                    if (proxy == null) continue;
                    proxyCache[cacheKey] = proxy;

                    var container = proxyContainers[totalProxied % DELEGATE_POOL_SIZE];
                    container.Methods.Add(proxy);
                    engine.injectedMethods.Add(proxy);
                    totalProxied++;
                }

                il[i].OpCode = DnOpCodes.Call;
                il[i].Operand = proxy;
            }
        }

        private MethodDef BuildStaticProxy(ModuleDef module, IMethod target,
            bool hasThis = false, TypeSig receiverTypeSig = null, bool useCallvirt = false,
            bool isNewObj = false)
        {
            var targetSig = target.MethodSig;
            if (targetSig == null) return null;

            TypeSig retTypeSig;
            if (isNewObj)
            {
                if (target.DeclaringType == null) return null;
                try
                {
                    var imported = module.Import(target.DeclaringType);
                    var asDefOrRef = imported as ITypeDefOrRef;
                    if (asDefOrRef == null) return null;
                    retTypeSig = asDefOrRef.ToTypeSig();
                }
                catch { return null; }
                if (retTypeSig == null) return null;
            }
            else
            {
                retTypeSig = targetSig.RetType;
            }

            TypeSig[] proxyParams;
            if (hasThis && receiverTypeSig != null)
            {
                proxyParams = new TypeSig[1 + targetSig.Params.Count];
                proxyParams[0] = receiverTypeSig;
                for (int pi = 0; pi < targetSig.Params.Count; pi++)
                    proxyParams[pi + 1] = targetSig.Params[pi];
            }
            else
            {
                proxyParams = targetSig.Params.ToArray();
            }

            var proxySig = MethodSig.CreateStatic(retTypeSig, proxyParams);

            var proxy = new MethodDefUser(engine.MakeName(),
                proxySig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            proxy.Body = new CilBody();
            proxy.Body.InitLocals = true;
            var il = proxy.Body.Instructions;

            int scrambleType = rng.Next(0, 5);
            switch (scrambleType)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Pop));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Pop));
                    break;
                case 2:
                    il.Add(Instruction.Create(DnOpCodes.Nop));
                    il.Add(Instruction.Create(DnOpCodes.Nop));
                    break;
                case 3:
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Pop));
                    break;
                default:
                    break;
            }

            var tickCount = module.Import(typeof(Environment).GetProperty("TickCount").GetGetMethod());
            Instruction deadStart = Instruction.Create(DnOpCodes.Ldnull);
            il.Add(Instruction.Create(DnOpCodes.Call, tickCount));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, deadStart));

            int totalParams = proxyParams.Length;
            for (int i = 0; i < totalParams; i++)
            {
                switch (i)
                {
                    case 0: il.Add(Instruction.Create(DnOpCodes.Ldarg_0)); break;
                    case 1: il.Add(Instruction.Create(DnOpCodes.Ldarg_1)); break;
                    case 2: il.Add(Instruction.Create(DnOpCodes.Ldarg_2)); break;
                    case 3: il.Add(Instruction.Create(DnOpCodes.Ldarg_3)); break;
                }
            }

            OpCode callOp;
            if (isNewObj) callOp = DnOpCodes.Newobj;
            else if (hasThis && useCallvirt) callOp = DnOpCodes.Callvirt;
            else callOp = DnOpCodes.Call;
            il.Add(Instruction.Create(callOp, module.Import(target)));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(deadStart);
            il.Add(Instruction.Create(DnOpCodes.Throw));
            return proxy;
        }
    }
}

