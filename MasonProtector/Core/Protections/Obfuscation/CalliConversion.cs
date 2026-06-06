using System;
using System.Collections.Generic;
using System.Linq;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class CalliConversionProtection
    {
        private Obfuscation engine;
        private Random rng;

        internal CalliConversionProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyCalliConversion(ModuleDef module)
        {
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    if (engine.MethodHasAsyncOrIteratorAttribute(method)) continue;
                    try
                    {
                        ConvertCallsToCalli(module, method);
                        method.Body.SimplifyBranches();
                        method.Body.OptimizeBranches();
                    }
                    catch { }
                }
            }
        }

        private TypeSig GetInstanceReceiverType(ModuleDef module, IMethod target)
        {
            var declType = target.DeclaringType;
            if (declType == null) return null;
            TypeDef td = null;
            try { td = declType.ResolveTypeDef(); } catch { }
            if (td != null)
            {
                if (td.IsValueType) return null;
                if (td.HasGenericParameters) return null;
                if (td.Module != null && td.Module != module)
                {
                    string extNs = td.Namespace?.String ?? "";
                    string extNm = td.Name?.String ?? "";
                    if (!IsKnownSafeExternalType(extNs, extNm)) return null;
                }
            }
            else
            {
                var tr = declType as TypeRef;
                if (tr == null) return null;
                string ns = tr.Namespace?.String ?? "";
                string nm = tr.Name?.String ?? "";
                if (nm.Contains("`")) return null;
                if (IsKnownValueType(ns, nm)) return null;
                if (!IsKnownSafeExternalType(ns, nm)) return null;
            }
            try { return module.Import(declType.ToTypeSig()); }
            catch { return null; }
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

        private void ConvertCallsToCalli(ModuleDef module, MethodDef method)
        {
            if (method.Body.HasExceptionHandlers) return;
            var il = method.Body.Instructions;
            for (int i = 0; i < il.Count; i++)
            {
                bool isCall     = il[i].OpCode == DnOpCodes.Call;
                bool isCallvirt = il[i].OpCode == DnOpCodes.Callvirt;
                if (!isCall && !isCallvirt) continue;

                if (i > 0 && il[i - 1].OpCode == DnOpCodes.Constrained) continue;

                var target = il[i].Operand as IMethod;
                if (target == null) continue;
                if (engine.IsCompilerInfrastructureCall(target)) continue;
                if (engine.IsCompilerGeneratedOwner(target)) continue;

                if (target.Name == ".ctor" || target.Name == ".cctor") continue;

                var targetSig = target.MethodSig;
                if (targetSig == null) continue;
                if (targetSig.GenParamCount > 0) continue;
                if (targetSig.RetType == null) continue;

                if (targetSig.RetType.IsByRef || targetSig.RetType.IsPointer) continue;
                bool hasComplexParam = false;
                foreach (var p in targetSig.Params)
                {
                    if (p == null || p.IsByRef || p.IsPointer) { hasComplexParam = true; break; }
                }
                if (hasComplexParam) continue;

                var cconv = targetSig.CallingConvention & dnlib.DotNet.CallingConvention.Mask;
                if (cconv != dnlib.DotNet.CallingConvention.Default) continue;

                bool hasThis = targetSig.HasThis;

                if (hasThis && isCallvirt)
                {
                    MethodDef mdResolved = null;
                    try { mdResolved = target.ResolveMethodDef(); } catch { }
                    if (mdResolved == null) continue;
                    if (mdResolved.IsVirtual && !mdResolved.IsFinal)
                    {
                        bool typeFinal = mdResolved.DeclaringType != null && mdResolved.DeclaringType.IsSealed;
                        if (!typeFinal) continue;
                    }
                }

                TypeSig receiverType = null;
                int totalParams = targetSig.Params.Count;

                if (hasThis)
                {
                    receiverType = GetInstanceReceiverType(module, target);
                    if (receiverType == null) continue;
                    totalParams = 1 + targetSig.Params.Count;
                    if (totalParams > 4) continue;
                }
                else
                {
                    if (targetSig.Params.Count > 4) continue;
                }

                if (!engine.LevelChance(0.5, 0.8, 1.0)) continue;

                var importer = new Importer(module);
                var importedRet = importer.Import(targetSig.RetType);

                TypeSig[] calliParams;
                if (hasThis)
                {
                    calliParams = new TypeSig[1 + targetSig.Params.Count];
                    calliParams[0] = importer.Import(receiverType);
                    for (int pi = 0; pi < targetSig.Params.Count; pi++)
                        calliParams[pi + 1] = importer.Import(targetSig.Params[pi]);
                }
                else
                {
                    calliParams = new TypeSig[targetSig.Params.Count];
                    for (int pi = 0; pi < targetSig.Params.Count; pi++)
                        calliParams[pi] = importer.Import(targetSig.Params[pi]);
                }

                var calliSig = MethodSig.CreateStatic(importedRet, calliParams);

                il[i].OpCode = DnOpCodes.Ldftn;
                il[i].Operand = target;
                il.Insert(i + 1, Instruction.Create(DnOpCodes.Calli, calliSig));
                i++;
            }
        }
    }
}

