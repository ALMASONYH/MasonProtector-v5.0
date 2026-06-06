using System.Collections.Generic;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class PreAnalysis
    {
        private ModuleDef module;

        internal class AnalysisResult
        {
            public bool HasReflection { get; set; }
            public bool HasSerialization { get; set; }
            public HashSet<TypeDef> SerializableTypes { get; set; }
            public HashSet<MethodDef> ReflectionMethods { get; set; }

            public HashSet<string> ReflectionLiterals { get; set; }

            public AnalysisResult()
            {
                SerializableTypes = new HashSet<TypeDef>();
                ReflectionMethods = new HashSet<MethodDef>();
                ReflectionLiterals = new HashSet<string>(System.StringComparer.Ordinal);
            }
        }

        internal PreAnalysis(ModuleDef mod)
        {
            module = mod;
        }

        internal AnalysisResult Analyze()
        {
            var result = new AnalysisResult();

            foreach (TypeDef type in module.GetTypes())
            {
                ScanTypeForPatterns(type, result);
            }

            return result;
        }

        private void ScanTypeForPatterns(TypeDef type, AnalysisResult result)
        {
            if (type.IsSerializable)
            {
                result.HasSerialization = true;
                result.SerializableTypes.Add(type);
            }

            foreach (var iface in type.Interfaces)
            {
                if (iface.Interface != null)
                {
                    string ifName = iface.Interface.FullName;
                    if (ifName == "System.Runtime.Serialization.ISerializable" ||
                        ifName == "System.Runtime.Serialization.IDeserializationCallback")
                    {
                        result.HasSerialization = true;
                        result.SerializableTypes.Add(type);
                    }
                }
            }

            foreach (MethodDef method in type.Methods)
            {
                if (!method.HasBody || !method.Body.HasInstructions) continue;

                var instrs = method.Body.Instructions;
                for (int idx = 0; idx < instrs.Count; idx++)
                {
                    var inst = instrs[idx];
                    if (inst.OpCode != DnOpCodes.Call && inst.OpCode != DnOpCodes.Callvirt) continue;

                    var target = inst.Operand as IMethod;
                    if (target == null || target.DeclaringType == null) continue;

                    string declType = target.DeclaringType.FullName;
                    string mName = target.Name;

                    if (declType == "System.Type" || declType == "System.Reflection.Assembly" ||
                        declType == "System.Activator")
                    {
                        if (mName == "GetMethod" || mName == "GetType" || mName == "GetField" ||
                            mName == "GetProperty" || mName == "GetEvent" || mName == "GetMember" ||
                            mName == "GetNestedType" || mName == "CreateInstance" || mName == "InvokeMember" ||
                            mName == "GetMethods" || mName == "GetFields")
                        {
                            result.HasReflection = true;
                            result.ReflectionMethods.Add(method);

                            for (int b = idx - 1; b >= 0 && b >= idx - 14; b--)
                            {
                                if (instrs[b].OpCode == DnOpCodes.Ldstr)
                                {
                                    string lit = instrs[b].Operand as string;
                                    if (!string.IsNullOrEmpty(lit))
                                    {
                                        result.ReflectionLiterals.Add(lit);

                                        int dot = lit.LastIndexOf('.');
                                        if (dot >= 0 && dot < lit.Length - 1)
                                            result.ReflectionLiterals.Add(lit.Substring(dot + 1));
                                    }
                                }

                                if (instrs[b].OpCode == DnOpCodes.Ret) break;
                            }
                        }
                    }
                }
            }
        }
    }
}

