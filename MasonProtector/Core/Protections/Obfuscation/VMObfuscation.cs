using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System;
using dnlib.DotNet.Emit;
using dnlib.DotNet;
using DnFieldAttributes = dnlib.DotNet.FieldAttributes;
using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;

namespace MasonProtector.Core
{

    internal class VMObfuscationProtection
    {
        private Obfuscation engine;
        private Random rng;

        private const byte VOP_NOP      = 0;
        private const byte VOP_PUSH_I4  = 1;
        private const byte VOP_ADD      = 2;
        private const byte VOP_SUB      = 3;
        private const byte VOP_MUL      = 4;
        private const byte VOP_XOR      = 5;
        private const byte VOP_AND      = 6;
        private const byte VOP_OR       = 7;
        private const byte VOP_NOT      = 8;
        private const byte VOP_NEG      = 9;
        private const byte VOP_POP      = 10;
        private const byte VOP_DUP      = 11;
        private const byte VOP_LDLOC    = 12;
        private const byte VOP_STLOC    = 13;
        private const byte VOP_LDARG    = 14;
        private const byte VOP_BR       = 15;
        private const byte VOP_BRFALSE  = 16;
        private const byte VOP_BRTRUE   = 17;
        private const byte VOP_CEQ      = 18;
        private const byte VOP_CGT      = 19;
        private const byte VOP_CGT_UN   = 20;
        private const byte VOP_CLT      = 21;
        private const byte VOP_CLT_UN   = 22;
        private const byte VOP_SHL      = 23;
        private const byte VOP_SHR      = 24;
        private const byte VOP_SHR_UN   = 25;
        private const byte VOP_DIV      = 26;
        private const byte VOP_DIV_UN   = 27;
        private const byte VOP_REM      = 28;
        private const byte VOP_REM_UN   = 29;
        private const byte VOP_RET      = 30;
        private const byte VOP_CONV_I1  = 31;
        private const byte VOP_CONV_U1  = 32;
        private const byte VOP_CONV_I2  = 33;
        private const byte VOP_CONV_U2  = 34;

        internal VMObfuscationProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyVMObfuscation(ModuleDef module)
        {
            var vmType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            vmType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(vmType);
            engine.injectedTypes.Add(vmType);

            int[] opcodeMap = new int[256];
            for (int i = 0; i < 256; i++) opcodeMap[i] = i;
            for (int i = 255; i > 0; i--)
            {
                int j = rng.Next(0, i + 1);
                int t = opcodeMap[i]; opcodeMap[i] = opcodeMap[j]; opcodeMap[j] = t;
            }

            var bytecodeField = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(new SZArraySig(module.CorLibTypes.Byte))),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(bytecodeField);

            var dispatcher = BuildVMDispatcher(module, vmType, bytecodeField, opcodeMap);
            vmType.Methods.Add(dispatcher);
            engine.injectedMethods.Add(dispatcher);

            var collectedBytecodes = new List<KeyValuePair<int, byte[]>>();

            int virtualized = 0;
            foreach (TypeDef type in module.GetTypes().ToList())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods.ToList())
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    if (method.IsConstructor || method.IsStaticConstructor) continue;
                    if (!method.IsStatic) continue;
                    if (method.Body == null) continue;
                    if (method.Body.HasExceptionHandlers) continue;
                    if (method.HasGenericParameters) continue;
                    if (method.IsPinvokeImpl) continue;
                    if (method.Body.Instructions.Count < 4) continue;

                    int numLocals;
                    int numArgs;
                    bool returnsInt;
                    if (!IsVMCompatible(method, out numLocals, out numArgs, out returnsInt)) continue;

                    try
                    {
                        byte[] bc = EmitVMBytecode(method, opcodeMap);
                        if (bc == null || bc.Length == 0) continue;
                        byte xorKey = (byte)rng.Next(1, 255);
                        for (int b = 0; b < bc.Length; b++)
                        {
                            byte mask = (byte)(xorKey ^ (byte)b);
                            bc[b] ^= mask;
                        }

                        int slot = virtualized;
                        collectedBytecodes.Add(new KeyValuePair<int, byte[]>(slot, bc));

                        EmitVMStub(module, method, slot, xorKey, numLocals, numArgs, returnsInt, dispatcher);
                        engine.virtualizedMethods.Add(method);

                        virtualized++;
                    }
                    catch { }
                }
            }

            if (virtualized == 0) return;

            var initMethod = BuildVMInit(module, vmType, bytecodeField, collectedBytecodes, virtualized);
            vmType.Methods.Add(initMethod);
            engine.injectedMethods.Add(initMethod);

            var modType = module.Types.FirstOrDefault(t => t.Name == "<Module>");
            if (modType != null)
                engine.InjectCallInCctor(module, modType, initMethod);
        }

        private bool IsIntType(TypeSig t)
        {
            if (t == null) return false;
            string fn = t.FullName;
            return fn == "System.Int32"  || fn == "System.UInt32"
                || fn == "System.Int16"  || fn == "System.UInt16"
                || fn == "System.SByte"  || fn == "System.Byte"
                || fn == "System.Boolean"|| fn == "System.Char";
        }

        private OpCode StubReturnConvOp(TypeSig t)
        {
            if (t == null) return null;
            string fn = t.FullName;
            if (fn == "System.SByte")   return DnOpCodes.Conv_I1;
            if (fn == "System.Byte"
             || fn == "System.Boolean") return DnOpCodes.Conv_U1;
            if (fn == "System.Int16")   return DnOpCodes.Conv_I2;
            if (fn == "System.UInt16"
             || fn == "System.Char")    return DnOpCodes.Conv_U2;
            return null;
        }

        private bool IsVoidType(TypeSig t)
        {
            return t != null && t.FullName == "System.Void";
        }

        private bool IsVMCompatible(MethodDef method, out int numLocals, out int numArgs, out bool returnsInt)
        {
            numLocals = 0;
            numArgs = 0;
            returnsInt = false;

            var ret = method.ReturnType;
            if (IsVoidType(ret)) returnsInt = false;
            else if (IsIntType(ret)) returnsInt = true;
            else return false;

            int argCount = 0;
            foreach (var p in method.Parameters)
            {
                if (p.IsHiddenThisParameter) return false;
                if (!IsIntType(p.Type)) return false;
                argCount++;
            }
            numArgs = argCount;

            if (method.Body.HasVariables)
            {
                foreach (var v in method.Body.Variables)
                {
                    if (!IsIntType(v.Type)) return false;
                }
                numLocals = method.Body.Variables.Count;
            }

            if (numArgs > 255 || numLocals > 255) return false;

            foreach (var inst in method.Body.Instructions)
            {
                if (!IsAllowedOpcode(inst.OpCode)) return false;
            }
            return true;
        }

        private bool IsAllowedOpcode(OpCode op)
        {
            if (op == DnOpCodes.Nop) return true;
            if (op == DnOpCodes.Ret) return true;
            if (op == DnOpCodes.Pop) return true;
            if (op == DnOpCodes.Dup) return true;
            if (IsLdcI4(op)) return true;
            if (IsLdarg(op)) return true;
            if (IsLdloc(op)) return true;
            if (IsStloc(op)) return true;
            if (op == DnOpCodes.Add || op == DnOpCodes.Sub || op == DnOpCodes.Mul) return true;
            if (op == DnOpCodes.Div || op == DnOpCodes.Div_Un) return true;
            if (op == DnOpCodes.Rem || op == DnOpCodes.Rem_Un) return true;
            if (op == DnOpCodes.Xor || op == DnOpCodes.And || op == DnOpCodes.Or) return true;
            if (op == DnOpCodes.Not || op == DnOpCodes.Neg) return true;
            if (op == DnOpCodes.Shl || op == DnOpCodes.Shr || op == DnOpCodes.Shr_Un) return true;
            if (op == DnOpCodes.Ceq || op == DnOpCodes.Cgt || op == DnOpCodes.Cgt_Un
                || op == DnOpCodes.Clt || op == DnOpCodes.Clt_Un) return true;
            if (op == DnOpCodes.Conv_I4 || op == DnOpCodes.Conv_U4) return true;
            if (op == DnOpCodes.Conv_I1 || op == DnOpCodes.Conv_U1) return true;
            if (op == DnOpCodes.Conv_I2 || op == DnOpCodes.Conv_U2) return true;
            if (op == DnOpCodes.Conv_I  || op == DnOpCodes.Conv_U)  return true;
            if (op == DnOpCodes.Br || op == DnOpCodes.Br_S) return true;
            if (op == DnOpCodes.Brfalse || op == DnOpCodes.Brfalse_S) return true;
            if (op == DnOpCodes.Brtrue || op == DnOpCodes.Brtrue_S) return true;
            if (op == DnOpCodes.Beq || op == DnOpCodes.Beq_S) return true;
            if (op == DnOpCodes.Bne_Un || op == DnOpCodes.Bne_Un_S) return true;
            if (op == DnOpCodes.Bgt || op == DnOpCodes.Bgt_S) return true;
            if (op == DnOpCodes.Bgt_Un || op == DnOpCodes.Bgt_Un_S) return true;
            if (op == DnOpCodes.Blt || op == DnOpCodes.Blt_S) return true;
            if (op == DnOpCodes.Blt_Un || op == DnOpCodes.Blt_Un_S) return true;
            if (op == DnOpCodes.Bge || op == DnOpCodes.Bge_S) return true;
            if (op == DnOpCodes.Bge_Un || op == DnOpCodes.Bge_Un_S) return true;
            if (op == DnOpCodes.Ble || op == DnOpCodes.Ble_S) return true;
            if (op == DnOpCodes.Ble_Un || op == DnOpCodes.Ble_Un_S) return true;
            return false;
        }

        private bool IsLdcI4(OpCode op)
        {
            return op == DnOpCodes.Ldc_I4 || op == DnOpCodes.Ldc_I4_S
                || op == DnOpCodes.Ldc_I4_0 || op == DnOpCodes.Ldc_I4_1
                || op == DnOpCodes.Ldc_I4_2 || op == DnOpCodes.Ldc_I4_3
                || op == DnOpCodes.Ldc_I4_4 || op == DnOpCodes.Ldc_I4_5
                || op == DnOpCodes.Ldc_I4_6 || op == DnOpCodes.Ldc_I4_7
                || op == DnOpCodes.Ldc_I4_8 || op == DnOpCodes.Ldc_I4_M1;
        }

        private bool IsLdarg(OpCode op)
        {
            return op == DnOpCodes.Ldarg || op == DnOpCodes.Ldarg_S
                || op == DnOpCodes.Ldarg_0 || op == DnOpCodes.Ldarg_1
                || op == DnOpCodes.Ldarg_2 || op == DnOpCodes.Ldarg_3;
        }

        private bool IsLdloc(OpCode op)
        {
            return op == DnOpCodes.Ldloc || op == DnOpCodes.Ldloc_S
                || op == DnOpCodes.Ldloc_0 || op == DnOpCodes.Ldloc_1
                || op == DnOpCodes.Ldloc_2 || op == DnOpCodes.Ldloc_3;
        }

        private bool IsStloc(OpCode op)
        {
            return op == DnOpCodes.Stloc || op == DnOpCodes.Stloc_S
                || op == DnOpCodes.Stloc_0 || op == DnOpCodes.Stloc_1
                || op == DnOpCodes.Stloc_2 || op == DnOpCodes.Stloc_3;
        }

        private int GetArgIndex(Instruction inst)
        {
            var op = inst.OpCode;
            if (op == DnOpCodes.Ldarg_0) return 0;
            if (op == DnOpCodes.Ldarg_1) return 1;
            if (op == DnOpCodes.Ldarg_2) return 2;
            if (op == DnOpCodes.Ldarg_3) return 3;
            var p = inst.Operand as Parameter;
            if (p != null) return p.Index;
            return Convert.ToInt32(inst.Operand);
        }

        private int GetLocalIndex(Instruction inst)
        {
            var op = inst.OpCode;
            if (op == DnOpCodes.Ldloc_0 || op == DnOpCodes.Stloc_0) return 0;
            if (op == DnOpCodes.Ldloc_1 || op == DnOpCodes.Stloc_1) return 1;
            if (op == DnOpCodes.Ldloc_2 || op == DnOpCodes.Stloc_2) return 2;
            if (op == DnOpCodes.Ldloc_3 || op == DnOpCodes.Stloc_3) return 3;
            var l = inst.Operand as Local;
            if (l != null) return l.Index;
            return Convert.ToInt32(inst.Operand);
        }

        private void EmitInt32LE(List<byte> bc, int v)
        {
            bc.Add((byte)(v & 0xFF));
            bc.Add((byte)((v >> 8) & 0xFF));
            bc.Add((byte)((v >> 16) & 0xFF));
            bc.Add((byte)((v >> 24) & 0xFF));
        }

        private byte[] EmitVMBytecode(MethodDef method, int[] opcodeMap)
        {
            var bc = new List<byte>();
            var ipOfIl = new Dictionary<Instruction, int>();
            var pendingBranches = new List<KeyValuePair<int, Instruction>>();

            foreach (var inst in method.Body.Instructions)
            {
                ipOfIl[inst] = bc.Count;
                var op = inst.OpCode;

                if (op == DnOpCodes.Nop || op == DnOpCodes.Conv_I4 || op == DnOpCodes.Conv_U4
                    || op == DnOpCodes.Conv_I || op == DnOpCodes.Conv_U)
                {
                    bc.Add((byte)opcodeMap[VOP_NOP]);
                }
                else if (op == DnOpCodes.Conv_I1) bc.Add((byte)opcodeMap[VOP_CONV_I1]);
                else if (op == DnOpCodes.Conv_U1) bc.Add((byte)opcodeMap[VOP_CONV_U1]);
                else if (op == DnOpCodes.Conv_I2) bc.Add((byte)opcodeMap[VOP_CONV_I2]);
                else if (op == DnOpCodes.Conv_U2) bc.Add((byte)opcodeMap[VOP_CONV_U2]);
                else if (op == DnOpCodes.Ret)
                {
                    bc.Add((byte)opcodeMap[VOP_RET]);
                }
                else if (IsLdcI4(op))
                {
                    int val = inst.GetLdcI4Value();
                    bc.Add((byte)opcodeMap[VOP_PUSH_I4]);
                    EmitInt32LE(bc, val);
                }
                else if (op == DnOpCodes.Add) bc.Add((byte)opcodeMap[VOP_ADD]);
                else if (op == DnOpCodes.Sub) bc.Add((byte)opcodeMap[VOP_SUB]);
                else if (op == DnOpCodes.Mul) bc.Add((byte)opcodeMap[VOP_MUL]);
                else if (op == DnOpCodes.Div) bc.Add((byte)opcodeMap[VOP_DIV]);
                else if (op == DnOpCodes.Div_Un) bc.Add((byte)opcodeMap[VOP_DIV_UN]);
                else if (op == DnOpCodes.Rem) bc.Add((byte)opcodeMap[VOP_REM]);
                else if (op == DnOpCodes.Rem_Un) bc.Add((byte)opcodeMap[VOP_REM_UN]);
                else if (op == DnOpCodes.Xor) bc.Add((byte)opcodeMap[VOP_XOR]);
                else if (op == DnOpCodes.And) bc.Add((byte)opcodeMap[VOP_AND]);
                else if (op == DnOpCodes.Or)  bc.Add((byte)opcodeMap[VOP_OR]);
                else if (op == DnOpCodes.Not) bc.Add((byte)opcodeMap[VOP_NOT]);
                else if (op == DnOpCodes.Neg) bc.Add((byte)opcodeMap[VOP_NEG]);
                else if (op == DnOpCodes.Shl) bc.Add((byte)opcodeMap[VOP_SHL]);
                else if (op == DnOpCodes.Shr) bc.Add((byte)opcodeMap[VOP_SHR]);
                else if (op == DnOpCodes.Shr_Un) bc.Add((byte)opcodeMap[VOP_SHR_UN]);
                else if (op == DnOpCodes.Pop) bc.Add((byte)opcodeMap[VOP_POP]);
                else if (op == DnOpCodes.Dup) bc.Add((byte)opcodeMap[VOP_DUP]);
                else if (op == DnOpCodes.Ceq) bc.Add((byte)opcodeMap[VOP_CEQ]);
                else if (op == DnOpCodes.Cgt) bc.Add((byte)opcodeMap[VOP_CGT]);
                else if (op == DnOpCodes.Cgt_Un) bc.Add((byte)opcodeMap[VOP_CGT_UN]);
                else if (op == DnOpCodes.Clt) bc.Add((byte)opcodeMap[VOP_CLT]);
                else if (op == DnOpCodes.Clt_Un) bc.Add((byte)opcodeMap[VOP_CLT_UN]);
                else if (IsLdarg(op))
                {
                    int idx = GetArgIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    bc.Add((byte)opcodeMap[VOP_LDARG]);
                    bc.Add((byte)idx);
                }
                else if (IsLdloc(op))
                {
                    int idx = GetLocalIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    bc.Add((byte)opcodeMap[VOP_LDLOC]);
                    bc.Add((byte)idx);
                }
                else if (IsStloc(op))
                {
                    int idx = GetLocalIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    if (idx < method.Body.Variables.Count)
                    {
                        var lty = method.Body.Variables[idx].Type;
                        if (lty != null)
                        {
                            string lfn = lty.FullName;
                            if (lfn == "System.SByte")    bc.Add((byte)opcodeMap[VOP_CONV_I1]);
                            else if (lfn == "System.Byte"
                                  || lfn == "System.Boolean") bc.Add((byte)opcodeMap[VOP_CONV_U1]);
                            else if (lfn == "System.Int16") bc.Add((byte)opcodeMap[VOP_CONV_I2]);
                            else if (lfn == "System.UInt16"
                                  || lfn == "System.Char")   bc.Add((byte)opcodeMap[VOP_CONV_U2]);
                        }
                    }
                    bc.Add((byte)opcodeMap[VOP_STLOC]);
                    bc.Add((byte)idx);
                }
                else if (op == DnOpCodes.Br || op == DnOpCodes.Br_S)
                {
                    bc.Add((byte)opcodeMap[VOP_BR]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Brfalse || op == DnOpCodes.Brfalse_S)
                {
                    bc.Add((byte)opcodeMap[VOP_BRFALSE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Brtrue || op == DnOpCodes.Brtrue_S)
                {
                    bc.Add((byte)opcodeMap[VOP_BRTRUE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Beq || op == DnOpCodes.Beq_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CEQ]);
                    bc.Add((byte)opcodeMap[VOP_BRTRUE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Bne_Un || op == DnOpCodes.Bne_Un_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CEQ]);
                    bc.Add((byte)opcodeMap[VOP_BRFALSE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Bgt || op == DnOpCodes.Bgt_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CGT]);
                    bc.Add((byte)opcodeMap[VOP_BRTRUE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Bgt_Un || op == DnOpCodes.Bgt_Un_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CGT_UN]);
                    bc.Add((byte)opcodeMap[VOP_BRTRUE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Blt || op == DnOpCodes.Blt_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CLT]);
                    bc.Add((byte)opcodeMap[VOP_BRTRUE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Blt_Un || op == DnOpCodes.Blt_Un_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CLT_UN]);
                    bc.Add((byte)opcodeMap[VOP_BRTRUE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Bge || op == DnOpCodes.Bge_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CLT]);
                    bc.Add((byte)opcodeMap[VOP_BRFALSE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Bge_Un || op == DnOpCodes.Bge_Un_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CLT_UN]);
                    bc.Add((byte)opcodeMap[VOP_BRFALSE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Ble || op == DnOpCodes.Ble_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CGT]);
                    bc.Add((byte)opcodeMap[VOP_BRFALSE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Ble_Un || op == DnOpCodes.Ble_Un_S)
                {
                    bc.Add((byte)opcodeMap[VOP_CGT_UN]);
                    bc.Add((byte)opcodeMap[VOP_BRFALSE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else
                {
                    return null;
                }
            }

            foreach (var pb in pendingBranches)
            {
                var target = pb.Value;
                if (target == null || !ipOfIl.ContainsKey(target)) return null;
                int targetIp = ipOfIl[target];
                bc[pb.Key]     = (byte)(targetIp & 0xFF);
                bc[pb.Key + 1] = (byte)((targetIp >> 8) & 0xFF);
                bc[pb.Key + 2] = (byte)((targetIp >> 16) & 0xFF);
                bc[pb.Key + 3] = (byte)((targetIp >> 24) & 0xFF);
            }

            return bc.ToArray();
        }

        private void EmitVMStub(ModuleDef module, MethodDef method, int slot, byte xorKey,
            int numLocals, int numArgs, bool returnsInt, MethodDef dispatcher)
        {
            method.Body.Instructions.Clear();
            method.Body.Variables.Clear();
            method.Body.ExceptionHandlers.Clear();
            method.Body.InitLocals = true;

            var il = method.Body.Instructions;
            var int32Type = module.CorLibTypes.Int32.TypeDefOrRef;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, slot));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, (int)xorKey));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, numLocals));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, numArgs));
            il.Add(Instruction.Create(DnOpCodes.Newarr, int32Type));
            for (int i = 0; i < numArgs; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[i]));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            }

            il.Add(Instruction.Create(DnOpCodes.Call, dispatcher));

            if (returnsInt)
            {
                var retConv = StubReturnConvOp(method.ReturnType);
                if (retConv != null)
                    il.Add(Instruction.Create(retConv));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Pop));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
        }

        private MethodDef BuildVMDispatcher(ModuleDef module, TypeDef vmType,
            FieldDef bytecodeField, int[] opcodeMap)
        {
            var int32 = module.CorLibTypes.Int32;
            var int32Arr = new SZArraySig(int32);
            var byteArr = new SZArraySig(module.CorLibTypes.Byte);

            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(int32, int32, int32, int32, int32Arr),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(byteArr));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32Arr));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32Arr));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));

            const int LOC_CODE   = 0;
            const int LOC_IP     = 1;
            const int LOC_OP     = 2;
            const int LOC_STACK  = 3;
            const int LOC_SP     = 4;
            const int LOC_LOCALS = 5;
            const int LOC_T1     = 6;
            const int LOC_T2     = 7;

            const int ARG_SLOT      = 0;
            const int ARG_KEY       = 1;
            const int ARG_NUMLOCALS = 2;
            const int ARG_ARGS      = 3;

            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, bytecodeField));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_SLOT]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_CODE]));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 1024));
            il.Add(Instruction.Create(DnOpCodes.Newarr, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_STACK]));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));

            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_NUMLOCALS]));
            il.Add(Instruction.Create(DnOpCodes.Newarr, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_LOCALS]));

            var loopStart = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]);
            var loopEndRet = Instruction.Create(DnOpCodes.Nop);
            var advanceIp1 = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]);

            il.Add(loopStart);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, loopEndRet));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_KEY]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_OP]));

            var blkPush     = Instruction.Create(DnOpCodes.Nop);
            var blkAdd      = Instruction.Create(DnOpCodes.Nop);
            var blkSub      = Instruction.Create(DnOpCodes.Nop);
            var blkMul      = Instruction.Create(DnOpCodes.Nop);
            var blkDiv      = Instruction.Create(DnOpCodes.Nop);
            var blkDivUn    = Instruction.Create(DnOpCodes.Nop);
            var blkRem      = Instruction.Create(DnOpCodes.Nop);
            var blkRemUn    = Instruction.Create(DnOpCodes.Nop);
            var blkXor      = Instruction.Create(DnOpCodes.Nop);
            var blkAnd      = Instruction.Create(DnOpCodes.Nop);
            var blkOr       = Instruction.Create(DnOpCodes.Nop);
            var blkNot      = Instruction.Create(DnOpCodes.Nop);
            var blkNeg      = Instruction.Create(DnOpCodes.Nop);
            var blkPop      = Instruction.Create(DnOpCodes.Nop);
            var blkDup      = Instruction.Create(DnOpCodes.Nop);
            var blkLdloc    = Instruction.Create(DnOpCodes.Nop);
            var blkStloc    = Instruction.Create(DnOpCodes.Nop);
            var blkLdarg    = Instruction.Create(DnOpCodes.Nop);
            var blkBr       = Instruction.Create(DnOpCodes.Nop);
            var blkBrFalse  = Instruction.Create(DnOpCodes.Nop);
            var blkBrTrue   = Instruction.Create(DnOpCodes.Nop);
            var blkCeq      = Instruction.Create(DnOpCodes.Nop);
            var blkCgt      = Instruction.Create(DnOpCodes.Nop);
            var blkCgtUn    = Instruction.Create(DnOpCodes.Nop);
            var blkClt      = Instruction.Create(DnOpCodes.Nop);
            var blkCltUn    = Instruction.Create(DnOpCodes.Nop);
            var blkShl      = Instruction.Create(DnOpCodes.Nop);
            var blkShr      = Instruction.Create(DnOpCodes.Nop);
            var blkShrUn    = Instruction.Create(DnOpCodes.Nop);
            var blkConvI1   = Instruction.Create(DnOpCodes.Nop);
            var blkConvU1   = Instruction.Create(DnOpCodes.Nop);
            var blkConvI2   = Instruction.Create(DnOpCodes.Nop);
            var blkConvU2   = Instruction.Create(DnOpCodes.Nop);

            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_RET],     loopEndRet);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_PUSH_I4], blkPush);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_ADD],     blkAdd);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SUB],     blkSub);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_MUL],     blkMul);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_DIV],     blkDiv);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_DIV_UN],  blkDivUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_REM],     blkRem);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_REM_UN],  blkRemUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_XOR],     blkXor);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_AND],     blkAnd);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_OR],      blkOr);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_NOT],     blkNot);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_NEG],     blkNeg);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_POP],     blkPop);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_DUP],     blkDup);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDLOC],   blkLdloc);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_STLOC],   blkStloc);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDARG],   blkLdarg);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_BR],      blkBr);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_BRFALSE], blkBrFalse);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_BRTRUE],  blkBrTrue);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CEQ],     blkCeq);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CGT],     blkCgt);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CGT_UN],  blkCgtUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CLT],     blkClt);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CLT_UN],  blkCltUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SHL],     blkShl);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SHR],     blkShr);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SHR_UN],  blkShrUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_I1], blkConvI1);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_U1], blkConvU1);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_I2], blkConvI2);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_U2], blkConvU2);

            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkPush);
            EmitReadInt32(il, method, LOC_CODE, LOC_IP, ARG_KEY, 1, LOC_T1);
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 5));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            EmitBinaryOp(il, method, blkAdd,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Add, advanceIp1);
            EmitBinaryOp(il, method, blkSub,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Sub, advanceIp1);
            EmitBinaryOp(il, method, blkMul,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Mul, advanceIp1);
            EmitBinaryOp(il, method, blkDiv,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Div, advanceIp1);
            EmitBinaryOp(il, method, blkDivUn,  LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Div_Un, advanceIp1);
            EmitBinaryOp(il, method, blkRem,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Rem, advanceIp1);
            EmitBinaryOp(il, method, blkRemUn,  LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Rem_Un, advanceIp1);
            EmitBinaryOp(il, method, blkXor,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Xor, advanceIp1);
            EmitBinaryOp(il, method, blkAnd,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.And, advanceIp1);
            EmitBinaryOp(il, method, blkOr,     LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Or,  advanceIp1);
            EmitBinaryOp(il, method, blkShl,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Shl, advanceIp1);
            EmitBinaryOp(il, method, blkShr,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Shr, advanceIp1);
            EmitBinaryOp(il, method, blkShrUn,  LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Shr_Un, advanceIp1);

            EmitCmpOp(il, method, blkCeq,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Ceq,    advanceIp1);
            EmitCmpOp(il, method, blkCgt,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Cgt,    advanceIp1);
            EmitCmpOp(il, method, blkCgtUn,  LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Cgt_Un, advanceIp1);
            EmitCmpOp(il, method, blkClt,    LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Clt,    advanceIp1);
            EmitCmpOp(il, method, blkCltUn,  LOC_STACK, LOC_SP, LOC_T1, LOC_T2, DnOpCodes.Clt_Un, advanceIp1);

            il.Add(blkNot);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Not));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkNeg);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Neg));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkConvI1);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Conv_I1));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkConvU1);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkConvI2);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Conv_I2));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkConvU2);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFFFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkPop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkDup);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, advanceIp1));

            il.Add(blkLdloc);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_KEY]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T2]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_LOCALS]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T2]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkStloc);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_KEY]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T2]));
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_LOCALS]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T2]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkLdarg);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_KEY]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFF));
            il.Add(Instruction.Create(DnOpCodes.And));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T2]));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_ARGS]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T2]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkBr);
            EmitReadInt32(il, method, LOC_CODE, LOC_IP, ARG_KEY, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkBrFalse);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T2);
            EmitReadInt32(il, method, LOC_CODE, LOC_IP, ARG_KEY, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T2]));
            var brfNotTaken = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]);
            il.Add(Instruction.Create(DnOpCodes.Brtrue, brfNotTaken));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));
            il.Add(brfNotTaken);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 5));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkBrTrue);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T2);
            EmitReadInt32(il, method, LOC_CODE, LOC_IP, ARG_KEY, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T2]));
            var brtNotTaken = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]);
            il.Add(Instruction.Create(DnOpCodes.Brfalse, brtNotTaken));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));
            il.Add(brtNotTaken);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 5));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(advanceIp1);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(loopEndRet);
            var afterRet = Instruction.Create(DnOpCodes.Ret);
            var emptyStack = Instruction.Create(DnOpCodes.Ldc_I4_0);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ble, emptyStack));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Br, afterRet));
            il.Add(emptyStack);
            il.Add(afterRet);

            return method;
        }

        private void EmitDispatchEntry(IList<Instruction> il, Local opLocal, int opcodeValue, Instruction target)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldloc, opLocal));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, opcodeValue));
            il.Add(Instruction.Create(DnOpCodes.Beq, target));
        }

        private void EmitStackPush(IList<Instruction> il, MethodDef method, int LOC_STACK, int LOC_SP, int LOC_VAL)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_VAL]));
            il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
        }

        private void EmitStackPop(IList<Instruction> il, MethodDef method, int LOC_STACK, int LOC_SP, int LOC_DEST)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
        }

        private void EmitReadInt32(IList<Instruction> il, MethodDef method, int LOC_CODE, int LOC_IP, int ARG_KEY, int offset, int LOC_DEST)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
            for (int i = 0; i < 4; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_DEST]));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, offset + i));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
                il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_KEY]));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, offset + i));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 0xFF));
                il.Add(Instruction.Create(DnOpCodes.And));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                if (i > 0)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i * 8));
                    il.Add(Instruction.Create(DnOpCodes.Shl));
                }
                il.Add(Instruction.Create(DnOpCodes.Or));
                il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
            }
        }

        private void EmitBinaryOp(IList<Instruction> il, MethodDef method, Instruction blockStart,
            int LOC_STACK, int LOC_SP, int LOC_T1, int LOC_T2, OpCode binOp, Instruction afterTarget)
        {
            il.Add(blockStart);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T2);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T2]));
            il.Add(Instruction.Create(binOp));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, afterTarget));
        }

        private void EmitCmpOp(IList<Instruction> il, MethodDef method, Instruction blockStart,
            int LOC_STACK, int LOC_SP, int LOC_T1, int LOC_T2, OpCode cmpOp, Instruction afterTarget)
        {
            il.Add(blockStart);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T2);
            EmitStackPop(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T2]));
            il.Add(Instruction.Create(cmpOp));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            EmitStackPush(il, method, LOC_STACK, LOC_SP, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Br, afterTarget));
        }

        private MethodDef BuildVMInit(ModuleDef module, TypeDef vmType,
            FieldDef bytecodeField, List<KeyValuePair<int, byte[]>> bytecodes, int totalSlots)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, totalSlots));
            il.Add(Instruction.Create(DnOpCodes.Newarr, new TypeSpecUser(new SZArraySig(module.CorLibTypes.Byte))));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, bytecodeField));

            foreach (var pair in bytecodes)
            {
                int slotIdx = pair.Key;
                byte[] bc = pair.Value;

                il.Add(Instruction.Create(DnOpCodes.Ldsfld, bytecodeField));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, slotIdx));

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, bc.Length));
                il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));

                for (int b = 0; b < bc.Length; b++)
                {
                    il.Add(Instruction.Create(DnOpCodes.Dup));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, b));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, (int)bc[b]));
                    il.Add(Instruction.Create(DnOpCodes.Stelem_I1));
                }

                il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            }

            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }
    }

    internal class VMObfuscationV2Protection
    {

        private const byte VOP_NOP        = 0;
        private const byte VOP_RET        = 1;
        private const byte VOP_LDARG      = 2;
        private const byte VOP_STARG      = 3;
        private const byte VOP_LDLOC      = 4;
        private const byte VOP_STLOC      = 5;
        private const byte VOP_POP        = 6;
        private const byte VOP_DUP        = 7;
        private const byte VOP_LDNULL     = 8;
        private const byte VOP_LDC_I4     = 9;
        private const byte VOP_LDSTR      = 10;
        private const byte VOP_LDSFLD     = 11;
        private const byte VOP_STSFLD     = 12;
        private const byte VOP_LDFLD      = 13;
        private const byte VOP_STFLD      = 14;
        private const byte VOP_CALL       = 15;
        private const byte VOP_CALLVIRT   = 16;
        private const byte VOP_NEWOBJ     = 17;
        private const byte VOP_NEWARR     = 18;
        private const byte VOP_LDLEN      = 19;
        private const byte VOP_LDELEM_REF = 20;
        private const byte VOP_STELEM_REF = 21;
        private const byte VOP_BR         = 22;
        private const byte VOP_BRTRUE     = 23;
        private const byte VOP_BRFALSE    = 24;
        private const byte VOP_THROW      = 25;
        private const byte VOP_BOX        = 26;
        private const byte VOP_UNBOX_ANY  = 27;
        private const byte VOP_CASTCLASS  = 28;
        private const byte VOP_ISINST     = 29;
        private const byte VOP_ADD        = 30;
        private const byte VOP_SUB        = 31;
        private const byte VOP_MUL        = 32;
        private const byte VOP_DIV        = 33;
        private const byte VOP_REM        = 34;
        private const byte VOP_AND        = 35;
        private const byte VOP_OR         = 36;
        private const byte VOP_XOR        = 37;
        private const byte VOP_NEG        = 38;
        private const byte VOP_NOT        = 39;
        private const byte VOP_SHL        = 40;
        private const byte VOP_SHR        = 41;
        private const byte VOP_CEQ        = 42;
        private const byte VOP_CGT        = 43;
        private const byte VOP_CLT        = 44;
        private const byte VOP_CONV_I1    = 45;
        private const byte VOP_CONV_U1    = 46;
        private const byte VOP_CONV_I2    = 47;
        private const byte VOP_CONV_U2    = 48;
        private const byte VOP_CONV_I4    = 49;
        private const byte VOP_CONV_U4    = 50;
        private const byte VOP_DIV_UN     = 51;
        private const byte VOP_REM_UN     = 52;
        private const byte VOP_SHR_UN     = 53;
        private const byte VOP_CGT_UN     = 54;
        private const byte VOP_CLT_UN     = 55;
        private const byte VOP_LEAVE      = 56;
        private const byte VOP_LDC_I8     = 57;
        private const byte VOP_CONV_I8    = 58;
        private const byte VOP_CONV_U8    = 59;
        private const byte VOP_LDC_R4     = 60;
        private const byte VOP_LDC_R8     = 61;
        private const byte VOP_CONV_R4    = 62;
        private const byte VOP_CONV_R8    = 63;
        private const byte VOP_LDELEM_NORM = 64;
        private const byte VOP_STELEM_VT   = 65;
        private const byte VOP_ENDFINALLY  = 66;
        private const byte VOP_LDFTN       = 67;
        private const byte VOP_NEWDEL      = 68;
        private const byte VOP_SWITCH      = 69;
        private const byte VOP_LDTYPE      = 70;

        private const int OP_COUNT = 71;

        private MethodDef _wideBin;
        private MethodDef _wideUn;
        private MethodDef _wideConv;
        private MethodDef _stElem;
        private MethodDef _findFinally;

        private FieldDef _fldLongs;
        private System.Collections.Generic.List<long> _longPool;
        private System.Collections.Generic.Dictionary<long, int> _longIndex;
        private FieldDef _fldDoubles;
        private System.Collections.Generic.List<double> _doublePool;
        private System.Collections.Generic.Dictionary<double, int> _doubleIndex;

        private Obfuscation engine;
        private Random rng;

        internal VMObfuscationV2Protection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyVMObfuscationV2(ModuleDef module)
        {

            var candidates = new List<MethodDef>();
            int _totalUserMethods = 0;
            foreach (TypeDef type in module.GetTypes().ToList())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                if (engine.IsTypeUserExcluded(type)) continue;
                foreach (MethodDef m in type.Methods.ToList())
                {
                    if (engine.IsMethodUserExcluded(m)) continue;

                    if (!engine.CanProcessMethod(m, true)) continue;
                    if (m.IsConstructor || m.IsStaticConstructor) continue;
                    if (!m.IsStatic)
                    {
                        var dt0 = m.DeclaringType;
                        if (dt0 == null) continue;
                        bool vt0; try { vt0 = dt0.IsValueType; } catch { continue; }
                        if (vt0 || m.IsVirtual || m.IsAbstract || dt0.HasGenericParameters) continue;
                    }
                    if (m.HasGenericParameters) continue;
                    if (m.IsPinvokeImpl) continue;
                    if (m.Body == null || m.Body.Instructions.Count < 2) continue;
                    _totalUserMethods++;
                    if (IsCandidate(m)) candidates.Add(m);
                }
            }
            if (candidates.Count == 0) return;

            var vmType = new TypeDefUser("", engine.MakeName(),
                module.CorLibTypes.Object.TypeDefOrRef);
            vmType.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
            module.Types.Add(vmType);
            engine.injectedTypes.Add(vmType);

            int[] opcodeMap = new int[256];
            for (int i = 0; i < 256; i++) opcodeMap[i] = i;
            for (int i = 255; i > 0; i--)
            {
                int j = rng.Next(0, i + 1);
                int t = opcodeMap[i]; opcodeMap[i] = opcodeMap[j]; opcodeMap[j] = t;
            }

            var byteArrArrSig = new SZArraySig(new SZArraySig(module.CorLibTypes.Byte));
            var byteArrSig    = new SZArraySig(module.CorLibTypes.Byte);
            var stringArrSig  = new SZArraySig(module.CorLibTypes.String);

            var methodBaseTypeRef = module.CorLibTypes.GetTypeRef("System.Reflection", "MethodBase");
            var typeTypeRef       = module.CorLibTypes.GetTypeRef("System", "Type");
            var methodBaseArrSig  = new SZArraySig(new ClassSig(methodBaseTypeRef));
            var typeArrSig        = new SZArraySig(new ClassSig(typeTypeRef));

            var fldCode = new FieldDefUser(engine.MakeName(),
                new FieldSig(byteArrArrSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldCode);

            var fldSeeds = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Int32)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldSeeds);

            var fldNumLocals = new FieldDefUser(engine.MakeName(),
                new FieldSig(byteArrSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldNumLocals);

            var fldStrings = new FieldDefUser(engine.MakeName(),
                new FieldSig(stringArrSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldStrings);

            var fldMethods = new FieldDefUser(engine.MakeName(),
                new FieldSig(methodBaseArrSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldMethods);

            var fldTypes = new FieldDefUser(engine.MakeName(),
                new FieldSig(typeArrSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldTypes);

            var fieldInfoTypeRef = module.CorLibTypes.GetTypeRef("System.Reflection", "FieldInfo");
            var fieldInfoArrSig  = new SZArraySig(new ClassSig(fieldInfoTypeRef));
            var fldFields = new FieldDefUser(engine.MakeName(),
                new FieldSig(fieldInfoArrSig),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldFields);

            var fldEH = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(new SZArraySig(module.CorLibTypes.Int32))),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldEH);

            var fldHash = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.UInt32)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(fldHash);

            _fldLongs = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Int64)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(_fldLongs);

            _fldDoubles = new FieldDefUser(engine.MakeName(),
                new FieldSig(new SZArraySig(module.CorLibTypes.Double)),
                DnFieldAttributes.Assembly | DnFieldAttributes.Static);
            vmType.Fields.Add(_fldDoubles);

            _longPool = new List<long>();
            _longIndex = new Dictionary<long, int>();
            _doublePool = new List<double>();
            _doubleIndex = new Dictionary<double, int>();
            var stringPool = new List<string>();
            var stringIndex = new Dictionary<string, int>(StringComparer.Ordinal);
            var methodPool = new List<IMethod>();
            var methodIndex = new Dictionary<uint, int>();
            var typePool = new List<ITypeDefOrRef>();
            var typeIndex = new Dictionary<uint, int>();
            var fieldPool = new List<IField>();
            var fieldIndex = new Dictionary<uint, int>();

            int mvidMix = MvidToSeed(module.Mvid ?? Guid.Empty);

            var collectedCodes = new List<byte[]>();
            var collectedSeeds = new List<uint>();
            var collectedNumLocals = new List<byte>();
            var collectedEH = new List<int[]>();
            var collectedHashes = new List<uint>();
            var actuallyVirtualized = new List<MethodDef>();
            var slotForMethod = new Dictionary<MethodDef, int>();

            foreach (var m in candidates)
            {
                int numLocals = m.Body.HasVariables ? m.Body.Variables.Count : 0;
                if (numLocals > 255) continue;

                byte[] bc;
                List<int> ehList;
                try
                {
                    bc = EmitBytecode(m, opcodeMap, stringPool, stringIndex,
                        methodPool, methodIndex, typePool, typeIndex, fieldPool, fieldIndex, out ehList);
                }
                catch { continue; }
                if (bc == null || bc.Length == 0) continue;

                uint fnv = 2166136261u;
                for (int b = 0; b < bc.Length; b++) { fnv ^= bc[b]; fnv *= 16777619u; }

                uint xs32Seed;
                do { xs32Seed = (uint)rng.Next(); } while (xs32Seed == 0);
                uint xs32St = xs32Seed;
                for (int b = 0; b < bc.Length; b++)
                {
                    xs32St ^= xs32St << 13;
                    xs32St ^= xs32St >> 17;
                    xs32St ^= xs32St << 5;
                    bc[b] ^= (byte)xs32St;
                }

                int slot = actuallyVirtualized.Count;
                slotForMethod[m] = slot;
                collectedCodes.Add(bc);
                collectedSeeds.Add(xs32Seed ^ (uint)mvidMix);
                collectedNumLocals.Add((byte)numLocals);
                collectedEH.Add(ehList != null ? ehList.ToArray() : new int[0]);
                collectedHashes.Add(fnv);
                actuallyVirtualized.Add(m);
                engine.virtualizedMethods.Add(m);
            }
            engine.vmVirtualizedCount = actuallyVirtualized.Count;
            if (actuallyVirtualized.Count == 0)
            {

                module.Types.Remove(vmType);
                engine.injectedTypes.Remove(vmType);
                return;
            }

            var normInt = BuildNormInt(module, vmType);
            var coerceThis = BuildCoerceThis(module, vmType);
            var coerceValue = BuildCoerceValue(module, vmType);
            var coerceArgs = BuildCoerceArgs(module, vmType, coerceValue);
            var findCatch = BuildFindCatch(module, vmType);
            _wideBin  = BuildWideBin(module, vmType);
            _wideUn   = BuildWideUn(module, vmType);
            _wideConv = BuildWideConv(module, vmType);
            _stElem   = BuildStElem(module, vmType);
            _findFinally = BuildFindFinally(module, vmType);
            var shroud = engine.EnsureShroud(module);
            var dispatcher = BuildDispatcher(module, vmType, fldCode, fldNumLocals,
                fldStrings, fldMethods, fldTypes, fldFields, fldEH, fldHash, opcodeMap, normInt, coerceThis, coerceArgs, findCatch, shroud);
            vmType.Methods.Add(dispatcher);
            engine.injectedMethods.Add(dispatcher);

            var initMethod = BuildInit(module, vmType, fldCode, fldSeeds, fldNumLocals,
                fldStrings, fldMethods, fldTypes, fldFields, fldEH, fldHash, collectedCodes, collectedSeeds, collectedNumLocals, collectedEH, collectedHashes,
                stringPool, methodPool, typePool, fieldPool);
            vmType.Methods.Add(initMethod);
            engine.injectedMethods.Add(initMethod);

            var modType = module.Types.FirstOrDefault(t => t.Name == "<Module>");
            if (modType != null)
                engine.InjectCallInCctor(module, modType, initMethod);

            foreach (var m in actuallyVirtualized)
            {
                int slot = slotForMethod[m];
                EmitStub(module, m, slot, dispatcher);
            }

        }

        private bool IsCandidate(MethodDef m)
        {
            if (!engine.CanProcessMethod(m, true)) return false;
            if (engine.virtualizedMethods.Contains(m)) return false;
            if (m.IsConstructor || m.IsStaticConstructor) return false;
            if (!m.IsStatic)
            {
                var dt = m.DeclaringType;
                if (dt == null) return false;
                bool vt; try { vt = dt.IsValueType; } catch { return false; }
                if (vt) return false;
                if (m.IsVirtual || m.IsAbstract) return false;
                if (dt.HasGenericParameters) return false;
            }
            if (m.HasGenericParameters) return false;
            if (m.IsPinvokeImpl) return false;
            if (m.Body == null) return false;
            if (m.Body.Instructions.Count < 2) return false;

            if (m.Body.HasExceptionHandlers)
            {
                foreach (var eh in m.Body.ExceptionHandlers)
                {
                    if (eh.HandlerType != ExceptionHandlerType.Catch &&
                        eh.HandlerType != ExceptionHandlerType.Finally) return false;
                    if (eh.TryStart == null || eh.TryEnd == null || eh.HandlerStart == null) return false;
                }
            }

            var ret = m.ReturnType;
            if (!IsAllowedSigType(ret) && !IsVoid(ret)) return false;
            foreach (var p in m.Parameters)
            {
                if (p.IsHiddenThisParameter) continue;
                if (!IsAllowedSigType(p.Type)) return false;
            }
            if (m.Body.HasVariables)
            {
                foreach (var v in m.Body.Variables)
                {
                    if (!IsAllowedSigType(v.Type)) return false;
                }
            }

            bool hasAddr = false, hasInstFld = false;
            foreach (var inst in m.Body.Instructions)
            {
                if (!IsAllowedOpcode(inst)) return false;
                var oc = inst.OpCode;
                if (IsLdloca(oc) || IsLdarga(oc)) hasAddr = true;
                else if (oc == DnOpCodes.Ldfld || oc == DnOpCodes.Stfld) hasInstFld = true;
            }

            if (hasAddr && hasInstFld) return false;
            return true;
        }

        private bool IsVoid(TypeSig t)
        {
            return t != null && t.FullName == "System.Void";
        }

        private bool IsAllowedSigType(TypeSig t)
        {
            if (t == null) return false;
            string fn = t.FullName;

            if (fn == "System.Int32"  || fn == "System.UInt32"
             || fn == "System.Int16"  || fn == "System.UInt16"
             || fn == "System.SByte"  || fn == "System.Byte"
             || fn == "System.Boolean"|| fn == "System.Char"
             || fn == "System.String" || fn == "System.Object") return true;

            if (fn == "System.Int64" || fn == "System.UInt64"
             || fn == "System.Double" || fn == "System.Single") return true;

            if (fn == "System.Decimal") return true;

            if (fn == "System.IntPtr" || fn == "System.UIntPtr") return false;
            if (t.IsByRef || t.IsPointer || t.IsPinned || t.IsFunctionPointer) return false;

            try { if (!t.IsValueType) return true; } catch { return false; }

            if (IsEnumType(t)) return true;

            return false;
        }

        private bool IsLdcI4(OpCode op)
        {
            return op == DnOpCodes.Ldc_I4 || op == DnOpCodes.Ldc_I4_S
                || op == DnOpCodes.Ldc_I4_0 || op == DnOpCodes.Ldc_I4_1
                || op == DnOpCodes.Ldc_I4_2 || op == DnOpCodes.Ldc_I4_3
                || op == DnOpCodes.Ldc_I4_4 || op == DnOpCodes.Ldc_I4_5
                || op == DnOpCodes.Ldc_I4_6 || op == DnOpCodes.Ldc_I4_7
                || op == DnOpCodes.Ldc_I4_8 || op == DnOpCodes.Ldc_I4_M1;
        }

        private bool IsAllowedOpcode(Instruction inst)
        {
            var op = inst.OpCode;
            if (op == DnOpCodes.Nop) return true;
            if (op == DnOpCodes.Ret) return true;
            if (op == DnOpCodes.Pop) return true;
            if (op == DnOpCodes.Dup) return true;
            if (op == DnOpCodes.Ldnull) return true;
            if (IsLdarg(op) || IsLdloc(op) || IsStloc(op)) return true;

            if (op == DnOpCodes.Starg || op == DnOpCodes.Starg_S) return true;

            if (IsLdloca(op))
            {
                var l = inst.Operand as Local;
                return l != null && IsRebondableVTSlotType(l.Type);
            }
            if (IsLdarga(op))
            {
                var p = inst.Operand as Parameter;
                return p != null && !p.IsHiddenThisParameter && IsRebondableVTSlotType(p.Type);
            }
            if (op == DnOpCodes.Ldstr) return true;
            if (op == DnOpCodes.Br || op == DnOpCodes.Br_S) return true;
            if (op == DnOpCodes.Brfalse || op == DnOpCodes.Brfalse_S) return true;
            if (op == DnOpCodes.Brtrue  || op == DnOpCodes.Brtrue_S)  return true;

            if (op == DnOpCodes.Switch) return true;

            if (op == DnOpCodes.Throw) return true;
            if (op == DnOpCodes.Leave || op == DnOpCodes.Leave_S) return true;
            if (op == DnOpCodes.Endfinally) return true;

            if (op == DnOpCodes.Call)     return CallTargetOK(inst);
            if (op == DnOpCodes.Callvirt) return CallTargetOK(inst);
            if (op == DnOpCodes.Newobj)
            {

                if (IsDelegateNewobj(inst.Operand as IMethod)) return true;
                return CallTargetOK(inst);
            }

            if (op == DnOpCodes.Ldftn)
            {
                var mrf = inst.Operand as IMethod;
                return mrf != null && !(mrf is MethodSpec);
            }
            if (op == DnOpCodes.Castclass) return inst.Operand is ITypeDefOrRef;
            if (op == DnOpCodes.Isinst)    return inst.Operand is ITypeDefOrRef;

            if (op == DnOpCodes.Ldlen) return true;
            if (op == DnOpCodes.Ldelem_Ref) return true;
            if (op == DnOpCodes.Stelem_Ref) return true;

            if (op == DnOpCodes.Ldelem_I4 || op == DnOpCodes.Stelem_I4) return true;
            if (op == DnOpCodes.Ldelem_I8 || op == DnOpCodes.Stelem_I8) return true;
            if (op == DnOpCodes.Ldelem_R4 || op == DnOpCodes.Stelem_R4) return true;
            if (op == DnOpCodes.Ldelem_R8 || op == DnOpCodes.Stelem_R8) return true;

            if (op == DnOpCodes.Ldelem_I1 || op == DnOpCodes.Ldelem_U1
             || op == DnOpCodes.Ldelem_I2 || op == DnOpCodes.Ldelem_U2) return true;
            if (op == DnOpCodes.Stelem_I1 || op == DnOpCodes.Stelem_I2) return true;
            if (op == DnOpCodes.Newarr)
            {
                var et = inst.Operand as ITypeDefOrRef;
                if (et == null) return false;
                var ets = et.ToTypeSig();
                try { if (!ets.IsValueType) return true; } catch { return false; }
                string efn = ets.FullName;
                return efn == "System.Int32"  || efn == "System.Int64"
                    || efn == "System.Single" || efn == "System.Double"
                    || efn == "System.Byte"   || efn == "System.SByte"
                    || efn == "System.Int16"  || efn == "System.UInt16"
                    || efn == "System.Char"   || efn == "System.Boolean";
            }
            if (op == DnOpCodes.Ldsfld || op == DnOpCodes.Stsfld
                || op == DnOpCodes.Ldfld || op == DnOpCodes.Stfld)
            {
                var fr = inst.Operand as IField;
                return fr != null && FieldAccessOK(fr);
            }

            if (IsLdcI4(op)) return true;

            if (op == DnOpCodes.Ldc_I8) return true;
            if (op == DnOpCodes.Conv_I8 || op == DnOpCodes.Conv_U8) return true;

            if (op == DnOpCodes.Ldc_R4 || op == DnOpCodes.Ldc_R8) return true;
            if (op == DnOpCodes.Conv_R4 || op == DnOpCodes.Conv_R8) return true;

            if (op == DnOpCodes.Add || op == DnOpCodes.Sub || op == DnOpCodes.Mul) return true;
            if (op == DnOpCodes.Div || op == DnOpCodes.Div_Un) return true;
            if (op == DnOpCodes.Rem || op == DnOpCodes.Rem_Un) return true;
            if (op == DnOpCodes.And || op == DnOpCodes.Or || op == DnOpCodes.Xor) return true;
            if (op == DnOpCodes.Neg || op == DnOpCodes.Not) return true;
            if (op == DnOpCodes.Shl || op == DnOpCodes.Shr || op == DnOpCodes.Shr_Un) return true;

            if (op == DnOpCodes.Ceq || op == DnOpCodes.Cgt || op == DnOpCodes.Cgt_Un
                || op == DnOpCodes.Clt || op == DnOpCodes.Clt_Un) return true;

            if (op == DnOpCodes.Conv_I1 || op == DnOpCodes.Conv_U1
                || op == DnOpCodes.Conv_I2 || op == DnOpCodes.Conv_U2
                || op == DnOpCodes.Conv_I4 || op == DnOpCodes.Conv_U4) return true;

            if (op == DnOpCodes.Beq || op == DnOpCodes.Beq_S) return true;
            if (op == DnOpCodes.Bne_Un || op == DnOpCodes.Bne_Un_S) return true;
            if (op == DnOpCodes.Bgt || op == DnOpCodes.Bgt_S) return true;
            if (op == DnOpCodes.Bgt_Un || op == DnOpCodes.Bgt_Un_S) return true;
            if (op == DnOpCodes.Blt || op == DnOpCodes.Blt_S) return true;
            if (op == DnOpCodes.Blt_Un || op == DnOpCodes.Blt_Un_S) return true;
            if (op == DnOpCodes.Bge || op == DnOpCodes.Bge_S) return true;
            if (op == DnOpCodes.Bge_Un || op == DnOpCodes.Bge_Un_S) return true;
            if (op == DnOpCodes.Ble || op == DnOpCodes.Ble_S) return true;
            if (op == DnOpCodes.Ble_Un || op == DnOpCodes.Ble_Un_S) return true;

            if (op == DnOpCodes.Box)
            {
                var bt = inst.Operand as ITypeDefOrRef;
                return bt != null && bt.FullName == "System.Int32";
            }

            if (op == DnOpCodes.Unbox_Any) return true;

            if (op == DnOpCodes.Ldtoken)
                return inst.Operand is ITypeDefOrRef;

            if (op == DnOpCodes.Sizeof)
            {
                var st = inst.Operand as ITypeDefOrRef;
                return st != null && GetKnownSizeof(st.FullName) > 0;
            }
            return false;
        }

        private static int GetKnownSizeof(string fullName)
        {
            switch (fullName)
            {
                case "System.Boolean": case "System.Byte": case "System.SByte": return 1;
                case "System.Char": case "System.Int16": case "System.UInt16": return 2;
                case "System.Int32": case "System.UInt32": case "System.Single": return 4;
                case "System.Int64": case "System.UInt64": case "System.Double": return 8;
                case "System.Decimal": return 16;
                default: return 0;
            }
        }

        private TypeSig SubstituteGenerics(TypeSig t, GenericInstSig typeInst, IList<TypeSig> methodArgs)
        {
            if (t == null) return null;
            var gv = t as GenericVar;
            if (gv != null)
            {
                int i = (int)gv.Number;
                if (typeInst != null && i >= 0 && i < typeInst.GenericArguments.Count)
                    return typeInst.GenericArguments[i];
                return null;
            }
            var mv = t as GenericMVar;
            if (mv != null)
            {
                int i = (int)mv.Number;
                if (methodArgs != null && i >= 0 && i < methodArgs.Count)
                    return methodArgs[i];
                return null;
            }
            return t;
        }

        private bool IsDelegateCtor(IMethod mr)
        {
            if (mr == null || mr.Name != ".ctor") return false;
            var sig = mr.MethodSig;
            if (sig == null || sig.Params.Count != 2) return false;
            var p0 = sig.Params[0];
            var p1 = sig.Params[1];
            if (p0 == null || p1 == null || p0.FullName != "System.Object") return false;
            return p1.ElementType == dnlib.DotNet.ElementType.I || p1.FullName == "System.IntPtr";
        }

        private bool IsDelegateNewobj(IMethod mr)
        {
            if (IsDelegateCtor(mr)) return true;
            return mr != null && mr.DeclaringType != null && IsDelegateType(mr.DeclaringType);
        }

        private bool IsDelegateType(ITypeDefOrRef t)
        {
            if (t == null) return false;
            try
            {
                var gi = t.ToTypeSig() as GenericInstSig;
                ITypeDefOrRef cur = gi != null ? gi.GenericType.TypeDefOrRef : t;
                var td = cur != null ? cur.ResolveTypeDef() : null;
                int guard = 0;
                while (td != null && guard++ < 10)
                {
                    var bt = td.BaseType;
                    if (bt == null) return false;
                    string bn = bt.FullName;
                    if (bn == "System.MulticastDelegate" || bn == "System.Delegate") return true;
                    if (bn == "System.Object" || bn == "System.ValueType") return false;
                    td = bt.ResolveTypeDef();
                }
            }
            catch { }
            return false;
        }

        private bool IsGetTypeFromHandleCall(Instruction inst)
        {
            if (inst == null || inst.OpCode != DnOpCodes.Call) return false;
            var mr = inst.Operand as IMethod;
            if (mr == null || mr.Name != "GetTypeFromHandle") return false;
            var dt = mr.DeclaringType;
            return dt != null && dt.FullName == "System.Type";
        }

        private bool CallTargetOK(Instruction inst)
        {

            if (IsGetTypeFromHandleCall(inst)) return true;
            var mr = inst.Operand as IMethod;
            if (mr == null) return false;
            var sig = mr.MethodSig;
            if (sig == null) return false;

            var dt = mr.DeclaringType;
            GenericInstSig typeInst = dt != null ? dt.ToTypeSig() as GenericInstSig : null;

            IList<TypeSig> methodArgs = null;
            var ms = mr as MethodSpec;
            if (ms != null)
            {
                var gim = ms.GenericInstMethodSig;
                if (gim == null) return false;
                methodArgs = gim.GenericArguments;
            }
            else if (sig.GenParamCount != 0)
            {

                return false;
            }

            var ret = SubstituteGenerics(sig.RetType, typeInst, methodArgs);
            if (!IsVoid(ret) && !IsAllowedSigType(ret)) return false;
            foreach (var p in sig.Params)
            {
                var ap = SubstituteGenerics(p, typeInst, methodArgs);
                if (!IsCallParamType(ap)) return false;
            }
            return true;
        }

        private bool IsCallParamType(TypeSig t)
        {
            if (t == null) return false;
            string fn = t.FullName;
            if (fn == "System.Int32" || fn == "System.String" || fn == "System.Object") return true;

            if (fn == "System.Boolean" || fn == "System.SByte"  || fn == "System.Byte"
             || fn == "System.Char"    || fn == "System.Int16"  || fn == "System.UInt16") return true;

            if (fn == "System.UInt32" || fn == "System.UInt64") return true;

            if (fn == "System.Decimal") return true;

            if (fn == "System.Int64" || fn == "System.Double" || fn == "System.Single") return true;
            if (t.IsByRef || t.IsPointer || t.IsPinned || t.IsFunctionPointer) return false;
            try { if (!t.IsValueType) return true; } catch { return false; }

            if (IsEnumType(t)) return true;
            return false;
        }

        private bool FieldAccessOK(IField fr)
        {
            var sig = fr.FieldSig;
            if (sig == null) return false;
            var dt = fr.DeclaringType;
            GenericInstSig typeInst = dt != null ? dt.ToTypeSig() as GenericInstSig : null;

            var ft = SubstituteGenerics(sig.Type, typeInst, null);
            if (!IsCallParamType(ft)) return false;
            return true;
        }

        private bool IsLdarg(OpCode op)
        {
            return op == DnOpCodes.Ldarg || op == DnOpCodes.Ldarg_S
                || op == DnOpCodes.Ldarg_0 || op == DnOpCodes.Ldarg_1
                || op == DnOpCodes.Ldarg_2 || op == DnOpCodes.Ldarg_3;
        }

        private bool IsLdloc(OpCode op)
        {
            return op == DnOpCodes.Ldloc || op == DnOpCodes.Ldloc_S
                || op == DnOpCodes.Ldloc_0 || op == DnOpCodes.Ldloc_1
                || op == DnOpCodes.Ldloc_2 || op == DnOpCodes.Ldloc_3;
        }

        private bool IsStloc(OpCode op)
        {
            return op == DnOpCodes.Stloc || op == DnOpCodes.Stloc_S
                || op == DnOpCodes.Stloc_0 || op == DnOpCodes.Stloc_1
                || op == DnOpCodes.Stloc_2 || op == DnOpCodes.Stloc_3;
        }

        private int GetArgIndex(Instruction inst)
        {
            var op = inst.OpCode;
            if (op == DnOpCodes.Ldarg_0) return 0;
            if (op == DnOpCodes.Ldarg_1) return 1;
            if (op == DnOpCodes.Ldarg_2) return 2;
            if (op == DnOpCodes.Ldarg_3) return 3;
            var p = inst.Operand as Parameter;
            if (p != null) return p.Index;
            return Convert.ToInt32(inst.Operand);
        }

        private int GetLocalIndex(Instruction inst)
        {
            var op = inst.OpCode;
            if (op == DnOpCodes.Ldloc_0 || op == DnOpCodes.Stloc_0) return 0;
            if (op == DnOpCodes.Ldloc_1 || op == DnOpCodes.Stloc_1) return 1;
            if (op == DnOpCodes.Ldloc_2 || op == DnOpCodes.Stloc_2) return 2;
            if (op == DnOpCodes.Ldloc_3 || op == DnOpCodes.Stloc_3) return 3;
            var l = inst.Operand as Local;
            if (l != null) return l.Index;
            return Convert.ToInt32(inst.Operand);
        }

        private bool IsLdloca(OpCode op)
        {
            return op == DnOpCodes.Ldloca || op == DnOpCodes.Ldloca_S;
        }

        private bool IsLdarga(OpCode op)
        {
            return op == DnOpCodes.Ldarga || op == DnOpCodes.Ldarga_S;
        }

        private bool IsInt32FamilyName(string fn)
        {
            return fn == "System.Int32"  || fn == "System.UInt32"
                || fn == "System.Int16"  || fn == "System.UInt16"
                || fn == "System.SByte"  || fn == "System.Byte"
                || fn == "System.Boolean"|| fn == "System.Char";
        }

        private bool IsRebondableVTSlotType(TypeSig t)
        {
            if (t == null) return false;
            string fn = t.FullName;
            return fn == "System.Int32"
                || fn == "System.Int16"  || fn == "System.UInt16"
                || fn == "System.SByte"  || fn == "System.Byte"
                || fn == "System.Boolean"|| fn == "System.Char"
                || fn == "System.UInt32"  || fn == "System.UInt64"
                || fn == "System.Decimal"

                || fn == "System.Int64"  || fn == "System.Double" || fn == "System.Single";
        }

        private bool IsEnumType(TypeSig t)
        {
            return EnumUnderlyingElementType(t) != ElementType.End;
        }

        private ElementType EnumUnderlyingElementType(TypeSig t)
        {
            if (t == null) return ElementType.End;
            if (t.IsByRef || t.IsPointer || t.IsPinned || t.IsFunctionPointer) return ElementType.End;
            try
            {
                if (!t.IsValueType) return ElementType.End;
                var tdr = t.ToTypeDefOrRef();
                if (tdr == null) return ElementType.End;
                var td = tdr.ResolveTypeDef();
                if (td == null || !td.IsEnum) return ElementType.End;

                TypeSig underlying = null;
                foreach (var ef in td.Fields)
                {
                    if (ef.IsStatic || ef.FieldSig == null) continue;
                    underlying = ef.FieldSig.Type;
                    break;
                }
                if (underlying == null) return ElementType.End;
                var et = underlying.ElementType;

                switch (et)
                {
                    case ElementType.I4:
                    case ElementType.U4:
                    case ElementType.I2:
                    case ElementType.U2:
                    case ElementType.I1:
                    case ElementType.U1:
                    case ElementType.Char:
                    case ElementType.Boolean:
                    case ElementType.I8:
                    case ElementType.U8:
                        return et;
                    default:
                        return ElementType.End;
                }
            }
            catch { return ElementType.End; }
        }

        private static bool IsEnumInt32Family(ElementType et)
        {
            return et == ElementType.I4 || et == ElementType.U4
                || et == ElementType.I2 || et == ElementType.U2
                || et == ElementType.I1 || et == ElementType.U1
                || et == ElementType.Char || et == ElementType.Boolean;
        }

        private byte[] EmitBytecode(MethodDef method, int[] opcodeMap,
            List<string> stringPool, Dictionary<string, int> stringIndex,
            List<IMethod> methodPool, Dictionary<uint, int> methodIndex,
            List<ITypeDefOrRef> typePool, Dictionary<uint, int> typeIndex,
            List<IField> fieldPool, Dictionary<uint, int> fieldIndex,
            out List<int> ehList)
        {
            ehList = new List<int>();
            var bc = new List<byte>();
            var ipOfIl = new Dictionary<Instruction, int>();
            var pendingBranches = new List<KeyValuePair<int, Instruction>>();
            var insts = method.Body.Instructions;

            for (int _i = 0; _i < insts.Count; _i++)
            {
                var inst = insts[_i];
                ipOfIl[inst] = bc.Count;
                var op = inst.OpCode;

                if (op == DnOpCodes.Nop)
                {
                    bc.Add((byte)opcodeMap[VOP_NOP]);
                }
                else if (op == DnOpCodes.Ret)
                {
                    bc.Add((byte)opcodeMap[VOP_RET]);
                }
                else if (op == DnOpCodes.Pop)
                {
                    bc.Add((byte)opcodeMap[VOP_POP]);
                }
                else if (op == DnOpCodes.Dup)
                {
                    bc.Add((byte)opcodeMap[VOP_DUP]);
                }
                else if (op == DnOpCodes.Ldnull)
                {
                    bc.Add((byte)opcodeMap[VOP_LDNULL]);
                }
                else if (IsLdarg(op))
                {
                    int idx = GetArgIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    bc.Add((byte)opcodeMap[VOP_LDARG]);
                    bc.Add((byte)idx);
                }
                else if (IsLdloc(op))
                {
                    int idx = GetLocalIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    bc.Add((byte)opcodeMap[VOP_LDLOC]);
                    bc.Add((byte)idx);
                }
                else if (IsStloc(op))
                {
                    int idx = GetLocalIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    bc.Add((byte)opcodeMap[VOP_STLOC]);
                    bc.Add((byte)idx);
                }
                else if (IsLdloca(op))
                {

                    int idx = GetLocalIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    bc.Add((byte)opcodeMap[VOP_LDLOC]);
                    bc.Add((byte)idx);
                }
                else if (IsLdarga(op))
                {
                    int idx = GetArgIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    bc.Add((byte)opcodeMap[VOP_LDARG]);
                    bc.Add((byte)idx);
                }
                else if (op == DnOpCodes.Starg || op == DnOpCodes.Starg_S)
                {
                    int idx = GetArgIndex(inst);
                    if (idx < 0 || idx > 255) return null;
                    bc.Add((byte)opcodeMap[VOP_STARG]);
                    bc.Add((byte)idx);
                }
                else if (op == DnOpCodes.Ldstr)
                {
                    string s = inst.Operand as string ?? "";
                    int sidx;
                    if (!stringIndex.TryGetValue(s, out sidx))
                    {
                        sidx = stringPool.Count;
                        stringPool.Add(s);
                        stringIndex[s] = sidx;
                    }
                    bc.Add((byte)opcodeMap[VOP_LDSTR]);
                    EmitInt32LE(bc, sidx);
                }
                else if (op == DnOpCodes.Br || op == DnOpCodes.Br_S)
                {
                    bc.Add((byte)opcodeMap[VOP_BR]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Brtrue || op == DnOpCodes.Brtrue_S)
                {
                    bc.Add((byte)opcodeMap[VOP_BRTRUE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Brfalse || op == DnOpCodes.Brfalse_S)
                {
                    bc.Add((byte)opcodeMap[VOP_BRFALSE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Leave || op == DnOpCodes.Leave_S)
                {

                    bc.Add((byte)opcodeMap[VOP_LEAVE]);
                    pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, (Instruction)inst.Operand));
                    EmitInt32LE(bc, 0);
                }
                else if (op == DnOpCodes.Throw)
                {
                    bc.Add((byte)opcodeMap[VOP_THROW]);
                }
                else if (op == DnOpCodes.Endfinally)
                {
                    bc.Add((byte)opcodeMap[VOP_ENDFINALLY]);
                }
                else if (op == DnOpCodes.Switch)
                {

                    var tgts = inst.Operand as IList<Instruction>;
                    if (tgts == null) return null;
                    bc.Add((byte)opcodeMap[VOP_SWITCH]);
                    EmitInt32LE(bc, tgts.Count);
                    for (int k = 0; k < tgts.Count; k++)
                    {
                        if (tgts[k] == null) return null;
                        pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, tgts[k]));
                        EmitInt32LE(bc, 0);
                    }
                }
                else if (op == DnOpCodes.Ldftn)
                {

                    var mr = inst.Operand as IMethod;
                    if (mr == null) return null;
                    uint key = mr.MDToken.Raw;
                    int midx;
                    if (!methodIndex.TryGetValue(key, out midx))
                    {
                        midx = methodPool.Count;
                        methodPool.Add(mr);
                        methodIndex[key] = midx;
                    }
                    bc.Add((byte)opcodeMap[VOP_LDFTN]);
                    EmitInt32LE(bc, midx);
                }
                else if (op == DnOpCodes.Newobj && IsDelegateNewobj(inst.Operand as IMethod))
                {

                    var dtok = (inst.Operand as IMethod).DeclaringType;
                    uint key = dtok.MDToken.Raw;
                    int tidx;
                    if (!typeIndex.TryGetValue(key, out tidx))
                    {
                        tidx = typePool.Count;
                        typePool.Add(dtok);
                        typeIndex[key] = tidx;
                    }
                    bc.Add((byte)opcodeMap[VOP_NEWDEL]);
                    EmitInt32LE(bc, tidx);
                }
                else if (op == DnOpCodes.Call || op == DnOpCodes.Callvirt || op == DnOpCodes.Newobj)
                {
                    var mr = inst.Operand as IMethod;
                    if (mr == null) return null;
                    uint key = mr.MDToken.Raw;
                    int midx;
                    if (!methodIndex.TryGetValue(key, out midx))
                    {
                        midx = methodPool.Count;
                        methodPool.Add(mr);
                        methodIndex[key] = midx;
                    }
                    byte vop;
                    if (op == DnOpCodes.Call) vop = VOP_CALL;
                    else if (op == DnOpCodes.Callvirt) vop = VOP_CALLVIRT;
                    else vop = VOP_NEWOBJ;
                    bc.Add((byte)opcodeMap[vop]);
                    EmitInt32LE(bc, midx);
                }
                else if (op == DnOpCodes.Castclass)
                {
                    var tr = inst.Operand as ITypeDefOrRef;
                    if (tr == null) return null;
                    uint key = tr.MDToken.Raw;
                    int tidx;
                    if (!typeIndex.TryGetValue(key, out tidx))
                    {
                        tidx = typePool.Count;
                        typePool.Add(tr);
                        typeIndex[key] = tidx;
                    }
                    bc.Add((byte)opcodeMap[VOP_CASTCLASS]);
                    EmitInt32LE(bc, tidx);
                }
                else if (op == DnOpCodes.Isinst)
                {
                    var tr = inst.Operand as ITypeDefOrRef;
                    if (tr == null) return null;
                    uint key = tr.MDToken.Raw;
                    int tidx;
                    if (!typeIndex.TryGetValue(key, out tidx))
                    {
                        tidx = typePool.Count;
                        typePool.Add(tr);
                        typeIndex[key] = tidx;
                    }
                    bc.Add((byte)opcodeMap[VOP_ISINST]);
                    EmitInt32LE(bc, tidx);
                }
                else if (op == DnOpCodes.Newarr)
                {
                    var tr = inst.Operand as ITypeDefOrRef;
                    if (tr == null) return null;
                    uint key = tr.MDToken.Raw;
                    int tidx;
                    if (!typeIndex.TryGetValue(key, out tidx))
                    {
                        tidx = typePool.Count;
                        typePool.Add(tr);
                        typeIndex[key] = tidx;
                    }
                    bc.Add((byte)opcodeMap[VOP_NEWARR]);
                    EmitInt32LE(bc, tidx);
                }
                else if (op == DnOpCodes.Ldlen)       bc.Add((byte)opcodeMap[VOP_LDLEN]);

                else if (op == DnOpCodes.Ldelem_Ref || op == DnOpCodes.Ldelem_I4 || op == DnOpCodes.Ldelem_I8
                      || op == DnOpCodes.Ldelem_R4  || op == DnOpCodes.Ldelem_R8)
                    bc.Add((byte)opcodeMap[VOP_LDELEM_REF]);
                else if (op == DnOpCodes.Stelem_Ref || op == DnOpCodes.Stelem_I4 || op == DnOpCodes.Stelem_I8
                      || op == DnOpCodes.Stelem_R4  || op == DnOpCodes.Stelem_R8)
                    bc.Add((byte)opcodeMap[VOP_STELEM_REF]);

                else if (op == DnOpCodes.Ldelem_I1 || op == DnOpCodes.Ldelem_U1
                      || op == DnOpCodes.Ldelem_I2 || op == DnOpCodes.Ldelem_U2)
                    bc.Add((byte)opcodeMap[VOP_LDELEM_NORM]);
                else if (op == DnOpCodes.Stelem_I1 || op == DnOpCodes.Stelem_I2)
                    bc.Add((byte)opcodeMap[VOP_STELEM_VT]);
                else if (op == DnOpCodes.Ldsfld || op == DnOpCodes.Stsfld
                      || op == DnOpCodes.Ldfld  || op == DnOpCodes.Stfld)
                {
                    var fr = inst.Operand as IField;
                    if (fr == null) return null;
                    uint key = fr.MDToken.Raw;
                    int fidx;
                    if (!fieldIndex.TryGetValue(key, out fidx))
                    {
                        fidx = fieldPool.Count;
                        fieldPool.Add(fr);
                        fieldIndex[key] = fidx;
                    }
                    byte vop = op == DnOpCodes.Ldsfld ? VOP_LDSFLD
                             : op == DnOpCodes.Stsfld ? VOP_STSFLD
                             : op == DnOpCodes.Ldfld  ? VOP_LDFLD : VOP_STFLD;
                    bc.Add((byte)opcodeMap[vop]);
                    EmitInt32LE(bc, fidx);
                }
                else if (IsLdcI4(op))
                {
                    int val = inst.GetLdcI4Value();
                    bc.Add((byte)opcodeMap[VOP_LDC_I4]);
                    EmitInt32LE(bc, val);
                }
                else if (op == DnOpCodes.Ldc_I8)
                {
                    long lv = (long)inst.Operand;
                    int li;
                    if (!_longIndex.TryGetValue(lv, out li))
                    {
                        li = _longPool.Count;
                        _longPool.Add(lv);
                        _longIndex[lv] = li;
                    }
                    bc.Add((byte)opcodeMap[VOP_LDC_I8]);
                    EmitInt32LE(bc, li);
                }
                else if (op == DnOpCodes.Conv_I8) bc.Add((byte)opcodeMap[VOP_CONV_I8]);
                else if (op == DnOpCodes.Conv_U8) bc.Add((byte)opcodeMap[VOP_CONV_U8]);
                else if (op == DnOpCodes.Ldc_R8)
                {
                    double dv = (double)inst.Operand;
                    int di;
                    if (!_doubleIndex.TryGetValue(dv, out di))
                    {
                        di = _doublePool.Count; _doublePool.Add(dv); _doubleIndex[dv] = di;
                    }
                    bc.Add((byte)opcodeMap[VOP_LDC_R8]);
                    EmitInt32LE(bc, di);
                }
                else if (op == DnOpCodes.Ldc_R4)
                {
                    double dv = (double)(float)inst.Operand;
                    int di;
                    if (!_doubleIndex.TryGetValue(dv, out di))
                    {
                        di = _doublePool.Count; _doublePool.Add(dv); _doubleIndex[dv] = di;
                    }
                    bc.Add((byte)opcodeMap[VOP_LDC_R4]);
                    EmitInt32LE(bc, di);
                }
                else if (op == DnOpCodes.Conv_R4) bc.Add((byte)opcodeMap[VOP_CONV_R4]);
                else if (op == DnOpCodes.Conv_R8) bc.Add((byte)opcodeMap[VOP_CONV_R8]);
                else if (op == DnOpCodes.Add) bc.Add((byte)opcodeMap[VOP_ADD]);
                else if (op == DnOpCodes.Sub) bc.Add((byte)opcodeMap[VOP_SUB]);
                else if (op == DnOpCodes.Mul) bc.Add((byte)opcodeMap[VOP_MUL]);
                else if (op == DnOpCodes.Div) bc.Add((byte)opcodeMap[VOP_DIV]);
                else if (op == DnOpCodes.Div_Un) bc.Add((byte)opcodeMap[VOP_DIV_UN]);
                else if (op == DnOpCodes.Rem) bc.Add((byte)opcodeMap[VOP_REM]);
                else if (op == DnOpCodes.Rem_Un) bc.Add((byte)opcodeMap[VOP_REM_UN]);
                else if (op == DnOpCodes.And) bc.Add((byte)opcodeMap[VOP_AND]);
                else if (op == DnOpCodes.Or)  bc.Add((byte)opcodeMap[VOP_OR]);
                else if (op == DnOpCodes.Xor) bc.Add((byte)opcodeMap[VOP_XOR]);
                else if (op == DnOpCodes.Neg) bc.Add((byte)opcodeMap[VOP_NEG]);
                else if (op == DnOpCodes.Not) bc.Add((byte)opcodeMap[VOP_NOT]);
                else if (op == DnOpCodes.Shl) bc.Add((byte)opcodeMap[VOP_SHL]);
                else if (op == DnOpCodes.Shr) bc.Add((byte)opcodeMap[VOP_SHR]);
                else if (op == DnOpCodes.Shr_Un) bc.Add((byte)opcodeMap[VOP_SHR_UN]);
                else if (op == DnOpCodes.Ceq) bc.Add((byte)opcodeMap[VOP_CEQ]);
                else if (op == DnOpCodes.Cgt) bc.Add((byte)opcodeMap[VOP_CGT]);
                else if (op == DnOpCodes.Cgt_Un) bc.Add((byte)opcodeMap[VOP_CGT_UN]);
                else if (op == DnOpCodes.Clt) bc.Add((byte)opcodeMap[VOP_CLT]);
                else if (op == DnOpCodes.Clt_Un) bc.Add((byte)opcodeMap[VOP_CLT_UN]);
                else if (op == DnOpCodes.Conv_I1) bc.Add((byte)opcodeMap[VOP_CONV_I1]);
                else if (op == DnOpCodes.Conv_U1) bc.Add((byte)opcodeMap[VOP_CONV_U1]);
                else if (op == DnOpCodes.Conv_I2) bc.Add((byte)opcodeMap[VOP_CONV_I2]);
                else if (op == DnOpCodes.Conv_U2) bc.Add((byte)opcodeMap[VOP_CONV_U2]);
                else if (op == DnOpCodes.Conv_I4) bc.Add((byte)opcodeMap[VOP_CONV_I4]);
                else if (op == DnOpCodes.Conv_U4) bc.Add((byte)opcodeMap[VOP_CONV_U4]);

                else if (op == DnOpCodes.Box || op == DnOpCodes.Unbox_Any)
                    bc.Add((byte)opcodeMap[VOP_NOP]);

                else if (op == DnOpCodes.Beq || op == DnOpCodes.Beq_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CEQ, VOP_BRTRUE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Bne_Un || op == DnOpCodes.Bne_Un_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CEQ, VOP_BRFALSE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Bgt || op == DnOpCodes.Bgt_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CGT, VOP_BRTRUE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Bgt_Un || op == DnOpCodes.Bgt_Un_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CGT_UN, VOP_BRTRUE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Blt || op == DnOpCodes.Blt_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CLT, VOP_BRTRUE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Blt_Un || op == DnOpCodes.Blt_Un_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CLT_UN, VOP_BRTRUE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Bge || op == DnOpCodes.Bge_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CLT, VOP_BRFALSE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Bge_Un || op == DnOpCodes.Bge_Un_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CLT_UN, VOP_BRFALSE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Ble || op == DnOpCodes.Ble_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CGT, VOP_BRFALSE, pendingBranches, (Instruction)inst.Operand);
                else if (op == DnOpCodes.Ble_Un || op == DnOpCodes.Ble_Un_S)
                    EmitCmpBranch(bc, opcodeMap, VOP_CGT_UN, VOP_BRFALSE, pendingBranches, (Instruction)inst.Operand);

                else if (op == DnOpCodes.Ldtoken && inst.Operand is ITypeDefOrRef)
                {

                    if (_i + 1 >= insts.Count) return null;
                    var next = insts[_i + 1];
                    if (!IsGetTypeFromHandleCall(next)) return null;
                    var tr = (ITypeDefOrRef)inst.Operand;
                    uint key = tr.MDToken.Raw;
                    int tidx;
                    if (!typeIndex.TryGetValue(key, out tidx))
                    {
                        tidx = typePool.Count;
                        typePool.Add(tr);
                        typeIndex[key] = tidx;
                    }
                    bc.Add((byte)opcodeMap[VOP_LDTYPE]);
                    EmitInt32LE(bc, tidx);

                    _i++;
                    ipOfIl[insts[_i]] = bc.Count;
                }

                else if (op == DnOpCodes.Sizeof)
                {
                    var st = inst.Operand as ITypeDefOrRef;
                    if (st == null) return null;
                    int sz = GetKnownSizeof(st.FullName);
                    if (sz <= 0) return null;
                    bc.Add((byte)opcodeMap[VOP_LDC_I4]);
                    EmitInt32LE(bc, sz);
                }
                else
                {
                    return null;
                }
            }

            foreach (var pb in pendingBranches)
            {
                var target = pb.Value;
                if (target == null || !ipOfIl.ContainsKey(target)) return null;
                int targetIp = ipOfIl[target];
                bc[pb.Key]     = (byte)(targetIp & 0xFF);
                bc[pb.Key + 1] = (byte)((targetIp >> 8) & 0xFF);
                bc[pb.Key + 2] = (byte)((targetIp >> 16) & 0xFF);
                bc[pb.Key + 3] = (byte)((targetIp >> 24) & 0xFF);
            }

            if (method.Body.HasExceptionHandlers)
            {
                foreach (var eh in method.Body.ExceptionHandlers)
                {
                    bool isFinally = eh.HandlerType == ExceptionHandlerType.Finally;
                    if (eh.HandlerType != ExceptionHandlerType.Catch && !isFinally) return null;
                    if (eh.TryStart == null || eh.HandlerStart == null) return null;
                    if (!ipOfIl.ContainsKey(eh.TryStart) || !ipOfIl.ContainsKey(eh.HandlerStart)) return null;
                    int ts = ipOfIl[eh.TryStart];
                    int te = (eh.TryEnd != null && ipOfIl.ContainsKey(eh.TryEnd)) ? ipOfIl[eh.TryEnd] : bc.Count;
                    int hs = ipOfIl[eh.HandlerStart];
                    int cti = -2;
                    if (!isFinally)
                    {
                        cti = -1;
                        if (eh.CatchType != null)
                        {
                            uint key = eh.CatchType.MDToken.Raw;
                            int tidx;
                            if (!typeIndex.TryGetValue(key, out tidx))
                            {
                                tidx = typePool.Count;
                                typePool.Add(eh.CatchType);
                                typeIndex[key] = tidx;
                            }
                            cti = tidx;
                        }
                    }
                    ehList.Add(ts); ehList.Add(te); ehList.Add(hs); ehList.Add(cti);
                }
            }

            return bc.ToArray();
        }

        private void EmitInt32LE(List<byte> bc, int v)
        {
            bc.Add((byte)(v & 0xFF));
            bc.Add((byte)((v >> 8) & 0xFF));
            bc.Add((byte)((v >> 16) & 0xFF));
            bc.Add((byte)((v >> 24) & 0xFF));
        }

        private void EmitCmpBranch(List<byte> bc, int[] opcodeMap, byte cmpVop, byte brVop,
            List<KeyValuePair<int, Instruction>> pendingBranches, Instruction target)
        {
            bc.Add((byte)opcodeMap[cmpVop]);
            bc.Add((byte)opcodeMap[brVop]);
            pendingBranches.Add(new KeyValuePair<int, Instruction>(bc.Count, target));
            EmitInt32LE(bc, 0);
        }

        private void EmitStub(ModuleDef module, MethodDef method, int slot, MethodDef dispatcher)
        {
            method.Body.Instructions.Clear();
            method.Body.Variables.Clear();
            method.Body.ExceptionHandlers.Clear();
            method.Body.InitLocals = true;

            var il = method.Body.Instructions;
            var objectTypeRef = module.CorLibTypes.Object.TypeDefOrRef;

            int numArgs = method.Parameters.Count;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, slot));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, numArgs));
            il.Add(Instruction.Create(DnOpCodes.Newarr, objectTypeRef));
            for (int i = 0; i < numArgs; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[i]));
                var pft = method.Parameters[i].Type;

                if (pft != null && pft.IsValueType)
                {
                    string pfn = pft.FullName;
                    ITypeDefOrRef bt;

                    var enumUnderlying = EnumUnderlyingElementType(pft);
                    if (enumUnderlying != ElementType.End)
                    {

                        bt = (enumUnderlying == ElementType.I8 || enumUnderlying == ElementType.U8)
                            ? module.CorLibTypes.Int64.TypeDefOrRef
                            : module.CorLibTypes.Int32.TypeDefOrRef;
                    }
                    else
                    {
                        bt = (pfn == "System.Int64" || pfn == "System.UInt64") ? module.CorLibTypes.Int64.TypeDefOrRef
                           : pfn == "System.Double" ? module.CorLibTypes.Double.TypeDefOrRef
                           : pfn == "System.Single" ? module.CorLibTypes.Single.TypeDefOrRef
                           : IsInt32FamilyName(pfn) ? module.CorLibTypes.Int32.TypeDefOrRef
                           : pft.ToTypeDefOrRef();
                    }
                    il.Add(Instruction.Create(DnOpCodes.Box, bt));
                }
                il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            }

            il.Add(Instruction.Create(DnOpCodes.Call, dispatcher));

            if (IsVoid(method.ReturnType))
            {
                il.Add(Instruction.Create(DnOpCodes.Pop));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
            else
            {
                var rt = method.ReturnType;
                if (rt != null && rt.IsValueType)
                {

                    string rfn = rt.FullName;
                    ITypeDefOrRef ut;
                    var enumUnderlyingRet = EnumUnderlyingElementType(rt);
                    if (enumUnderlyingRet != ElementType.End)
                    {

                        ut = (enumUnderlyingRet == ElementType.I8 || enumUnderlyingRet == ElementType.U8)
                            ? module.CorLibTypes.Int64.TypeDefOrRef
                            : module.CorLibTypes.Int32.TypeDefOrRef;
                    }
                    else
                    {
                        ut = (rfn == "System.Int64" || rfn == "System.UInt64") ? module.CorLibTypes.Int64.TypeDefOrRef
                           : rfn == "System.Double" ? module.CorLibTypes.Double.TypeDefOrRef
                           : rfn == "System.Single" ? module.CorLibTypes.Single.TypeDefOrRef
                           : IsInt32FamilyName(rfn) ? module.CorLibTypes.Int32.TypeDefOrRef
                           : rt.ToTypeDefOrRef();
                    }
                    il.Add(Instruction.Create(DnOpCodes.Unbox_Any, ut));
                }
                else
                    il.Add(Instruction.Create(DnOpCodes.Castclass, rt.ToTypeDefOrRef()));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
        }

        private MethodDef BuildDispatcher(ModuleDef module, TypeDef vmType,
            FieldDef fldCode, FieldDef fldNumLocals,
            FieldDef fldStrings, FieldDef fldMethods, FieldDef fldTypes, FieldDef fldFields, FieldDef fldEH,
            FieldDef fldHash, int[] opcodeMap, MethodDef normInt, MethodDef coerceThis, MethodDef coerceArgs, MethodDef findCatch, NativeShroud shroud)
        {
            var int32 = module.CorLibTypes.Int32;
            var byteT = module.CorLibTypes.Byte;
            var objT  = module.CorLibTypes.Object;
            var stringT = module.CorLibTypes.String;

            var byteArr = new SZArraySig(byteT);
            var objArr  = new SZArraySig(objT);

            var sig = MethodSig.CreateStatic(objT, int32, objArr);
            var method = new MethodDefUser(engine.MakeName(), sig,
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;

            method.Body.Variables.Add(new Local(byteArr));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(objArr));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(objArr));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(objT));
            method.Body.Variables.Add(new Local(objT));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(objT));
            method.Body.Variables.Add(new Local(objT));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(objT));
            method.Body.Variables.Add(new Local(new SZArraySig(int32)));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));
            method.Body.Variables.Add(new Local(int32));

            const int LOC_CODE = 0;
            const int LOC_IP = 1;
            const int LOC_OP = 2;
            const int LOC_STACK = 3;
            const int LOC_SP = 4;
            const int LOC_LOCALS = 5;
            const int LOC_T1 = 6;
            const int LOC_O1 = 7;
            const int LOC_O2 = 8;
            const int LOC_RETURNED = 9;
            const int LOC_RETVAL = 10;
            const int LOC_EX = 11;
            const int LOC_FINFROM = 12;
            const int LOC_PENDKIND = 13;
            const int LOC_PENDTGT = 14;
            const int LOC_PENDBND = 15;
            const int LOC_PENDEXC = 16;
            const int LOC_EH = 17;
            const int LOC_SWN = 18;
            const int LOC_SWIDX = 19;
            const int LOC_HFNV = 20;
            const int LOC_HIDX = 21;

            const int ARG_SLOT = 0;
            const int ARG_ARGS = 1;

            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldCode));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_SLOT]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_CODE]));

            {
                unchecked { il.Add(Instruction.Create(DnOpCodes.Ldc_I4, (int)2166136261u)); }
                il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_HFNV]));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_HIDX]));

                var hLoopCond = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_HIDX]);
                var hLoopBody = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]);
                var hAfterLoop = Instruction.Create(DnOpCodes.Nop);
                il.Add(Instruction.Create(DnOpCodes.Br, hLoopCond));

                il.Add(hLoopBody);
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_HIDX]));
                il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_HFNV]));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                unchecked { il.Add(Instruction.Create(DnOpCodes.Ldc_I4, (int)16777619u)); }
                il.Add(Instruction.Create(DnOpCodes.Mul));
                il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_HFNV]));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_HIDX]));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_HIDX]));

                il.Add(hLoopCond);
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
                il.Add(Instruction.Create(DnOpCodes.Ldlen));
                il.Add(Instruction.Create(DnOpCodes.Conv_I4));
                il.Add(Instruction.Create(DnOpCodes.Blt, hLoopBody));

                il.Add(hAfterLoop);

                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_HFNV]));
                il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldHash));
                il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_SLOT]));
                il.Add(Instruction.Create(DnOpCodes.Ldelem_U4));
                il.Add(Instruction.Create(DnOpCodes.Conv_I4));
                var hMatch = Instruction.Create(DnOpCodes.Nop);
                il.Add(Instruction.Create(DnOpCodes.Beq, hMatch));

                il.Add(Instruction.Create(DnOpCodes.Call, shroud.GetCurrentProcess));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
                il.Add(Instruction.Create(DnOpCodes.Call, shroud.TerminateProcess));
                il.Add(Instruction.Create(DnOpCodes.Pop));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
                il.Add(Instruction.Create(DnOpCodes.Call, shroud.ExitProcess));

                il.Add(hMatch);
            }

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 1024));
            il.Add(Instruction.Create(DnOpCodes.Newarr, objT.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_STACK]));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldNumLocals));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_SLOT]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Newarr, objT.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_LOCALS]));

            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldEH));
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_SLOT]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_EH]));

            var loopStart = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]);
            var loopEnd   = Instruction.Create(DnOpCodes.Nop);
            var advance1  = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]);

            var outerLoop = Instruction.Create(DnOpCodes.Nop);
            var afterTry  = Instruction.Create(DnOpCodes.Nop);

            var runFin      = Instruction.Create(DnOpCodes.Nop);
            var resumeLeave = Instruction.Create(DnOpCodes.Nop);
            var resumeCatch = Instruction.Create(DnOpCodes.Nop);
            var doRethrow   = Instruction.Create(DnOpCodes.Nop);

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_RETURNED]));
            il.Add(outerLoop);

            il.Add(loopStart);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, loopEnd));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_OP]));

            var blkNop      = Instruction.Create(DnOpCodes.Nop);
            var blkRet      = Instruction.Create(DnOpCodes.Nop);
            var blkLdarg    = Instruction.Create(DnOpCodes.Nop);
            var blkStarg    = Instruction.Create(DnOpCodes.Nop);
            var blkLdloc    = Instruction.Create(DnOpCodes.Nop);
            var blkStloc    = Instruction.Create(DnOpCodes.Nop);
            var blkPop      = Instruction.Create(DnOpCodes.Nop);
            var blkDup      = Instruction.Create(DnOpCodes.Nop);
            var blkLdnull   = Instruction.Create(DnOpCodes.Nop);
            var blkLdstr    = Instruction.Create(DnOpCodes.Nop);
            var blkBr       = Instruction.Create(DnOpCodes.Nop);
            var blkBrtrue   = Instruction.Create(DnOpCodes.Nop);
            var blkBrfalse  = Instruction.Create(DnOpCodes.Nop);
            var blkCall     = Instruction.Create(DnOpCodes.Nop);
            var blkCallvirt = Instruction.Create(DnOpCodes.Nop);
            var blkNewobj   = Instruction.Create(DnOpCodes.Nop);
            var blkCastclass = Instruction.Create(DnOpCodes.Nop);
            var blkIsinst    = Instruction.Create(DnOpCodes.Nop);
            var blkLdcI4   = Instruction.Create(DnOpCodes.Nop);
            var blkAdd     = Instruction.Create(DnOpCodes.Nop);
            var blkSub     = Instruction.Create(DnOpCodes.Nop);
            var blkMul     = Instruction.Create(DnOpCodes.Nop);
            var blkDiv     = Instruction.Create(DnOpCodes.Nop);
            var blkDivUn   = Instruction.Create(DnOpCodes.Nop);
            var blkRem     = Instruction.Create(DnOpCodes.Nop);
            var blkRemUn   = Instruction.Create(DnOpCodes.Nop);
            var blkAnd     = Instruction.Create(DnOpCodes.Nop);
            var blkOr      = Instruction.Create(DnOpCodes.Nop);
            var blkXor     = Instruction.Create(DnOpCodes.Nop);
            var blkNeg     = Instruction.Create(DnOpCodes.Nop);
            var blkNot     = Instruction.Create(DnOpCodes.Nop);
            var blkShl     = Instruction.Create(DnOpCodes.Nop);
            var blkShr     = Instruction.Create(DnOpCodes.Nop);
            var blkShrUn   = Instruction.Create(DnOpCodes.Nop);
            var blkCeq     = Instruction.Create(DnOpCodes.Nop);
            var blkCgt     = Instruction.Create(DnOpCodes.Nop);
            var blkCgtUn   = Instruction.Create(DnOpCodes.Nop);
            var blkClt     = Instruction.Create(DnOpCodes.Nop);
            var blkCltUn   = Instruction.Create(DnOpCodes.Nop);
            var blkConvI1  = Instruction.Create(DnOpCodes.Nop);
            var blkConvU1  = Instruction.Create(DnOpCodes.Nop);
            var blkConvI2  = Instruction.Create(DnOpCodes.Nop);
            var blkConvU2  = Instruction.Create(DnOpCodes.Nop);
            var blkConvI4  = Instruction.Create(DnOpCodes.Nop);
            var blkConvU4  = Instruction.Create(DnOpCodes.Nop);
            var blkLdsfld  = Instruction.Create(DnOpCodes.Nop);
            var blkStsfld  = Instruction.Create(DnOpCodes.Nop);
            var blkLdfld   = Instruction.Create(DnOpCodes.Nop);
            var blkStfld   = Instruction.Create(DnOpCodes.Nop);
            var blkThrow   = Instruction.Create(DnOpCodes.Nop);
            var blkLeave   = Instruction.Create(DnOpCodes.Nop);
            var blkEndfin  = Instruction.Create(DnOpCodes.Nop);
            var blkLdftn   = Instruction.Create(DnOpCodes.Nop);
            var blkNewDel  = Instruction.Create(DnOpCodes.Nop);
            var blkNewarr  = Instruction.Create(DnOpCodes.Nop);
            var blkLdlen   = Instruction.Create(DnOpCodes.Nop);
            var blkLdelem  = Instruction.Create(DnOpCodes.Nop);
            var blkStelem  = Instruction.Create(DnOpCodes.Nop);
            var blkLdcI8   = Instruction.Create(DnOpCodes.Nop);
            var blkConvI8  = Instruction.Create(DnOpCodes.Nop);
            var blkConvU8  = Instruction.Create(DnOpCodes.Nop);
            var blkLdcR4   = Instruction.Create(DnOpCodes.Nop);
            var blkLdcR8   = Instruction.Create(DnOpCodes.Nop);
            var blkConvR4  = Instruction.Create(DnOpCodes.Nop);
            var blkConvR8  = Instruction.Create(DnOpCodes.Nop);
            var blkLdelemN = Instruction.Create(DnOpCodes.Nop);
            var blkStelemVT= Instruction.Create(DnOpCodes.Nop);
            var blkSwitch  = Instruction.Create(DnOpCodes.Nop);
            var blkLdtype  = Instruction.Create(DnOpCodes.Nop);

            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_NOP],     blkNop);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_RET],     blkRet);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDARG],   blkLdarg);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_STARG],   blkStarg);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDLOC],   blkLdloc);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_STLOC],   blkStloc);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_POP],     blkPop);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_DUP],     blkDup);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDNULL],  blkLdnull);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDSTR],   blkLdstr);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_BR],      blkBr);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_BRTRUE],  blkBrtrue);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_BRFALSE], blkBrfalse);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CALL],    blkCall);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CALLVIRT], blkCallvirt);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_NEWOBJ],   blkNewobj);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CASTCLASS], blkCastclass);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_ISINST],    blkIsinst);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDC_I4],   blkLdcI4);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_ADD],      blkAdd);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SUB],      blkSub);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_MUL],      blkMul);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_DIV],      blkDiv);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_DIV_UN],   blkDivUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_REM],      blkRem);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_REM_UN],   blkRemUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_AND],      blkAnd);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_OR],       blkOr);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_XOR],      blkXor);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_NEG],      blkNeg);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_NOT],      blkNot);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SHL],      blkShl);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SHR],      blkShr);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SHR_UN],   blkShrUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CEQ],      blkCeq);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CGT],      blkCgt);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CGT_UN],   blkCgtUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CLT],      blkClt);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CLT_UN],   blkCltUn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_I1],  blkConvI1);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_U1],  blkConvU1);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_I2],  blkConvI2);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_U2],  blkConvU2);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_I4],  blkConvI4);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_U4],  blkConvU4);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDSFLD],   blkLdsfld);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_STSFLD],   blkStsfld);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDFLD],    blkLdfld);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_STFLD],    blkStfld);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_THROW],   blkThrow);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LEAVE],   blkLeave);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_ENDFINALLY], blkEndfin);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDFTN],    blkLdftn);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_NEWDEL],   blkNewDel);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_NEWARR],  blkNewarr);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDLEN],   blkLdlen);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDELEM_REF], blkLdelem);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_STELEM_REF], blkStelem);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDC_I8],   blkLdcI8);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_I8],  blkConvI8);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_U8],  blkConvU8);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDC_R4],   blkLdcR4);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDC_R8],   blkLdcR8);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_R4],  blkConvR4);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_CONV_R8],  blkConvR8);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDELEM_NORM], blkLdelemN);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_STELEM_VT],   blkStelemVT);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_SWITCH],   blkSwitch);
            EmitDispatchEntry(il, method.Body.Variables[LOC_OP], opcodeMap[VOP_LDTYPE],   blkLdtype);

            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkNop);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkRet);
            il.Add(Instruction.Create(DnOpCodes.Br, loopEnd));

            il.Add(blkLdarg);
            EmitReadByteAtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_ARGS]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 2, loopStart);

            il.Add(blkStarg);
            EmitReadByteAtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldarg, method.Parameters[ARG_ARGS]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            EmitAdvanceIp(il, method, LOC_IP, 2, loopStart);

            il.Add(blkLdloc);
            EmitReadByteAtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_LOCALS]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 2, loopStart);

            il.Add(blkStloc);
            EmitReadByteAtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_LOCALS]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            EmitAdvanceIp(il, method, LOC_IP, 2, loopStart);

            il.Add(blkPop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkDup);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkLdnull);
            il.Add(Instruction.Create(DnOpCodes.Ldnull));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkLdstr);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldStrings));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkBr);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkBrtrue);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitTruthiness(il, method, LOC_O1, module);
            var brtNotTaken = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]);
            il.Add(Instruction.Create(DnOpCodes.Brfalse, brtNotTaken));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));
            il.Add(brtNotTaken);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 5));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkBrfalse);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitTruthiness(il, method, LOC_O1, module);
            var brfNotTaken = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]);
            il.Add(Instruction.Create(DnOpCodes.Brtrue, brfNotTaken));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));
            il.Add(brfNotTaken);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 5));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkSwitch);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_SWN);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, module.CorLibTypes.Int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SWIDX]));
            var swSkip = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SWIDX]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Blt, swSkip));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SWIDX]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SWN]));
            il.Add(Instruction.Create(DnOpCodes.Bge, swSkip));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 5));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SWIDX]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 4));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SWN]));
            EmitReadInt32AtIpPlusVar(il, method, LOC_CODE, LOC_IP, LOC_SWN, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(swSkip);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 5));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SWN]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 4));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(blkLdtype);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitResolveTypeFromTokens(il, method, fldTypes, LOC_T1, LOC_O1, module);
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            EmitCallBlock(il, method, blkCall, fldMethods, LOC_STACK, LOC_SP, LOC_T1, LOC_O1, LOC_O2, false, loopStart, LOC_CODE, LOC_IP, module, normInt, coerceThis, coerceArgs);

            EmitCallBlock(il, method, blkCallvirt, fldMethods, LOC_STACK, LOC_SP, LOC_T1, LOC_O1, LOC_O2, true, loopStart, LOC_CODE, LOC_IP, module, normInt, coerceThis, coerceArgs);

            EmitNewobjBlock(il, method, blkNewobj, fldMethods, LOC_STACK, LOC_SP, LOC_T1, LOC_O1, LOC_O2, loopStart, LOC_CODE, LOC_IP, module, normInt, coerceArgs);

            il.Add(blkCastclass);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitResolveTypeFromTokens(il, method, fldTypes, LOC_T1, LOC_O2, module);

            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkIsinst);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitResolveTypeFromTokens(il, method, fldTypes, LOC_T1, LOC_O2, module);

            {
                var typeIsInst = module.Import(typeof(Type).GetMethod("IsInstanceOfType", new[] { typeof(object) }));
                var pushNull = Instruction.Create(DnOpCodes.Ldnull);
                var afterPush = Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]);
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
                il.Add(Instruction.Create(DnOpCodes.Castclass, module.Import(typeof(Type))));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
                il.Add(Instruction.Create(DnOpCodes.Callvirt, typeIsInst));
                il.Add(Instruction.Create(DnOpCodes.Brfalse, pushNull));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
                il.Add(Instruction.Create(DnOpCodes.Br, afterPush));
                il.Add(pushNull);
                il.Add(afterPush);
                EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            }
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkLdcI4);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Box, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            EmitIntBinaryBlock(il, method, blkAdd,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Add,    module, advance1);
            EmitIntBinaryBlock(il, method, blkSub,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Sub,    module, advance1);
            EmitIntBinaryBlock(il, method, blkMul,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Mul,    module, advance1);
            EmitIntBinaryBlock(il, method, blkDiv,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Div,    module, advance1);
            EmitIntBinaryBlock(il, method, blkDivUn, LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Div_Un, module, advance1);
            EmitIntBinaryBlock(il, method, blkRem,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Rem,    module, advance1);
            EmitIntBinaryBlock(il, method, blkRemUn, LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Rem_Un, module, advance1);
            EmitIntBinaryBlock(il, method, blkAnd,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.And,    module, advance1);
            EmitIntBinaryBlock(il, method, blkOr,    LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Or,     module, advance1);
            EmitIntBinaryBlock(il, method, blkXor,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Xor,    module, advance1);
            EmitIntBinaryBlock(il, method, blkShl,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Shl,    module, advance1);
            EmitIntBinaryBlock(il, method, blkShr,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Shr,    module, advance1);
            EmitIntBinaryBlock(il, method, blkShrUn, LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Shr_Un, module, advance1);
            EmitCmpBlockRobust(il, method, blkCeq,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Ceq,    module, advance1);
            EmitIntBinaryBlock(il, method, blkCgt,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Cgt,    module, advance1);
            EmitCmpBlockRobust(il, method, blkCgtUn, LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Cgt_Un, module, advance1);
            EmitIntBinaryBlock(il, method, blkClt,   LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Clt,    module, advance1);
            EmitCmpBlockRobust(il, method, blkCltUn, LOC_STACK, LOC_SP, LOC_O1, LOC_O2, DnOpCodes.Clt_Un, module, advance1);
            EmitIntUnaryBlock(il, method, blkNeg,    LOC_STACK, LOC_SP, LOC_O1, DnOpCodes.Neg,     module, advance1);
            EmitIntUnaryBlock(il, method, blkNot,    LOC_STACK, LOC_SP, LOC_O1, DnOpCodes.Not,     module, advance1);
            EmitIntUnaryBlock(il, method, blkConvI1, LOC_STACK, LOC_SP, LOC_O1, DnOpCodes.Conv_I1, module, advance1);
            EmitIntUnaryBlock(il, method, blkConvU1, LOC_STACK, LOC_SP, LOC_O1, DnOpCodes.Conv_U1, module, advance1);
            EmitIntUnaryBlock(il, method, blkConvI2, LOC_STACK, LOC_SP, LOC_O1, DnOpCodes.Conv_I2, module, advance1);
            EmitIntUnaryBlock(il, method, blkConvU2, LOC_STACK, LOC_SP, LOC_O1, DnOpCodes.Conv_U2, module, advance1);
            EmitIntUnaryBlock(il, method, blkConvI4, LOC_STACK, LOC_SP, LOC_O1, DnOpCodes.Conv_I4, module, advance1);
            EmitIntUnaryBlock(il, method, blkConvU4, LOC_STACK, LOC_SP, LOC_O1, DnOpCodes.Conv_U4, module, advance1);

            var fiGetValue = module.Import(typeof(FieldInfo).GetMethod("GetValue", new[] { typeof(object) }));
            var fiSetValue = module.Import(typeof(FieldInfo).GetMethod("SetValue", new[] { typeof(object), typeof(object) }));

            il.Add(blkLdsfld);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldFields));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldnull));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, fiGetValue));
            il.Add(Instruction.Create(DnOpCodes.Call, normInt));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkStsfld);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldFields));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldnull));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, fiSetValue));
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkLdfld);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldFields));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, fiGetValue));
            il.Add(Instruction.Create(DnOpCodes.Call, normInt));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkStfld);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldFields));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, fiSetValue));
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkThrow);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Throw));

            il.Add(blkLeave);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_FINFROM]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDKIND]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDTGT]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDBND]));
            il.Add(Instruction.Create(DnOpCodes.Br, runFin));

            il.Add(blkEndfin);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Br, runFin));

            var runFinHave = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EH]);
            il.Add(runFin);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EH]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_FINFROM]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDBND]));
            il.Add(Instruction.Create(DnOpCodes.Call, _findFinally));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Bge, runFinHave));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDKIND]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Beq, resumeLeave));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDKIND]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Beq, resumeCatch));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_RETURNED]));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));

            il.Add(runFinHave);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_FINFROM]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EH]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(resumeLeave);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDTGT]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(resumeCatch);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDEXC]));
            il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDTGT]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            var arrayType      = module.Import(typeof(Array));
            var arrCreate      = module.Import(typeof(Array).GetMethod("CreateInstance", new[] { typeof(Type), typeof(int) }));
            var arrGetValue    = module.Import(typeof(Array).GetMethod("GetValue", new[] { typeof(int) }));
            var arrSetValue    = module.Import(typeof(Array).GetMethod("SetValue", new[] { typeof(object), typeof(int) }));
            var arrLenGet      = module.Import(typeof(Array).GetProperty("Length").GetGetMethod());

            il.Add(blkNewarr);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldTypes));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Call, arrCreate));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkLdlen);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, arrayType));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, arrLenGet));
            il.Add(Instruction.Create(DnOpCodes.Box, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkLdelem);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, arrayType));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, arrGetValue));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkStelem);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_EX);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EX]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, arrayType));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, arrSetValue));
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkLdelemN);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, arrayType));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, arrGetValue));
            il.Add(Instruction.Create(DnOpCodes.Call, normInt));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkStelemVT);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_EX);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EX]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, arrayType));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Call, _stElem));
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            var i64ref = module.CorLibTypes.Int64.TypeDefOrRef;
            var toI64d = module.Import(typeof(Convert).GetMethod("ToInt64", new[] { typeof(object) }));

            il.Add(blkLdcI8);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, _fldLongs));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I8));
            il.Add(Instruction.Create(DnOpCodes.Box, i64ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            var cvR8 = module.CorLibTypes.Double.TypeDefOrRef;
            var cvR4 = module.CorLibTypes.Single.TypeDefOrRef;

            il.Add(blkConvI8);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            var ci8f = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var ci8i = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var ci8done = Instruction.Create(DnOpCodes.Box, i64ref);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, cvR8));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, ci8f));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, cvR8));
            il.Add(Instruction.Create(DnOpCodes.Conv_I8));
            il.Add(Instruction.Create(DnOpCodes.Br, ci8done));
            il.Add(ci8f);
            il.Add(Instruction.Create(DnOpCodes.Isinst, cvR4));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, ci8i));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, cvR4));
            il.Add(Instruction.Create(DnOpCodes.Conv_I8));
            il.Add(Instruction.Create(DnOpCodes.Br, ci8done));
            il.Add(ci8i);
            il.Add(Instruction.Create(DnOpCodes.Call, toI64d));
            il.Add(ci8done);
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkConvU8);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            var cu8f = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var cu8L = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var cu8i = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var u8done = Instruction.Create(DnOpCodes.Box, i64ref);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, cvR8));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, cu8f));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, cvR8));
            il.Add(Instruction.Create(DnOpCodes.Conv_U8));
            il.Add(Instruction.Create(DnOpCodes.Br, u8done));
            il.Add(cu8f);
            il.Add(Instruction.Create(DnOpCodes.Isinst, cvR4));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, cu8L));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, cvR4));
            il.Add(Instruction.Create(DnOpCodes.Conv_U8));
            il.Add(Instruction.Create(DnOpCodes.Br, u8done));
            il.Add(cu8L);
            il.Add(Instruction.Create(DnOpCodes.Isinst, i64ref));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, cu8i));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, i64ref));
            il.Add(Instruction.Create(DnOpCodes.Br, u8done));
            il.Add(cu8i);
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Conv_U8));
            il.Add(u8done);
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            var r8ref = module.CorLibTypes.Double.TypeDefOrRef;
            var r4ref = module.CorLibTypes.Single.TypeDefOrRef;
            var toR8d = module.Import(typeof(Convert).GetMethod("ToDouble", new[] { typeof(object) }));
            var toR4d = module.Import(typeof(Convert).GetMethod("ToSingle", new[] { typeof(object) }));

            il.Add(blkLdcR8);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, _fldDoubles));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_R8));
            il.Add(Instruction.Create(DnOpCodes.Box, r8ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkLdcR4);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, _fldDoubles));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_R8));
            il.Add(Instruction.Create(DnOpCodes.Conv_R4));
            il.Add(Instruction.Create(DnOpCodes.Box, r4ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(blkConvR8);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Call, toR8d));
            il.Add(Instruction.Create(DnOpCodes.Box, r8ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkConvR4);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Call, toR4d));
            il.Add(Instruction.Create(DnOpCodes.Box, r4ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));

            il.Add(blkLdftn);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldMethods));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            var miType   = module.Import(typeof(System.Reflection.MethodInfo));
            var createDel = module.Import(typeof(Delegate).GetMethod("CreateDelegate",
                new[] { typeof(Type), typeof(object), typeof(System.Reflection.MethodInfo) }));
            il.Add(blkNewDel);
            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldTypes));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, miType));
            il.Add(Instruction.Create(DnOpCodes.Call, createDel));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);

            il.Add(advance1);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));

            il.Add(loopEnd);
            var emptyStack = Instruction.Create(DnOpCodes.Ldnull);
            var storeRet   = Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_RETVAL]);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ble, emptyStack));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Br, storeRet));
            il.Add(emptyStack);
            il.Add(storeRet);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_RETURNED]));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));

            var catchStart = Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_EX]);
            var afterUnwrap = Instruction.Create(DnOpCodes.Nop);
            var rethrowLbl  = Instruction.Create(DnOpCodes.Nop);
            var tieType = module.Import(typeof(System.Reflection.TargetInvocationException));
            var innerGet = module.Import(typeof(Exception).GetProperty("InnerException").GetGetMethod());

            il.Add(catchStart);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EX]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, tieType));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, afterUnwrap));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EX]));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, innerGet));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, afterUnwrap));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_EX]));
            il.Add(afterUnwrap);
            var catRethrowSetup = Instruction.Create(DnOpCodes.Ldc_I4_3);
            var catFind         = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EH]);
            var catNoFin        = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDKIND]);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EH]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EX]));
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldTypes));
            il.Add(Instruction.Create(DnOpCodes.Call, findCatch));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_FINFROM]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EX]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDEXC]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Blt, catRethrowSetup));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDKIND]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDTGT]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDBND]));
            il.Add(Instruction.Create(DnOpCodes.Br, catFind));
            il.Add(catRethrowSetup);
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDKIND]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_PENDBND]));

            il.Add(catFind);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDBND]));
            il.Add(Instruction.Create(DnOpCodes.Call, _findFinally));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Blt, catNoFin));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EH]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_FINFROM]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EH]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_RETURNED]));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));

            il.Add(catNoFin);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Bne_Un, rethrowLbl));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EX]));
            il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDTGT]));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_RETURNED]));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));
            il.Add(rethrowLbl);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_EX]));
            il.Add(Instruction.Create(DnOpCodes.Throw));

            il.Add(afterTry);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_RETURNED]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Beq, doRethrow));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_RETURNED]));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, outerLoop));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_RETVAL]));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(doRethrow);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_PENDEXC]));
            il.Add(Instruction.Create(DnOpCodes.Throw));

            var eh = new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart     = loopStart,
                TryEnd       = catchStart,
                HandlerStart = catchStart,
                HandlerEnd   = afterTry,
                CatchType    = module.CorLibTypes.GetTypeRef("System", "Exception"),
            };
            method.Body.ExceptionHandlers.Add(eh);

            return method;
        }

        private void EmitDispatchEntry(IList<Instruction> il, Local opLocal, int opcodeValue, Instruction target)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldloc, opLocal));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, opcodeValue));
            il.Add(Instruction.Create(DnOpCodes.Beq, target));
        }

        private void EmitObjPush(IList<Instruction> il, MethodDef method, int LOC_STACK, int LOC_SP, int LOC_VAL)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_VAL]));
            il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
        }

        private void EmitObjPop(IList<Instruction> il, MethodDef method, int LOC_STACK, int LOC_SP, int LOC_DEST)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
        }

        private int WideBinSel(OpCode op)
        {
            if (op == DnOpCodes.Add) return 0;  if (op == DnOpCodes.Sub) return 1;
            if (op == DnOpCodes.Mul) return 2;  if (op == DnOpCodes.Div) return 3;
            if (op == DnOpCodes.Rem) return 4;  if (op == DnOpCodes.And) return 5;
            if (op == DnOpCodes.Or)  return 6;  if (op == DnOpCodes.Xor) return 7;
            if (op == DnOpCodes.Shl) return 8;  if (op == DnOpCodes.Shr) return 9;
            if (op == DnOpCodes.Div_Un) return 10; if (op == DnOpCodes.Rem_Un) return 11;
            if (op == DnOpCodes.Shr_Un) return 12; if (op == DnOpCodes.Cgt) return 13;
            if (op == DnOpCodes.Clt) return 14;
            return 0;
        }

        private void EmitIntBinaryBlock(IList<Instruction> il, MethodDef method, Instruction blkStart,
            int LOC_STACK, int LOC_SP, int LOC_O1, int LOC_O2, OpCode arithOp, ModuleDef mod, Instruction advance1)
        {
            var i32 = mod.CorLibTypes.Int32.TypeDefOrRef;
            il.Add(blkStart);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            var wide = Instruction.Create(DnOpCodes.Nop);
            var push = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, i32));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, wide));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, i32));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, wide));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, i32));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, i32));
            il.Add(Instruction.Create(arithOp));
            il.Add(Instruction.Create(DnOpCodes.Box, i32));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Br, push));
            il.Add(wide);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, WideBinSel(arithOp)));
            il.Add(Instruction.Create(DnOpCodes.Call, _wideBin));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            il.Add(push);
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));
        }

        private void EmitIntUnaryBlock(IList<Instruction> il, MethodDef method, Instruction blkStart,
            int LOC_STACK, int LOC_SP, int LOC_O1, OpCode unaryOp, ModuleDef mod, Instruction advance1)
        {
            var i32 = mod.CorLibTypes.Int32.TypeDefOrRef;
            il.Add(blkStart);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            var wide = Instruction.Create(DnOpCodes.Nop);
            var push = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, i32));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, wide));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, i32));
            il.Add(Instruction.Create(unaryOp));
            il.Add(Instruction.Create(DnOpCodes.Box, i32));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Br, push));
            il.Add(wide);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            bool isNeg = unaryOp == DnOpCodes.Neg, isNot = unaryOp == DnOpCodes.Not;
            if (isNeg || isNot)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, isNeg ? 0 : 1));
                il.Add(Instruction.Create(DnOpCodes.Call, _wideUn));
            }
            else
            {
                int sel = unaryOp == DnOpCodes.Conv_I1 ? 0 : unaryOp == DnOpCodes.Conv_U1 ? 1
                        : unaryOp == DnOpCodes.Conv_I2 ? 2 : unaryOp == DnOpCodes.Conv_U2 ? 3
                        : unaryOp == DnOpCodes.Conv_I4 ? 4 : 5;
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, sel));
                il.Add(Instruction.Create(DnOpCodes.Call, _wideConv));
            }
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            il.Add(push);
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));
        }

        private void EmitCmpBlockRobust(IList<Instruction> il, MethodDef method, Instruction blkStart,
            int LOC_STACK, int LOC_SP, int LOC_O1, int LOC_O2, OpCode cmpOp, ModuleDef mod, Instruction advance1)
        {
            var i32 = mod.CorLibTypes.Int32.TypeDefOrRef;
            var i64 = mod.CorLibTypes.Int64.TypeDefOrRef;
            var r8  = mod.CorLibTypes.Double.TypeDefOrRef;
            var r4  = mod.CorLibTypes.Single.TypeDefOrRef;
            il.Add(blkStart);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O2);
            EmitObjPop(il, method, LOC_STACK, LOC_SP, LOC_O1);
            var longCase  = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var dblCase   = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var fltCase   = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var refCase   = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]);
            var doneStore = Instruction.Create(DnOpCodes.Box, i32);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, i32));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, longCase));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, i32));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, longCase));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, i32));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, i32));
            il.Add(Instruction.Create(cmpOp));
            il.Add(Instruction.Create(DnOpCodes.Br, doneStore));

            il.Add(longCase);
            il.Add(Instruction.Create(DnOpCodes.Isinst, i64));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, dblCase));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, i64));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, dblCase));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, i64));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, i64));
            il.Add(Instruction.Create(cmpOp));
            il.Add(Instruction.Create(DnOpCodes.Br, doneStore));

            il.Add(dblCase);
            il.Add(Instruction.Create(DnOpCodes.Isinst, r8));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, fltCase));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, r8));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, fltCase));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, r8));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, r8));
            il.Add(Instruction.Create(cmpOp));
            il.Add(Instruction.Create(DnOpCodes.Br, doneStore));

            il.Add(fltCase);
            il.Add(Instruction.Create(DnOpCodes.Isinst, r4));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, refCase));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, r4));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, refCase));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, r4));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, r4));
            il.Add(Instruction.Create(cmpOp));
            il.Add(Instruction.Create(DnOpCodes.Br, doneStore));
            il.Add(refCase);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(cmpOp));
            il.Add(doneStore);
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O1]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O1);
            il.Add(Instruction.Create(DnOpCodes.Br, advance1));
        }

        private void EmitTruthiness(IList<Instruction> il, MethodDef method, int LOC_O1, ModuleDef mod)
        {
            var i32 = mod.CorLibTypes.Int32.TypeDefOrRef;
            var isIntCase = Instruction.Create(DnOpCodes.Unbox_Any, i32);
            var done = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, i32));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, isIntCase));
            il.Add(Instruction.Create(DnOpCodes.Pop));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Ldnull));
            il.Add(Instruction.Create(DnOpCodes.Cgt_Un));
            il.Add(Instruction.Create(DnOpCodes.Br, done));
            il.Add(isIntCase);
            il.Add(done);
        }

        private void EmitReadByteAtIpPlus(IList<Instruction> il, MethodDef method,
            int LOC_CODE, int LOC_IP, int offset, int LOC_DEST)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, offset));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
        }

        private void EmitReadInt32AtIpPlus(IList<Instruction> il, MethodDef method,
            int LOC_CODE, int LOC_IP, int offset, int LOC_DEST)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
            for (int i = 0; i < 4; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_DEST]));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, offset + i));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
                if (i > 0)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i * 8));
                    il.Add(Instruction.Create(DnOpCodes.Shl));
                }
                il.Add(Instruction.Create(DnOpCodes.Or));
                il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
            }
        }

        private void EmitReadInt32AtIpPlusVar(IList<Instruction> il, MethodDef method,
            int LOC_CODE, int LOC_IP, int LOC_OFF, int LOC_DEST)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
            for (int i = 0; i < 4; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_DEST]));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_CODE]));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_OFF]));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
                if (i > 0)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i * 8));
                    il.Add(Instruction.Create(DnOpCodes.Shl));
                }
                il.Add(Instruction.Create(DnOpCodes.Or));
                il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST]));
            }
        }

        private void EmitAdvanceIp(IList<Instruction> il, MethodDef method,
            int LOC_IP, int delta, Instruction loopStart)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, delta));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_IP]));
            il.Add(Instruction.Create(DnOpCodes.Br, loopStart));
        }

        private void EmitResolveMethodFromTokens(IList<Instruction> il, MethodDef method,
            FieldDef fldMethods, int LOC_IDX, int LOC_DEST_OBJ, ModuleDef mod)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldMethods));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IDX]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST_OBJ]));
        }

        private void EmitResolveTypeFromTokens(IList<Instruction> il, MethodDef method,
            FieldDef fldTypes, int LOC_IDX, int LOC_DEST_OBJ, ModuleDef mod)
        {
            il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldTypes));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_IDX]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_DEST_OBJ]));
        }

        private void EmitCallBlock(IList<Instruction> il, MethodDef method, Instruction blkStart,
            FieldDef fldMethods, int LOC_STACK, int LOC_SP, int LOC_T1, int LOC_O1, int LOC_O2,
            bool isVirtual, Instruction loopStart, int LOC_CODE, int LOC_IP,
            ModuleDef mod, MethodDef normInt, MethodDef coerceThis, MethodDef coerceArgs)
        {
            var methodBaseType = mod.Import(typeof(MethodBase));
            var methodInfoType = mod.Import(typeof(MethodInfo));
            var getParams      = mod.Import(typeof(MethodBase).GetMethod("GetParameters", Type.EmptyTypes));
            var invokeMethod   = mod.Import(typeof(MethodBase).GetMethod("Invoke", new[] { typeof(object), typeof(object[]) }));
            var isStaticGet    = mod.Import(typeof(MethodBase).GetProperty("IsStatic").GetGetMethod());
            var returnTypeGet  = mod.Import(typeof(MethodInfo).GetProperty("ReturnType").GetGetMethod());
            var fullNameGet    = mod.Import(typeof(Type).GetProperty("FullName").GetGetMethod());
            var stringEquality = mod.Import(typeof(string).GetMethod("op_Equality", new[] { typeof(string), typeof(string) }));

            il.Add(blkStart);

            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);

            EmitResolveMethodFromTokens(il, method, fldMethods, LOC_T1, LOC_O1, mod);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, methodBaseType));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getParams));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Newarr, mod.CorLibTypes.Object.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O2]));

            var fillStart = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]);
            var fillEnd   = Instruction.Create(DnOpCodes.Nop);

            il.Add(fillStart);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ble, fillEnd));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));

            il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Br, fillStart));
            il.Add(fillEnd);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, methodBaseType));
            il.Add(Instruction.Create(DnOpCodes.Call, coerceArgs));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O2]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, methodBaseType));

            var pushNullTarget = Instruction.Create(DnOpCodes.Ldnull);
            var afterTarget    = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, methodBaseType));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, isStaticGet));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, pushNullTarget));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, methodBaseType));
            il.Add(Instruction.Create(DnOpCodes.Call, coerceThis));
            il.Add(Instruction.Create(DnOpCodes.Br, afterTarget));

            il.Add(pushNullTarget);

            il.Add(afterTarget);

            il.Add(Instruction.Create(DnOpCodes.Callvirt, invokeMethod));

            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O2]));

            var voidCase    = Instruction.Create(DnOpCodes.Nop);
            var afterReturn = Instruction.Create(DnOpCodes.Nop);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Isinst, methodInfoType));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, voidCase));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, methodInfoType));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, returnTypeGet));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, fullNameGet));
            il.Add(Instruction.Create(DnOpCodes.Ldstr, "System.Void"));
            il.Add(Instruction.Create(DnOpCodes.Call, stringEquality));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, voidCase));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Call, normInt));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O2]));
            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O2);
            il.Add(Instruction.Create(DnOpCodes.Br, afterReturn));

            il.Add(voidCase);

            il.Add(afterReturn);

            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);
        }

        private void EmitNewobjBlock(IList<Instruction> il, MethodDef method, Instruction blkStart,
            FieldDef fldMethods, int LOC_STACK, int LOC_SP, int LOC_T1, int LOC_O1, int LOC_O2,
            Instruction loopStart, int LOC_CODE, int LOC_IP, ModuleDef mod, MethodDef normInt,
            MethodDef coerceArgs)
        {
            var methodBaseType = mod.Import(typeof(MethodBase));
            var ctorInfoType   = mod.Import(typeof(ConstructorInfo));
            var getParams      = mod.Import(typeof(MethodBase).GetMethod("GetParameters", Type.EmptyTypes));
            var ctorInvoke     = mod.Import(typeof(ConstructorInfo).GetMethod("Invoke", new[] { typeof(object[]) }));

            il.Add(blkStart);

            EmitReadInt32AtIpPlus(il, method, LOC_CODE, LOC_IP, 1, LOC_T1);

            EmitResolveMethodFromTokens(il, method, fldMethods, LOC_T1, LOC_O1, mod);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, methodBaseType));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getParams));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Newarr, mod.CorLibTypes.Object.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O2]));

            var fillStart = Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]);
            var fillEnd   = Instruction.Create(DnOpCodes.Nop);

            il.Add(fillStart);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ble, fillEnd));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_T1]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_T1]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Sub));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_STACK]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_SP]));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Br, fillStart));
            il.Add(fillEnd);

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, methodBaseType));
            il.Add(Instruction.Create(DnOpCodes.Call, coerceArgs));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O2]));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O1]));
            il.Add(Instruction.Create(DnOpCodes.Castclass, ctorInfoType));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, method.Body.Variables[LOC_O2]));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, ctorInvoke));
            il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[LOC_O2]));

            EmitObjPush(il, method, LOC_STACK, LOC_SP, LOC_O2);

            EmitAdvanceIp(il, method, LOC_IP, 5, loopStart);
        }

        private MethodDef BuildNormInt(ModuleDef module, TypeDef vmType)
        {
            var objT = module.CorLibTypes.Object;
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(objT, objT),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            var il = m.Body.Instructions;
            AddNormCase(il, module, module.CorLibTypes.Boolean.TypeDefOrRef);
            AddNormCase(il, module, module.CorLibTypes.Char.TypeDefOrRef);
            AddNormCase(il, module, module.CorLibTypes.Byte.TypeDefOrRef);
            AddNormCase(il, module, module.CorLibTypes.SByte.TypeDefOrRef);
            AddNormCase(il, module, module.CorLibTypes.Int16.TypeDefOrRef);
            AddNormCase(il, module, module.CorLibTypes.UInt16.TypeDefOrRef);
            AddNormCase(il, module, module.CorLibTypes.UInt32.TypeDefOrRef);

            {
                var nu8 = Instruction.Create(DnOpCodes.Nop);
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Isinst, module.CorLibTypes.UInt64.TypeDefOrRef));
                il.Add(Instruction.Create(DnOpCodes.Brfalse, nu8));
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Unbox_Any, module.CorLibTypes.UInt64.TypeDefOrRef));
                il.Add(Instruction.Create(DnOpCodes.Box, module.CorLibTypes.Int64.TypeDefOrRef));
                il.Add(Instruction.Create(DnOpCodes.Ret));
                il.Add(nu8);
            }

            {
                var enumTypeRef      = module.Import(typeof(System.Enum));
                var getUnderlying    = module.Import(typeof(Enum).GetMethod("GetUnderlyingType", new[] { typeof(Type) }));
                var getTypeOfVal     = module.Import(typeof(object).GetMethod("GetType", Type.EmptyTypes));
                var getTypeFromHandle = module.Import(typeof(Type).GetMethod("GetTypeFromHandle", new[] { typeof(RuntimeTypeHandle) }));
                var convertToInt64  = module.Import(typeof(Convert).GetMethod("ToInt64",  new[] { typeof(object) }));
                var convertToUInt64 = module.Import(typeof(Convert).GetMethod("ToUInt64", new[] { typeof(object) }));
                var convertToInt32  = module.Import(typeof(Convert).GetMethod("ToInt32",  new[] { typeof(object) }));
                var int64r  = module.CorLibTypes.Int64.TypeDefOrRef;
                var int32r  = module.CorLibTypes.Int32.TypeDefOrRef;
                var ulong8r = module.CorLibTypes.UInt64.TypeDefOrRef;

                m.Body.Variables.Add(new Local(new ClassSig(module.CorLibTypes.GetTypeRef("System", "Type"))));
                m.Body.InitLocals = true;
                var utLoc = m.Body.Variables[m.Body.Variables.Count - 1];

                var nEnum     = Instruction.Create(DnOpCodes.Nop);
                var doLong64  = Instruction.Create(DnOpCodes.Nop);
                var doULong64 = Instruction.Create(DnOpCodes.Nop);

                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Isinst, enumTypeRef));
                il.Add(Instruction.Create(DnOpCodes.Brfalse, nEnum));

                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Callvirt, getTypeOfVal));
                il.Add(Instruction.Create(DnOpCodes.Call, getUnderlying));
                il.Add(Instruction.Create(DnOpCodes.Stloc, utLoc));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, utLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldtoken, int64r));
                il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
                il.Add(Instruction.Create(DnOpCodes.Ceq));
                il.Add(Instruction.Create(DnOpCodes.Brtrue, doLong64));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, utLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldtoken, ulong8r));
                il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
                il.Add(Instruction.Create(DnOpCodes.Ceq));
                il.Add(Instruction.Create(DnOpCodes.Brtrue, doULong64));

                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Call, convertToInt32));
                il.Add(Instruction.Create(DnOpCodes.Box, int32r));
                il.Add(Instruction.Create(DnOpCodes.Ret));

                il.Add(doLong64);
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Call, convertToInt64));
                il.Add(Instruction.Create(DnOpCodes.Box, int64r));
                il.Add(Instruction.Create(DnOpCodes.Ret));

                il.Add(doULong64);
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Call, convertToUInt64));
                il.Add(Instruction.Create(DnOpCodes.Box, int64r));
                il.Add(Instruction.Create(DnOpCodes.Ret));
                il.Add(nEnum);
            }
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private void AddNormCase(IList<Instruction> il, ModuleDef module, ITypeDefOrRef tref)
        {
            var next = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Isinst, tref));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, next));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, tref));
            il.Add(Instruction.Create(DnOpCodes.Box, module.CorLibTypes.Int32.TypeDefOrRef));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(next);
        }

        private MethodDef BuildCoerceThis(ModuleDef module, TypeDef vmType)
        {
            var objT        = module.CorLibTypes.Object;
            var mbTypeRef   = module.CorLibTypes.GetTypeRef("System.Reflection", "MethodBase");
            var typeTypeRef = module.CorLibTypes.GetTypeRef("System", "Type");
            var exTypeRef   = module.CorLibTypes.GetTypeRef("System", "Exception");

            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(objT, objT, new ClassSig(mbTypeRef)),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(new ClassSig(typeTypeRef)));
            m.Body.Variables.Add(new Local(objT));
            var il = m.Body.Instructions;

            var getDeclType = module.Import(typeof(MethodBase).GetProperty("DeclaringType").GetGetMethod());
            var isInstOf    = module.Import(typeof(Type).GetMethod("IsInstanceOfType", new[] { typeof(object) }));
            var changeType  = module.Import(typeof(Convert).GetMethod("ChangeType", new[] { typeof(object), typeof(Type) }));
            var getTypeFromHandle = module.Import(typeof(Type).GetMethod("GetTypeFromHandle", new[] { typeof(RuntimeTypeHandle) }));
            var uint32r = module.CorLibTypes.UInt32.TypeDefOrRef;
            var int32r  = module.CorLibTypes.Int32.TypeDefOrRef;
            var uint64r = module.CorLibTypes.UInt64.TypeDefOrRef;
            var int64r  = module.CorLibTypes.Int64.TypeDefOrRef;

            var notNull = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, notNull));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(notNull);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getDeclType));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            var tNotNull = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, tNotNull));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(tNotNull);

            var notInst = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, isInstOf));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, notInst));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(notInst);

            var tryStart     = Instruction.Create(DnOpCodes.Ldarg_0);
            var handlerStart = Instruction.Create(DnOpCodes.Pop);
            var afterTry     = Instruction.Create(DnOpCodes.Ldloc_1);
            var ulongChk     = Instruction.Create(DnOpCodes.Ldloc_0);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, uint32r));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            il.Add(Instruction.Create(DnOpCodes.Ceq));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, ulongChk));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int32r));
            il.Add(Instruction.Create(DnOpCodes.Box, uint32r));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(ulongChk);
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, uint64r));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            il.Add(Instruction.Create(DnOpCodes.Ceq));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, tryStart));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int64r));
            il.Add(Instruction.Create(DnOpCodes.Box, uint64r));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Call, changeType));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));
            il.Add(handlerStart);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));
            il.Add(afterTry);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            var eh = new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart     = tryStart,
                TryEnd       = handlerStart,
                HandlerStart = handlerStart,
                HandlerEnd   = afterTry,
                CatchType    = exTypeRef,
            };
            m.Body.ExceptionHandlers.Add(eh);

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildCoerceValue(ModuleDef module, TypeDef vmType)
        {
            var objT      = module.CorLibTypes.Object;
            var typeRef   = module.CorLibTypes.GetTypeRef("System", "Type");
            var exTypeRef = module.CorLibTypes.GetTypeRef("System", "Exception");

            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(objT, objT, new ClassSig(typeRef)),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(objT));
            var il = m.Body.Instructions;

            var isByRefGet = module.Import(typeof(Type).GetProperty("IsByRef").GetGetMethod());
            var isInstOf   = module.Import(typeof(Type).GetMethod("IsInstanceOfType", new[] { typeof(object) }));
            var changeType = module.Import(typeof(Convert).GetMethod("ChangeType", new[] { typeof(object), typeof(Type) }));
            var getTypeFromHandle = module.Import(typeof(Type).GetMethod("GetTypeFromHandle", new[] { typeof(RuntimeTypeHandle) }));
            var uint32r = module.CorLibTypes.UInt32.TypeDefOrRef;
            var int32r  = module.CorLibTypes.Int32.TypeDefOrRef;
            var uint64r = module.CorLibTypes.UInt64.TypeDefOrRef;
            var int64r  = module.CorLibTypes.Int64.TypeDefOrRef;

            var l1 = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, l1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(l1);

            var l2 = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, l2));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(l2);

            var l3 = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, isByRefGet));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, l3));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(l3);

            var l4 = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, isInstOf));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, l4));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(l4);

            var tryStart     = Instruction.Create(DnOpCodes.Ldarg_0);
            var handlerStart = Instruction.Create(DnOpCodes.Pop);
            var afterTry     = Instruction.Create(DnOpCodes.Ldloc_0);
            var ulongChk     = Instruction.Create(DnOpCodes.Ldarg_1);
            var enumEntry    = Instruction.Create(DnOpCodes.Ldarg_1);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, uint32r));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            il.Add(Instruction.Create(DnOpCodes.Ceq));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, ulongChk));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int32r));
            il.Add(Instruction.Create(DnOpCodes.Box, uint32r));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(ulongChk);
            il.Add(Instruction.Create(DnOpCodes.Ldtoken, uint64r));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
            il.Add(Instruction.Create(DnOpCodes.Ceq));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, enumEntry));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, int64r));
            il.Add(Instruction.Create(DnOpCodes.Box, uint64r));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            {
                var isEnumGet    = module.Import(typeof(Type).GetProperty("IsEnum").GetGetMethod());
                var enumToObject = module.Import(typeof(Enum).GetMethod("ToObject", new[] { typeof(Type), typeof(long) }));
                var toInt64      = module.Import(typeof(Convert).GetMethod("ToInt64", new[] { typeof(object) }));
                var enumChk = Instruction.Create(DnOpCodes.Nop);
                il.Add(enumEntry);
                il.Add(Instruction.Create(DnOpCodes.Callvirt, isEnumGet));
                il.Add(Instruction.Create(DnOpCodes.Brfalse, enumChk));
                il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Call, toInt64));
                il.Add(Instruction.Create(DnOpCodes.Call, enumToObject));
                il.Add(Instruction.Create(DnOpCodes.Ret));
                il.Add(enumChk);
            }

            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Call, changeType));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));
            il.Add(handlerStart);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterTry));
            il.Add(afterTry);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            m.Body.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
            {
                TryStart = tryStart, TryEnd = handlerStart,
                HandlerStart = handlerStart, HandlerEnd = afterTry, CatchType = exTypeRef,
            });

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildCoerceArgs(ModuleDef module, TypeDef vmType, MethodDef coerceValue)
        {
            var objT     = module.CorLibTypes.Object;
            var objArr   = new SZArraySig(objT);
            var mbRef    = module.CorLibTypes.GetTypeRef("System.Reflection", "MethodBase");
            var piRef    = module.CorLibTypes.GetTypeRef("System.Reflection", "ParameterInfo");
            var piArr    = new SZArraySig(new ClassSig(piRef));

            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(objArr, objArr, new ClassSig(mbRef)),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(piArr));
            m.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = m.Body.Instructions;

            var getParams = module.Import(typeof(MethodBase).GetMethod("GetParameters", Type.EmptyTypes));
            var ptypeGet  = module.Import(typeof(System.Reflection.ParameterInfo).GetProperty("ParameterType").GetGetMethod());

            var ok = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, ok));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, ok));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(ok);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getParams));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            var loop = Instruction.Create(DnOpCodes.Ldloc_1);
            var end  = Instruction.Create(DnOpCodes.Ldarg_0);
            il.Add(loop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, end));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, ptypeGet));
            il.Add(Instruction.Create(DnOpCodes.Call, coerceValue));
            il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Br, loop));
            il.Add(end);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildFindCatch(ModuleDef module, TypeDef vmType)
        {
            var i32  = module.CorLibTypes.Int32;
            var objT = module.CorLibTypes.Object;
            var typeRef = module.CorLibTypes.GetTypeRef("System", "Type");
            var typeArr = new SZArraySig(new ClassSig(typeRef));
            var ehArr   = new SZArraySig(i32);

            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(i32, ehArr, i32, objT, typeArr),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(i32));
            m.Body.Variables.Add(new Local(i32));
            var il = m.Body.Instructions;

            var isInstOf = module.Import(typeof(Type).GetMethod("IsInstanceOfType", new[] { typeof(object) }));

            var retNeg = Instruction.Create(DnOpCodes.Ldc_I4_M1);
            var loop   = Instruction.Create(DnOpCodes.Ldloc_0);
            var next   = Instruction.Create(DnOpCodes.Ldloc_0);
            var retHs  = Instruction.Create(DnOpCodes.Ldarg_0);
            var popNext= Instruction.Create(DnOpCodes.Pop);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, retNeg));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, retNeg));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(loop);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_3));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, retNeg));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Blt, next));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, next));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_3));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Blt, next));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Blt, retHs));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, next));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, next));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_3));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
            il.Add(Instruction.Create(DnOpCodes.Dup));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, popNext));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, isInstOf));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, retHs));
            il.Add(Instruction.Create(DnOpCodes.Br, next));

            il.Add(popNext);
            il.Add(Instruction.Create(DnOpCodes.Br, next));

            il.Add(retHs);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(next);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Br, loop));

            il.Add(retNeg);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildFindFinally(ModuleDef module, TypeDef vmType)
        {
            var i32  = module.CorLibTypes.Int32;
            var ehArr = new SZArraySig(i32);
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(i32, ehArr, i32, i32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(i32));
            var il = m.Body.Instructions;

            var retNeg = Instruction.Create(DnOpCodes.Ldc_I4_M1);
            var loop   = Instruction.Create(DnOpCodes.Ldloc_0);
            var next   = Instruction.Create(DnOpCodes.Ldloc_0);
            var retI   = Instruction.Create(DnOpCodes.Ldloc_0);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, retNeg));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(loop);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_3));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldlen));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, retNeg));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_3));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, -2));
            il.Add(Instruction.Create(DnOpCodes.Bne_Un, next));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Blt, next));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, next));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Blt, retI));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_I4));
            il.Add(Instruction.Create(DnOpCodes.Bge, retI));

            il.Add(Instruction.Create(DnOpCodes.Br, next));
            il.Add(retI);
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(next);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Br, loop));
            il.Add(retNeg);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildWideBin(ModuleDef module, TypeDef vmType)
        {
            var objT = module.CorLibTypes.Object;
            var i64 = module.CorLibTypes.Int64;
            var i32 = module.CorLibTypes.Int32;
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(objT, objT, objT, i32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(i64));
            m.Body.Variables.Add(new Local(i64));
            m.Body.Variables.Add(new Local(module.CorLibTypes.Double));
            m.Body.Variables.Add(new Local(module.CorLibTypes.Double));
            m.Body.Variables.Add(new Local(module.CorLibTypes.Single));
            m.Body.Variables.Add(new Local(module.CorLibTypes.Single));
            var il = m.Body.Instructions;
            var toI64 = module.Import(typeof(Convert).GetMethod("ToInt64", new[] { typeof(object) }));
            var toR8  = module.Import(typeof(Convert).GetMethod("ToDouble", new[] { typeof(object) }));
            var toR4  = module.Import(typeof(Convert).GetMethod("ToSingle", new[] { typeof(object) }));
            var i64r = i64.TypeDefOrRef;
            var i32r = i32.TypeDefOrRef;
            var r8r  = module.CorLibTypes.Double.TypeDefOrRef;
            var r4r  = module.CorLibTypes.Single.TypeDefOrRef;
            var dblT = module.CorLibTypes.Double.TypeDefOrRef;
            var sglT = module.CorLibTypes.Single.TypeDefOrRef;

            var doDouble = Instruction.Create(DnOpCodes.Ldarg_0);
            var doFloat  = Instruction.Create(DnOpCodes.Ldarg_0);
            var doLong   = Instruction.Create(DnOpCodes.Ldarg_0);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Isinst, dblT));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, doDouble));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Isinst, dblT));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, doDouble));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Isinst, sglT));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, doFloat));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Isinst, sglT));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, doFloat));
            il.Add(Instruction.Create(DnOpCodes.Br, doLong));

            il.Add(doDouble);
            il.Add(Instruction.Create(DnOpCodes.Call, toR8));
            il.Add(Instruction.Create(DnOpCodes.Stloc, m.Body.Variables[2]));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Call, toR8));
            il.Add(Instruction.Create(DnOpCodes.Stloc, m.Body.Variables[3]));
            var dt = new Instruction[15];
            var dDef = Instruction.Create(DnOpCodes.Ldc_R8, 0.0);
            for (int i = 0; i < 15; i++) dt[i] = dDef;
            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Switch, dt));
            il.Add(dDef);
            il.Add(Instruction.Create(DnOpCodes.Box, r8r));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            Action<int, OpCode, bool> dOp = (idx, op, isCmp) =>
            {
                var b = Instruction.Create(DnOpCodes.Ldloc, m.Body.Variables[2]);
                dt[idx] = b;
                il.Add(b);
                il.Add(Instruction.Create(DnOpCodes.Ldloc, m.Body.Variables[3]));
                il.Add(Instruction.Create(op));
                il.Add(Instruction.Create(DnOpCodes.Box, isCmp ? i32r : r8r));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            };
            dOp(0, DnOpCodes.Add, false); dOp(1, DnOpCodes.Sub, false); dOp(2, DnOpCodes.Mul, false);
            dOp(3, DnOpCodes.Div, false); dOp(4, DnOpCodes.Rem, false);
            dOp(13, DnOpCodes.Cgt, true); dOp(14, DnOpCodes.Clt, true);

            il.Add(doFloat);
            il.Add(Instruction.Create(DnOpCodes.Call, toR4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, m.Body.Variables[4]));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Call, toR4));
            il.Add(Instruction.Create(DnOpCodes.Stloc, m.Body.Variables[5]));
            var ft = new Instruction[15];
            var fDef = Instruction.Create(DnOpCodes.Ldc_R4, 0.0f);
            for (int i = 0; i < 15; i++) ft[i] = fDef;
            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Switch, ft));
            il.Add(fDef);
            il.Add(Instruction.Create(DnOpCodes.Box, r4r));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            Action<int, OpCode, bool> fOp = (idx, op, isCmp) =>
            {
                var b = Instruction.Create(DnOpCodes.Ldloc, m.Body.Variables[4]);
                ft[idx] = b;
                il.Add(b);
                il.Add(Instruction.Create(DnOpCodes.Ldloc, m.Body.Variables[5]));
                il.Add(Instruction.Create(op));
                il.Add(Instruction.Create(DnOpCodes.Box, isCmp ? i32r : r4r));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            };
            fOp(0, DnOpCodes.Add, false); fOp(1, DnOpCodes.Sub, false); fOp(2, DnOpCodes.Mul, false);
            fOp(3, DnOpCodes.Div, false); fOp(4, DnOpCodes.Rem, false);
            fOp(13, DnOpCodes.Cgt, true); fOp(14, DnOpCodes.Clt, true);

            il.Add(doLong);
            il.Add(Instruction.Create(DnOpCodes.Call, toI64));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Call, toI64));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            var t = new Instruction[15];
            for (int i = 0; i < 15; i++) t[i] = Instruction.Create(DnOpCodes.Ldloc_0);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Switch, t));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Conv_I8));
            il.Add(Instruction.Create(DnOpCodes.Box, i64r));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            Action<int, OpCode> arith = (idx, op) =>
            {
                il.Add(t[idx]);
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(op));
                il.Add(Instruction.Create(DnOpCodes.Box, i64r));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            };
            Action<int, OpCode> shiftOp = (idx, op) =>
            {
                il.Add(t[idx]);
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.Conv_I4));
                il.Add(Instruction.Create(op));
                il.Add(Instruction.Create(DnOpCodes.Box, i64r));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            };
            Action<int, OpCode> cmp = (idx, op) =>
            {
                il.Add(t[idx]);
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(op));
                il.Add(Instruction.Create(DnOpCodes.Box, i32r));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            };
            arith(0, DnOpCodes.Add); arith(1, DnOpCodes.Sub); arith(2, DnOpCodes.Mul);
            arith(3, DnOpCodes.Div); arith(4, DnOpCodes.Rem);
            arith(5, DnOpCodes.And); arith(6, DnOpCodes.Or);  arith(7, DnOpCodes.Xor);
            shiftOp(8, DnOpCodes.Shl); shiftOp(9, DnOpCodes.Shr);
            arith(10, DnOpCodes.Div_Un); arith(11, DnOpCodes.Rem_Un); shiftOp(12, DnOpCodes.Shr_Un);
            cmp(13, DnOpCodes.Cgt); cmp(14, DnOpCodes.Clt);

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildWideUn(ModuleDef module, TypeDef vmType)
        {
            var objT = module.CorLibTypes.Object;
            var i64 = module.CorLibTypes.Int64;
            var i32 = module.CorLibTypes.Int32;
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(objT, objT, i32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(i64));
            var il = m.Body.Instructions;
            var toI64 = module.Import(typeof(Convert).GetMethod("ToInt64", new[] { typeof(object) }));
            var toR8  = module.Import(typeof(Convert).GetMethod("ToDouble", new[] { typeof(object) }));
            var toR4  = module.Import(typeof(Convert).GetMethod("ToSingle", new[] { typeof(object) }));
            var i64r = i64.TypeDefOrRef;
            var r8r  = module.CorLibTypes.Double.TypeDefOrRef;
            var r4r  = module.CorLibTypes.Single.TypeDefOrRef;

            var doF = Instruction.Create(DnOpCodes.Ldarg_0);
            var doL = Instruction.Create(DnOpCodes.Ldarg_0);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Isinst, r8r));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, doF));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Call, toR8));
            il.Add(Instruction.Create(DnOpCodes.Neg));
            il.Add(Instruction.Create(DnOpCodes.Box, r8r));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(doF);
            il.Add(Instruction.Create(DnOpCodes.Isinst, r4r));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, doL));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Call, toR4));
            il.Add(Instruction.Create(DnOpCodes.Neg));
            il.Add(Instruction.Create(DnOpCodes.Box, r4r));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(doL);
            il.Add(Instruction.Create(DnOpCodes.Call, toI64));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            var notBlk = Instruction.Create(DnOpCodes.Ldloc_0);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, notBlk));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Neg));
            il.Add(Instruction.Create(DnOpCodes.Box, i64r));
            il.Add(Instruction.Create(DnOpCodes.Ret));
            il.Add(notBlk);
            il.Add(Instruction.Create(DnOpCodes.Not));
            il.Add(Instruction.Create(DnOpCodes.Box, i64r));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildWideConv(ModuleDef module, TypeDef vmType)
        {
            var objT = module.CorLibTypes.Object;
            var i64 = module.CorLibTypes.Int64;
            var i32 = module.CorLibTypes.Int32;
            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(objT, objT, i32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(i64));
            var il = m.Body.Instructions;
            var toI64 = module.Import(typeof(Convert).GetMethod("ToInt64", new[] { typeof(object) }));
            var i32r = i32.TypeDefOrRef;
            var r8r  = module.CorLibTypes.Double.TypeDefOrRef;
            var r4r  = module.CorLibTypes.Single.TypeDefOrRef;

            var srcF = Instruction.Create(DnOpCodes.Ldarg_0);
            var srcL = Instruction.Create(DnOpCodes.Ldarg_0);
            var afterSrc = Instruction.Create(DnOpCodes.Nop);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Isinst, r8r));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, srcF));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, r8r));
            il.Add(Instruction.Create(DnOpCodes.Conv_I8));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Br, afterSrc));
            il.Add(srcF);
            il.Add(Instruction.Create(DnOpCodes.Isinst, r4r));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, srcL));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Unbox_Any, r4r));
            il.Add(Instruction.Create(DnOpCodes.Conv_I8));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Br, afterSrc));
            il.Add(srcL);
            il.Add(Instruction.Create(DnOpCodes.Call, toI64));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(afterSrc);

            var t = new Instruction[6];
            for (int i = 0; i < 6; i++) t[i] = Instruction.Create(DnOpCodes.Ldloc_0);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Switch, t));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Conv_I4));
            il.Add(Instruction.Create(DnOpCodes.Box, i32r));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            Action<int, OpCode> conv = (idx, op) =>
            {
                il.Add(t[idx]);
                il.Add(Instruction.Create(op));
                il.Add(Instruction.Create(DnOpCodes.Box, i32r));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            };
            conv(0, DnOpCodes.Conv_I1); conv(1, DnOpCodes.Conv_U1);
            conv(2, DnOpCodes.Conv_I2); conv(3, DnOpCodes.Conv_U2);
            conv(4, DnOpCodes.Conv_I4); conv(5, DnOpCodes.Conv_U4);

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildStElem(ModuleDef module, TypeDef vmType)
        {
            var objT  = module.CorLibTypes.Object;
            var i32   = module.CorLibTypes.Int32;
            var voidT = module.CorLibTypes.Void;
            var arrayRef = module.CorLibTypes.GetTypeRef("System", "Array");
            var typeRef  = module.CorLibTypes.GetTypeRef("System", "Type");

            var m = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(voidT, new ClassSig(arrayRef), i32, objT),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            m.Body = new CilBody();
            m.Body.InitLocals = true;
            m.Body.Variables.Add(new Local(new ClassSig(typeRef)));
            m.Body.Variables.Add(new Local(objT));
            var il = m.Body.Instructions;

            var getType    = module.Import(typeof(object).GetMethod("GetType", Type.EmptyTypes));
            var getElemType= module.Import(typeof(Type).GetMethod("GetElementType", Type.EmptyTypes));
            var isInstOf   = module.Import(typeof(Type).GetMethod("IsInstanceOfType", new[] { typeof(object) }));
            var changeType = module.Import(typeof(Convert).GetMethod("ChangeType", new[] { typeof(object), typeof(Type) }));
            var setValue   = module.Import(typeof(Array).GetMethod("SetValue", new[] { typeof(object), typeof(int) }));

            var doSet = Instruction.Create(DnOpCodes.Ldarg_0);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getType));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getElemType));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_2));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Brfalse, doSet));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, isInstOf));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, doSet));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Call, changeType));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(doSet);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, setValue));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            vmType.Methods.Add(m);
            engine.injectedMethods.Add(m);
            return m;
        }

        private MethodDef BuildInit(ModuleDef module, TypeDef vmType,
            FieldDef fldCode, FieldDef fldSeeds, FieldDef fldNumLocals,
            FieldDef fldStrings, FieldDef fldMethods, FieldDef fldTypes, FieldDef fldFields, FieldDef fldEH, FieldDef fldHash,
            List<byte[]> codes, List<uint> seeds, List<byte> numLocals, List<int[]> ehTables, List<uint> hashes,
            List<string> strings, List<IMethod> methodImports,
            List<ITypeDefOrRef> typeImports, List<IField> fieldImports)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Void),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
            method.Body = new CilBody();
            method.Body.InitLocals = true;
            var byteArrLoc = new Local(new SZArraySig(module.CorLibTypes.Byte));
            var decIdxLoc  = new Local(module.CorLibTypes.Int32);
            var decStLoc   = new Local(module.CorLibTypes.UInt32);
            var varMvidB   = new Local(new SZArraySig(module.CorLibTypes.Byte));
            var varH       = new Local(module.CorLibTypes.UInt32);
            var varChunk   = new Local(module.CorLibTypes.UInt32);
            var varJ       = new Local(module.CorLibTypes.Int32);
            var varMix     = new Local(module.CorLibTypes.UInt32);
            method.Body.Variables.Add(byteArrLoc);
            method.Body.Variables.Add(decIdxLoc);
            method.Body.Variables.Add(decStLoc);
            method.Body.Variables.Add(varMvidB);
            method.Body.Variables.Add(varH);
            method.Body.Variables.Add(varChunk);
            method.Body.Variables.Add(varJ);
            method.Body.Variables.Add(varMix);
            var il = method.Body.Instructions;

            int n = codes.Count;

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, new TypeSpecUser(new SZArraySig(module.CorLibTypes.Byte))));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldCode));
            for (int i = 0; i < n; i++)
            {
                var bc = codes[i];
                il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldCode));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, bc.Length));
                il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
                for (int b = 0; b < bc.Length; b++)
                {
                    il.Add(Instruction.Create(DnOpCodes.Dup));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, b));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, (int)bc[b]));
                    il.Add(Instruction.Create(DnOpCodes.Stelem_I1));
                }
                il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int32.TypeDefOrRef));
            for (int i = 0; i < n; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)seeds[i])));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldSeeds));

            var importer = new Importer(module);
            ITypeDefOrRef sysGuid  = importer.Import(typeof(Guid));
            IMethod getTypeFromH   = importer.Import(typeof(Type).GetMethod("GetTypeFromHandle", new[] { typeof(RuntimeTypeHandle) }));
            IMethod getPropModule  = importer.Import(typeof(Type).GetProperty("Module").GetGetMethod());
            IMethod getPropMvid    = importer.Import(typeof(System.Reflection.Module).GetProperty("ModuleVersionId").GetGetMethod());
            IMethod guidToByteArr  = importer.Import(typeof(Guid).GetMethod("ToByteArray", Type.EmptyTypes));

            il.Add(Instruction.Create(DnOpCodes.Ldtoken, (ITypeDefOrRef)vmType));
            il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromH));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getPropModule));
            il.Add(Instruction.Create(DnOpCodes.Callvirt, getPropMvid));
            var varGuidLoc = new Local(importer.ImportAsTypeSig(typeof(Guid)));
            method.Body.Variables.Add(varGuidLoc);
            il.Add(Instruction.Create(DnOpCodes.Stloc, varGuidLoc));
            il.Add(Instruction.Create(DnOpCodes.Ldloca, varGuidLoc));
            il.Add(Instruction.Create(DnOpCodes.Call, guidToByteArr));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varMvidB));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x9E3779B9u)));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varJ));

            var mixLoopCond = Instruction.Create(DnOpCodes.Ldloc, varJ);
            var mixLoopBody = Instruction.Create(DnOpCodes.Ldloc, varMvidB);
            il.Add(Instruction.Create(DnOpCodes.Br, mixLoopCond));

            il.Add(mixLoopBody);
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_8));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_2));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varMvidB));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_3));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 24));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varChunk));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varChunk));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x85EBCA6Bu)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
            il.Add(Instruction.Create(DnOpCodes.Shl));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 19));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0xC2B2AE35u)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varJ));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_4));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varJ));

            il.Add(mixLoopCond);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Blt, mixLoopBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0x85EBCA6Bu)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)0xC2B2AE35u)));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));

            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 16));
            il.Add(Instruction.Create(DnOpCodes.Shr_Un));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, varH));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Stloc, varMix));

            for (int i = 0; i < n; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldCode));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldelem_Ref));
                il.Add(Instruction.Create(DnOpCodes.Stloc, byteArrLoc));

                il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldSeeds));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldelem_U4));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, varMix));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Stloc, decStLoc));

                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                il.Add(Instruction.Create(DnOpCodes.Stloc, decIdxLoc));

                var loopCond = Instruction.Create(DnOpCodes.Ldloc, decIdxLoc);
                var loopBody = Instruction.Create(DnOpCodes.Ldloc, decStLoc);
                il.Add(Instruction.Create(DnOpCodes.Br, loopCond));

                il.Add(loopBody);
                il.Add(Instruction.Create(DnOpCodes.Ldloc, decStLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 13));
                il.Add(Instruction.Create(DnOpCodes.Shl));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Stloc, decStLoc));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, decStLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, decStLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, 17));
                il.Add(Instruction.Create(DnOpCodes.Shr_Un));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Stloc, decStLoc));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, decStLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, decStLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_5));
                il.Add(Instruction.Create(DnOpCodes.Shl));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Stloc, decStLoc));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, byteArrLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, decIdxLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, byteArrLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, decIdxLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldelem_U1));
                il.Add(Instruction.Create(DnOpCodes.Ldloc, decStLoc));
                il.Add(Instruction.Create(DnOpCodes.Conv_U1));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Conv_U1));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I1));

                il.Add(Instruction.Create(DnOpCodes.Ldloc, decIdxLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Stloc, decIdxLoc));

                il.Add(loopCond);
                il.Add(Instruction.Create(DnOpCodes.Ldloc, byteArrLoc));
                il.Add(Instruction.Create(DnOpCodes.Ldlen));
                il.Add(Instruction.Create(DnOpCodes.Conv_I4));
                il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Byte.TypeDefOrRef));
            for (int i = 0; i < n; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, (int)numLocals[i]));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I1));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldNumLocals));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, strings.Count));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.String.TypeDefOrRef));
            for (int i = 0; i < strings.Count; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldstr, strings[i]));
                il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldStrings));

            var methodBaseTypeRef    = module.CorLibTypes.GetTypeRef("System.Reflection", "MethodBase");
            var typeTypeRef          = module.CorLibTypes.GetTypeRef("System", "Type");
            var getMethodFromHandle  = module.Import(typeof(MethodBase).GetMethod(
                "GetMethodFromHandle", new[] { typeof(RuntimeMethodHandle) }));

            var getMethodFromHandle2 = module.Import(typeof(MethodBase).GetMethod(
                "GetMethodFromHandle", new[] { typeof(RuntimeMethodHandle), typeof(RuntimeTypeHandle) }));
            var getTypeFromHandle    = module.Import(typeof(Type).GetMethod(
                "GetTypeFromHandle", new[] { typeof(RuntimeTypeHandle) }));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, methodImports.Count));
            il.Add(Instruction.Create(DnOpCodes.Newarr, methodBaseTypeRef));
            for (int i = 0; i < methodImports.Count; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldtoken, methodImports[i]));
                var declTok = methodImports[i].DeclaringType;
                var declSig = declTok != null ? declTok.ToTypeSig() : null;
                if (declSig is GenericInstSig)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldtoken, declTok));
                    il.Add(Instruction.Create(DnOpCodes.Call, getMethodFromHandle2));
                }
                else
                {
                    il.Add(Instruction.Create(DnOpCodes.Call, getMethodFromHandle));
                }
                il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldMethods));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, typeImports.Count));
            il.Add(Instruction.Create(DnOpCodes.Newarr, typeTypeRef));
            for (int i = 0; i < typeImports.Count; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldtoken, typeImports[i]));
                il.Add(Instruction.Create(DnOpCodes.Call, getTypeFromHandle));
                il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldTypes));

            var fieldInfoTypeRef2  = module.CorLibTypes.GetTypeRef("System.Reflection", "FieldInfo");
            var getFieldFromHandle = module.Import(typeof(FieldInfo).GetMethod(
                "GetFieldFromHandle", new[] { typeof(RuntimeFieldHandle) }));
            var getFieldFromHandle2 = module.Import(typeof(FieldInfo).GetMethod(
                "GetFieldFromHandle", new[] { typeof(RuntimeFieldHandle), typeof(RuntimeTypeHandle) }));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, fieldImports.Count));
            il.Add(Instruction.Create(DnOpCodes.Newarr, fieldInfoTypeRef2));
            for (int i = 0; i < fieldImports.Count; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldtoken, fieldImports[i]));
                var fdeclTok = fieldImports[i].DeclaringType;
                var fdeclSig = fdeclTok != null ? fdeclTok.ToTypeSig() : null;
                if (fdeclSig is GenericInstSig)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldtoken, fdeclTok));
                    il.Add(Instruction.Create(DnOpCodes.Call, getFieldFromHandle2));
                }
                else
                {
                    il.Add(Instruction.Create(DnOpCodes.Call, getFieldFromHandle));
                }
                il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldFields));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, ehTables.Count));
            il.Add(Instruction.Create(DnOpCodes.Newarr, new TypeSpecUser(new SZArraySig(module.CorLibTypes.Int32))));
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldEH));
            for (int i = 0; i < ehTables.Count; i++)
            {
                var rec = ehTables[i] ?? new int[0];
                il.Add(Instruction.Create(DnOpCodes.Ldsfld, fldEH));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rec.Length));
                il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int32.TypeDefOrRef));
                for (int b = 0; b < rec.Length; b++)
                {
                    il.Add(Instruction.Create(DnOpCodes.Dup));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, b));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rec[b]));
                    il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
                }
                il.Add(Instruction.Create(DnOpCodes.Stelem_Ref));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, _longPool.Count));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Int64.TypeDefOrRef));
            for (int i = 0; i < _longPool.Count; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I8, _longPool[i]));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I8));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, _fldLongs));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, _doublePool.Count));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.Double.TypeDefOrRef));
            for (int i = 0; i < _doublePool.Count; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_R8, _doublePool[i]));
                il.Add(Instruction.Create(DnOpCodes.Stelem_R8));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, _fldDoubles));

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, n));
            il.Add(Instruction.Create(DnOpCodes.Newarr, module.CorLibTypes.UInt32.TypeDefOrRef));
            for (int i = 0; i < n; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Dup));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, i));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, unchecked((int)hashes[i])));
                il.Add(Instruction.Create(DnOpCodes.Stelem_I4));
            }
            il.Add(Instruction.Create(DnOpCodes.Stsfld, fldHash));

            il.Add(Instruction.Create(DnOpCodes.Ret));
            return method;
        }

        private static int MvidToSeed(Guid mvid)
        {
            byte[] b = mvid.ToByteArray();
            uint h = 0x9E3779B9u;
            for (int i = 0; i < 16; i += 4)
            {
                uint chunk = unchecked((uint)(b[i] | (b[i+1] << 8) | (b[i+2] << 16) | (b[i+3] << 24)));
                h = unchecked((h ^ chunk) * 0x85EBCA6Bu);
                h = unchecked(((h << 13) | (h >> 19)) * 0xC2B2AE35u);
            }
            h ^= h >> 16;
            h = unchecked(h * 0x85EBCA6Bu);
            h ^= h >> 13;
            h = unchecked(h * 0xC2B2AE35u);
            h ^= h >> 16;
            return (int)(h | 1u);
        }
    }
}

