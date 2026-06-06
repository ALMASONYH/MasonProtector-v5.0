using System;
using System.Collections.Generic;
using System.Linq;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class ControlFlowProtection
    {
        private Obfuscation engine;
        private Random rng;
        private FieldDef cfZero;

        internal ControlFlowProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyControlFlow(ModuleDef module)
        {
            engine.activeOption = "ControlFlow";
            bool allowDesigner = true;
            cfZero = EnsureCfZero(module);
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method, allowDesigner)) continue;
                    if (method.IsConstructor || method.IsStaticConstructor) continue;
                    if (!method.HasBody || !method.Body.HasInstructions) continue;
                    if (method == module.EntryPoint) continue;
                    try
                    {
                        bool changed = false;
                        if (!method.Body.HasExceptionHandlers)
                        {
                            try { changed = FlattenWithBranches(module, method); }
                            catch { changed = false; }
                        }
                        if (!changed)
                            changed = InjectInlineFlow(module, method);
                        if (changed)
                        {
                            engine.controlFlowFlattenedMethods.Add(method);
                            method.Body.SimplifyBranches();
                            method.Body.OptimizeBranches();
                        }
                    }
                    catch { }
                }
            }
        }

        private FieldDef EnsureCfZero(ModuleDef module)
        {
            try
            {
                TypeDef host = module.GlobalType;
                if (host == null) return null;
                var f = new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    dnlib.DotNet.FieldAttributes.Assembly | dnlib.DotNet.FieldAttributes.Static);
                host.Fields.Add(f);
                return f;
            }
            catch { return null; }
        }

        private bool InjectInlineFlow(ModuleDef module, MethodDef method)
        {
            if (cfZero == null) return false;
            var body = method.Body;
            body.SimplifyBranches();
            body.SimplifyMacros(method.Parameters);
            var il = body.Instructions;
            int n = il.Count;
            if (n < 1) return false;

            var idxOf = new Dictionary<Instruction, int>(n);
            for (int i = 0; i < n; i++) idxOf[il[i]] = i;

            var ehBoundary = new HashSet<Instruction>();
            foreach (var eh in body.ExceptionHandlers)
            {
                if (eh.TryStart != null) ehBoundary.Add(eh.TryStart);
                if (eh.TryEnd != null) ehBoundary.Add(eh.TryEnd);
                if (eh.HandlerStart != null) ehBoundary.Add(eh.HandlerStart);
                if (eh.HandlerEnd != null) ehBoundary.Add(eh.HandlerEnd);
                if (eh.FilterStart != null) ehBoundary.Add(eh.FilterStart);
            }

            var depth = new int[n];
            var filled = new bool[n];
            var wi = new Stack<int>();
            var wd = new Stack<int>();
            wi.Push(0); wd.Push(0);
            foreach (var eh in body.ExceptionHandlers)
            {
                if (eh.HandlerStart != null && idxOf.ContainsKey(eh.HandlerStart))
                {
                    int hd = (eh.HandlerType == ExceptionHandlerType.Catch ||
                              eh.HandlerType == ExceptionHandlerType.Filter) ? 1 : 0;
                    wi.Push(idxOf[eh.HandlerStart]); wd.Push(hd);
                }
                if (eh.FilterStart != null && idxOf.ContainsKey(eh.FilterStart))
                {
                    wi.Push(idxOf[eh.FilterStart]); wd.Push(1);
                }
            }
            while (wi.Count > 0)
            {
                int i = wi.Pop(); int d = wd.Pop();
                if (i < 0 || i >= n) return false;
                if (filled[i]) { if (depth[i] != d) return false; continue; }
                depth[i] = d; filled[i] = true;
                int d2 = d + GetStackDelta(il[i]);
                if (d2 < 0) return false;
                var op = il[i].OpCode;
                Code code = op.Code;
                FlowControl fc = op.FlowControl;
                if (fc == FlowControl.Return || code == Code.Throw || code == Code.Rethrow)
                {
                }
                else if (code == Code.Leave || code == Code.Leave_S)
                {
                    var t = il[i].Operand as Instruction;
                    if (t != null && idxOf.ContainsKey(t)) { wi.Push(idxOf[t]); wd.Push(0); }
                }
                else if (code == Code.Endfinally)
                {
                }
                else if (fc == FlowControl.Branch)
                {
                    var t = il[i].Operand as Instruction;
                    if (t == null || !idxOf.ContainsKey(t)) return false;
                    wi.Push(idxOf[t]); wd.Push(d2);
                }
                else if (fc == FlowControl.Cond_Branch)
                {
                    if (code == Code.Switch)
                    {
                        var ts = il[i].Operand as Instruction[];
                        if (ts == null) return false;
                        foreach (var t in ts)
                        {
                            if (t == null || !idxOf.ContainsKey(t)) return false;
                            wi.Push(idxOf[t]); wd.Push(d2);
                        }
                    }
                    else
                    {
                        var t = il[i].Operand as Instruction;
                        if (t == null || !idxOf.ContainsKey(t)) return false;
                        wi.Push(idxOf[t]); wd.Push(d2);
                    }
                    if (i + 1 < n) { wi.Push(i + 1); wd.Push(d2); } else return false;
                }
                else
                {
                    if (i + 1 < n) { wi.Push(i + 1); wd.Push(d2); } else return false;
                }
            }

            int gap = engine.LevelRange(7, 11, 4, 6, 2, 3);
            var points = new List<Instruction>();
            int since = gap;
            for (int i = 0; i < n; i++)
            {
                if (!filled[i]) continue;
                if (depth[i] != 0) continue;
                if (ehBoundary.Contains(il[i])) continue;
                since++;
                if (since >= gap) { points.Add(il[i]); since = 0; }
            }
            if (points.Count == 0) return false;

            var junk = new Local(module.CorLibTypes.Int32);
            body.Variables.Add(junk);
            body.InitLocals = true;

            foreach (var p in points)
            {
                int pi = il.IndexOf(p);
                if (pi < 0) continue;
                var ins = new List<Instruction>();
                ins.Add(Instruction.Create(DnOpCodes.Ldsfld, cfZero));
                ins.Add(Instruction.Create(DnOpCodes.Brfalse, p));
                int jn = engine.LevelPick(1, 2, 3);
                for (int k = 0; k < jn; k++)
                {
                    ins.Add(Instruction.Create(DnOpCodes.Ldloc, junk));
                    ins.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    int pick = rng.Next(0, 3);
                    ins.Add(Instruction.Create(pick == 0 ? DnOpCodes.Xor :
                                               pick == 1 ? DnOpCodes.Add : DnOpCodes.Mul));
                    ins.Add(Instruction.Create(DnOpCodes.Stloc, junk));
                }
                for (int k = 0; k < ins.Count; k++) il.Insert(pi + k, ins[k]);
            }
            return true;
        }

        private class DispatchEntry
        {
            public int Hash;
            public Instruction Target;
        }

        private void EmitTransition(List<Instruction> il, int fromHash, int toHash,
            Local sA, Local sB, Local sC)
        {
            int delta = fromHash ^ toHash;
            int dA = rng.Next();
            int dB = rng.Next();
            int dC = delta ^ dA ^ dB;
            il.Add(Instruction.Create(DnOpCodes.Ldloc, sA));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, dA));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, sA));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, sB));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, dB));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, sB));
            il.Add(Instruction.Create(DnOpCodes.Ldloc, sC));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, dC));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc, sC));
        }

        private bool FlattenWithBranches(ModuleDef module, MethodDef method)
        {
            var body = method.Body;
            body.SimplifyBranches();
            body.SimplifyMacros(method.Parameters);
            var il = body.Instructions;
            int n = il.Count;
            if (n < 4) return false;

            var idxOf = new Dictionary<Instruction, int>(n);
            for (int i = 0; i < n; i++) idxOf[il[i]] = i;

            for (int i = 0; i < n; i++)
            {
                var op = il[i].OpCode;
                if (op.Code == Code.Switch) return false;
                var fc = op.FlowControl;
                if (fc == FlowControl.Break || fc == FlowControl.Meta || fc == FlowControl.Phi) return false;
                if ((fc == FlowControl.Branch || fc == FlowControl.Cond_Branch) &&
                    !(il[i].Operand is Instruction)) return false;
            }

            var isLeader = new bool[n];
            isLeader[0] = true;
            for (int i = 0; i < n; i++)
            {
                var op = il[i].OpCode;
                var fc = op.FlowControl;
                if (fc == FlowControl.Branch || fc == FlowControl.Cond_Branch)
                {
                    var tgt = il[i].Operand as Instruction;
                    if (tgt == null || !idxOf.ContainsKey(tgt)) return false;
                    isLeader[idxOf[tgt]] = true;
                    if (i + 1 < n) isLeader[i + 1] = true;
                }
                else if (fc == FlowControl.Return || op.Code == Code.Throw || op.Code == Code.Rethrow)
                {
                    if (i + 1 < n) isLeader[i + 1] = true;
                }
            }

            var depth = new int[n];
            var filled = new bool[n];
            var wi = new Stack<int>();
            var wd = new Stack<int>();
            wi.Push(0); wd.Push(0);
            while (wi.Count > 0)
            {
                int i = wi.Pop(); int d = wd.Pop();
                if (i < 0 || i >= n) return false;
                if (filled[i]) { if (depth[i] != d) return false; continue; }
                depth[i] = d; filled[i] = true;
                int d2 = d + GetStackDelta(il[i]);
                if (d2 < 0) return false;
                var op = il[i].OpCode;
                var fc = op.FlowControl;
                if (fc == FlowControl.Return || op.Code == Code.Throw || op.Code == Code.Rethrow)
                {
                }
                else if (fc == FlowControl.Branch)
                {
                    wi.Push(idxOf[(Instruction)il[i].Operand]); wd.Push(d2);
                }
                else if (fc == FlowControl.Cond_Branch)
                {
                    wi.Push(idxOf[(Instruction)il[i].Operand]); wd.Push(d2);
                    if (i + 1 >= n) return false;
                    wi.Push(i + 1); wd.Push(d2);
                }
                else
                {
                    if (i + 1 >= n) return false;
                    wi.Push(i + 1); wd.Push(d2);
                }
            }

            for (int i = 0; i < n; i++)
            {
                if (!filled[i]) return false;
                if (isLeader[i] && depth[i] != 0) return false;
            }

            int blockSize = engine.LevelRange(5, 9, 2, 4, 1, 2);
            if (n > 400) blockSize = Math.Max(blockSize, n / 250);
            int sinceLeader = 0;
            for (int i = 0; i < n; i++)
            {
                if (isLeader[i]) { sinceLeader = 0; continue; }
                sinceLeader++;
                if (sinceLeader >= blockSize && depth[i] == 0) { isLeader[i] = true; sinceLeader = 0; }
            }

            var starts = new List<int>();
            for (int i = 0; i < n; i++) if (isLeader[i]) starts.Add(i);
            int bc = starts.Count;
            if (bc < 2) return false;
            if (bc > engine.LevelPick(150, 320, 520)) return false;

            var blockOfIdx = new int[n];
            for (int b = 0; b < bc; b++)
            {
                int s = starts[b];
                int e = (b + 1 < bc) ? starts[b + 1] : n;
                for (int i = s; i < e; i++) blockOfIdx[i] = b;
            }

            int[] hashes = new int[bc];
            var used = new HashSet<int>();
            for (int b = 0; b < bc; b++)
            { int h; do { h = rng.Next(1024, int.MaxValue); } while (used.Contains(h)); hashes[b] = h; used.Add(h); }

            int bogusCount = Math.Min(bc / engine.LevelPick(6, 2, 1) + engine.LevelPick(1, 6, 16),
                                      engine.LevelPick(5, 34, 96));
            int[] bogusHashes = new int[bogusCount];
            for (int i = 0; i < bogusCount; i++)
            { int h; do { h = rng.Next(1024, int.MaxValue); } while (used.Contains(h)); bogusHashes[i] = h; used.Add(h); }

            var sA = new Local(module.CorLibTypes.Int32);
            var sB = new Local(module.CorLibTypes.Int32);
            var sC = new Local(module.CorLibTypes.Int32);
            var sJ = new Local(module.CorLibTypes.Int32);
            body.Variables.Add(sA); body.Variables.Add(sB); body.Variables.Add(sC); body.Variables.Add(sJ);
            body.InitLocals = true;

            bool isVoid = method.ReturnType == null || method.ReturnType.FullName == "System.Void";
            Local retLocal = null;
            if (!isVoid) { retLocal = new Local(method.ReturnType); body.Variables.Add(retLocal); }

            var blockEntries = new Instruction[bc];
            for (int b = 0; b < bc; b++) blockEntries[b] = Instruction.Create(DnOpCodes.Nop);
            var bogusEntries = new Instruction[bogusCount];
            for (int i = 0; i < bogusCount; i++) bogusEntries[i] = Instruction.Create(DnOpCodes.Nop);
            var loopHead = Instruction.Create(DnOpCodes.Nop);
            var exitPoint = isVoid ? Instruction.Create(DnOpCodes.Ret) : Instruction.Create(DnOpCodes.Ldloc, retLocal);
            Instruction exitRet = isVoid ? null : Instruction.Create(DnOpCodes.Ret);

            int initB = rng.Next(), initC = rng.Next();
            int initA = hashes[0] ^ initB ^ initC;

            var o = new List<Instruction>();
            o.Add(Instruction.Create(DnOpCodes.Ldc_I4, initA)); o.Add(Instruction.Create(DnOpCodes.Stloc, sA));
            o.Add(Instruction.Create(DnOpCodes.Ldc_I4, initB)); o.Add(Instruction.Create(DnOpCodes.Stloc, sB));
            o.Add(Instruction.Create(DnOpCodes.Ldc_I4, initC)); o.Add(Instruction.Create(DnOpCodes.Stloc, sC));
            o.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next())); o.Add(Instruction.Create(DnOpCodes.Stloc, sJ));
            o.Add(loopHead);

            var entries = new List<DispatchEntry>();
            for (int b = 0; b < bc; b++) entries.Add(new DispatchEntry { Hash = hashes[b], Target = blockEntries[b] });
            for (int i = 0; i < bogusCount; i++) entries.Add(new DispatchEntry { Hash = bogusHashes[i], Target = bogusEntries[i] });
            entries = entries.OrderBy(_ => rng.Next()).ToList();
            foreach (var en in entries)
            {
                EmitDispatchJunk(o, sJ);
                EmitStateKey(o, sA, sB, sC);
                o.Add(Instruction.Create(DnOpCodes.Ldc_I4, en.Hash));
                o.Add(Instruction.Create(DnOpCodes.Beq, en.Target));
            }
            o.Add(Instruction.Create(DnOpCodes.Br, exitPoint));

            int[] order = Enumerable.Range(0, bc).OrderBy(_ => rng.Next()).ToArray();
            foreach (int b in order)
            {
                int s = starts[b];
                int e = (b + 1 < bc) ? starts[b + 1] : n;
                o.Add(blockEntries[b]);

                var last = il[e - 1];
                var lop = last.OpCode;
                var lfc = lop.FlowControl;
                bool isCond = lfc == FlowControl.Cond_Branch;
                bool isBr = lfc == FlowControl.Branch;
                bool isRet = lfc == FlowControl.Return;
                bool isThrow = lop.Code == Code.Throw || lop.Code == Code.Rethrow;

                int bodyEnd = (isCond || isBr || isRet) ? (e - 1) : e;
                for (int i = s; i < bodyEnd; i++) o.Add(il[i]);

                if (isRet)
                {
                    if (!isVoid) o.Add(Instruction.Create(DnOpCodes.Stloc, retLocal));
                    o.Add(Instruction.Create(DnOpCodes.Br, exitPoint));
                }
                else if (isThrow)
                {
                }
                else if (isBr)
                {
                    int tb = blockOfIdx[idxOf[(Instruction)last.Operand]];
                    EmitTransition(o, hashes[b], hashes[tb], sA, sB, sC);
                    o.Add(Instruction.Create(DnOpCodes.Br, loopHead));
                }
                else if (isCond)
                {
                    var ltaken = Instruction.Create(DnOpCodes.Nop);
                    o.Add(Instruction.Create(lop, ltaken));
                    int fallBlock = blockOfIdx[e < n ? e : (n - 1)];
                    EmitTransition(o, hashes[b], hashes[fallBlock], sA, sB, sC);
                    o.Add(Instruction.Create(DnOpCodes.Br, loopHead));
                    o.Add(ltaken);
                    int tb = blockOfIdx[idxOf[(Instruction)last.Operand]];
                    EmitTransition(o, hashes[b], hashes[tb], sA, sB, sC);
                    o.Add(Instruction.Create(DnOpCodes.Br, loopHead));
                }
                else
                {
                    int nextBlock = blockOfIdx[e < n ? e : (n - 1)];
                    EmitTransition(o, hashes[b], hashes[nextBlock], sA, sB, sC);
                    o.Add(Instruction.Create(DnOpCodes.Br, loopHead));
                }
            }

            for (int i = 0; i < bogusCount; i++)
            {
                o.Add(bogusEntries[i]);
                EmitBogusBlock(o, sA, sB, sC);
                o.Add(Instruction.Create(DnOpCodes.Br, exitPoint));
            }

            o.Add(exitPoint);
            if (exitRet != null) o.Add(exitRet);

            il.Clear();
            foreach (var ins in o) il.Add(ins);
            body.OptimizeBranches();
            return true;
        }

        private void EmitStateKey(List<Instruction> il, Local sA, Local sB, Local sC)
        {
            int variant = rng.Next(0, 3);
            switch (variant)
            {
                case 0:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sA));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sB));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sC));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                case 1:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sB));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sC));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sA));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
                default:
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sC));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sA));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc, sB));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    break;
            }
        }

        private void EmitDispatchJunk(List<Instruction> il, Local junk)
        {
            int n = engine.LevelPick(0, 2, 6);
            for (int i = 0; i < n; i++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc, junk));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                switch (rng.Next(0, 4))
                {
                    case 0: il.Add(Instruction.Create(DnOpCodes.Xor)); break;
                    case 1: il.Add(Instruction.Create(DnOpCodes.Add)); break;
                    case 2: il.Add(Instruction.Create(DnOpCodes.Sub)); break;
                    default: il.Add(Instruction.Create(DnOpCodes.Mul)); break;
                }
                il.Add(Instruction.Create(DnOpCodes.Stloc, junk));
            }
        }

        private void EmitBogusBlock(List<Instruction> il, Local sA, Local sB, Local sC)
        {
            int ops = rng.Next(3, 7);
            for (int i = 0; i < ops; i++)
            {
                Local target;
                int pick = rng.Next(0, 3);
                if (pick == 0) target = sA;
                else if (pick == 1) target = sB;
                else target = sC;

                int op = rng.Next(0, 5);
                switch (op)
                {
                    case 0:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc, target));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Xor));
                        il.Add(Instruction.Create(DnOpCodes.Stloc, target));
                        break;
                    case 1:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc, target));
                        il.Add(Instruction.Create(DnOpCodes.Not));
                        il.Add(Instruction.Create(DnOpCodes.Stloc, target));
                        break;
                    case 2:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc, target));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Add));
                        il.Add(Instruction.Create(DnOpCodes.Stloc, target));
                        break;
                    case 3:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc, target));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 16)));
                        il.Add(Instruction.Create(DnOpCodes.Shl));
                        il.Add(Instruction.Create(DnOpCodes.Stloc, target));
                        break;
                    default:
                        il.Add(Instruction.Create(DnOpCodes.Ldloc, target));
                        il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                        il.Add(Instruction.Create(DnOpCodes.Sub));
                        il.Add(Instruction.Create(DnOpCodes.Stloc, target));
                        break;
                }
            }
        }

        private int GetStackDelta(Instruction inst)
        {
            int push = 0, pop = 0;
            switch (inst.OpCode.StackBehaviourPush)
            {
                case StackBehaviour.Push0: push = 0; break;
                case StackBehaviour.Push1:
                case StackBehaviour.Pushi:
                case StackBehaviour.Pushi8:
                case StackBehaviour.Pushr4:
                case StackBehaviour.Pushr8:
                case StackBehaviour.Pushref: push = 1; break;
                case StackBehaviour.Push1_push1: push = 2; break;
                case StackBehaviour.Varpush:
                    if (inst.OpCode == DnOpCodes.Newobj)
                    {
                        push = 1;
                    }
                    else if (inst.OpCode == DnOpCodes.Call || inst.OpCode == DnOpCodes.Callvirt)
                    {
                        var mr = inst.Operand as IMethod;
                        if (mr != null && mr.MethodSig != null && mr.MethodSig.RetType != null &&
                            mr.MethodSig.RetType.FullName != "System.Void")
                            push = 1;
                    }
                    break;
                default: push = 0; break;
            }
            switch (inst.OpCode.StackBehaviourPop)
            {
                case StackBehaviour.Pop0: pop = 0; break;
                case StackBehaviour.Pop1:
                case StackBehaviour.Popi:
                case StackBehaviour.Popref: pop = 1; break;
                case StackBehaviour.Pop1_pop1:
                case StackBehaviour.Popi_pop1:
                case StackBehaviour.Popi_popi:
                case StackBehaviour.Popi_popi8:
                case StackBehaviour.Popi_popr4:
                case StackBehaviour.Popi_popr8:
                case StackBehaviour.Popref_pop1:
                case StackBehaviour.Popref_popi: pop = 2; break;
                case StackBehaviour.Popi_popi_popi:
                case StackBehaviour.Popref_popi_popi:
                case StackBehaviour.Popref_popi_popi8:
                case StackBehaviour.Popref_popi_popr4:
                case StackBehaviour.Popref_popi_popr8:
                case StackBehaviour.Popref_popi_popref:
                case StackBehaviour.Popref_popi_pop1: pop = 3; break;
                case StackBehaviour.Varpop:
                    if (inst.OpCode == DnOpCodes.Call || inst.OpCode == DnOpCodes.Callvirt || inst.OpCode == DnOpCodes.Newobj)
                    {
                        var m = inst.Operand as IMethod;
                        if (m != null && m.MethodSig != null)
                        {
                            pop = m.MethodSig.Params.Count;
                            if (m.MethodSig.HasThis && inst.OpCode != DnOpCodes.Newobj) pop++;
                        }
                    }
                    break;
                default: pop = 0; break;
            }
            return push - pop;
        }
    }
}

