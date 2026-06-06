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
    internal class BranchConfusionProtection
    {
        private Obfuscation engine;
        private Random rng;

        private List<TypeDef> hostTypes;

        internal BranchConfusionProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyBranchConfusion(ModuleDef module, TypeDef modType)
        {
            hostTypes = new List<TypeDef>();

            CreateBranchHostTypes(module);
            PopulateHostsWithFields(module);
            PopulateHostsWithMethods(module);
            InjectExtraDecoyMethods(module);
            ConfuseUserMethods(module);
        }

        private FieldDef bcZero;

        private void ConfuseUserMethods(ModuleDef module)
        {
            bcZero = EnsureZeroField(module);
            if (bcZero == null) return;
            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                if (engine.injectedTypes.Contains(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    if (method.IsConstructor || method.IsStaticConstructor) continue;
                    if (!method.HasBody || !method.Body.HasInstructions) continue;
                    if (method == module.EntryPoint) continue;
                    try { InjectBranchFan(module, method); } catch { }
                }
            }
        }

        private FieldDef EnsureZeroField(ModuleDef module)
        {
            try
            {
                TypeDef host = module.GlobalType;
                if (host == null && hostTypes != null && hostTypes.Count > 0) host = hostTypes[0];
                if (host == null) return null;
                var f = new FieldDefUser(engine.MakeName(),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                host.Fields.Add(f);
                return f;
            }
            catch { return null; }
        }

        private bool InjectBranchFan(ModuleDef module, MethodDef method)
        {
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
                int d2 = d + StackDelta(il[i]);
                if (d2 < 0) return false;
                Code code = il[i].OpCode.Code;
                FlowControl fc = il[i].OpCode.FlowControl;
                if (fc == FlowControl.Return || code == Code.Throw || code == Code.Rethrow) { }
                else if (code == Code.Leave || code == Code.Leave_S)
                {
                    var t = il[i].Operand as Instruction;
                    if (t != null && idxOf.ContainsKey(t)) { wi.Push(idxOf[t]); wd.Push(0); }
                }
                else if (code == Code.Endfinally) { }
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
                        foreach (var t in ts) { if (t == null || !idxOf.ContainsKey(t)) return false; wi.Push(idxOf[t]); wd.Push(d2); }
                    }
                    else
                    {
                        var t = il[i].Operand as Instruction;
                        if (t == null || !idxOf.ContainsKey(t)) return false;
                        wi.Push(idxOf[t]); wd.Push(d2);
                    }
                    if (i + 1 < n) { wi.Push(i + 1); wd.Push(d2); } else return false;
                }
                else { if (i + 1 < n) { wi.Push(i + 1); wd.Push(d2); } else return false; }
            }

            int gap = engine.LevelRange(8, 12, 4, 7, 3, 4);
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
                var bogus = Instruction.Create(DnOpCodes.Nop);
                var ins = new List<Instruction>();
                ins.Add(Instruction.Create(DnOpCodes.Ldsfld, bcZero));
                ins.Add(Instruction.Create(DnOpCodes.Brtrue, bogus));
                ins.Add(Instruction.Create(DnOpCodes.Ldsfld, bcZero));
                ins.Add(Instruction.Create(DnOpCodes.Brfalse, p));
                ins.Add(bogus);
                ins.Add(Instruction.Create(DnOpCodes.Ldloc, junk));
                ins.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                ins.Add(Instruction.Create(rng.Next(0, 2) == 0 ? DnOpCodes.Xor : DnOpCodes.Add));
                ins.Add(Instruction.Create(DnOpCodes.Stloc, junk));
                ins.Add(Instruction.Create(DnOpCodes.Br, p));
                for (int k = 0; k < ins.Count; k++) il.Insert(pi + k, ins[k]);
            }
            body.OptimizeBranches();
            return true;
        }

        private int StackDelta(Instruction inst)
        {
            int push = 0, pop = 0;
            switch (inst.OpCode.StackBehaviourPush)
            {
                case StackBehaviour.Push1: case StackBehaviour.Pushi: case StackBehaviour.Pushi8:
                case StackBehaviour.Pushr4: case StackBehaviour.Pushr8: case StackBehaviour.Pushref: push = 1; break;
                case StackBehaviour.Push1_push1: push = 2; break;
                case StackBehaviour.Varpush:
                    if (inst.OpCode == DnOpCodes.Newobj) push = 1;
                    else if (inst.OpCode == DnOpCodes.Call || inst.OpCode == DnOpCodes.Callvirt)
                    {
                        var mr = inst.Operand as IMethod;
                        if (mr != null && mr.MethodSig != null && mr.MethodSig.RetType != null &&
                            mr.MethodSig.RetType.FullName != "System.Void") push = 1;
                    }
                    break;
            }
            switch (inst.OpCode.StackBehaviourPop)
            {
                case StackBehaviour.Pop1: case StackBehaviour.Popi: case StackBehaviour.Popref: pop = 1; break;
                case StackBehaviour.Pop1_pop1: case StackBehaviour.Popi_pop1: case StackBehaviour.Popi_popi:
                case StackBehaviour.Popi_popi8: case StackBehaviour.Popi_popr4: case StackBehaviour.Popi_popr8:
                case StackBehaviour.Popref_pop1: case StackBehaviour.Popref_popi: pop = 2; break;
                case StackBehaviour.Popi_popi_popi: case StackBehaviour.Popref_popi_popi:
                case StackBehaviour.Popref_popi_popi8: case StackBehaviour.Popref_popi_popr4:
                case StackBehaviour.Popref_popi_popr8: case StackBehaviour.Popref_popi_popref:
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
            }
            return push - pop;
        }

        private void CreateBranchHostTypes(ModuleDef module)
        {
            int hostCount = rng.Next(16, 28);
            for (int i = 0; i < hostCount; i++)
            {
                var host = new TypeDefUser("", engine.MakeName(),
                    module.CorLibTypes.Object.TypeDefOrRef);
                host.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;
                module.Types.Add(host);
                engine.injectedTypes.Add(host);
                hostTypes.Add(host);
            }
        }

        private void PopulateHostsWithFields(ModuleDef module)
        {
            foreach (TypeDef host in hostTypes)
            {
                int fieldCount = rng.Next(10, 22);
                for (int f = 0; f < fieldCount; f++)
                {
                    TypeSig fieldType;
                    int t = rng.Next(0, 6);
                    if (t == 0) fieldType = module.CorLibTypes.Int32;
                    else if (t == 1) fieldType = module.CorLibTypes.Int64;
                    else if (t == 2) fieldType = module.CorLibTypes.Boolean;
                    else if (t == 3) fieldType = module.CorLibTypes.Byte;
                    else if (t == 4) fieldType = module.CorLibTypes.Double;
                    else fieldType = new SZArraySig(module.CorLibTypes.Int32);

                    host.Fields.Add(new FieldDefUser(engine.MakeName(),
                        new FieldSig(fieldType),
                        DnFieldAttributes.Private | DnFieldAttributes.Static));
                }
            }
        }

        private void PopulateHostsWithMethods(ModuleDef module)
        {
            foreach (TypeDef host in hostTypes)
            {
                int methodCount = rng.Next(3, 7);
                for (int m = 0; m < methodCount; m++)
                {
                    MethodDef method;
                    int kind = rng.Next(0, 4);
                    if (kind == 0)
                        method = BuildSwitchMethod(module);
                    else if (kind == 1)
                        method = BuildNestedTryCatch(module);
                    else if (kind == 2)
                        method = BuildLoopMethod(module);
                    else
                        method = BuildBranchyMethod(module);

                    host.Methods.Add(method);
                    engine.injectedMethods.Add(method);
                }
            }
        }

        private void InjectExtraDecoyMethods(ModuleDef module)
        {
            int extraCount = rng.Next(8, 16);
            for (int i = 0; i < extraCount; i++)
            {
                TypeDef host = hostTypes[rng.Next(hostTypes.Count)];
                MethodDef method;
                int kind = rng.Next(0, 4);
                if (kind == 0)
                    method = BuildSwitchMethod(module);
                else if (kind == 1)
                    method = BuildNestedTryCatch(module);
                else if (kind == 2)
                    method = BuildLoopMethod(module);
                else
                    method = BuildBranchyMethod(module);

                host.Methods.Add(method);
                engine.injectedMethods.Add(method);
            }
        }

        private MethodDef BuildSwitchMethod(ModuleDef module)
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
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            var retLabel = Instruction.Create(DnOpCodes.Ldloc_0);

            int caseCount = rng.Next(4, 8);
            var caseTargets = new Instruction[caseCount];
            for (int c = 0; c < caseCount; c++)
            {
                caseTargets[c] = Instruction.Create(DnOpCodes.Nop);
            }

            var defaultTarget = Instruction.Create(DnOpCodes.Nop);

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, caseCount));
            il.Add(Instruction.Create(DnOpCodes.Rem));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Switch, caseTargets));
            il.Add(Instruction.Create(DnOpCodes.Br, defaultTarget));

            for (int c = 0; c < caseCount; c++)
            {
                il.Add(caseTargets[c]);
                int ops = rng.Next(3, 7);
                for (int r = 0; r < ops; r++)
                {
                    EmitRandomALU(il, rng);
                }
                il.Add(Instruction.Create(DnOpCodes.Br, retLabel));
            }

            il.Add(defaultTarget);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Not));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Br, retLabel));

            il.Add(retLabel);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildNestedTryCatch(ModuleDef module)
        {
            var method = new MethodDefUser(engine.MakeName(),
                MethodSig.CreateStatic(module.CorLibTypes.Int32,
                    module.CorLibTypes.Int32),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            var afterAll = Instruction.Create(DnOpCodes.Ldloc_0);

            var outerTryStart = Instruction.Create(DnOpCodes.Ldarg_0);
            var innerTryStart = Instruction.Create(DnOpCodes.Ldloc_0);
            var innerHandlerStart = Instruction.Create(DnOpCodes.Pop);
            var innerAfter = Instruction.Create(DnOpCodes.Nop);
            var outerHandlerStart = Instruction.Create(DnOpCodes.Pop);

            il.Add(outerTryStart);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(innerTryStart);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            for (int r = 0; r < rng.Next(3, 6); r++)
            {
                int op = rng.Next(0, 4);
                if (op == 0)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_2));
                }
                else if (op == 1)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                }
                else if (op == 2)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Sub));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                }
                else
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 16)));
                    il.Add(Instruction.Create(DnOpCodes.Shr));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_2));
                }
            }

            il.Add(Instruction.Create(DnOpCodes.Leave, innerAfter));

            il.Add(innerHandlerStart);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Leave, innerAfter));

            il.Add(innerAfter);

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            for (int r = 0; r < rng.Next(2, 5); r++)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }

            il.Add(Instruction.Create(DnOpCodes.Leave, afterAll));

            il.Add(outerHandlerStart);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_M1));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Leave, afterAll));

            var outerHandlerEnd = Instruction.Create(DnOpCodes.Nop);
            il.Add(outerHandlerEnd);

            il.Add(afterAll);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            var innerHandler = new ExceptionHandler(ExceptionHandlerType.Catch);
            innerHandler.TryStart = innerTryStart;
            innerHandler.TryEnd = innerHandlerStart;
            innerHandler.HandlerStart = innerHandlerStart;
            innerHandler.HandlerEnd = innerAfter;
            innerHandler.CatchType = module.CorLibTypes.GetTypeRef("System", "Exception");
            method.Body.ExceptionHandlers.Add(innerHandler);

            var outerHandler = new ExceptionHandler(ExceptionHandlerType.Catch);
            outerHandler.TryStart = outerTryStart;
            outerHandler.TryEnd = outerHandlerStart;
            outerHandler.HandlerStart = outerHandlerStart;
            outerHandler.HandlerEnd = outerHandlerEnd;
            outerHandler.CatchType = module.CorLibTypes.GetTypeRef("System", "Exception");
            method.Body.ExceptionHandlers.Add(outerHandler);

            return method;
        }

        private MethodDef BuildLoopMethod(ModuleDef module)
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
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            int loopBound = rng.Next(4, 12);

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));

            var loopCheck = Instruction.Create(DnOpCodes.Ldloc_2);
            var loopBody = Instruction.Create(DnOpCodes.Nop);

            il.Add(Instruction.Create(DnOpCodes.Br, loopCheck));

            il.Add(loopBody);

            for (int r = 0; r < rng.Next(4, 8); r++)
            {
                int op = rng.Next(0, 6);
                if (op == 0)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_3));
                }
                else if (op == 1)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Add));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                }
                else if (op == 2)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Not));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                }
                else if (op == 3)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_3));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Or));
                    il.Add(Instruction.Create(DnOpCodes.Stloc, method.Body.Variables[4]));
                }
                else if (op == 4)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 8)));
                    il.Add(Instruction.Create(DnOpCodes.Shl));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                }
                else
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Sub));
                    il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                }
            }

            var innerLoopCheck = Instruction.Create(DnOpCodes.Ldloc_3);
            var innerLoopBody = Instruction.Create(DnOpCodes.Nop);

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_3));
            il.Add(Instruction.Create(DnOpCodes.Br, innerLoopCheck));

            il.Add(innerLoopBody);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_3));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_3));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_3));

            il.Add(innerLoopCheck);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(2, 6)));
            il.Add(Instruction.Create(DnOpCodes.Blt, innerLoopBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));

            il.Add(loopCheck);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, loopBound));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildBranchyMethod(ModuleDef module)
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
            method.Body.Variables.Add(new Local(module.CorLibTypes.Boolean));
            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_1));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            var retLabel = Instruction.Create(DnOpCodes.Ldloc_0);

            int branchCount = rng.Next(4, 8);
            for (int b = 0; b < branchCount; b++)
            {
                var elseLabel = Instruction.Create(DnOpCodes.Nop);
                var mergeLabel = Instruction.Create(DnOpCodes.Nop);

                int condKind = rng.Next(0, 4);
                if (condKind == 0)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.And));
                    il.Add(Instruction.Create(DnOpCodes.Brfalse, elseLabel));
                }
                else if (condKind == 1)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Bgt, elseLabel));
                }
                else if (condKind == 2)
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
                    il.Add(Instruction.Create(DnOpCodes.Xor));
                    il.Add(Instruction.Create(DnOpCodes.Brtrue, elseLabel));
                }
                else
                {
                    il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 16)));
                    il.Add(Instruction.Create(DnOpCodes.Shr));
                    il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                    il.Add(Instruction.Create(DnOpCodes.Beq, elseLabel));
                }

                int thenOps = rng.Next(2, 5);
                for (int t = 0; t < thenOps; t++)
                {
                    EmitRandomALU(il, rng);
                }
                il.Add(Instruction.Create(DnOpCodes.Br, mergeLabel));

                il.Add(elseLabel);
                int elseOps = rng.Next(2, 5);
                for (int e = 0; e < elseOps; e++)
                {
                    EmitRandomALU(il, rng);
                }

                il.Add(mergeLabel);
            }

            var tryStart = Instruction.Create(DnOpCodes.Ldloc_0);
            var handlerStart = Instruction.Create(DnOpCodes.Pop);
            var handlerEnd = Instruction.Create(DnOpCodes.Nop);

            il.Add(tryStart);
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_2));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_2));
            il.Add(Instruction.Create(DnOpCodes.Not));
            il.Add(Instruction.Create(DnOpCodes.Stloc_3));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_3));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Leave, retLabel));

            il.Add(handlerStart);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next()));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Leave, retLabel));
            il.Add(handlerEnd);

            il.Add(retLabel);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            var exHandler = new ExceptionHandler(ExceptionHandlerType.Catch);
            exHandler.TryStart = tryStart;
            exHandler.TryEnd = handlerStart;
            exHandler.HandlerStart = handlerStart;
            exHandler.HandlerEnd = handlerEnd;
            exHandler.CatchType = module.CorLibTypes.GetTypeRef("System", "Exception");
            method.Body.ExceptionHandlers.Add(exHandler);

            return method;
        }

        private void EmitRandomALU(IList<Instruction> il, Random r)
        {
            int op = r.Next(0, 10);
            if (op == 0)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, r.Next()));
                il.Add(Instruction.Create(DnOpCodes.Xor));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            else if (op == 1)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Not));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            else if (op == 2)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, r.Next()));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            else if (op == 3)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, r.Next()));
                il.Add(Instruction.Create(DnOpCodes.Sub));
                il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            }
            else if (op == 4)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, r.Next(1, 16)));
                il.Add(Instruction.Create(DnOpCodes.Shl));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            else if (op == 5)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, r.Next(1, 16)));
                il.Add(Instruction.Create(DnOpCodes.Shr));
                il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            }
            else if (op == 6)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.And));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            else if (op == 7)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.Or));
                il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            }
            else if (op == 8)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.Not));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.And));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, r.Next()));
                il.Add(Instruction.Create(DnOpCodes.Mul));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
        }
    }
}

