using System;
using System.Collections.Generic;
using System.Text;
using dnlib.DotNet;
using dnlib.DotNet.Emit;

using DnFieldAttributes = dnlib.DotNet.FieldAttributes;
using DnMethodAttributes = dnlib.DotNet.MethodAttributes;
using DnMethodImplAttributes = dnlib.DotNet.MethodImplAttributes;
using DnTypeAttributes = dnlib.DotNet.TypeAttributes;
using DnOpCodes = dnlib.DotNet.Emit.OpCodes;

namespace MasonProtector.Core
{
    internal class JunkCodeProtection
    {
        private Obfuscation engine;
        private Random rng;

        private static readonly string[] ClassNames = new string[]
        {
            "BufferManager", "CacheProvider", "ConfigResolver", "DataConverter",
            "EntryValidator", "FormatHelper", "HashProvider", "IndexTracker",
            "JobScheduler", "KeyRegistry", "LayoutManager", "MetricsCollector",
            "NodeFactory", "ObjectPool", "PathResolver", "QueryBuilder",
            "ResourceLoader", "SessionContext", "TokenParser", "UtilityBase",
            "ValidationPipeline", "WorkflowEngine", "AllocTracker", "BatchProcessor",
            "ChunkWriter", "DiagnosticSink", "EventDispatcher", "FrameAssembler",
            "GuidHelper", "HandleRegistry", "InstructionCache", "JournalWriter",
            "KernelContext", "LinkResolver", "MappingProvider", "NormalizationPass",
            "OffsetTable", "PacketBuilder", "QueueProcessor", "RangeChecker",
            "SegmentParser", "TypeResolver", "UriEncoder", "VersionTracker",
            "WindowManager", "AccessTracker", "BindingContext", "ClipboardHelper"
        };

        private static readonly string[] MethodNames = new string[]
        {
            "NormalizeBuffer", "ResolveCacheEntry", "ComputeChecksum", "ValidateRange",
            "FlushPendingItems", "BuildIndexTable", "ParseSegmentHeader", "AllocateSlot",
            "ReleaseHandle", "AcquireLease", "ExpandCapacity", "TrimExcess",
            "ScanForDelimiter", "ExtractToken", "FormatEntry", "SerializePayload",
            "DeserializeHeader", "MapToRegion", "UnmapRegion", "BindContext",
            "DetachContext", "RefreshState", "PropagateChange", "RevertSnapshot",
            "CommitTransaction", "RollbackChanges", "EncodeSegment", "DecodeSegment",
            "CompressBlock", "DecompressBlock", "HashContent", "VerifySignature",
            "LoadConfiguration", "SaveConfiguration", "ReloadPolicy", "ApplyFilter",
            "ClearFilter", "EnumerateKeys", "FindByIndex", "InsertOrUpdate",
            "RemoveExpired", "PurgeCache", "RebuildIndex", "RebalanceTree",
            "RotateBuffer", "ShrinkWindow", "GrowWindow", "MergePartitions",
            "SplitPartition", "WalkGraph", "TraverseNodes", "VisitLeaves",
            "SortEntries", "GroupByKey", "AggregateValues", "ProjectFields"
        };

        private static readonly string[] FieldNames = new string[]
        {
            "_capacity", "_threshold", "_version", "_generation", "_epoch",
            "_segmentSize", "_blockCount", "_entryMask", "_chainLength", "_refCount",
            "_tickStamp", "_sequenceId", "_slotIndex", "_bucketCount", "_loadFactor",
            "_patchLevel", "_checkFlags", "_statusWord", "_errorCode", "_handleBits"
        };

        private static readonly string[] NamespaceSegments = new string[]
        {
            "Internal", "Runtime", "Diagnostics", "Platform", "Core",
            "Utilities", "Helpers", "Infrastructure", "Services", "Primitives",
            "IO", "Collections", "Threading", "Interop", "Security"
        };

        private List<MethodDef> allJunkMethods = new List<MethodDef>();

        private IMethod _stringConcat2;
        private IMethod _stringGetLength;
        private IMethod _mathAbs;
        private IMethod _mathMax;
        private IMethod _mathMin;
        private IMethod _stringIsNullOrEmpty;
        private IMethod _environmentTickCount;

        internal JunkCodeProtection(Obfuscation eng)
        {
            engine = eng;
            rng = eng.rng;
        }

        internal void ApplyJunkCode(ModuleDef module, int count)
        {
            ImportBclMembers(module);

            int classCount = Math.Max(3, count);
            if (classCount > 30) classCount = 30;

            var junkClasses = new List<TypeDef>();
            var guardFields = new List<FieldDef>();

            for (int c = 0; c < classCount; c++)
            {
                string ns = BuildRealisticNamespace();
                string cn = PickName(ClassNames, c);

                var junkClass = new TypeDefUser(ns, cn,
                    module.CorLibTypes.Object.TypeDefOrRef);
                junkClass.Attributes = DnTypeAttributes.NotPublic | DnTypeAttributes.Abstract |
                    DnTypeAttributes.Sealed | DnTypeAttributes.BeforeFieldInit;

                var guardField = new FieldDefUser(
                    PickName(FieldNames, c),
                    new FieldSig(module.CorLibTypes.Int32),
                    DnFieldAttributes.Assembly | DnFieldAttributes.Static);
                junkClass.Fields.Add(guardField);
                guardFields.Add(guardField);

                int extraFields = rng.Next(2, 6);
                for (int f = 0; f < extraFields; f++)
                {
                    TypeSig ft;
                    switch (rng.Next(0, 5))
                    {
                        case 0: ft = module.CorLibTypes.Int32; break;
                        case 1: ft = module.CorLibTypes.String; break;
                        case 2: ft = module.CorLibTypes.Boolean; break;
                        case 3: ft = module.CorLibTypes.Int64; break;
                        default: ft = new SZArraySig(module.CorLibTypes.Byte); break;
                    }
                    junkClass.Fields.Add(new FieldDefUser(
                        PickName(FieldNames, c * 7 + f + 100),
                        new FieldSig(ft),
                        DnFieldAttributes.Assembly | DnFieldAttributes.Static));
                }

                module.Types.Add(junkClass);
                engine.injectedTypes.Add(junkClass);
                junkClasses.Add(junkClass);
            }

            for (int c = 0; c < junkClasses.Count; c++)
            {
                var junkClass = junkClasses[c];
                int methodCount = rng.Next(3, 7);
                for (int m = 0; m < methodCount; m++)
                {
                    var jm = BuildRealisticMethod(module, junkClass, m + c * 10);
                    junkClass.Methods.Add(jm);
                    engine.injectedMethods.Add(jm);
                    allJunkMethods.Add(jm);
                }
            }

            for (int c = 0; c < junkClasses.Count; c++)
            {
                var junkClass = junkClasses[c];
                int crossCount = rng.Next(1, 3);
                for (int x = 0; x < crossCount; x++)
                {
                    int targetClassIdx = rng.Next(0, junkClasses.Count);
                    var targetClass = junkClasses[targetClassIdx];
                    if (targetClass.Methods.Count == 0) continue;
                    var caller = BuildCrossCallMethod(module, junkClass, targetClass, c * 100 + x);
                    if (caller == null) continue;
                    junkClass.Methods.Add(caller);
                    engine.injectedMethods.Add(caller);
                    allJunkMethods.Add(caller);
                }
            }

            InjectOpaqueCalls(module, guardFields);
        }

        private void InjectOpaqueCalls(ModuleDef module, List<FieldDef> guardFields)
        {
            if (allJunkMethods.Count == 0 || guardFields.Count == 0) return;

            var callableJunk = new List<MethodDef>();
            foreach (var jm in allJunkMethods)
            {
                if (jm.MethodSig == null) continue;
                var ret = jm.MethodSig.RetType;
                if (ret == null) continue;
                bool okRet = ret.FullName == "System.Void" || ret.FullName == "System.Int32" ||
                             ret.FullName == "System.Boolean" || ret.FullName == "System.String";
                if (!okRet) continue;
                bool okParams = jm.Parameters.Count == 0 ||
                    (jm.Parameters.Count == 1 && jm.MethodSig.Params[0].FullName == "System.Int32") ||
                    (jm.Parameters.Count == 1 && jm.MethodSig.Params[0].FullName == "System.String");
                if (okParams) callableJunk.Add(jm);
            }
            if (callableJunk.Count == 0) return;

            foreach (TypeDef type in module.GetTypes())
            {
                if (engine.IsCompilerGenerated(type)) continue;
                if (engine.injectedTypes.Contains(type)) continue;
                foreach (MethodDef method in type.Methods)
                {
                    if (!engine.CanProcessMethod(method)) continue;
                    if (method.IsConstructor || method.IsStaticConstructor) continue;
                    if (rng.Next(0, 3) != 0) continue;
                    try
                    {
                        InjectOpaqueGatedCall(module, method, callableJunk, guardFields);
                    }
                    catch { }
                }
            }
        }

        private void InjectOpaqueGatedCall(ModuleDef module, MethodDef method,
            List<MethodDef> callableJunk, List<FieldDef> guardFields)
        {
            if (method.Body == null || !method.Body.HasInstructions) return;
            var il = method.Body.Instructions;
            var safe = engine.FindSafeInsertPositions(il, method.Body.ExceptionHandlers);
            if (safe.Count == 0) return;

            int posIdx = rng.Next(0, safe.Count);
            int pos = safe[posIdx];
            if (pos >= il.Count) return;

            var target = il[pos];
            var junkMethod = callableJunk[rng.Next(0, callableJunk.Count)];
            var guardField = guardFields[rng.Next(0, guardFields.Count)];

            var seq = new List<Instruction>();

            int variant = rng.Next(0, 3);
            switch (variant)
            {
                case 0:
                    seq.Add(Instruction.Create(DnOpCodes.Ldsfld, guardField));
                    seq.Add(Instruction.Create(DnOpCodes.Ldsfld, guardField));
                    seq.Add(Instruction.Create(DnOpCodes.Sub));
                    seq.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                    seq.Add(Instruction.Create(DnOpCodes.Ceq));
                    seq.Add(Instruction.Create(DnOpCodes.Brfalse, target));
                    break;
                case 1:
                    seq.Add(Instruction.Create(DnOpCodes.Ldsfld, guardField));
                    seq.Add(Instruction.Create(DnOpCodes.Ldsfld, guardField));
                    seq.Add(Instruction.Create(DnOpCodes.Xor));
                    seq.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                    seq.Add(Instruction.Create(DnOpCodes.Ceq));
                    seq.Add(Instruction.Create(DnOpCodes.Brfalse, target));
                    break;
                default:
                    seq.Add(Instruction.Create(DnOpCodes.Ldsfld, guardField));
                    seq.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                    seq.Add(Instruction.Create(DnOpCodes.Clt));
                    seq.Add(Instruction.Create(DnOpCodes.Brfalse, target));
                    break;
            }

            bool needsArg = junkMethod.Parameters.Count == 1;
            bool argIsInt = needsArg && junkMethod.MethodSig != null &&
                            junkMethod.MethodSig.Params[0].FullName == "System.Int32";

            if (needsArg)
            {
                if (argIsInt)
                    seq.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 1000)));
                else
                    seq.Add(Instruction.Create(DnOpCodes.Ldstr, ""));
            }

            seq.Add(Instruction.Create(DnOpCodes.Call, junkMethod));

            var retType = junkMethod.MethodSig != null ? junkMethod.MethodSig.RetType : null;
            if (retType != null && retType.FullName != "System.Void")
                seq.Add(Instruction.Create(DnOpCodes.Pop));

            for (int i = seq.Count - 1; i >= 0; i--)
                il.Insert(pos, seq[i]);
        }

        private MethodDef BuildRealisticMethod(ModuleDef module, TypeDef owner, int seed)
        {
            int pattern = seed % 8;
            switch (pattern)
            {
                case 0: return BuildStringProcessingMethod(module, owner, seed);
                case 1: return BuildArithmeticAccumulatorMethod(module, owner, seed);
                case 2: return BuildRangeClampMethod(module, owner, seed);
                case 3: return BuildRangeValidationMethod(module, owner, seed);
                case 4: return BuildNormalizationMethod(module, owner, seed);
                case 5: return BuildFlagCheckMethod(module, owner, seed);
                case 6: return BuildChecksumMethod(module, owner, seed);
                default: return BuildFormatHelperMethod(module, owner, seed);
            }
        }

        private MethodDef BuildStringProcessingMethod(ModuleDef module, TypeDef owner, int seed)
        {
            string name = PickName(MethodNames, seed);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.String,
                module.CorLibTypes.String);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.String));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

            var il = method.Body.Instructions;

            il.Add(Instruction.Create(DnOpCodes.Ldstr, ""));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            if (_stringGetLength != null && _mathAbs != null)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Call, _stringGetLength));
                il.Add(Instruction.Create(DnOpCodes.Stloc_1));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rng.Next(1, 5)));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Call, _mathAbs));
                il.Add(Instruction.Create(DnOpCodes.Pop));
            }

            if (_stringConcat2 != null)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Ldstr, ""));
                il.Add(Instruction.Create(DnOpCodes.Call, _stringConcat2));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildArithmeticAccumulatorMethod(ModuleDef module, TypeDef owner, int seed)
        {
            string name = PickName(MethodNames, seed + 1);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.Int32,
                module.CorLibTypes.Int32);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

            var il = method.Body.Instructions;

            int initVal = rng.Next(1, 100);
            int step = rng.Next(1, 16);
            int loopCount = rng.Next(3, 8);

            var loopBody = Instruction.Create(DnOpCodes.Ldloc_0);
            var loopCheck = Instruction.Create(DnOpCodes.Ldloc_1);

            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, initVal));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Br, loopCheck));

            il.Add(loopBody);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, step));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(loopCheck);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, loopCount));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            if (_mathAbs != null)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Call, _mathAbs));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildRangeClampMethod(ModuleDef module, TypeDef owner, int seed)
        {
            string name = PickName(MethodNames, seed + 2);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.Int32,
                module.CorLibTypes.Int32);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

            var il = method.Body.Instructions;

            int threshold = rng.Next(2, 20);
            int multiplier = rng.Next(1, 8);

            if (_mathMax != null && _mathMin != null)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
                il.Add(Instruction.Create(DnOpCodes.Call, _mathMax));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, threshold));
                il.Add(Instruction.Create(DnOpCodes.Call, _mathMin));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, threshold));
                il.Add(Instruction.Create(DnOpCodes.Add));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, multiplier));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildRangeValidationMethod(ModuleDef module, TypeDef owner, int seed)
        {
            string name = PickName(MethodNames, seed + 3);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.Boolean,
                module.CorLibTypes.Int32);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

            var il = method.Body.Instructions;

            int lo = rng.Next(1, 50);
            int hi = lo + rng.Next(10, 200);

            var retFalse = Instruction.Create(DnOpCodes.Ldc_I4_0);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, lo));
            il.Add(Instruction.Create(DnOpCodes.Clt));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, retFalse));

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, hi));
            il.Add(Instruction.Create(DnOpCodes.Cgt));
            il.Add(Instruction.Create(DnOpCodes.Brtrue, retFalse));

            int divisor = rng.Next(2, 16);
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, divisor));
            il.Add(Instruction.Create(DnOpCodes.Rem));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Ceq));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            il.Add(retFalse);
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildNormalizationMethod(ModuleDef module, TypeDef owner, int seed)
        {
            string name = PickName(MethodNames, seed + 4);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.Int32,
                module.CorLibTypes.Int32);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

            var il = method.Body.Instructions;

            int factor = rng.Next(2, 64);
            int bias = rng.Next(0, 32);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, factor));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, factor));
            il.Add(Instruction.Create(DnOpCodes.Rem));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, bias));
            il.Add(Instruction.Create(DnOpCodes.Or));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            if (_mathMax != null)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
                il.Add(Instruction.Create(DnOpCodes.Call, _mathMax));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ret));
            }

            return method;
        }

        private MethodDef BuildFlagCheckMethod(ModuleDef module, TypeDef owner, int seed)
        {
            string name = PickName(MethodNames, seed + 5);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.Boolean);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

            var il = method.Body.Instructions;

            int mask = rng.Next(1, 255);

            if (_environmentTickCount != null)
            {
                il.Add(Instruction.Create(DnOpCodes.Call, _environmentTickCount));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, mask));
                il.Add(Instruction.Create(DnOpCodes.And));
                il.Add(Instruction.Create(DnOpCodes.Stloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, -1));
                il.Add(Instruction.Create(DnOpCodes.Cgt));
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, mask));
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4, mask));
                il.Add(Instruction.Create(DnOpCodes.Ceq));
            }
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildChecksumMethod(ModuleDef module, TypeDef owner, int seed)
        {
            string name = PickName(MethodNames, seed + 6);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.Int32,
                module.CorLibTypes.Int32);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

            var il = method.Body.Instructions;

            int prime = PickPrime(seed);
            int rounds = rng.Next(2, 5);

            var loopBody = Instruction.Create(DnOpCodes.Ldloc_0);
            var loopCheck = Instruction.Create(DnOpCodes.Ldloc_1);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, prime));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_0));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            il.Add(Instruction.Create(DnOpCodes.Br, loopCheck));

            il.Add(loopBody);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, prime));
            il.Add(Instruction.Create(DnOpCodes.Mul));
            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Xor));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_1));

            il.Add(loopCheck);
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, rounds));
            il.Add(Instruction.Create(DnOpCodes.Blt, loopBody));

            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildFormatHelperMethod(ModuleDef module, TypeDef owner, int seed)
        {
            string name = PickName(MethodNames, seed + 7);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.String,
                module.CorLibTypes.Int32);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));
            method.Body.Variables.Add(new Local(module.CorLibTypes.String));

            var il = method.Body.Instructions;

            int scale = rng.Next(1, 100);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, scale));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));

            if (_stringConcat2 != null)
            {
                il.Add(Instruction.Create(DnOpCodes.Ldstr, "entry-"));
                il.Add(Instruction.Create(DnOpCodes.Ldstr, "0"));
                il.Add(Instruction.Create(DnOpCodes.Call, _stringConcat2));
                il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            }
            else
            {
                il.Add(Instruction.Create(DnOpCodes.Ldstr, "entry-0"));
                il.Add(Instruction.Create(DnOpCodes.Stloc_1));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldloc_1));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef BuildCrossCallMethod(ModuleDef module, TypeDef caller,
            TypeDef target, int seed)
        {
            MethodDef targetMethod = null;
            foreach (var m in target.Methods)
            {
                if (!engine.injectedMethods.Contains(m)) continue;
                if (m.MethodSig == null) continue;
                var ret = m.MethodSig.RetType;
                if (ret == null) continue;
                if ((ret.FullName == "System.Int32" || ret.FullName == "System.Boolean") &&
                    m.Parameters.Count == 1 &&
                    m.MethodSig.Params[0].FullName == "System.Int32")
                {
                    targetMethod = m;
                    break;
                }
            }

            if (targetMethod == null) return null;

            string name = PickName(MethodNames, seed + 200);
            var method = CreateStaticMethod(module, name, module.CorLibTypes.Int32,
                module.CorLibTypes.Int32);

            method.Body = new CilBody();
            method.Body.InitLocals = true;
            method.Body.Variables.Add(new Local(module.CorLibTypes.Int32));

            var il = method.Body.Instructions;
            int multiplier = rng.Next(1, 8);

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Ldc_I4, multiplier));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Call, targetMethod));

            var retType = targetMethod.MethodSig.RetType;
            if (retType.FullName == "System.Boolean")
            {
                il.Add(Instruction.Create(DnOpCodes.Ldc_I4_1));
                il.Add(Instruction.Create(DnOpCodes.And));
            }

            il.Add(Instruction.Create(DnOpCodes.Ldarg_0));
            il.Add(Instruction.Create(DnOpCodes.Add));
            il.Add(Instruction.Create(DnOpCodes.Stloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ldloc_0));
            il.Add(Instruction.Create(DnOpCodes.Ret));

            return method;
        }

        private MethodDef CreateStaticMethod(ModuleDef module, string name,
            TypeSig retType, params TypeSig[] paramTypes)
        {
            return new MethodDefUser(name,
                MethodSig.CreateStatic(retType, paramTypes),
                DnMethodImplAttributes.IL | DnMethodImplAttributes.Managed,
                DnMethodAttributes.Assembly | DnMethodAttributes.Static | DnMethodAttributes.HideBySig);
        }

        private string BuildRealisticNamespace()
        {
            int segs = rng.Next(1, 3);
            var sb = new StringBuilder();
            for (int i = 0; i < segs; i++)
            {
                if (i > 0) sb.Append('.');
                sb.Append(NamespaceSegments[rng.Next(0, NamespaceSegments.Length)]);
            }
            return sb.ToString();
        }

        private string PickName(string[] pool, int seed)
        {
            int idx = ((seed % pool.Length) + pool.Length) % pool.Length;
            return pool[idx];
        }

        private int PickPrime(int seed)
        {
            int[] primes = new int[] { 17, 31, 37, 53, 61, 67, 79, 97, 101, 113, 127, 131 };
            return primes[((seed % primes.Length) + primes.Length) % primes.Length];
        }

        private void ImportBclMembers(ModuleDef module)
        {
            try
            {
                _stringConcat2 = module.Import(
                    typeof(string).GetMethod("Concat", new[] { typeof(string), typeof(string) }));
            }
            catch { }
            try
            {
                _stringGetLength = module.Import(
                    typeof(string).GetProperty("Length").GetGetMethod());
            }
            catch { }
            try
            {
                _mathAbs = module.Import(
                    typeof(System.Math).GetMethod("Abs", new[] { typeof(int) }));
            }
            catch { }
            try
            {
                _mathMax = module.Import(
                    typeof(System.Math).GetMethod("Max", new[] { typeof(int), typeof(int) }));
            }
            catch { }
            try
            {
                _mathMin = module.Import(
                    typeof(System.Math).GetMethod("Min", new[] { typeof(int), typeof(int) }));
            }
            catch { }
            try
            {
                _stringIsNullOrEmpty = module.Import(
                    typeof(string).GetMethod("IsNullOrEmpty", new[] { typeof(string) }));
            }
            catch { }
            try
            {
                _environmentTickCount = module.Import(
                    typeof(System.Environment).GetProperty("TickCount").GetGetMethod());
            }
            catch { }
        }
    }
}
