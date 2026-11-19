# 36 题迁移说明

来源：[QudeLeap/Lean-QuantumAlg-Bench](https://github.com/QudeLeap/Lean-QuantumAlg-Bench)，
commit `b540e86938ea82a546cfa55bed766adc894c2400`。36 个原 Statement 文件对应 36 个本地任务、44 个证明目标。
原题及定义的 SHA-256、目标数量与本地状态见 `bench/migration.json`。
原定义的 Apache-2.0 署名保留；Goals 文件是原题声明的类型翻译。未读取模型评测答案用于迁移。

## 转换方式

- 不引入 Lean-QuantumAlg、QAlgBench 或 cslib 依赖，也不复制其 Register/Gate/Circuit 基础库。
- 原有限寄存器变为 Mathlib 的有限索引类型，纯态向量变为 EuclideanSpace。
- `Matrix (Fin d) (Fin d) ℂ` 使用本库 `Operator d`；输入酉门使用现有 `GoogleQHL.Unitary d`。
- 已知 H、X、Y、Z、RY、CNOT、受控矩阵与张量积以矩阵直接定义，保留 big-endian 张量次序。
- 原门结构之间的相等目标写成底层矩阵相等；原归一化纯态参数展开为向量与显式 norm=1 假设。
- 置换 oracle 直接定义成置换矩阵，酉性仍是需要提交的证明目标。
- 原题的参数、前提、结论和一题多目标组织均保留，不增加“结论已成立”的假设来简化目标。
- `Foundation.certifiedUnitary` / `certifiedProgram` 将酉矩阵证书接到真实 QHL `apply` 构造子。
  纯代数/渐近分析题属于数学支撑层，不伪装成量子程序或资源优化题。

这是规格迁移，不是 36 个完整算法实现或 Google 官方题集。
没有建立旧版工程与新版工程之间逐题机械等价证明；类型翻译及显式矩阵定义接受源码审查。

## 原题限制

两道原题把“共轭转置等于自身且 trace=1”命名为 IsDensityOperator，却未包含 PSD。
这里保留原来的数学前提并改名 IsHermitianTraceOne；没有擅自增加 PSD，也不把它当作本库的 PartialDensity。
部分 Hamiltonian/QSP/训练性命题本来就以局部误差、谱展开或矩条件为假设，迁移没有证明这些前提。
目标规格通过类型检查，不代表命题必真或已有完整参考证明。

## 验收与计分

每题提交一个证明字符串数组，按该题目标顺序排列。44 个目标不能拆成 44 道题改变分母。
同一题所有证明通过 Lean 和传递公理审计才计为 accepted；缺证明、错误证明或额外公理均不能通过。
正式题集分母固定 36；12 题 calibration 仅作评测器自测，不能混入正式分数。
参考自测只覆盖 `bench/references.jsonl` 中列出的题，不称为全套 gold solutions。

| 序号 | 原题/本地 task_id | 类别 | 目标数 |
| --- | --- | --- | --- |
| 1 | BitOracleUnitaryHermitian | Circuits | 2 |
| 2 | ControlledPhaseFromCNOTHadamards | Circuits | 1 |
| 3 | ControlledRYTwoCNOTSynthesis | Circuits | 1 |
| 4 | ControlledUnitaryInvariantSubspaces | Circuits | 1 |
| 5 | ExactQROMFactorization | Circuits | 4 |
| 6 | HadamardTensorHadamardMatrix | Circuits | 2 |
| 7 | PhaseKickbackControlledEigenunitary | Circuits | 1 |
| 8 | VanishingPauliYExpectationRealCircuits | Circuits | 2 |
| 9 | WalshHadamardBooleanCharacter | Circuits | 1 |
| 10 | EigenvectorsModularMultiplicationShor | Fourier | 1 |
| 11 | FiniteQFTUnitarity | Fourier | 1 |
| 12 | ProductStateFactorizationQFT8Ket3 | Fourier | 1 |
| 13 | QPESuperpositionExactEigenvectors | Fourier | 1 |
| 14 | FidelityBoundHiddenSubgroupCosetStates | HSPRepresentation | 1 |
| 15 | RankStrongFourierSamplingConditionalState | HSPRepresentation | 1 |
| 16 | WeakFourierSamplingTranspositionSn | HSPRepresentation | 1 |
| 17 | AccumulationProductFormulaErrorsManySmallTerms | HamiltonianSimulation | 1 |
| 18 | FirstOrderLieTrotterGlobalErrorScaling | HamiltonianSimulation | 1 |
| 19 | LeadingCommutatorTermTwoTermExponentialProduct | HamiltonianSimulation | 1 |
| 20 | CoefficientOneNormTruncatedTaylorSimulation | LCUBlockQSVT | 1 |
| 21 | LCUBlockEncodingPrepareSelect | LCUBlockQSVT | 2 |
| 22 | CommonStabilizerFullRankStates | LinearAlgebra | 1 |
| 23 | FidelityHammingWeightTruncatedPhaseState | LinearAlgebra | 2 |
| 24 | HilbertSchmidtTranspositionInvariance | LinearAlgebra | 1 |
| 25 | LinearDependenceRvsFtwo | LinearAlgebra | 1 |
| 26 | LocalMarginalUnreadProjectiveMeasurement | LinearAlgebra | 1 |
| 27 | OrthonormalityCoherentMarkovChainRows | LinearAlgebra | 1 |
| 28 | PostMeasurementStateObservedQubit | LinearAlgebra | 1 |
| 29 | SpectralProjectorsBooleanPhaseOracle | LinearAlgebra | 1 |
| 30 | UnitaryExtensionMarkovChainIsometry | LinearAlgebra | 1 |
| 31 | WeylAverageShiftOperator | LinearAlgebra | 1 |
| 32 | ApproximateTwoDesignDepthHaarLossFluctuations | PQCLieTrainability | 1 |
| 33 | ParityMaximumFejerKernelQSPResponse | QSPParameterTrace | 1 |
| 34 | PostselectedSpectralTransformationTrigonometricQSP | QSPParameterTrace | 1 |
| 35 | SharedParameterShiftRuleRXTensorRZ | QSPParameterTrace | 1 |
| 36 | ThirdMomentTwoControlledSWAPTests | QSPParameterTrace | 1 |
