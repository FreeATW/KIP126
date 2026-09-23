# 谱序列模块当前状态

本文件只记录继续开发所需的当前结论，不保存讨论过程或已放弃的架构。
实现事实以 `KIP126/` 下的 Lean 源码为准；本文件在实现变化时直接更新，不创建并行版本。

## 已确定的结构

- Mathlib 的 `CategoryTheory.SpectralSequence` 是唯一的通用谱序列类型。
- KIP126 的具体计算仍从 `FilteredComplex` 的代表元模型出发；`Z_r`、`B_r`、
  `pageObj = Z_r/B_r` 和 `pageDifferential` 不是从任意 Mathlib 谱序列反向恢复的附加数据。
- canonical 页面直接装配成 Mathlib 谱序列，不再经过
  `PageHomologyWitness`、`PageHomologyFactorization` 或另一套 presentation 包装。
- 有限页、`E_∞` 的代数对象以及向 abutment 的收敛比较是三个不同层次，不能混为一体。

## 已完成的有限页主链

当前代码已经实现以下依赖链：

```text
FilteredComplex
  -> cycleSubobject / boundarySubobject
  -> pageObj = Z_r / B_r
  -> pageDifferential
  -> pageComplex（含 d_r² = 0）
  -> 相邻页的 kernel / image 计算
  -> pageHomologyIso : H(E_r) ≅ E_(r+1)
  -> canonicalPageSpectralSequence
  -> PageTrajectory / IsPermanent（元素级逐页存活）
```

关键装配位于：

- `KIP126/Def/SpectralSequence/PageDifferential/`：通用页微分关系和 crossing；
- `KIP126/Def/SpectralSequence/Permanence/Data.lean`：逐页后继类和永久循环；
- `KIP126/Def/SpectralSequence/FilteredPage/Complex.lean`
- `KIP126/Def/SpectralSequence/FilteredPage/AssemblyProofs.lean`
- `KIP126/Def/SpectralSequence/FilteredComplex/Relations/Data.lean`

因此 canonical 谱序列的页面和微分仍可通过 KIP126 的 `Z_r/B_r` 模型计算，
同时它本身可以使用只依赖 Mathlib `SpectralSequence` 接口的通用结果。

## 尚未完成的工作

按建议的先后顺序：

1. 完成任意有限页的代表元、lift 和 crossing 关系；目前四个关系定理仍是占位证明。
2. 建立 canonical 页面关于 filtered-complex morphism 的函子性，并产生相应的
   Mathlib 谱序列态射。
3. 明确并实现 canonical 页号/双分次与 Adams 常用约定之间的 reindex。
4. 比较两条已有构造路径：直接的 `Z_r/B_r` 页面与 spectral-object 产生的谱序列。
5. 建立有限页稳定、permanent cycle、`pageObj ... ⊤` 与 `E_∞` 的接口。
6. 在上述基础上重做收敛层，使页面比较、稳定性及 abutment coherence 都成为显式数据或定理。
7. 最后补充少量 canonical sequence 的暴露和 `simp` 引理，降低下游使用成本。

## 当前明确的证明缺口

`KIP126/Def/SpectralSequence` 中有五个实际的 `sorry`：

- `FilteredComplex/Relations/Proofs.lean`
  - `differentialRelationOfLift`
  - `liftOfDifferentialRelation`
  - `differentialRelationCrossedOfTwo`
  - `liftRelOfNotCrossed`
- `Convergence/Proofs.lean`
  - `strongConvergenceFromComparison`

前四项属于有限页代表元关系。第五项不应直接按现有陈述填证明：
`PageAbutmentComparisonWitness` 目前只给逐点、逐页的比较，而结论要求后续页面稳定、
页面间 coherence 和统一的 `E_∞` 数据。继续收敛工作前，应先加强假设，或者删除这个
自动构造定理，改为显式要求 `StrongConvergenceWitness`。

## 下次继续时

优先从四个有限页关系定理开始；这一步最直接承接 KIPBase 基于 `SSData` 的证明，
也会检验当前 `PageView` 和代表元接口是否足够。不要重新引入 witness 装配层，
也不要另建一套 `Z_r`、`B_r`、页面或谱序列定义。
