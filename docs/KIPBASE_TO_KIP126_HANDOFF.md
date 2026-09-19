# KIPBase → KIP126 迁移交接说明

本文件用于新 session 继续完成 KIPBase 到 KIP126 的完整迁移。新 session 应先阅读本文件，再执行仓库级检查。

## 1. 工作目录与只读目录

主工作目录：

```text
/inspire/hdd/global_user/czxs25250150/KIP126-layout-work
```

相邻目录：

```text
/inspire/hdd/global_user/czxs25250150/KIP126
```

相邻目录由守护进程管理，必须保持只读，禁止在其中修改、切换分支或提交。

## 2. 分支和交接状态

目标分支：

```text
feat/def-challenge-layout
```

交接时已知状态（新 session 必须重新核对）：

- 工作区干净；
- 最近核验的代码头：`1810679890a57537e1d3b5b1ac30e74faa64e287`；纯文档提交后以
  `git rev-parse HEAD` 为准；
- `origin/main`：`dc4a7d1b50d50f3c535acb6b46eb5c5aadbfc964`；
- 本分支已包含 `origin/main`；
- PR #97：<https://github.com/SII-MATH/KIP126/pull/97>；
- 最近的比较和讨论没有产生额外代码修改。

当前 session 已重新核对的状态（2026-09-19）：

- 工作区干净；当前实现提交：`9267418`（canonical page lift 的 boundary-factorization 定理、页面同调
  epi--mono 分解接口、直接 PageView 入口、回归检查及状态记录）；此前的
  `pageDifferential_Z_succ_le`、`pageDifferential_B_succ`、`pageComplex` 和条件谱序列装配提交均已保留；
- `origin/main`：`dc4a7d1b50d50f3c535acb6b46eb5c5aadbfc964`；本分支相对
  `origin/main` 无落后提交；
- 已补入 canonical `pageObj` 的零页等价律（含 `pageObj_isZero_iff`）、嵌套商映射/第三同构辅助构造，
  稳定三角形中项同调群的 exactness，有限页 `Z_succ` 的容易方向，以及两个通用核/上像引理；这些改动均未引入
  `KIPBase` import；
- 本地 `scripts/shared-main-cache.sh run lake build KIP126` 曾通过（1906/1906）；当前增量的
  `FilteredPage.Complex`、`FilteredPage` 和 `FilteredComplexRelations` 检查均通过，
  `scripts/Axioms.lean` 通过（4763 个 KIP126 声明，仅允许
  `propext`、`Classical.choice`、`Quot.sound`），源码清单通过（18 sources, 88 artifacts）；
- 反向 `Z_{n+1}` 包含已接入生产 `FilteredDifferential/Proofs.lean`，并在
  `Checks/SpectralSequence/FilteredDifferential.lean` 增加回归检查；有限页 `Z_succ` 两个方向和
  `B_succ` 均已接入生产证明，完整 Mathlib assembly 和四个关系义务仍开放；
- 在本次 session 后，canonical finite quotient page 已有 Mathlib
  `HomologicalComplex` 适配（`pageComplex`），并新增显式的
  `PageHomologyWitness` → Mathlib `SpectralSequence` 条件装配器；同时加入
  `PageHomologyFactorization`，把每个页面的同调比较精确化为 Mathlib
  `ofEpiMonoFactorisation` 所需的 epi--mono 分解，并提供
  `PageHomologyWitness.ofFactorization` 的打包构造；已有的
  `PageHomologyWitness.toFactorization` 也可反向暴露同一分解。具体分解的数学证明仍未完成。
  `PageView.ofPageHomologyWitness` 与
  `PageView.ofPageHomologyFactorization` 已把该装配器接入四个关系命题的
  canonical 页面入口。相邻页同调同构 witness 本身仍是开放证明义务，没有把它当作无条件的
  `toSpectralSequence` 结论。另已证明 `PageView.isLift_sub_factors_boundary`：同一
  page 元素的两个 lift 之差经 canonical `boundarySubobject` 因子化；这替代了旧
  associated-graded lift 唯一性在 page quotient 语义下不成立的版本。
- 迁移校验器仍因归档文件中既有的
  `KIPBase/SpectralSequence/BoundedExtension.lean` trust-debt 漂移而拒绝刷新归档；
  PR #97 的自动构建门禁还报告历史大分支的范围/新增 `set_option` 策略问题，需拆分
  PR 或由人工审核处理。
- PR #97 当前远端头为 `1810679`，状态为 `BLOCKED`：Blueprint 门禁报告相对
  `origin/main` 的 diff 超过 2000 行/文件审查上限；sandboxed-build 门禁报告分支历史相对
  `origin/main` 新增 `set_option`，并将 `scope` 标为需人工审核。这与本地缓存构建和 Axiom
  审计的通过结果是两个独立门。

## 3. 开始工作前的安全步骤

必须先阅读：

- `/inspire/hdd/global_user/czxs25250150/AGENTS.md`；
- `docs/DEF_CHALLENGE_LAYOUT_SPEC.md`；
- `README.md`；
- `PROJECT_BOUNDARY.md`；
- `docs/ROADMAP.md`；
- 相关 Blueprint 节点；
- 现有 Lean import 图。

然后执行：

```bash
git fetch --prune origin
git status --short --branch
git branch --show-current
git rev-parse HEAD
git rev-parse origin/main
git rev-list --left-right --count origin/main...HEAD
```

安全合并最新 `main`：

- 保留已有提交；
- 不执行 `git reset`；
- 不强推；
- 不覆盖未提交工作；
- 如果发现未提交工作，先保护并分析，禁止删除。

## 4. 已确认的总体原则

### 4.1 唯一权威定义

KIP126 是新布局和主接口的权威来源。KIPBase 只有在提供独有且有价值的数学内容时才迁移。

迁移后的仓库不得长期维护两套同义权威定义。

### 4.2 定义与证明的选择

- 定义优先采用 KIP126；
- KIPBase 中已完成且语义匹配的证明，适配到 KIP126 类型；
- KIP126 已有等价定义或证明时，不再复制同义声明；
- 不能只按 axiom/sorry 数量决定保留哪个版本，要同时考虑数学语义、接口稳定性、依赖关系和可复用性。

### 4.3 Filtration

- 采用 KIP126 的 Filtration 定义；
- 吸收 KIPBase 中有价值且可迁移的泛化引理和证明；
- 清理同义的第二套过滤定义。

### 4.4 Convergence

- 采用 KIP126 的 `PageAbutmentComparisonWitness` 和 `StrongConvergenceWitness`；
- 吸收 KIPBase 的 `detect_zero`、`detect_difference` 以及完备性/穷尽性相关证明；
- 当前不迁移整个旧 `ConvergenceMorphism` 范畴；
- 不把旧的弱收敛接口当作已完成证明；
- 旧模型中隐含的 `E∞` 必须改为 KIP126 的显式页面和端点比较接口。

### 4.5 FilteredComplex

采用 KIP126 基于 Mathlib `ChainComplex` 的 `FilteredComplex` 作为唯一底层定义。

吸收 KIPBase 中已完成的页面数学，并适配到 KIP126 类型：

- `homologyObj`；
- `homologyFiltration`；
- `cycleSubobject`；
- `boundarySubobject`；
- `B_le_Z_aux`；
- `toSSData`；
- `pageDifferential`；
- `toPreSS`；
- `toSpectralSequence`。

以下四个 KIPBase 定理仍然是开放目标，不能作为现成证明迁移：

- `differentialRelation_of_lift`；
- `lift_of_differentialRelation`；
- `differentialRelation_crossed_of_two`；
- `lift_rel_of_not_crossed`。

它们只能写入 Challenge 的 `Statement.lean`，真实证明完成后才能增加 `Proof.lean`。

旧 `weakConvergence` 中标注未完成的收敛同构，也不能作为证明来源。

## 5. 迁移目标

完整落实：

```text
docs/DEF_CHALLENGE_LAYOUT_SPEC.md
```

### 5.1 Def

按数学依赖顺序整理到：

```text
KIP126/Def/<数学模块>/<概念>/
```

约定：

- 候选数据放 `Data.lean`；
- 独立性质的 Prop 放 `Predicates.lean`；
- 已完成证明放 `Proofs.lean`；
- 一个文件只承担一个主要概念；
- 类型构造必需的结构律可以留在构造链中；
- 不机械拆分每个辅助引理；
- 尽量保留现有公开声明名和数学陈述。

### 5.2 Challenge

建立并完成必要的：

```text
KIP126/Challenge/Tools
KIP126/Challenge/Near126
KIP126/Challenge/Final
KIP126/Challenge/Geometry
```

要求：

- 节点对应 spec 中的依赖图和 milestone；
- 开放节点有可编译、精确的 `Statement.lean`；
- 只有真实证明完成后才增加 `Proof.lean`；
- 禁止 `sorry`；
- 禁止新增项目 axiom；
- 禁止任意选取对象、弱化命题或占位证明；
- Blueprint 中“目标命题可编译”不能标记为证明完成。

### 5.3 External

- 文献和计算输入继续放在 `External/`；
- 通过显式 `ExternalResult` / `ExternalEvidence` 进入证明；
- 区分外部 BJM/BX 原始判据和项目内部关于 Theorem 7.3 的选择无关性推导；
- 不把外部事实伪装成内部 Lean 定理。

### 5.4 KIPBase 隔离

- KIP126 生产代码不得直接 import KIPBase；
- 兼容层只能作为迁移辅助；
- 所有消费者迁移后清理临时兼容入口；
- 不留下两套权威定义。

## 6. 工作方法

1. 先完成仓库级 inventory：
   - KIPBase 的所有声明；
   - KIP126 的现有声明；
   - 同名、等价和独有声明；
   - axiom、sorry、递归公理依赖；
   - imports 和 Blueprint `\lean` / `\uses` 映射。
2. 如果使用并行 agent，按互不重叠的数学区域分工，例如过滤、复形与页面、收敛、Geometry、External、Blueprint/回归检查。
3. 主 agent 统一处理共享入口、公共 imports、声明冲突、兼容层清理、Blueprint 映射和最终集成。
4. 不停在目录骨架或试点切片；先完成一个过滤对象和一个 Challenge 的端到端链路，再继续其余迁移。
5. 每批修改建立可审查的独立提交。

## 7. Lean 与 Blueprint 检查

- 使用仓库规定的缓存包装器；
- 运行最窄的 Lean 检查；
- 不要在新检出中直接冷启动 `lake build`；
- 只在实际变更需要时运行 Blueprint 生成和声明检查；
- 最终核对：
  - import DAG；
  - 所有已移动声明；
  - Blueprint `\lean` / `\uses`；
  - README 和 Roadmap；
  - 回归检查；
  - `scripts/Axioms.lean`；
  - 主库没有新增项目 axiom 或 sorryAx；
  - 尚未证明的主目标仍保持开放。

## 8. Git 与 PR 交付

- 继续使用 `feat/def-challenge-layout`；
- 不修改相邻只读检出；
- 不 reset；
- 不强推；
- 保留已有提交；
- 将独立完成的提交推送到 `origin/feat/def-challenge-layout`；
- 仓库要求通过 PR 交付；
- 如果 GitHub CLI 认证无效，先完成并推送所有可独立完成的工作，最后报告具体认证阻碍。

## 9. 最终报告

最终报告必须列出：

1. 旧模块到新模块的完整映射；
2. KIPBase 独有内容的处理方式；
3. 尚未完成的数学证明义务；
4. 运行过的检查及结果；
5. `scripts/Axioms.lean` 结果；
6. 提交 SHA；
7. 分支和远端状态；
8. PR 状态；
9. 仍然存在的认证、CI 或外部依赖阻碍。

新 session 不要重复询问本文件已经确认的设计选择。只有仓库内容和本文件无法解决的真实冲突才暂停询问。
