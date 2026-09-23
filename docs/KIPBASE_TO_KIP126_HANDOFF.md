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

本文件描述迁移工作的约束，不把历史分支、提交号或本地检查结果作为当前验收证据。
开始工作时按 AGENTS.md fetch 并核对实际分支、最新 origin/main、PR base/head 和
该 head 的检查结果；不要根据旧交接记录切换分支或宣称 CI 已通过。

当前目录映射和未完成分层见 `docs/DEF_CHALLENGE_LAYOUT_STATUS.md`；
有限页构造和剩余数学缺口见 `docs/SPECTRAL_SEQUENCE_STATUS.md`。
当前源码已直接构造 `pageHomologyIso`、`canonicalPageSpectralSequence`
和 `PageView.canonical`，不再要求额外的 page-homology witness/factorization 输入。
四个代表元关系定理仍未完成；有限页装配不等于收敛或论文主定理已经完成。

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
- `pageDifferential`；
- `pageComplex`；
- `pageHomologyIso`；
- `canonicalPageSpectralSequence`。

旧 `SSData` / `PreSS` 及其装配函数只作迁移参考，不重新引入平行谱序列模型。

以下四个 KIPBase 定理仍然是开放目标，不能作为现成证明迁移：

- `differentialRelation_of_lift`；
- `lift_of_differentialRelation`；
- `differentialRelation_crossed_of_two`；
- `lift_rel_of_not_crossed`。

它们是内部支持定理，位于 `Def/SpectralSequence/FilteredComplex/Relations/Proofs.lean`；
开发期间可用 `by sorry`，完成前不能作为已证结论或 Blueprint 完成证据。

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
- 定理和证明放 `Proofs.lean`，开发中的未完成证明可显式使用 `by sorry`；
- 一个文件只承担一个主要概念；
- Data 中不放命名引理；构造需要的性质先在下层 Proofs 证明，再由后续 Data 使用；
- 辅助证明仍遵守分层，不为满足目录形式创建空层；
- 尽量保留现有公开声明名和数学陈述。

### 5.2 Challenge

建立并完成必要的：

```text
KIP126/Challenge/Tools
KIP126/Challenge/Near126
KIP126/Challenge/Final
KIP126/Solution/Tools
KIP126/Solution/Near126
KIP126/Solution/Final
```

要求：

- 节点对应 spec 中的依赖图和 milestone；
- 使用 `<category>/<semantic_name>.lean`，不再采用 `Statement.lean` / `Proof.lean` 布局；
- Challenge 与 Solution 的相对路径和完整定理签名同步；
- Challenge 定理始终保留 `by sorry`；证明只写在 Solution，开发中的 Solution 可暂用 `by sorry`；
- Solution 及其证明依赖不得调用 Challenge 占位声明；
- 禁止新增项目 axiom；
- 禁止任意选取对象、弱化命题或把占位证明当作完成证据；
- Blueprint 中“目标命题可编译”不能标记为证明完成。

几何终点的 Challenge/Solution 声明推迟到 permanent-cycle 主链就绪后加入，
项目的几何目标不变。

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
  - 规范库没有项目 axiom；已完成的 Solution/Def 证明及其依赖不含 sorryAx，
    Challenge 占位与开发中证明分别记录，不能冒充完成证据；
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
