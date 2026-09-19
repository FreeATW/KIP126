# KIP126 Roadmap

本 Roadmap 回答 KIP126 如何从既有形式化成果出发，形成可持续推进的代码基线，
完成论文形式化，并通过最终审计。数学声明、`\label`、`\lean`、`\uses` 与节点状态以
[`../blueprint/src/content.tex`](../blueprint/src/content.tex) 及其章节为准；已实现接口和
import graph 以 `KIP126/**/*.lean` 为准；项目范围、信任边界与最终验收边界以
[`../PROJECT_BOUNDARY.md`](../PROJECT_BOUNDARY.md) 为准。实时进度镜像维护在 Multica
的 AIM-179 主 Wiki，本文件维护长期稳定的阶段、依赖顺序和验收口径。

## 三阶段总览

| 阶段 | 目标 | 主要产物 | 阶段出口 |
| --- | --- | --- | --- |
| 一、建立包络面 | 分析所有旧仓库，逐章识别可借鉴的完成度 | 以 aimpaper 为唯一语义标准的自足、可编译 KIP126 基线 | 17 章均完成参考调研；选用或重写的实现达到 aimpaper 的语义、分次和定理强度 |
| 二、继续形式化 | 在包络面基线上按数学依赖补完 Blueprint 与 Lean | 17 个章级模块及其 Lean 入口、外部输入接口和内部证明 | 所有应由项目实现的节点均完成；只允许保留经 `PROJECT_BOUNDARY.md` 明确分类的外部、开放或政策边界节点 |
| 三、最终审计 | 对全仓库而非单个模块做论文一致性、完整性、信任和可复现性审计 | 最终审计记录、干净构建结果和主定理依赖锥报告 | 满足 `PROJECT_BOUNDARY.md` 的全部最终验收条件，而不只是“构建通过” |

三个阶段按产物依赖排列。第二阶段只以第一阶段形成的 KIP126 基线为起点；旧仓库不
定义项目的目标语义，只提供实现和证明思路。凡是弱于或不对齐 aimpaper 的参考实现，
都不能直接充当完成结果，仍须按 aimpaper 的语义、分次、page convention 和定理强度
重新实现。第二阶段中的模块级检查是持续门槛，不能代替第三阶段结束时面向整个仓库
的完整审计。

## 第一阶段：从旧仓库建立包络面

KIP126 不是从零开始的单线实现，而是此前多轮谱序列、extension spectral
sequence、stable homotopy、synthetic spectra、classical Adams 和论文端点等多轮
实现探索的**最优进度包络面**。第一阶段的产物不是一份调研报告，而是将各仓库中
真正成熟、语义忠实且可维护的部分迁入同一规范接口之后形成的可编译代码仓库。

“包络面”不表示机械合并所有文件，也不以代码行数或 `sorry` 数量最少作为选择标准。
同一概念只保留一个面向 aimpaper 的权威实现；比 aimpaper 语义更弱、分次或 page
convention 不一致、定理强度不对齐，或把数学内容藏入公理/typeclass 字段的旧实现，
都只能作为 proof pattern 或实现线索，不能降低最终形式化目标。

所有旧仓库只作为只读参考。最终 KIP126 不得通过 path dependency 依赖它们，也不
继承它们锁定的旧版 Lean/Mathlib。

### 第一阶段完成条件

1. 17 章均完成参考调研；没有可借鉴实现的章节也有明确结论；
2. 每个重复概念选定唯一权威实现，不以平行 alias 掩盖接口分叉；
3. 选中的成果已经迁入 KIP126 并在 Lean 4.32.2 / Mathlib v4.32.2 下构建，不依赖
   旧仓库本机路径；
4. 迁入源码不新增 `sorry`、`admit` 或项目自定义 `axiom`；外部事实改写为显式条件
   输入；
5. 任何定义相等、索引换算和 adapter 均有证明义务与回归测试，不允许弱化或改变
   aimpaper 的语义和定理强度；
6. 形成可供第二阶段继续实现的、自足且可审计的 KIP126 包络面基线。

## 第二阶段：在包络面上继续形式化

第二阶段以第一阶段形成的 KIP126 为唯一代码基线。旧仓库仍可用于查找证明思路，
但参考实现不决定目标 statement；所有新增声明与证明都必须严格达到 aimpaper 的
语义、分次、page convention 和定理强度。

### 模块划分口径

Blueprint 使用平铺 chapter：`content.tex` 中没有 `\part` 或嵌套目录，只用注释标出
“数学定义 → 外部输入 → 内部证明”三层。每章对应一组按数学概念划分的 Lean 模块，
而不是单个源文件；`KIP126/Def.lean`、`KIP126/External.lean` 和
`KIP126/Challenge.lean` 是这些模块的包入口。旧路径与新路径的逐项对应及开放节点
见 [`DEF_CHALLENGE_LAYOUT_STATUS.md`](DEF_CHALLENGE_LAYOUT_STATUS.md)。
章级 Blueprint 节点数量与完成度不在本文件汇总，以对应章节子 Wiki 的当前记录为准。

- `content.tex` 只保留按依赖顺序的平铺 `\input` 清单与三层注释；没有 LaTeX
  `\part`。`blueprint/print` 和 `blueprint/web` 是生成物，不手工编辑；
  `blueprint/lean_decls` 也是被忽略的生成物，声明检查前由 `leanblueprint web`
  重新生成，不手工编辑或提交。
- 章节不按代码行数均分，而按数学定义、外部黑盒和内部消费者的边界拆分。每个
  公开声明只有一个权威实现；包入口只汇总 import，不复制声明。

### 依赖顺序

1. **数学定义层**：Algebraic foundations → spectral-sequence machinery → stable
   objects → classical Adams → extension SS → synthetic objects → synthetic ESS →
   page extensions → computation schemas → Kervaire setup。
2. **外部输入层**：在所有 statement 所需对象已经定义后，再陈述逐条 external
   literature result；具体 Lin 输出与附录表依赖 computation schema。
3. **内部证明层**：comparison/generalized rules 消费外部定理与计算输入，随后完成
   near-126 reduction，最后推出 geometric conclusions。
4. **技术审计层**：provenance 与 coverage 章节保持平铺，但不作为所有数学章节的
   父节点；`ExternalResult` 等 Lean 技术类型按需 import，不改变数学 DAG 的方向。

### 模块增量验收

每个模块进入下一依赖层前，必须满足：

1. `lake build` 通过，新增源码无项目 `sorry`、`admit` 或自定义 `axiom`；
2. 相关 Blueprint 节点有准确 `\lean`、`\uses` 和状态标记，DAG 无未知依赖、环或
   无意孤立节点；
3. `leanblueprint pdf`、`leanblueprint web` 和 `leanblueprint checkdecls` 通过；
4. 外部文献、Lin 输出和附录数据都以显式、类型正确的输入进入 Lean，不伪装成项目
   内部定理或全局公理；
5. 生成物只由工具生成，不手工编辑。

### 当前执行前沿

当前执行前沿已推进到稳定同伦/合成同伦输入包、附录 401 行 typed catalogue、BJM/BX
选择传输接口以及 Theorem 6.1/6.12/7.3 的精确开放命题。下一步按依赖图补齐
page-extension、near-126 coherence 和几何端点的真实证明，同时为每个外部输入补上
具体实例与 evidence；这些开放目标继续保持 `notready`。主 Wiki 负责更新章级完成状态和
下一步；本文件只在阶段、模块边界、依赖顺序变化时更新。

## 第三阶段：最终完整审计

第三阶段在第二阶段的正式节点全部完成后执行。此前每个模块已经通过增量检查，但
最终审计必须从干净检出出发，对完整依赖锥和全部外部输入重新核验，不能简单汇总
历史 CI 结果。

### 审计范围

1. **源码与信任边界**：扫描全部项目源码中的 `sorry`、`admit`、项目自定义
   `axiom`、可疑 `opaque` 和通过 typeclass/structure 字段隐藏的数学假设；对最终
   主定理及关键中间结论运行 `#print axioms`。
2. **Blueprint 完整性**：验证全部正式节点的 `\lean`、`\uses`、状态和声明映射；
   DAG 不得有未知依赖、环、重复 label 或无意孤立节点。
3. **外部输入边界**：逐条确认文献定理、Lin 程序输出和附录数据被建模为显式、类型
   正确的条件输入；外部事实不得被提升为无条件内部定理。
4. **架构与去重**：删除临时 compatibility shim、过渡 alias、重复模型和未使用
   import；确认 Mathlib `CategoryTheory.SpectralSequence` 仍是唯一通用谱序列内核，
   Classical、Synthetic、Comparison、External 与 Kervaire 边界清晰。
5. **可复现构建**：在无缓存、干净检出的 Lean 4.32.2 / Mathlib v4.32.2 环境中运行
   完整 `lake build`、回归测试、Blueprint PDF/web 和声明检查；生成物必须可由工具
   重建。
6. **论文一致性**：逐章核对 aimpaper 的 statement、分次、page convention 和定理
   强度；仅复用了较弱或不对齐的参考实现，不算完成对应节点。

### 最终完成条件

只有同时满足以下条件，KIP126 才可视为完成：

1. 所有应由项目内部实现的 Blueprint 节点均具有真实、可解析的 `leanok` 或锁定的
   `mathlibok`；保留的 `notready` 只能是经 `PROJECT_BOUNDARY.md` 明确分类并有完整
   边界记录的外部、开放或政策节点；
2. 主定理及其完整依赖锥不含 `sorryAx` 或项目自定义公理；
3. 所有外部文献和计算输入均以显式、类型正确且边界明确的条件进入 Lean；
4. 干净环境中的完整构建、回归、Blueprint 和声明检查全部通过；
5. `PROJECT_BOUNDARY.md` 所列范围、信任与验收条件全部满足。

## 跨阶段架构原则

1. **一个概念，一个权威实现。** 不保留多套平行定义或只为兼容旧仓库而存在的
   永久别名。
2. **先语义，后完成度数字。** 无 `sorry` 的定义性退化不能替代论文要求有内容的
   同构、构造或比较定理。
3. **适配优于伪统一。** 不同分次和领域对象通过有证明义务的 adapter/reindex 接入，
   不在没有等价证明时粗暴替换。
4. **外部根显式化。** 文献定理、程序输出和附录表格作为显式、类型正确的条件输入，
   不转化为项目全局公理。
5. **最终包自足。** 旧仓库仅是只读参考；KIP126 不以它们作为运行时或构建依赖。
6. **共享 Core 保持最小。** 直接采用锁定 Mathlib 的
   `CategoryTheory.SpectralSequence`，只增加实际下游共用的过滤、关联分次、filtered
   complex、spectral-object adapter 等结构；领域数学留在对应模块。
