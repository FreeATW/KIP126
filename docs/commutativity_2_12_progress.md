# 第 2.12 条交换性证明：当前进度与待补缺口

记录日期：2026-09-22。本文记录本地工作状态，不宣称第 2.12 条已经证明。

本任务后续新增或修改的代码注释一律使用中文；数学记号、Lean 标识符和
Blueprint 标签保持原样，避免改变可检索的名称。

## 与 Blueprint 的对应关系

Blueprint 的 `thm:fess-commutative-square` 讨论交换方块的四条映射
`f、p、q、g` 所产生的扩张谱序列。其无 crossing 条件属于具体扩张关系
`d_n^f(x)=y`、`d_m^p(x)=z`、`d_l^g(z)=w` 和零扩张
`d_{k-1}^q(y)=0`，不是四个输入谱序列自身的页微分条件。
每条边仍涉及三个不同的谱序列：两个输入谱序列，以及由两项过滤复形构造的 ESS。
输入 `E∞` 与 ESS `E₀` 的对象比较，不等于谱序列之间的同一化，也不能直接
转移 crossing 命题。

Blueprint 的证明依赖 `prop:no-crossing-iff-uniform-detection`：无 crossing
当且仅当符合过滤下界的每个代表元都检测到指定目标。交换方块证明必须通过
这个代表元刻画选取共同的 `x` 代表元，并追踪 `qf=gp`。

## 已实现但尚未构成主证明的部分

- `Commutativity.lean` 中新增针对具体 `ExtensionDifferentialRelation` 的
  `NoCrossingRange`，下界与上界均按 Blueprint 记录；普通 `NoCrossing`
  是下界取源过滤次数加一的特例。零扩张也可使用该定义。
- `not_crossed_of_noCrossing` 在“本质微分页数非负”及“微分目标过滤次数
  等于源过滤次数加页数”两个显式前提下，将范围条件转为过滤复形代表元引理
  所需的关系级无 crossing 条件。现已证明过滤复形 ESS 的负页微分为零、
  本质关系只发生于非负页，并据此完成此转换在 ESS 上的特化。
- 已证明 `FilteredComplex.pageDifferential_on_kernel` 的规范计算式，并用它
  完成 `FilteredComplex.differentialRelation_of_lift`，正向代表元引理不再含
  `sorry`。该模块和依赖它的 `Commutativity.lean` 已分别通过本地离线编译。
- 已证明 `EssentialDifferentialRelation.d_ne_zero`：本质关系要求其页微分非零。
- 已证明 `FilteredComplex.lift_endpoints_of_differentialRelation`：利用 `T` 的
  投射性，把 ESS 微分关系的源、目标分别提升到对应过滤层。这个结论只给出
  两端的提升及源提升的实际微分。
- 已证明 `FilteredComplex.lift_boundary`，并据此完成
  `FilteredComplex.lift_of_differentialRelation`：页边缘的目标差可由
  下一源过滤层的微分修正，反向代表元引理现已没有 `sorry`。
- 已证明 `FilteredComplex.lift_boundary_at_differential` 与
  `FilteredComplex.boundary_zero_apply`；前者显式处理 `dToK` 的次数搬运，
  后者证明第零页边缘没有非零广义元素。竞争目标引理的负页分支也已完成。
- 已证明 `FilteredComplex.isLift_sub_lift`：同一关联分次类的两个源代表元
  之差确实提升自下一过滤层，供后续 crossing 论证使用。
- 已证明 `SSData.sub_factors_boundary_of_page_eq`：两个循环代表元若在
  同一页相等，它们在环境对象中的差落入对应边缘子对象。这是反向提升时
  进行边界修正所需的页商步骤。
- 已证明 `DifferentialRelation.targets_sub_factors_boundary`：同一源元素的
  两条同页微分关系，其目标差必落入目标页的边缘子对象；该结论本身无需
  投射性，已在 `Crossing.lean` 中线下编译通过。
- 已证明 `SSData.first_boundary_page`：边缘塔中第零级不包含、但第
  `n` 级包含的目标，有一个最小的首次出现页数。竞争目标引理已用它
  选出 `m<n`，使目标差属于 `B_{m+1}` 却不属于 `B_m`。
- 已完成 `FilteredComplex.differentialRelation_crossed_of_two_exact` 与
  普通版本 `differentialRelation_crossed_of_two`：不同目标通过首次出现
  的边缘页给出较短本质微分，且 crossing 的目标过滤次数恰为原目标次数。
  `FilteredComplex.lean` 目前已无 `sorry`。
- 已证明 `ESSRelationNoCrossingRange.target_unique_of_filteredComplex`：
  范围性无 crossing 排除同一源、同一页的不同目标；该证明使用精确目标
  crossing，而不是把范围性条件错误地加强为普通无 crossing。
- 已证明 `ESSRelationNoCrossingRange.lift_rel_of_filteredComplex`：在代表元的
  实际微分已经进入目标过滤层的前提下，范围性无 crossing 保证目标关联分次
  等于指定的类。已证明 `FilteredComplex.lift_zero_deeper` 和
  `ESSRelationNoCrossingRange.zero_lift_deeper_of_filteredComplex`：当该目标类
  为零时，实际微分可继续提升到下一过滤层。这些结论没有暗中假设完整统一检测。
- 已加入 `ConvergingSSSquare.aMap_comm`，从范畴方块的 `comm` 字段严格取出
  极限对象映射的等式 `qf=gp`；后续两项过滤复形的实际微分计算应使用此引理。
- 已定义 `UniformDetection`，并证明 `ESSRelationNoCrossingRange.uniformDetection_of_filteredComplex`。
  该命题给出 Blueprint 统一检测的“已进入目标过滤层”方向；为保持逻辑正确，
  `r≥0` 和目标过滤层入口仍是显式前提，尚未把入口结论伪装成无 crossing 的直接推论。
- 已证明 `FilteredComplex.zero_relation_deeper_lift`：零关系的无 crossing
  与反向提升结合后，确实可以选取源代表元，使实际微分进入目标层再深一层。
  该引理已独立离线编译通过，后续可直接用于 `q` 边的零扩张。
- 已在 `Commutativity.lean` 增加 `ESSRelationNoCrossing.zero_relation_deeper_lift`，
  将 ESS 的普通无 crossing 假设转换为上述过滤复形结论；主定理中的 `q` 零关系
  现在有了可直接调用的接口。
- 新增 `FilteredComplex.factor_max_or_zero`：在有界递减过滤中，已落入某层的
  映射要么为零，要么存在最大过滤次数且下一层不再因子。该有限搜索引理已
  本地离线编译通过，是构造“首次本质微分并产生 crossing”的下一步基础。
- 新增 `FilteredComplex.essentialRelation_of_maximal_lift`：把最大过滤层且
  非边界的过滤微分直接封装成本质关系，目标次数精确为该最大层。该接口已
  本地离线编译通过；剩余工作是证明最大层若低于原目标层，必可排除边界情形
  或进行边界修正，从而真正得到 crossing 矛盾。
- 新增 `FilteredComplex.boundary_correction_lift`：边界目标可由高一层源代表
  修正，保持源关联分次类不变，并把实际微分推进到目标下一过滤层。该边界
  修正接口已本地离线编译通过，正用于完成最大层分支的 crossing 论证。
- 新增 `FilteredComplex.essential_or_boundary_correction`：单步分支现在形式化
  为“非边界则产生本质关系；边界则推进一层”。结合最大层有限性即可进行
  有限迭代；该接口已本地离线编译通过。
- 新增 `FilteredComplex.transport_fil_nat_succ`：自然数后继对应的整数过滤
  次数搬运现在通过显式等式参数和 `eqToHom` 完成，并已独立离线编译通过。
- 另新增 `FilteredComplex.ofLE_transport_fil_nat_succ`，并在有限迭代中用
  `Subobject.arrow_congr` 完成包含态射的自然性转换。
- 已完成 `FilteredComplex.iterated_essential_or_zero`：以有界过滤层差的
  强归纳为基础，边界分支通过显式 `eqToHom` 搬运代表元，并用
  `Subobject.arrow_congr` 证明 `ofLE` 包含态射的自然性；顶层过滤层为零的
  分支也已单独处理。现已加强结论，确保最终本质关系或零微分代表元与
  起始源关联分次类相同；该递归定理已本地离线编译通过。
- 新增 `FilteredComplex.essential_ancestor_of_nonzero_boundary`：非零页边界
  在同一目标过滤次数上必来自更高源过滤层的本质微分。该引理沿微分页数
  下降归纳，已本地离线编译通过。它是处理“目标是边界”时构造 crossing
  的正确接口；仅把目标逐层推深的迭代不能替代这一论证。
- 新增 `FilteredComplex.filDiff_of_sub_lift`：同一关联分次类的两个源代表
  之差提升到下一层后，其下一层微分经包含态射等于原微分之差。这是从
  任意源代表元构造较高过滤源并产生 crossing 的代数接口，已本地编译通过。
- 已证明 `ESSRelationNoCrossingRange.no_nonzero_boundary` 与
  `higher_source_image_deeper`：范围内的非零边界或更高源的浅层非零像
  都会产生被无 crossing 排除的本质关系。由此证明正页的
  `ESSRelationNoCrossing.uniform_detection_full_of_pos`，并得到正页零扩张
  对每个源代表元的严格更深过滤结论 `zero_uniform_deeper_of_pos`。
- 新增第零页自动范围无 crossing 引理 `zero_page_automatic`：较高源过滤
  的非负本质微分不可能回到第零页的目标过滤次数。由此证明第零页的
  `uniform_detection_full_of_zero`，再与正页合并成适用于所有非负页的
  `uniform_detection_full` 和零关系的 `zero_uniform_deeper`。
- 已证明 `essComm_common_source_lift`：只要 f、p 中一条具体关系无 crossing，
  即可选取同一个源过滤代表元，同时使 f 与 p 的实际微分检测到指定的
  `y` 与 `z`。该证明还显式核对了方块三处公共顶点的过滤层定义相等，
  没有同一化四条边的 ESS。上述新引理均已本地离线编译通过。
- 对反向代表元、竞争目标两个新引理执行 `#print axioms` 审计并筛查
  `sorryAx`，未发现依赖 `sorryAx`。新增引理及依赖模块已本地离线编译通过。
- 当前相关 Lean 模块可以本地离线编译，但编译成功不代表这些 `sorry` 已消除。

本次检查执行了 `bash .lake/offline-build.sh KIPBase.SpectralSequence.Commutativity`，
退出码为零（最新一次共 1747 项）；`FilteredComplex.lean` 已无 `sorry`，
编译器仍报告 `BoundedExtension.lean` 和 `Commutativity.lean` 中的旧 `sorry`。
`git diff --check` 通过。

## 尚未解决的数学及形式化依赖

1. `essCommutativity` 的无 crossing 假设现已改为绑定具体的 (f,p,g,q)
   ESS 关系，且 (q) 边采用真正的零扩张关系；已通过本地离线编译。
   主定理的证明本体仍是 `sorry`，不能把“陈述已对齐”误报为“定理已证明”。
2. Blueprint 的普通无 crossing 统一检测已覆盖全部非负页；零 `q` 扩张
   对任意 `y` 代表元的严格更深过滤结论也已证明。范围性无 crossing 的
   `g` 边目前有 `uniform_detection_from_reference`，仍需在方块中用
   `qf=gp` 构造其“像已进入范围下界”的前提，并完成目标过滤层比较。
3. 方块的共同 `x` 代表元已由 `essComm_common_source_lift` 取得。尚需把
   两项复形微分与四个极限对象映射连接，随后用 `qf=gp`、`q` 的更深过滤
   及 `g` 的范围性检测，最终构造结论中的 ESS(q) 微分关系。
4. `BoundedExtension.lean` 中 `essDiff`、`essBoundary` 等抽象对象仍有
   `sorry`，因此依赖这些对象的若干旧版推论也未获得实质证明。
5. `Commutativity.lean` 中部分旧版定理只要求“存在某个态射”或断言
   任意给定的页间映射自动交换。这些陈述需要与 Blueprint 逐条核对；
   不能用零态射填补 `sorry`，也不能把任意映射的交换律当成公理。

## 后续证明顺序

页微分计算、双向代表元引理、竞争目标引理、有限迭代及范围性目标唯一性均已完成；
接下来证明无 crossing 的完整统一检测刻画，之后在方块中选共同代表元、
用过滤层上的 `qf=gp` 比较目标，最后组装第 2.12 条的
`DifferentialRelation`。每一步均需本地编译，并检查最终定理及其依赖
没有新增公理或 `sorry`。
