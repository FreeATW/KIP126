# 球谱 E₂ 乘法计算器

数据固定为 Zenodo 14875701 / v126.3.cw49，内部次数 `t ≤ 261`。
`E2pageCompute.lean` 直接使用全部 231848 条导出关系和 23822 个基单项式。

在项目根目录编译并运行示例：

```bash
lake build KIPBase.E2page
lake env lean KIPBase/E2pageExamples.lean
```

第二条命令运行 `#eval demo`，初始化一次全部索引，然后展示结果并运行回归检查。
优化后的初始化加检查耗时约 4.4 秒（不含 Lean 启动和导入时间）；重复查询应复用同一个 `Engine`。

自定义查询（可放在另一个 Lean 文件中）：

```lean
import KIPBase.E2pageCompute
open KIPBase.SphereE2.Compute

#eval do
  let e ← match loadEngine with
    | .ok e => pure e
    | .error msg => throw (IO.userError msg)
  for (a, b) in [("1,2", "1,1"), ("0,1;1,1", "1,1")] do
    match e.multiplyStrings a b with
    | .ok r => IO.println (displayResult r)
    | .error msg => IO.println s!"Error: {msg}"
```

编码沿用 CSV：`"1,2"` 是生成元 1 的平方，`"0,1;1,1"` 是生成元 0 与 1 之和。
`""` 表示单位，整个多项式字符串 `"0"` 表示零。
数字对可以乱序或重复，解析器会合并指数；多项式重复项在 F₂ 上抵消。
这里只接受编号，不接受 `"h_0"` 等名称作为输入。

- `e.multiplyStrings a b`：严格范围接口，超出内部次数 261 报错。
- `e.multiplyTruncated a b`：截断代数接口，丢弃乘积中内部次数大于 261 的项。
- `e.multiplyBasis #[(s,t,index), ...] #[(s',t',index'), ...]`：两组基坐标相乘。
  每个数组表示基向量之和；index 是各自双次数内的编号。
- 所有接口返回 `Except String Result`。`normalForm` 给出单项式和，
  `coordinates` 给出每一项的 `(s,t,index)`，也支持非齐次结果。
- 可选的最后一个参数是约化步数上限，默认 1000000。耗尽时返回错误，
  绝不把部分约化结果当作标准形。

示例结果：

| 输入 | 正规形 | 基坐标 |
|---|---|---|
| `"0,1"` × `"1,1"` | 0 | 空 |
| `"0,1"` × `"0,1"` | h₀² | (2,2,0) |
| `"1,2"` × `"1,1"` | h₀² h₂ | (3,6,0) |
| `"2,2"` × `"2,1"` | h₁² h₃ | (3,12,0) |

实现沿用同版原始 C++ 源码的单项式比较方向和首项约化。
初始化检查关系项序、齐次性、范围、数量、基坐标唯一性，以及所有基单项式的不可约性。
这些检查不是 Buchberger 判据的形式化证明；本实现采用导出的 Gröbner 基数据，
不重新做 S-多项式补全，也不证明它与真实 Ext 的同构。
计算器和回归检查均不使用 `sorry`。`E2page.lean` 的 `multiply_mem` 仍有一个
允许保留的 `sorry`；其三个具体乘法证明的有限字符串解析等式使用 `native_decide`。

若需要将计算结果视为原商代数中的元素，导入 `KIPBase.E2page` 后使用
`KIPBase.SphereE2.interpretComputedPolynomial result.normalForm`。
该解释函数本身不是约化算法正确性的证明。

## 在证明中自动比较 CSV 基坐标

新增 `KIPBase.E2pageTactic`，使用方式：

```lean
import KIPBase.E2pageTactic
open KIPBase.SphereE2

example : (h0 + h1) * h1 = h1 ^ 2 := by
  e2_mul

example : h1 ^ 3 * h0 = 0 := by
  have h : h1 ^ 3 = h0 ^ 2 * h2 := by e2_mul
  rw [h]
  e2_mul
```

它对等式两边分别展开、约化、查 CSV 基坐标，并比较完整的 `(s,t,index)` 列表。
不同双次数中的相同 index 不会混淆。既支持乘积，也支持包含加法、自然数系数和
自然数次幂的具体多项式等式。可展开的命名常量和局部 `let` 也可以使用。
未知变量不会被当作生成元；若 `x : E2` 未给出具体表达式，不能直接查表计算它。

`e2_mul 2000000` 指定约化步数上限。默认 1000000；范围检查是严格的 `t ≤ 261`，
不会利用截断把超范围乘积自动判为零。为控制展开资源，非零非单位多项式的幂指数
上限为 261。首次调用建立全部索引，同一 Lean 进程中的后续调用复用索引。

**当前证明信任状态：** `coordinateCheck_sound` 是暂留 `sorry` 的计算正确性桥接。
因此 `e2_mul` 目前是采用该桥接的自动化原型，生成的证明依赖 `sorryAx`，不能视为
已经完整认证的形式化证明。实际展开、Gröbner 约化和坐标比较均已实现，不使用
`sorry`；成功后还通过 `native_decide` 检查布尔计算结果。坐标不同或计算错误时，
tactic 报错而不关闭目标。每次成功使用都会输出桥接尚未证明的警告。

正反示例位于 `E2pageTacticExamples.lean`。待完成桥接正确性证明后，使用者的
`by e2_mul` 语句不需要改变。

## 连接到球谱的 Adams 第二页

导入 `KIPBase.StableHomotopy.AdamsE2Comparison`，使用命名空间
`KIPBase.StableHomotopy.SphereAdamsE2`。这里的 `Page 𝒮 s t` 直接取既有
`AdamsSS 𝒮 SphereSpectrum` 的第二页 `(s,t)` 分量，采用非负整数双次数。
`SphereE2.E2` 仍表示原来的截断数据环 D，计算器的实现不变。

按本次要求，新增四个显式外部公理：

| 声明 | 内容 |
|---|---|
| `pageModule` | 实际第二页各分量上的 F₂ 模结构，沿用已有加法群 |
| `pageMul` | 实际第二页上的双线性乘法 |
| `comparison s t ht` | 当 `ht : t ≤ 261` 时，D 的齐次分量到实际页的线性同构 |
| `comparison_mul` | 当 `t + t' ≤ 261` 时，上述同构保持乘法 |

这组选定的同构是外部数学输入，并非从 CSV 自动证明得到。
没有声明整个截断环到完整第二页总代数的环同态，也没有把范围外的截断零关系
搬到实际页。`pageMul` 提供运算；本模块没有另外公理化全次数的单位、结合律、
交换律或后续各页的乘法与 Leibniz 法则。

常用的已证明搬运定理：

- `mul_eq_of_data`：从 D 中的 `x * y = z` 得到实际页上的乘积等式。
- `mul_eq_zero_of_data`：零乘积的便捷版本。
- `comparison_eq_iff`：比较两个同次数的像，相当于比较 D 中的代表元素。
- `exists_data_preimage`：范围内每个实际页元素都有 D 中的原像。

完整可编译示例见 `KIPBase/StableHomotopy/AdamsE2ComparisonExamples.lean`。
其中 `dataH0 : E2At 1 1` 和 `dataH1 : E2At 1 2` 是带齐次性证明的数据元素：

```lean
example :
    pageMul 𝒮 1 1 1 2
      (comparison 𝒮 1 1 (by decide) dataH0)
      (comparison 𝒮 1 2 (by decide) dataH1) = 0 := by
  apply mul_eq_zero_of_data 𝒮 1 1 1 2 (by decide) (by decide) (by decide)
  change h0 * h1 = 0
  e2_mul
```

需导入比较模块和 `KIPBase.E2pageTactic`，并像示例文件一样提供
`𝒮` 的 `StableHomotopyCategory` 实例。实际页上的任意抽象元素虽有同构原像，
但只有给定具体数据表达式后才能交给计算器执行；公理同构的逆映射不是可执行算法。

新增搬运定理没有 `sorry`，但使用外部比较公理和现有 `mulAt`（其齐次性证明
`multiply_mem` 尚有 `sorry`）；通过 `e2_mul` 得到的具体等式还依赖
`coordinateCheck_sound` 的 `sorry`。这些依赖与“已经无条件证明实际 Adams
第二页的计算结果”有明确区别。
