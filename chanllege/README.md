# h₆² 在经典 Adams 谱序列中存活：独立 statement

目标来自指定 `paper/target.pdf` 的定理 1.4（亦即定理 7.1），PDF 第 2 页。
该 PDF 的 SHA-256 为
`7cae269851a88d10dd194651dbf7497b75ef8b8b914bc1901dfa3734cd8096b4`。

最终命题是 `KervaireChallenge.H6SquaredSurvivesToEInfinity`，
证明占位符单独保存在仓库根目录 `KIP126.lean` 的
`KIP126.h6_squared_survives` 中。前置定义不导入原有 `KIP126/` 实现。

| 文件 | 内容 |
| --- | --- |
| `Topology.lean` | 具体拓扑预谱、基点映射、稳定同伦代表元、稳定等价及其范畴局部化 |
| `Adams.lean` | 球谱、移位 HF₂、Adams 分解、几何正合偶、各页及非零存活 |
| `Statement.lean` | 无自由参数的最终目标命题 |
| `../KIP126.lean` | 最终定理及唯一的 `sorry` |

## 数学语义

这里的谱不是一个没有约束的抽象类型：它是带基点拓扑空间的序列，
结构映射由连续的 `I × Xₙ → Xₙ₊₁` 给出，并要求在两端和基点上为常值。
稳定等价通过实际的立方体映射、相对边界同伦和结构映射诱导的悬挂定义。
稳定同伦范畴取这些预谱关于稳定等价的范畴局部化。

球谱的各个移位用立方体球面 `Iⁿ/∂Iⁿ` 的最终水平表示及结构映射兼容性确定。
先加入不交基点再取商，因此零维球面是两个点，不会错误地成为一个点。
HF₂ 的移位由其真实稳定同伦群确定：指定次数为 `ZMod 2`，其他次数为零。

Adams 分解要求每一层由移位 HF₂ 的乘积组成，逼近映射在每个次数的模 2
上同调上满射，下一阶段由实际的路径空间同伦纤维给出。
正合偶的三个映射分别来自纤维投影、逼近映射及环路到纤维的映射。
这种注入分解给出经典 Adams 谱序列；参见
[Christensen，第 4 节、PDF 第 14 页](https://jdc.math.uwo.ca/papers/ideals.pdf)。

代码内部用 `(s,n)` 表示过滤次数和稳定茎；对外的 `E₂ s t` 使用论文的
`(s,t)`，其中 `n=t-s`。正合偶中的循环和边界采用

- `Zᵣ(s,n) = k⁻¹(im(D(s+r,n-1) → D(s+1,n-1)))`；
- `Bᵣ(s,n) = j(ker(D(s,n) → D(max(s+1-r,0),n)))`；
- `Eᵣ = Zᵣ/Bᵣ`，`Z∞ = ⋂ᵣ Zᵣ`，`B∞ = j(ker(D(s,n) → D(0,n)))`。

因此微分的次数是 `(s,t) → (s+r,t+r-1)`。
这里从 `E₁` 构造经典谱序列，最终元素位于 `E₂^(2,128)`，稳定茎为 `126`。
`SurvivesToEInfinity` 要求一个固定的 `E₁` 代表元属于全部循环子群，且不属于
最终边界子群；它同时要求原 `E₂` 类非零。

**h₆² 的识别方式**：指定 PDF 第 2 页给出经典 Adams 二线的生成元
`hᵢhⱼ` 和关系 `hᵢhᵢ₊₁=0`。在内部次数 128，唯一的生成元是 `h₆²`，故
`E₂^(2,128)=F₂{h₆²}`。本 statement 用“该次数的唯一非零元”精确刻画这个类。
这是一种针对本题的内在刻画，不是把任意命名的元素当作 `h₆`，也不是通用的
Ext 乘法实现。代码没有另行定义 Steenrod 代数、Yoneda 乘法或证明其与这一
刻画的比较定理；这些并非这一等价表述所需的原始概念。

`StableFoundations` 和 `SphereAdamsResolution` 记录标准构造的具体表示及
兼容性证明。当前没有构造这些记录的实例；最终命题**同时要求实例存在**，
并要求每一个这样的几何 Adams 分解中的目标类存活。因此不能利用空类型让
目标真空成立，也没有假设待证的存活结论。实例存在性和最终存活证明均留在
同一个最终定理的证明义务中，符合本次只写 statement 的范围。

## 检查

使用 Lean 4.32.2 和已安装的同版本 Mathlib 编译产物，逐个检查以上模块，
不运行原工程的完整构建。已有依赖时可在仓库根目录执行：

```bash
mkdir -p .lake/build/lib/lean/chanllege
lake env lean -o .lake/build/lib/lean/chanllege/Topology.olean chanllege/Topology.lean
lake env lean -o .lake/build/lib/lean/chanllege/Adams.olean chanllege/Adams.lean
lake env lean -o .lake/build/lib/lean/chanllege/Statement.olean chanllege/Statement.lean
lake env lean -o .lake/build/lib/lean/KIP126.olean KIP126.lean
```

`Adams.lean` 中还证明了以下语义检查，无证明占位符：

- 零类不满足非零存活谓词；
- 正合偶的有限页边界包含于循环，最终边界包含于最终循环；
- 满足存活谓词确实给出显式 `EInfinity` 商群中的非零元素。

最终定理使用 `sorry`，因此并未证明论文；它应当且确实依赖 `sorryAx`。
前置定义和上述检查只使用 Lean 的标准基础公理，没有项目自定义公理。
