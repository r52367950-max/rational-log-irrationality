# Theorem A：实际复用 OAI017Lean 源码的记录

固定上游版本：`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`。

原始源码路径为 `lean/OAI/NumberTheory/PiExponent/`；完整子树有 869 个 Lean 源文件（877 个含目录条目），本地源文件放在 `source/OAI/NumberTheory/PiExponent/`。上游工具链是 Lean 4.34.1，所固定 mathlib 为 `d13f23b723b8a846827a245b89c10fc7d3f11612`。不能把前一轮 Lean 4.24.0 的局部证书冒充这个工程的编译记录。

## 原定理与 Theorem A 的准确关系

原论文的插值定理假设所有中心的 Y 坐标等于 1，且每个加法坐标 `c_{ji}` 随 j 分别单射。它需要两条体积条件：`K θ^m < 1` 和 `K (w₀/v₀) θ^m < 1`。

Theorem A 的中心有两两不同的非零 Y 坐标 `y_j`，加法坐标任意，仅需后一条体积条件。因而 A 是一种不同中心配置的推广，并不能直接通过给原定理代入参数得到；原中心 Y 坐标相同，并不满足 A 的中心条件。

主要新步骤在 Y 已被证明恒定之后：原证明还要在 Y=1 的纤维中找出某个恒定加法坐标，从而利用该坐标区分中心；A 的 Y 单射直接保证恒定 Y 的曲线至多经过一个中心，无需第二次辅助多项式/重数过程。这也是去掉 `K θ^m < 1` 的具体数学原因。

## 已写入的新适配源码

### `DistinctMultiplicativeRigidity.lean`

这份源码直接 import 并调用上游定理，未把它们改写为公理：

- `Analysis/AlgebraicLogarithmicObstruction.lean` 中的 `constant_of_logarithmic_differential`。这是完整函数域障碍：对于有限生成型域扩张及 Kähler 微分，`dx=y⁻¹dy` 使 y 为常数。它已经包含导子延拓、有限扩张及超越基归约；不再仅有前一轮的 Laurent 留数局部结果。
- `Approximation/GenericNormalRigidity.lean` 中的 `constant_zeroth_coordinate_of_generic_normal_separation`。该定理本身只要求乘法坐标非零，完全没有要求等于 1，故可真正直接复用。
- `Jets/NormalBasisRigidity.lean` 中的 `weighted_normalBasis_exclusion`。它把法向基的乘积上界与权重严格分离条件转换成所需的不可能基配置，自动处理法向基等势性。
- `Geometry/CurveCenters.lean` 中的 `Centered.constant_coordinate`。新证明仅用坐标 0 的单射推出所有分支所属中心相同；没有引入原来的所有加法坐标单射条件。

新定理 `zeroth_constant_of_weighted_normal_comparison` 以具体加权重数上界为显式 `hupper` 输入，得到任意非零 Y 为常数；随后 `center_index_unique_of_constant_y` 与 `all_centered_branches_have_one_index` 完成 A 新中心配置的纤维归约。

### `DistinctMultiplicativePersistent.lean`

这份进一步适配不再把 `hupper` 作为独立前提：它调用上游 `PersistentWeightComparison.logarithmic_persistent_comparison` 与 `CurveComponentRigidity.coordinate_constant_of_persistent_comparison`，从真实多项式导数 word 在曲线函数域中的消失、原来的维数/prime height 界和权重分离推出 `Y=y_j`，再利用 Y 中心单射直接推出至多一个中心。

需要明确常数的区别：此模块使用上游的较大矩形比较常数 `comparisonConstant m sigma`，没有验证 A-r2 的较小阶乘常数 `C*`。这足以处理选择更大 successive 权重的存在性版本；不能拿它声称已机器验证稿件显示的具体显式下界 (1.4)。

### `DistinctMultiplicativeJets.lean`

这里把原始 `FormalLogJet.formalJet` 与仅缩放 Y 的多项式代换复合，实际构造：

`formalJetAt y c P = P(y(1+t), c_i+u_i+log(1+t))`。

相应源代码直接使用上游的：

- `WeightedSliceDegree.supportBound_aeval`：证明 Y 缩放不增加任意 W 加权次数。
- `FormalLogJet.derivation_map_of_X`：将生成元的计算扩展为所有多项式的 frame 对换恒等式。
- `FormalLogJet.formalJet_polynomialFrame`：保留原 frame 至 jet 的导数恒等式。
- `FormalJetDerivatives.jetFrameWord_mem_rationalWeightedIdeal`：把原成本累计估计用于新中心的真实对数 jet。
- `Polynomials/AuxiliaryPolynomial.lean` 中的 `eventually_exists_auxiliaryPolynomial`：将新线性求值映射作为参数，获得新中心的辅助多项式存在定理，体积条件正是 `K a^(m+1) ∏W/∏V < 1`。
- `JetGeometry.rationalCoefficientPackets_surjective_of_coordinatePowerIdeal`：从同时普通幂商满射转换为新中心真实 jet 的系数包满射。

`eventually_exists_auxiliaryPolynomialAt_nat` 与 `formalJetAt_polynomialFrameWord_vanishing` 是对新中心的重要新适配证明，均不需要任何坐标区分条件；区分条件只应在最后恒定 Y 的纤维论证使用。

### `DistinctMultiplicativeAmple.lean`

另有独立 AG 适配文件，详见 `ampleness_reuse.md`。它通过原始数值正性及吹起理论，从具体曲线次数的不等式得到充分大 n 的真实 scheme 理想 jet 满射，再提供到形式系数包的显式条件接口。

### `DistinctMultiplicativeFibre.lean`

上游 `FibreContact.weightedDegree_one` 被实际推广为任意常数乘法坐标的 `weightedDegree_constant`；原 `CoordinateContactBound.coordinate_contact_sum_le` 被直接调用来证明新的 `single_center_fibre_curve_inequality`。该最后单中心不等式无需任何加法坐标单射，也无需第二条纤维体积条件。其明确剩余输入是：新对数接触在常数 Y 上等于普通加法接触；这个比较仍需接入新中心的 branch API。

### `DistinctMultiplicativeStatement.lean`

此文件只定义完整待证明命题，未将主结论设为公理。实际 `packetMapAt` 使用新 `formalJetAt`、原 `WeightedSliceDegree.SupportBound` 的源 `≤H` 与原 rational coefficient packet 的目标 `<H`。

`SeparatedDistinctMultiplicativeInterpolationStatement` 包含完整的先后量词：固定 m、K、w₀、v₀、θ 与体积条件；先存在 successive bounds，每个边界只能读取较前的权重；再对所有超出边界的正权重成立；在中心之前选择可整除两套权重的整数 R；最后对所有非零且单射的乘法中心与任意加法中心，n 在各自的充分大范围内映射满射。这样可以准确区分完整主命题与已证明适配子命题。

## 仍不能声称已完成的部分

上游的低层局部代数、函数域障碍及最终 ample→理想 jet 定理并不局限 Y=1；但将它们连接到具体对数中心的若干高层 API 确实把 Y=1 写进定义。这些地方需要真正适配：

1. 把多中心曲线接触族由 `fullCenter c=(1,c)` 改为 `(y_j,c_j)`，连接新 jet 与分支正规模型的阶。
2. 用新辅助多项式与原持久分支、重数定理证明所有相应曲线的分离不等式。原持久分支/重数结果到新 Y 单射结尾已经写成直接适配；新 jet 在各任意 Y 中心的 branch/contact 阶如何给出函数域导数消失，及完整曲线接触组合，仍未接完。
3. 构造各新中心的实际多项式坐标 `t=Y/y_j−1`、截断对数理想与紧化理想层，并证明它们的曲线次数/接触公式。
4. 把实际全局 sections、源加权多项式与同时形式普通幂商连接，清楚证明比较图交换。这些桥接条件在新适配文件中保留为明确参数，没有隐藏或公理化。

因此，已有新适配证明加上直接调用的原定理会显著减少 A 的剩余形式化工作，但尚不是 Theorem A 的完整 Lean 证明。更不能单由 A 的形式化程度推论无理性指数结论成立。

## 编译状态

`DistinctMultiplicativeJets.lean` 已在固定 Lean 4.34.1 / mathlib 环境中编译通过（退出码 0）。同名 `.check.log` 中打印的八个新定理只依赖 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义公理。这里认证的是实际新中心 jet、源加权次数保持、对数 frame 对换、导数 word 成本消失、辅助多项式存在以及普通幂商至系数包的条件满射。

`DistinctMultiplicativeStatement.lean` 也已编译通过（退出码 0）。这认证了完整目标命题及实际映射的正确类型；它仍只是一份待证明的命题定义，不能把类型检查通过误称为主定理已证明。

`DistinctMultiplicativeRigidity.lean` 已编译通过（退出码 0），四个新定理的 `#print axioms` 全部只列上述标准三公理。这包含完整函数域对数微分障碍的直接复用，以及仅靠乘法坐标单射的新单中心结论；其中独立泛型法向比较定理仍以 `hupper` 为明确输入。

`DistinctMultiplicativeFibre.lean` 已编译通过（退出码 0），两个打印的新定理也仅依赖标准三公理。它认证任意常数 Y 的加权次数公式和最终单中心曲线不等式；对数接触等于普通接触的 `hμ` 仍是明确输入。

`DistinctMultiplicativePersistent.lean` 已编译通过（退出码 0），三个新定理的公理依赖也仅为标准三公理。它调用上游真实横截重数和持久分量证明，导出所需比较而不额外假定 `hupper`，认证任意非零中心上 `Y=y_j`、至多一个中心，以及自动满足充分大 N 矩形条件的版本。它仍使用上游较大比较常数，不能认证 A-r2 的具体阶乘下界。

`DistinctMultiplicativeAmple.lean` 也已严格编译通过（退出码 0），生成实际 `.olean`；三个定理的公理依赖仅为标准三公理。实际普通吹起上的统一曲线次数条件至丰沛性、实际理想喷射最终满射，以及带明确交换关系的同时形式系数包桥接均已核验。

以上六份不同乘法中心适配源码全部通过固定工具链的严格类型检查。实际日志为同名 `.check.log`；统一动态公理审计另见 `AdapterAxiomAudit.check.log`。工作副本只修改 import 头部以缩小原始 `import Mathlib`；归档原文和全部声明、证明正文逐字保留，具体修改数以最终头部补丁清单为准。

统一审计已经成功退出（退出码 0）。本轮九份实际复用/适配源码包含 68 个具名新定理；动态枚举共核查 99 条 theorem 声明，其中 31 条为编译器自动生成的辅助或方程声明。所有声明的完整传递公理依赖均不超出 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义公理。99 是审计声明数，不能误称为 99 个手写新定理。

这些通过记录是上述适配定理及目标命题的证书，仍不是完整 Theorem A 的证书。实际新中心紧化理想、branch/contact 与曲线次数接口，以及全局受权重多项式和同时局部商的交换关系，仍是完整形式化的明确剩余工作。
