# A 的任意非零乘法中心：局部接触桥与完整曲线不等式

本轮新增 `oai017/DistinctMultiplicativeContact.lean`，包含 28 个具名定理。固定 Lean 4.34.1 / mathlib 环境严格编译退出码为 0，实际 `.olean` 已生成；关键八个定理的 `#print axioms` 仅列 `propext`、`Classical.choice`、`Quot.sound`。没有新增公理、`sorry` 或 `admit`。旧已验证适配源码和上游证明正文没有修改。

## 已实际关闭的局部桥

对任意非零复数中心 a，定义真实函数域坐标归一化

\[
\widetilde z_0=a^{-1}z_0,\qquad \widetilde z_{i+1}=z_{i+1}.
\]

`centered_normalize` 证明旧中心 `(a,c)` 的实际离散赋值中心变为 `(1,c)`，乘法常数的赋值等于零是从上游 `CurveProductFormula.valuation_constant_eq_zero` 调用得到的。`normalize_nonconstant` 同时证明非恒定坐标族不会被归一化消掉。

`aeval_normalize_scaleY` 认证

\[
 P(z)=({\rm scaleY}\ a\ P)(\widetilde z),
\]

而 `scaleY_polynomialFrameWord` 证明归一化与全部真实 logarithmic frame 导数 word 对换。`aeval_scaleY` 还对任意交换环 A 成立，可以直接在真实局部 DVR 上调用，且不需要 A 是域。

新的 `logContactAt` 直接使用上游 `PlaceCenteredBranch.logContact` 对归一化坐标的实际 branch expansion，所用局部坐标因此正是

\[
z_0/a-1,\qquad z_{i+1}-c_i-\log(z_0/a).
\]

`logWord_field_order_lower_at` 从真实新 jet `formalJetAt a c F` 的加权理想成员关系，推出导数 word 在真实曲线函数域上的赋值阶下界。它不把阶比较假定为输入。

## 截断对数理想至真实接触长度

`localLogIdealAt` 是归一化坐标在原正规分支 DVR 中的截断对数纯幂理想。`normalized_lift_zero` 证明它的第零局部参数就是 `a⁻¹ * lift(Y)`，其余 `normalized_lift_succ` 等于原加法坐标的 lift。

在真实整数指数满足 `e_i v_i = R` 且截断尾项界 `v_{i+1} < T_i v_0` 时，`localLogIdealAt_colength_eq_contact` 实际证明

\[
\operatorname{length}(A/I)=R\,\mu_{a,c,V}.
\]

这里长度为原 DVR 商模的真实 `Module.length`，接触为上述实际 branch contact。证明直接复用上游 `LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact`，而不是声明一个额外比较公理。

## 已关闭 Persistent 的消失输入

`placesAt`、`centerAtIndex` 与 `familyContactAt` 构造了真实多中心有限分支族及接触函数。中心选择的证明信息只用作 Prop，接触数值来自实际归一化展开。

`logarithmic_words_vanish_at` 实际证明：若辅助多项式源加权次数至多 N，且在全部新中心 jet 的消失预算为 `(1+3σ)N`，曲线满足

\[
d_W(C)<(1+\sigma)\sum_P\mu_P,
\]

则所有成本至多 `σN` 的 frame word 在曲线上消失。推导使用真实局部阶下界、导数后的真实源次数界，以及上游真实函数域主除子次数平衡 `polynomial_eq_zero_of_excess_contact`。

`excess_implies_zeroth_center` 再由实际体积条件构造新中心辅助多项式，调用上游持久分量与真实横截重数比较，推出

\[
\exists j,\quad Y=y_j.
\]

因此新曲线结论没有独立的 `hupper` 或 `hvanish` 前提。

## 已关闭 Fibre 的接触比较输入，并证明完整内蕴曲线不等式

`logContactAt_constant_y` 通过实际归一化 `Y/a=1` 及上游 `logContact_one`，证明任意常数 Y 上的对数接触恰等于普通加法接触。它消去了旧适配器需要独立提供的 `hμ`。

`no_excess_of_constant_y` 利用 y 单射，使同一恒定 Y 曲线的所有相关分支都属于一个中心；再把上述真实接触等式接到实际 `single_center_fibre_curve_inequality`。没有要求任何加法坐标单射，也没有第二个纤维体积条件。

最终已通过内核检查的 `weighted_curve_inequality_at` 具有原内蕴曲线模型的实际假设：函数域 E 为 `Algebra.EssFiniteType ℂ E`，真实坐标 z 生成 E，且 `Algebra.trdeg ℂ E = 1`。正规分支残域为复数上的整代数、每个非恒定参数上的有限维性和实际 prime height 界都由上游真实定理导出，未作为额外缺口外加。

在 y 非零单射、加法中心任意，且满足唯一主维数条件

\[
K(1+3\sigma)^{m+1}\frac{\prod_iw_i}{\prod_iv_i}<1,
\]

与原乘积权重分离和 `(1+σ)w_i<v_i` 时，定理证明

\[
(1+\sigma)\sum_P\mu_P\le d_W(C).
\]

这是完整的新中心内蕴曲线不等式。其接口不再假定 `hμ`、`hvanish`、`hupper`，没有旧定理的第二条体积条件或加法单射条件。

## 主定理连接与认证范围

此文件已经关闭新中心的局部接触、截断理想长度、全体导数消失和内蕴曲线不等式，局部接触链不再留有待证明的比较或消失前提。体积、乘积权重分离和逐坐标比例只是预选权重的明确数值条件。

本轮 `DistinctMultiplicativeDegree.lean` 已将这个实际内蕴曲线不等式接到真实紧化理想、吹起曲线 degree 比较以及全局插值，得到无残余曲线 degree 假设的 `Degree.Weighted.eventual_interpolation_of_separated_weights`。随后 `DistinctMultiplicativeExistence.lean` 的 `exists_successive_curve_weights` 仅由 A 的主维数条件选出 σ 与中心无关的 successive 权重下界，并同时证明这里所需的全部数值条件；其 `separated_distinct_multiplicative_interpolation` 已严格编译为完整 `SeparatedDistinctMultiplicativeInterpolationStatement`。这两个 existence 定理的 `#print axioms` 同样只有标准三公理。因而 A 的 successive 大权重存在性版本已闭合，局部接触链或全局曲线 degree 桥均未被作为额外假设保留。

曲线权重分离仍采用上游较大的 `PersistentWeightComparison.comparisonConstant`。这适用于 Theorem A 的 successive 大权重存在性结论；不能把它误称为已认证稿件 A-r2 的较小阶乘常数 C* 及显示的具体界 (1.4)。

Contact 源码已冻结；严格编译记录：`oai017/DistinctMultiplicativeContact.check.log`。完整 A 存在性版本另见 `oai017/DistinctMultiplicativeExistence.lean` 和相应 `.check.log`；本轮全部新声明的整体公理计数以最终统一审计记录为准。
