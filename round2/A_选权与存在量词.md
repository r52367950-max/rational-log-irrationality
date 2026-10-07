# A 的选权与存在量词：完成记录

`DistinctMultiplicativeExistence.lean` 严格编译 exit 0。两条公开定理的传递公理仅 `propext`、`Classical.choice`、`Quot.sound`。

`exists_successive_curve_weights` 固定 m,K,w₀,v₀,θ 及总体积小于 1，先调用原 OAI 的有理小 σ 存在定理，取额外第二参数 β=0。因此不引入第二体积条件。随后取有理 D 严格大于

\[
\operatorname{weightSeparationFactor}(m,C_m(\sigma),w_0,v_0,\theta).
\]

第 i 个下界为

\[
b_i(\text{earlier})=\max\left(1,D\prod_{j<i}\text{earlier}_j\right).
\]

它只使用此前的正权重，不读取任何中心。将有限正权重扩展成自然数序列（第零项为 1，超出 m 后也为 1），证明逐级增长，再实际应用上游 `geometric_weight_products_separated`。Fin→ℕ 的嵌入保持集合基数、乘积及最大差异位置。由此得到新接触定理所需的精确分离条件。

体积比实际化简为

\[
\frac{\prod_iw_i}{\prod_iv_i}=(w_0/v_0)\theta^m,
\]

且 `(1+σ)θ<1` 给出每个正坐标的 `(1+σ)w_i<v_i`。这些均是证明结果，没有作为额外前提输入。

`separated_distinct_multiplicative_interpolation` 随后调用已证明的真实次数/插值定理，结论正是 `SeparatedDistinctMultiplicativeInterpolationStatement`，包括先取下界、后取权重、R 先于全部中心、eventual n 阈值允许依赖中心的全部量词。

该模块使用较大的上游矩形 C_m(σ)。稿件以较小阶乘 C* 写出的显示阈值属于另一个数值细化，本模块未宣称认证它。
