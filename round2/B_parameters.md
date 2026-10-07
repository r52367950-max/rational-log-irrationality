# B 的任意指数参数选择与最终逼近接口

2026-10-07。本轮模块：`oai017/RationalLogParameters.lean`；实际编译日志：`oai017/RationalLogParameters.check.log`。Lean 4.34.1、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。使用 `oai017/check.sh --adapter RationalLogParameters.lean`，退出码 0。24 个具名新定理全部逐一执行 `#print axioms`，仅依赖 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或新增公理。

## 已完成的存在性

`exists_fixed_parameters` 对**每一个实数 ν>2**、每一组固定正数 Λ、c、R₀≥1 和固定非负分母高度 ℓ，证明存在以下数据，而不要求提前提供期望的矛盾误差界：

- 原项目的有理数 θ、A、B、C 和实数 η，满足 θ<A<B<1、C>1、CB<1、Cθ/B>1、B/A>1，以及正的指数余量 `ν(A(1−η)−θ)−(1−θ)`；
- 正 ε、F₀，满足 ε 小于指数余量、ε≤1/2、F₀>2/θ、ν/F₀<ε/3；
- 一个足够大的**有限自然数 m≥1**，K=⌊C^m⌋≥1，有理 w₀=(B^m)⁻¹、v₀=2Kθ^m w₀，故 K(w₀/v₀)θ^m=1/2；
- 实际维数误差预算
  `(Λ F₀ m+2 log 2)/v₀ + (R₀ K+(K−1)ℓ)/w₀ < ε/3`，以及实际碰撞余量 `c η²Kθ^m/((m+1)v₀A^m)>2`；
- 一个正有理 σ，满足原 σ 扰动体积与权重条件。代码还保持可实现的较强条件 Kθ^m<1，便于复用原接口；这不把旧插值定理自动变成新 A。

存在性的主体直接调用固定 OAI017 源码的 `exists_parameters` 和 `exists_dimension_margin`。后者使用 (CB)^m→0、m/(Cθ/B)^m→0、(B/A)^m/(m+1)→∞，不是只验证一个 ν=3 的数值样例。

新增 `exists_dimension_margin_with_height` 在选择 m **之前**把容许误差除以 `max(1,R₀+ℓ)`，再调用原存在性定理。因此任意固定的底数高度被同一个 m 增长选择吸收；代码没有把“desired dimension margin”当作假设。

有理底数 r 的专用常数为：

`baseRadius r = 4(|log r|+1)+1`，`denominatorHeight r = log(r.den)`。

已证明前者大于 `4(‖log r‖+1)`，后者非负。`exists_rational_log_fixed_parameters` 对每个 r、每个 ν>2 给出参数存在性。这一步不需要 r>0 且 r≠1，因为它只选择数值参数；真实几何中心和主定理仍需要这两个条件。

## 无界坏逼近的实际顺次选择

`exists_selected_parameters` 接收一般实数 ω 的无界坏逼近假设

`∀Q∈ℕ, ∃p∈ℤ, ∃q∈ℕ, Q≤q ∧ |ω−p/q|≤q^(−ν)`。

它真实构造序列 p、q 和 w，其中 q_i≥2，w_(i+1)=⌈log q_i⌉，w₀=1；每一步在此前有限历史确定之后，选择下一分母超过当步阈值。代码不要求分母正密度、固定增长比或最终结论。因新 A 使用不同乘法坐标，选择过程也不要求 p_i≠0。

这些数据满足原放大的矩形重数常数所需的分离增长，以及一个共同最小权重 w* 和第三块误差预算

`Λ∑(1/w_i) + (θ+log4+log(2K)+ν+log(2R₀K))/w* < ε/3`。

`SelectedParameters.separated_weight_products` 直接复用原几何权重乘积比较；`rectangular_multiplicity_constant_bound` 使用原放大常数。它们并不认证稿件显示的较小 C* 阈值。

## 总误差和 H 极限

在选出的数据上定义三个真实误差表达式：

- arithmeticError：`ΛF₀m/v₀ + Λ∑1/w_i + θ/w* + (K−1)ℓ/w₀`；
- translationError：`ν/F₀ + log2/v₀ + (log4+log(2K)+ν)/w*`；
- holomorphicError：`R₀K/w₀ + log2/v₀ + log(2R₀K)/w*`。

`error_sum_eq` 核对它们等于三块参数预算的总和。`error_sum_lt_gap` 和 `collision_exceeds_error_sum` 由已构造的三块 ε/3 余量证明，无须 assembly 再假设它们。

`contradiction_of_eventual_bounds` 直接调用原 `asymptotic_determinant_bounds_inconsistent`。`contradiction_of_cofinal_bounds` 处理实数 H→∞，允许只在 A 给出的无界可整除次数类上选出非零子式，并允许平均指标和所选列随 H 改变。它需要由真实算术与解析 assembly 证明的输入为：

1. error(H)→0、collision(H)→本模块确定的碰撞极限；
2. 对每个 L，存在 H≥L 和实际归一化行列式值及平均指标，满足算术下界、解析上界及 0≤平均指标≤θ。

在这些输入下，代码选择同时超过两块极限阈值的 H，并调用原点态比较定理给出 False。没有用一个有限 H 的数值样例替代极限。

## 终点的精确边界

`strictBound_of_selected_contradictions`、`eventualLowerBound_of_selected_contradictions` 和 `exponent_two_of_selected_contradictions` 已将每个 ν>2 的实际选定数据矛盾接到稿件严格下界、**原项目** `EventualLowerBound` 与 **原项目** `irrationalityExponent = 2`。`rational_log_endpoint_of_selected_contradictions` 同时给出严格下界、无理性和 μ=2。

目前这些终点仍明确接收 `hcontra : ∀ν>2, SelectedParameters ... → False`。这不是新的公理，也不是已经完成对数主定理的宣称；它等待实际非零子式的算术/解析 assembly 和新 A 的全局几何满射，随后可由这些证明消去。参数存在性、实际顺次选取与数值余量已全部证明，无需未来用户再提供。

## 原始证明的可追溯复用

固定来源为 OpenAI `math` 提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`：

- [Approximation/Parameters.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Parameters.lean)：任意 ν>2 的有理参数及 η 选择；
- [LocalAlgebra/Dimension.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/Dimension.lean)：真实 floor K、体积、维数误差与碰撞增长存在性；
- [Approximation/WeightErrorMargin.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/WeightErrorMargin.lean)：共同最小权重预算；
- [Approximation/Comparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Comparison.lean)：点态和自然次数极限矛盾；
- [Approximation/Exponent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean)：无界逼近排除至原无理性指数。

一般 ω 的递归分母选择按原 `SuccessiveApproximations` 的构造扩展，并删去 π 特有的非零分子要求；它是本轮新的完整证明。上游源码仍按既有流程仅缩减 import 头部、保留数学正文。本轮没有修改上游证明，也没有重检完整原 Main。
