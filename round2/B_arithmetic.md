# Theorem B：实际有理底数矩阵的算术下界与非零 minor 接口

本轮文件直接复用固定版本 OAI017 的 `MatrixArithmetic`、`Arithmetic`、
`FormalMatrixBridge`、`FormalJetIndices` 与 `InterpolationMatrix`。
没有新设 `axiom`，没有 `sorry`，没有把目标行列式估计当作输入。
编译与公理依赖以同目录 Lean 检查日志为准。

最终严格检查：算术文件 6 条定理、packet/matrix 接口文件 10 条定理，
共 16 条均成功，零错误、零警告。所有 `#print axioms` 仅列出
`propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`。
两文件的 `.olean` 已由 Lean 4.34.1 生成，mathlib 固定于
`d13f23b723b8a846827a245b89c10fc7d3f11612`。

## 实际矩阵和清分母

设有理底数为 (r=A/B)，其中 (A,B\in\mathbb Z)、(B>0)。
第 (j) 个中心是 (y_j=r^j)。列单项式为 (Y^hX^\alpha)，
行系数为 (t^s u^\beta)。实际矩阵项是

\[
 [t^s u^\beta],
 \{y_j(1+t)\}^{h}
 \prod_i\{j p_i/q_i+u_i+L_{T_i}(t)\}^{\alpha_i}.
\]

`centeredSelectedMinor` 正是这些项组成的选择方阵，而非一个抽象满足下界的矩阵。
记 (w_i=\lceil\log q_i\rceil)、(e_i=\lfloor H/w_i\rfloor)。
原 `column_coordinate_le_floor` 给出实际列的 (\alpha_i\le e_i)。
取

\[
 D_H=\prod_i\operatorname{lcm}(1,\dots,T_i)^{e_i},\quad
 R_\beta=\prod_i q_i^{-\beta_i},\quad
 C_{h,\alpha}=B^{(K-1)h}\prod_i q_i^{\alpha_i}.
\]

此前实际项清分母适配器证明 (D_H R_\beta C_{h,\alpha} A_{\rho,c}\in\mathbb Z[i])。
额外底数因子的理由是精确恒等式

\[
 B^{(K-1)h}(A/B)^{jh}
   =A^{jh}B^{(K-1-j)h}\qquad(0\le j<K),
\]

不能将 (y_j^h) 当作独立于列的行因子移出矩阵。
只要实际选择方阵的行列式非零，原高斯整数行列式定理即给出

\[
 \log|\det A|\ge -M\log D_H
   -\sum_c\sum_i\alpha_{c,i}\log q_i
   -\sum_c (K-1)h_c\log B
   +\sum_\rho\sum_i\beta_{\rho,i}\log q_i.
\]

这在 `centeredSelectedMinor_clearing_bound` 中逐项由实际矩阵得出。

## 规范化误差，没有遗漏底数高度项

当 (T_i=\lceil Fw_i/v_0\rceil) 时，上游原始 `log_denominator_le` 证明

\[
 \frac{\log D_H}{H}\le
 C_{\mathrm{lcm}}\frac{Fm}{v_0}
 +C_{\mathrm{lcm}}\sum_i\frac1{w_i},
 \qquad C_{\mathrm{lcm}}=\log4+4.
\]

这是原代码可用的较宽 lcm 界，不是稿件中的 (4\log2)；
参数选择必须使用这个实际常数。稿件若坚持较小常数，需要另证更强的 lcm 估计。

列的预算 (w_0h+\sum_i w_i\alpha_i\le H) 给出

\[
 \sum_c\sum_i\alpha_{c,i}\log q_i\le MH,
 \quad
 \sum_c(K-1)h_c\log B\le MH\frac{(K-1)\log B}{w_0}.
\]

这里 (B\ge1) 从正整数性得到，故 (\log B\ge0)。
行的原始预算与 (\log q_i\le w_i<\log q_i+1) 给出

\[
 \sum_\rho\sum_i\beta_{\rho,i}\log q_i
 \ge MH b_H-MH\frac\theta{w_*},\qquad
 b_H=\frac1{MH}\sum_\rho\sum_i w_i\beta_{\rho,i},
\]

其中 (0<w_*\le w_i)。所以实际行列式满足

\[
 \frac{\log|\det A|}{MH}\ge -(1-b_H)-E_{\rm ar},
\]

\[
 E_{\rm ar}=
 C_{\mathrm{lcm}}\frac{Fm}{v_0}
 +C_{\mathrm{lcm}}\sum_i\frac1{w_i}
 +\frac\theta{w_*}
 +\frac{(K-1)\log B}{w_0}
 \le C_{\mathrm{lcm}}\frac{Fm}{v_0}
 +\frac{C_{\mathrm{lcm}}m+\theta}{w_*}
 +\frac{(K-1)\log B}{w_0}.
\]

Lean 端点是 `centeredSelectedMinor_arithmetic_lower_bound` 与
`centeredSelectedMinor_arithmetic_lower_bound_common_error`。
它们只要求实际行列式非零、基本权重正性及明确的底数分母。

在 (H\to\infty) 时其余参数固定。上述算术误差并不随 (H) 自动消失。
必须在选定 (K,F) 后通过足够大的 (v_0,w_0,w_*) 将它控制到允许误差；
特别不能丢弃固定的 ((K-1)\log B/w_0)。若 (B=1)，该项确实为零。

## 从实际 A packet 满射得到非零方阵

`RationalLogMatrixBridge.lean` 从本项目已有的真实
`DistinctMultiplicative.formalJetAt` 与 `packetMapAt` 出发。

1. `scaleY_monomial` 精确证明 multiplicative-center 伸缩把每个单项式乘以 (y^h)。
2. `centeredEntry_eq_coeff_truncatedFormalJetAt` 和
   `centeredMatrix_mulVec_eq_coeff` 识别上面的实际有限矩阵与截断 formal jet 的各系数。
3. `centered_formal_packets_surjective_iff_truncated` 复用原 formal-log tail 的统一
   `shiftEquiv` 与加权理想保持性，得到真实 formal packet 满射和截断 packet 满射的等价。
   multiplicative 伸缩 (y_j) 在每一行保留在实际多项式内部。
4. `centeredMatrix_surjective_of_rational_packets` 复用原
   `rationalJetIndexEquiv` 和 `polynomialOfCoefficients_of_weighted` 将 packet 满射转成有限矩阵线性映射满射。
5. 原 `exists_full_row_minor_of_surjective` 给出一个 injective 列选择及非零行列式。
   这并未把“存在非零 minor”另设成假设。

有限矩阵端点 `rationalBase_nonzero_centeredSelectedMinor` 消费实际
`packetMapAt` 的满射，返回上述算术下界所需的同一个实际
`centeredSelectedMinor` 非零行列式。
`truncationOrders_satisfy_packet_weight` 进一步从 (1\le F\theta)、
正权重及原 ceiling 定义证明等价转换需要的

\[
 V_i\le T_i V_0,
 \qquad V_0=v_0,quad V_i=w_i/\theta.
\]

综合端点 `actualPacket_exists_arithmetic_minor` 从实际 packet 满射和上述基本正性、
(1\le F\theta) 出发，直接返回 injective 列选择、实际非零行列式与 common-error 算术下界。
它的输入中没有行列式非零假设，也没有目标下界假设。

这条接口证明是有限维代数与精确 formal-jet 转换；它本身没有证明 A 的最终几何满射定理。
在完整 B 的应用中，满射由 A 的实际 `packetMapAt` 定理提供，后续解析上界与渐近归一化则由
`RationalLogAsymptotic.lean` 组装。不能把这个接口单独称为 A 或 B 主定理的证明。

## 可复现文件

- `oai017/RationalLogArithmeticAssembly.lean`：实际清分母、规范化下界与 common-error 界。
- `oai017/RationalLogMatrixBridge.lean`：实际 packet→finite matrix→非零 selected minor。
- `oai017/RationalLogRound2.check.log`：`-DautoImplicit=false` 两次成功检查合并日志和每条定理公理依赖。
- 命令：`./proof_review/oai017/check.sh --adapter RationalLogArithmeticAssembly.lean RationalLogMatrixBridge.lean`。

原始 OAI017 文件保留，适配器只添加新文件。所有原代码定理身体均保持原样；
工作副本仅采用已经审计过的最小化 import 头以降低编译内存。

## 后续补齐：选定参数直接满足 A 的数值假设

`RationalLogGeometryParameters.lean` 再增加 14 条严格核验的引理，
零错误、零警告、公理依赖同样只有上述标准三项。
它直接将新增高度项已经纳入的 `SelectedParameters` 接到原 OAI017
`Geometry/AdmissibleCurveWeights` 的具体权重证明；没有假设 A 的结论。

在命名空间 `RationalLogReview.GeometryParameters` 中，

\[
 W=(w_0,w_1,\ldots,w_m),\qquad
 V=(v_0,w_1/\theta,\ldots,w_m/\theta),
\]

所有尾部权重来自实际已选分母的 (w_i=\lceil\log q_i\rceil)。
`sourceWeights`、`targetWeights` 与解析组装的 `ofSelected` 权重定义相同。
它证明：

- `sourceWeights_pos`、`targetWeights_pos`：实际两组有理权重均为正。
- `curve_product_ratio`、`curve_fibre_product_ratio`：全维及纤维乘积比精确为
  ((w_0/v_0)\theta^m) 和 (	heta^m)。
- `curve_volume`、`curve_fibre_volume`：A 使用的膨胀单纯形体积严格小于 1，
  直接来自已经构造的 `sigma_volume` 与 `sigma_centers`。
- `curve_coordinate_ratio`：((1+\sigma)W_i<V_i) 对每个尾坐标成立。
- `curve_separated_weight_products`：把原自然数序号的 successive separation
  转为 Contact 的精确 `Finset (Fin (m+1))` 比较假设；比较常数与实际源码完全一致。

因此，上游固定权重的 A 几何证明所需的数值输入全部由真实
`SelectedParameters` 提供，无需额外假设体积、坐标比或有限集合分离。
这些数值引理仍须与固定权重 A 的实际几何定理组合，才能给 B 提供最终 packet 满射。

检查命令：`./proof_review/oai017/check.sh --adapter RationalLogGeometryParameters.lean`；
日志：`oai017/RationalLogGeometryParameters.check.log`。
