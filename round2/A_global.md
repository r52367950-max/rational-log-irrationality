# Theorem A：实际全局插值装配的核验与 Lean 证明

本轮已关闭此前的全局几何缺口。新增两个模块：

- `oai017/DistinctMultiplicativeGlobal.lean`：构造真实中心理想、紧化理想、实际全局截面到多项式的系数映射，以及多中心形式 jet 的比较。
- `oai017/DistinctMultiplicativeDegree.lean`：证明真实曲线模型存在、真实中心理想的局部长度、实际例外线丛与超平面线丛的次数公式，最后从数值权重假设得到实际插值。

二者均以 Lean 4.34.1、固定 mathlib 版本、`-DautoImplicit=false` 严格编译成功。没有 `sorry`、`admit`、新公理或修改上游原始证明正文。最后定理的 `#print axioms` 只输出 `propext`、`Classical.choice`、`Quot.sound`。

## 已证明的固定权重结论

公开定理为

```lean
OAI.PiExponent.DistinctMultiplicative.Degree.Weighted.
  eventual_interpolation_of_separated_weights
    w v hw hv K sigma hsigma hvol hseparated hratio
```

结论是原实际命题

```lean
EventualDistinctMultiplicativeInterpolation m K w v
```

参数 `w,v : Fin (m+1) → ℚ` 正，`sigma : ℚ` 正。三个数值假设是：

1. (K(1+3\sigma)^{m+1}\prod_i w_i/\prod_i v_i<1)。
2. 对等势集合 (A,B\subset\{0,\dots,m\})，若最高差异位置 (i\ne0\) 位于 (A\setminus B)，则上游已经证明的比较常数 (C_m(\sigma)) 满足 (C_m(\sigma)\prod_{j\in B}v_j<\prod_{j\in A}w_j)。
3. 对全部 (i=1,\dots,m)，((1+\sigma)w_i<v_i)。

这里没有额外纤维体积假设，也没有要求加法坐标族相异。不同中心只要求 (y_j\ne0) 且 (j\mapsto y_j) 单射。体积和有限集合比较条件取足够小的 σ 可以满足，存在量词由另一个 `DistinctMultiplicativeExistence.lean` 模块负责。

结论量词严格为：先选共同正整数 (R)，同时使 (R/w_i,R/v_i) 为正整数；然后对每一组上述中心 (y_j,c_j)，允许阈值 (N) 随该组中心而变；对所有 (n\ge N)，实际加权次数不超过 (nR) 的多项式空间，满射到实际新中心形式坐标下加权阶小于 (nR) 的 jet。共同 (R) 不依赖中心。

## 实际对象与证明

令 (e_i=R/v_i)。以截断对数 (G_i) 和 (T_i v_0>v_i)，定义中心 (j) 的坐标

\[
t_j=Y/y_j-1,\qquad
s_{ji}=X_i-c_{ji}-G_i(t_j),\qquad
I_j=(t_j^{e_0},s_{j1}^{e_1},\dots,s_{jm}^{e_m}).
\]

`Global.powerIdealAt` 起初通过代数自同构 `scaleY y_j` 的 comap 定义，随后真正证明它等于以上坐标幂的生成理想，亦等于旧理想沿 `scaleY y_j⁻¹` 的 map。根基是实际点 ((y_j,c_j)) 的点理想。因为 (y_j) 单射，各 (I_j) 两两互素。乘积 (I=\prod_j I_j) 在实际加权单项式射影紧化的仿射图上定义，再由理想层扩张为紧化上的实际理想层。支持严格为这些有限闭点，且完全位于仿射图。

取紧化超平面线丛 (L)，其次数标度由共同 (R) 定义。紧化为真正的积分、局部 Noether、proper 复概形；未假设光滑或正规。取实际吹起 \(\pi:B\to X\)，写

\[
A=\pi^*L,\qquad J=\mathcal O_B(-E),\qquad H=A^a\otimes J.
\]

标准 Rees 放大性证明给出 (a>1) 使 (H) ample。

对每条积分曲线 (C\subset B)，分三类。

1. 若 \(\pi(C)\) 为点，则 (\deg_C A=0)。由 (\deg_C H>0)，得到 (\deg_C J>0)，故 (\deg_C A+(1+\sigma)\deg_C J\ge0)。
2. 若 \(\pi(C)\) 不遇仿射图，则避开中心理想支持；实际例外线丛在 (C) 上有平凡 frame，故 (\deg_C J=0)。同样由 (H) ample 和 (a>0) 得到 (\deg_C A>0)。
3. 其余情形，由实际曲线像、吹起在支持补集的同构和实际曲线正规化，构造曲线函数域 (F)、生成它的仿射坐标 (z_0,\dots,z_m)、超越参数以及有限正规化态射。结构 `Degree.ModelData` 只储存这些对象和几何等式，没有次数不等式或插值断言字段；`Degree.exists_modelData` 实际证明该结构存在。

第三类的每个中心分支，以 (Y\mapsto y_j^{-1}Y) 归一化。实际原理想在分支 DVR 中的像恰好等于归一化截断对数理想：不是仅仅比较它们的阶，也不是输入一个理想相等假设。其他中心因乘法坐标的剩余值不同而成为单位理想。截断尾项满足严格权重界，因而

\[
\operatorname{length}(\mathcal O_p/I\mathcal O_p)
=\min_i e_i\operatorname{ord}_p(s_{ji})
=R\mu_j(p).
\]

这一等式为公开定理 `Degree.localIdealAt_length_eq_logContactAt`。经实际 ideal divisor 和 Euler characteristic 次数比较得到

\[
\deg_C J=-R\sum_{j,p}\mu_j(p).
\]

公开定理 `Degree.compactIdealAt_degree_eq_neg_contact_sum` 证明了正规化上的整型 Euler 次数等式；最终证明再通过有限双有理正规化不改变线丛次数的通用定理，转移到原积分曲线 (C)。超平面次数则由实际纯幂单项式图给出

\[
\deg_C A=R d_w(C).
\]

`DistinctMultiplicativeContact.weighted_curve_inequality_at` 已独立证明

\[
(1+\sigma)\sum_{j,p}\mu_j(p)\le d_w(C).
\]

其证明从真实辅助多项式、实际多中心导数字和比较引理开始；若出现过量接触，迫使 (z_0=y_{j_0})。此时 (y_j) 的单射性迫使全部中心分支位于同一中心，再化为普通加法坐标的单中心纤维估计。由此没有残留 `hμ`、导数消失假设、第二体积假设或真实接触的任意上界输入。

以上三类共同证明实际吹起上全部积分曲线满足

\[
\deg_C A+(1+\sigma)\deg_C J\ge0.
\]

公开定理 `Degree.Weighted.nonnegative_separated_curve_degrees` 已关闭 `Global.Weighted.NonnegativeSeparatedCurveDegrees`，它不再是最后主结论的前提。

数值放大性由 ample (H=aA+J) 与 nef (N=A+(1+\sigma)J) 的实际正组合给出：

\[
A+J=
\frac{\sigma}{a(1+\sigma)-1}H+
\frac{a-1}{a(1+\sigma)-1}N.
\]

得到 (A+J) ample，随后 Serre vanishing、实际吹起理想幂推前与高阶直像消失给出全部充分大 (n) 的实际 scheme jet restriction 满射。`Global.formalPackets_surjective_of_jetRestrictionAt` 以具体仿射系数映射和 CRT 转为实际 `formalJetAt` 的包满射；`Global.Weighted.eventual_section_supportBound` 实际证明截面系数的加权次数界 (nR)，不是从任意多项式表示满射假设获得。

因此固定权重定理的主结果只含规定的正性、体积、有限集合比较和坐标比值条件，不含全局截面满射、曲线次数界、contact 识别或一般化后的插值主结果假设。

## 验证命令

```sh
bash proof_review/oai017/check.sh --adapter DistinctMultiplicativeGlobal.lean
bash proof_review/oai017/check.sh --adapter DistinctMultiplicativeDegree.lean
```

二者最终 exit code 均为 0。Degree 有局部类型实例与无用 simp 参数的风格 warning，不影响核检查。四个最终 axioms 检查为：局部长度、全局例外次数、实际模型存在、固定权重实际插值，均只有上述三项标准公理。
