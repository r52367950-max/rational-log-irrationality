# OAI017 最后几何步骤的实际源码复用检查

检查对象：`https://github.com/openai/math` 的固定 commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`，本地原始 `OAI/NumberTheory/PiExponent/`。重点检查 `Ampleness/BlowupJetSurjectivity*.lean`、`GlobalBlowupJetSurjectivity.lean`、`NumericalAmplenessTheorem.lean`、`BlowupCurveMargin.lean`、`BlowupAmpleTwist.lean`、`Jets/AdmissibleJetSurjectivity.lean`、`Jets/JetGeometry.lean` 与局部多项式接口。原始文件未修改。

## 1. 决定性结论

**可以直接复用实际普通吹起上的“丰沛性 ⇒ 理想喷射最终满射”定理；该定理本身没有把乘法坐标固定为 1。** 它的输入是任意适当概形、任意理想层以及实际构造出的线丛，并非一个抽象 `JetEngine` 类。

`Ampleness/BlowupJetSurjectivityComplete.lean` 的最终定理是：

```lean
theorem eventual_blowup_jetRestriction_surjective
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n)
```

这里 `X : Scheme.{0}`，`R` 是 Noether 环；`I` 未附带特殊中心假设。`blowupBundle I A` 是原始普通 Rees 吹起上的 `O(-E) ⊗ p* A`。目标是实际 `I^n` 的闭子概形商模上的全局截面，结论不是形式符号上的假定满射。

较早的 `GlobalBlowupJetSurjectivity.lean` 仍要求 eventual `CechH1Transfer.SectionComparison`。**不能只引用这个早期版本并漏掉比较条件。** `BlowupJetSurjectivityComplete.lean` 已用 `GlobalReesCanonicalRecovery` 消除了该外加条件。因此复用最终版本可以省去重新形式化手稿 A 第 5 节专用的 Čech 计算，但不能省去实际中心理想与丰沛性的构造。

## 2. 从曲线不等式至丰沛性的复用

`NumericalAmplenessTheorem.isAmple_of_uniform_curve_margin` 接受任意适当复概形、实际丰沛线丛 `H`、实际线丛 `L`、同一个 `ε > 0`，以及

```lean
∀ C : IntegralCurve X,
  ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)
```

然后证明 `L.IsAmple`。这里没有中心坐标或 `AdmissibleParameters`。单纯逐条曲线正度数不能直接代替这个假设；手稿 A 的带 `σ` 曲线不等式恰好可以提供统一 margin。

`BlowupCurveMargin.margin_of_nonnegative_degree` 同样是通用实际线丛定理。给定 `a > 1`、`σ > 0`、`((A.pow a).tensor J).IsAmple` 和

```lean
0 ≤ (curveDegree p A C : ℝ) +
  (1 + σ) * (curveDegree p J C : ℝ)
```

它证明

```lean
marginCoefficient a σ * degree(A^a ⊗ J) ≤ degree(A ⊗ J)
```

其中 `marginCoefficient a σ = σ / (a * (1 + σ) - 1)`，源码也证明了其严格正性。`BlowupAmpleTwist` 又给出实际普通吹起的 `a > 1` 丰沛 exceptional twist；使用它时需满足基概形 integral、locally Noetherian、compact，且中心理想支撑不是整个基概形。适当 integral 复紧化与有限中心满足这些要求。

## 3. 已写出的实际适配器

新文件 `DistinctMultiplicativeAmple.lean` 包含以下三个证明，不添加公理或 `sorry`，且调用的是上述原始实际概形定理：

1. `eventual_jetRestriction_surjective_of_uniform_curve_margin`：统一曲线 margin ⇒ 实际普通吹起丰沛 ⇒ 实际 `I^n` 喷射最终满射。
2. `eventual_jetRestriction_surjective_of_nonnegative_curve_degree`：输入 proper integral 复概形 `X`、实际理想层 `I`（支撑非全体）、丰沛 `A`、`σ > 0` 以及所有普通吹起曲线上的 `degree(p*A)+(1+σ)degree(O(-E)) ≥ 0`。证明中自动选择 `a > 1` 的丰沛 twist，计算统一 margin，应用数值丰沛性，使用实际 tensor-commutation 同构，再调用最终喷射定理。
3. `formalCoefficientPackets_surjective_of_jetRestriction`：把原始理想喷射的实际截面目标连接到同时形式系数包。它接受明确的满射源表示 `P`、明确的满射局部商表示 `q` 和明确的交换方块等式 `hcompat`，再直接应用原始 `JetGeometry.rationalCoefficientPackets_surjective_of_coordinatePowerIdeal`。`f : α → J → MvPowerSeries ι ℂ` 完全任意，因此可代入不同的 `y_j` 的实际形式展开。

这些适配器的声明保留数学几何对象，没有用只包含若干数值量与满射字段的自定义引擎替换问题。第二个适配器特别形式化了手稿 A 第 7 至第 8 节的几何推导，而非最终定理的改名。

**实际编译完成。** 原始几何依赖最终构建显示 `Build completed successfully (5288 jobs)`，随后运行 `check.sh --adapter DistinctMultiplicativeAmple.lean`，以 Lean 4.34.1 和 `autoImplicit=false` 严格检查，退出码为 0，并生成实际的 `DistinctMultiplicativeAmple.olean`（116256 字节）。三个定理逐项 `#print axioms` 均且仅列出 `[propext, Classical.choice, Quot.sound]`，没有 `sorryAx` 或新增公理。日志分别为 `toolchain/oai-ag-complete-build.log` 与 `DistinctMultiplicativeAmple.check.log`。

归档的固定 commit 原始文件保持不变。编译工作副本把 umbrella import 行换成显式 Mathlib 导入的 `SupportCore`，并按编译错误补充个别 stock import；所有声明与证明正文保持原样。构建变更及其最终数量记录于 `import-header-patches.json`，需与“逐字原始导入头部编译”区分。编译成功的是上述三个带明确几何与表示假设的适配定理；尚未完成整个不同中心 Theorem A 的形式化。

实际依赖规模：这四个几何根模块的原始 OAI 传递导入闭包为 693 个模块，另直接涉及 192 个不同 Mathlib 导入根。对这 693 个原始模块扫描 `axiom`、`opaque`、`sorry`、`admit`，没有命中；这是源码筛查结果，不能代替编译与 `#print axioms`。故与只编译少量形式幂级数适配器相比，完整几何适配器的编译需要建立更大一部分原始开发。

## 4. 固定乘法坐标的边界

以下高层已完成接口确实固定乘法坐标为 1，不能对任意不同 `y_j` 原样调用：

- `Jets/AdmissibleJetSurjectivity.lean` 接受 `d : AdmissibleParameters ν Λ D`；它自动构造的是 `AdmissibleBlowupGeometry.centerIdeal d`，不能把新中心直接塞进 `d.curveCenters`。
- `FormalLogJet.formalJet c` 的 `Y` 像明确是 `1 + X 0`；加法坐标像是 `C(c_i) + X_i + formalLog`。
- `CompactJetPolynomial.center c = Fin.cases 1 c`；其 pure-power ideal 与整个 `CompactLogJetIdeal` 的包裹层均以此为中心。
- `AffineJetPackets.formalJet_packets_surjective` 要求加法中心数组 `c` injective，并在同一 `Y = 1` 上构造 CRT；新定理允许全部 `c_j` 相等，仅靠 `y_j` 区分中心，所以这里的 `hc` 不成立。
- `AdmissibleBlowupMargin.contactSum`、`poleDegree` 以及自动生成的 `AffineCurveDegreeData d` 仍围绕原始参数数据，不能自动代表手稿 A 的不同乘法中心。

相反，`AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction` 是通用 `Spec R` 仿射开图定理。它接受任意 `J : Ideal R`、`I.comap j = specIdeal J`、支撑位于该仿射图和线丛框架，就把实际截面喷射满射变成 `R / J^n` 的满射。因此这段可以复用，局部中心和不同 `y` 的 CRT 是需要接上的部分。

## 5. 对完整 Theorem A 尚未核验的精确义务

最终源定理复用之后，仍必须对新中心实际证明：

- 用 `Y/y_j - 1` 与 `X_i-c_{ji}-log_T(Y/y_j)` 构造多项式纯幂理想、紧化理想层 `I` 与有限支撑；建立局部理想同构并处理非零 `y_j`。
- 证明所有普通吹起曲线上的 degree 不等式；关键是手稿 A 的新曲线接触总和、不同乘法中心唯一性以及实际 exceptional/hyperplane degree 比较。适配器将这项写作显式 `hn`，没有把它伪装成已证结论。
- 从紧化全局截面得到符合 `W` 权重预算的实际多项式，并把喷射限制与 `P(y_j(1+t),c_{ji}+u_i+log(1+t))` 的多中心同时形式展开建立交换等式。
- 不同 `y_j` 的局部商同时表示与 CRT。可以按各中心缩放 `Y` 把**单中心局部**问题转到原始 `Y=1`，但不能用一个全局缩放把多个不同 `y_j` 同时都变成 1。

因此，实际源码提供了强于从零重建的通用几何尾段。完整新定理的 Lean 证明仍取决于这几项具体适配；已有 `AdmissibleJetSurjectivity` 对原始特殊中心的证明，不是新定理的证明。
