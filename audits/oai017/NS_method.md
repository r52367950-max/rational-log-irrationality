# 借鉴 NS 的最终命题核验与可移植复查

本轮参考的是 `openai/NavierStokesAndEuler` 固定版本
`f9e8bc5b38b6e212696e8a30e3e91517af887bbd`，其 Comparator 固定版本为
`19e111e2141cf333c7daff0f64c5f24acc91dd2e`。其方法先完成真实 candidate，
再把实际证明适配到独立参考命题，最后比较定义与 theorem type、检查传递
axioms，并在空核环境重放证明。没有移植 PDE 专用结论，也没有重建 NS 工程。

本轮最终入口为 `RationalLogMain` 模块的
`RationalLogReview.Main.strict_rational_log_main`；独立参考定义为
`RationalLogReview.MainReference.StrictRationalLogMain`：

```lean
∀ r : ℚ, 0 < r → r ≠ 1 →
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
    ∀ p : ℤ, (q : ℝ) ^ (-ν) < |Real.log (r : ℝ) - (p : ℝ) / (q : ℝ)|
```

`Round2MainReference.lean` 不导入 solution，只定义目标，没有目标证明占位。
`Round2MainTypeChecker.lean` 另加载 reference-only 环境，比较整个目标定义图
与 kernel primitives，再检查候选完整类型和仅有标准三个 axioms。检查器随后
把目标传递依赖送入新的空 `Lean.Kernel.Environment`，由 stock kernel 重放
声明/证明，并核对 inductive constructors、recursors 与 Quot primitives。
`verify_round2_main.py` 只有在 guard 成功后才生成正常 kernel 检查的
`statement_certificate`，拒绝时不生成 type-error 恢复性证明。

在交付 Lean 工程根目录，使用正常的 elan/Lake 与工程固定的 Lean4.34.1、
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`：

```sh
lake exe cache get
lake build
python3 verify_round2_main.py --runner lake --project-dir . --prepare-checker \
  --module RationalLogMain \
  --theorem RationalLogReview.Main.strict_rational_log_main
```

portable runner 实际调用 `lake env lean -DautoImplicit=false`；使用工程自身的
工具链，不引用工作区绝对路径、兼容 shim 或 stock executable 的重命名路径。
`--prepare-checker` 为首次复查编译 reference/checker，已由 `lake build` 编译时
可以省略。`--output-dir /path` 可指定 logs/receipts；`--source File.lean` 可按
依赖顺序先严格重编译所列本地证明文件。现有 `.olean` 不能单独当作最终验收，
必须看到 receipt 的 `status=accepted`，类型、定义图、fresh replay 和正常
certificate 均通过。

拒绝机制的可复现对照：

```sh
python3 verify_round2_main.py --runner lake --project-dir . \
  --module RationalLogAsymptotic \
  --theorem RationalLogReview.Analytic.rational_log_endpoint_of_cofinal_interpolation \
  --expect-reject
```

它仍要求 `CofinalActualInterpolation r hr`，确实不能匹配无条件 reference。
此前也实际跑通 rational exact-representation theorem 的 16,341 常量空核重放。

本环境没有安装 `landrun`、`lean4export`、`nanoda_bin`、Comparator binary 或
Rust/cargo。因此这里是已实现的独立 reference 环境比较与 stock Lean fresh
kernel replay；不是声称运行了完整 sandbox/export Comparator 或独立 nanoda。
NS 固定版本使用 Lean4.34.0-rc2，与本轮4.34.1环境没有混用。

最终验收结果由 `verification/RationalLogReview_Main_strict_rational_log_main.receipt.json`
与对应 guard/certificate logs 记录；该文件的成功状态才是最终判据。

本轮最终实际结果为 **accepted，EXIT 0**：独立 reference 图 16,343 常量
全部相同；实际 Main 闭包 114,072 常量在新建空 kernel environment 中重放
ACCEPTED；Quot primitives postcheck 通过；另生成的
`statement_certificate : StrictRationalLogMain` 严格编译成功。完整类型与
reference 匹配，无额外 geometry/interpolation 假设。所有传递 axioms 只有
`propext`、`Classical.choice`、`Quot.sound`。`final-main-receipt.json` 是上述
成功 receipt 的逐字节副本，并固定本地 proof sources 与验证程序/logs 的 hashes。
