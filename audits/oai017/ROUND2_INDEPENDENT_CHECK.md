# Round 2 最终命题独立检查

`Round2MainReference.lean` 只使用 stock mathlib 定义以下目标，不导入 solution，
不声明其证明，也没有 `axiom` / `sorry`：

```lean
∀ r : ℚ, 0 < r → r ≠ 1 →
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
    ∀ p : ℤ, (q : ℝ) ^ (-ν) < |Real.log (r : ℝ) - (p : ℝ) / (q : ℝ)|
```

`Round2MainTypeChecker.lean` 参考固定 Comparator 的实际 `compareAt`、
`checkAxioms`、`runBuiltinKernel` 方法：

1. 单独导入仅含 reference 的环境，比较目标涉及的整个常量定义图及官方
   Comparator 的 kernel primitive 列表与当前 solution 环境一致。
2. 比较候选 **整个 theorem type** 与 reference 定义相等；不自动应用
   geometry、interpolation、determinant 等额外参数。
3. 检查传递 axioms 只含 `propext`、`Classical.choice`、`Quot.sound`。
4. 收集目标证明/类型的全部常量依赖，补全 mutual inductives、constructors 和
   recursors，在新建空 `Lean.Kernel.Environment` 中 `replay`；核对新生成的
   Quot primitives 与原始常量一致。该步骤重新核验存储的 proof terms。
5. 上述 guard 全通过后，另编译 `statement_certificate : StrictRationalLogMain`
   并保存类型检查、kernel replay、axioms、源码/log hashes 的 receipt。

最终无条件 theorem 已实际完成验收：

- `RationalLogReview.Main.strict_rational_log_main` 的完整类型与独立
  `StrictRationalLogMain` 匹配；没有额外 geometry 或 interpolation 输入。
- reference-only 环境与 solution 环境的 **16,343 constants** 定义图相同。
- 从新建空 kernel environment 重放 **114,072 constants**，实际结果
  `FRESH_KERNEL_REPLAY_ACCEPTED`；Quot、Quot.mk、Quot.lift、Quot.ind
  的 postcheck 全部通过。
- guard 与独立 `statement_certificate` 均严格编译 EXIT 0，传递 axioms
  只有 `propext`、`Classical.choice`、`Quot.sound`。

完整成功记录是 `final-main-receipt.json`，与
`verification/RationalLogReview_Main_strict_rational_log_main.receipt.json`
逐字节相同。它记录最终 Main、实际本地依赖源码、reference/checker/validator
以及 guard/certificate logs 的 SHA-256。原 OAI 的完整 Main 没有重建；最终
新证明的原 OAI source import 闭包为 845 modules，全部已有实际编译产物。

工作区运行方式：

```sh
./check.sh --adapter Round2MainReference.lean Round2MainTypeChecker.lean
python3 verify_round2_main.py \
  --module RationalLogMain \
  --theorem RationalLogReview.Main.strict_rational_log_main
```

可用 `--source File1.lean --source File2.lean` 按拓扑顺序先重新严格编译本地
solution files。所有检查使用现有共享单进程 wrapper 和 `autoImplicit=false`。
交付工程的可移植运行方式见 `NS_method.md`；`--runner lake --project-dir .`
直接使用工程固定工具链，不依赖本工作区的绝对路径。

另已执行的对照检查：

- `Round2ReplaySmoke.lean` 将已存在的 rational exact-representation theorem
  的 **16,341 constants** 闭包送入空 stock kernel，结果 ACCEPTED，Quot
  postcheck 通过，axioms 为标准三个。它不是 B 主命题的证明。
- `verify_round2_main.py --module RationalLogAsymptotic --theorem
  RationalLogReview.Analytic.rational_log_endpoint_of_cofinal_interpolation
  --expect-reject` 确实拒绝当前条件 theorem。其完整类型仍要求
  `CofinalActualInterpolation r hr`，所以不匹配无条件 reference。
- 旧 `rational_logarithm_endpoint_from_manuscript_bound` 也被同一 guard 拒绝：
  它把 strict lower bound 作为输入，并不是该 bound 的无条件证明。

结果位于 `verification/*.receipt.json` 与对应 logs。拒绝时只编译 guard，
不生成一个 type-error 恢复性 certificate。

此环境没有 `landrun`、`lean4export`、`nanoda_bin`、Comparator binary，
也没有 Rust/cargo。本流程因此 **不是已运行的完整 sandbox/export Comparator，
也不是独立 nanoda kernel**；它实际执行独立 reference 环境比对和 stock Lean
空核环境的证明重放，诚实记录这一信任范围。工具链和 stock mathlib pins
仍是 ENVIRONMENT.md 的 Lean4.34.1 / d13f23b...。
