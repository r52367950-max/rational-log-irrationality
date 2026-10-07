# OAI September Navier–Stokes Lean：源码与验证流程审查

本轮参考的是独立仓库 `openai/NavierStokesAndEuler`，不是 October `openai/math` 中的 NS 计算性结果。2026-10-07 读取 `main` 后固定为 **`f9e8bc5b38b6e212696e8a30e3e91517af887bbd`**。递归 Git tree 完整，2673 个条目，`truncated=false`。本轮取回了 25 个关键文件，逐一计算 Git blob SHA-1，与该固定 tree 全部相符；记录见 `ns_millennium_meta/source-provenance.json`。

这里完成的是主命题、装配方法和核验程序的源码审查。**没有在本机完整构建 NS，也没有运行其 Comparator / nanoda；源码中的 `#print axioms` 命令不等于本次观察到的运行结果。** 原有 OAI017 的 Lean 4.34.1 / mathlib 环境与已验证模块保持独立。

## 实际主定理与接口

| 层次 | 固定版本源码与入口 | 实际承担的内容 |
|---|---|---|
| 独立参考命题 | `ComparatorChallenges/NavierStokes.lean:273`、`:280` | 两个 breakdown 命题的标准量词；其中 `sorry` 是 challenge 的待填证明，不能由 solution 引入。 |
| 独立定义 | `NavierStokes/ComparatorDefinitions.lean:191`、`:219`、`:236` | PDE、不可压缩性、初值、闭未来域光滑性，以及 R³ 的 L² / 统一能量条件或周期条件。该文件不导入 challenge。 |
| 已选具体构造 | `NavierStokes/ActualCandidateAssembly.lean:1153`、`:1177`、`:1183` | 从已证明的 finite-stage estimates、支持与端点条件得到 witness；固定实际 budget/threshold 后，导出无未完成构造假设的 `selected_candidate`。 |
| 全空间论文主定理 | `NavierStokes/R3/Theorem.lean:26`、`:46` | `theorem_1_1_with_initial_rest` 给出同一组 velocity/pressure/force/support 的全部性质，并排除同一强迫、同一零初值的全局光滑有限能量解；`theorem_1_1` 是 `breakdownStatement` 的无条件证明。 |
| 周期论文主定理 | `NavierStokes/PeriodicPaperTheorem.lean:155` | `periodic_corollary` 从全空间的实际 candidate 经压缩、periodization 和比较定理得到周期结论。 |
| 参考接口适配 | `NavierStokes/ComparatorR3Theorem.lean:38`；`NavierStokes/ComparatorTheorem.lean:47` | 从论文主定理获得真实 witness，再证明其满足 Comparator 的参考条件。 |
| 最终命名入口 | `NavierStokes/ComparatorSolution.lean:16`、`:24` | 在参考命名空间暴露两条同名 theorem，并附两个 `#print axioms`。 |

两个最终命题都是：对每个 `ν : ℝ`、`ν > 0`，存在光滑初始速度 `u₀` 与强迫 `f`，满足相应参考数据条件，而不存在满足相应条件的全局光滑速度/压力。R³ 的竞争解要求每个时刻 L² 可积且能量统一有界；周期版本要求速度与压力均空间一周期。构造选取零初值和非平凡的规定强迫。这些是源码中明确的 **forced** 结论，不应改述为零强迫的断言。

`NavierStokes/R3/ProblemStatement.lean:92` 的 `CandidateProperties` 同时包含：奇异前域上的光滑性、一个共同紧空间支集、全局光滑且正时间紧支集的 force、零初值、不可压缩、实际 NS residual 等式、`[0,1)` 上统一有限能量和时刻 1 的速度无界。`GlobalFiniteEnergySolution`（`:125`）的竞争解没有额外紧支集、周期性或压力增长假设。`breakdownStatement`（`:150`）先只是目标 `Prop`；在 `R3/Theorem.lean` 中才给出证明。这个区分是本次研究装配应遵守的范例。

## Comparator 实际怎样防止“只验证了弱接口”

该仓库 `ComparatorChallenges/NavierStokes.json` 固定：

```json
{
  "challenge_module": "ComparatorChallenges.NavierStokes",
  "solution_module": "NavierStokes.ComparatorSolution",
  "enable_nanoda": true,
  "theorem_names": [
    "NavierStokes.Comparator.navier_stokes_breakdown_R3",
    "NavierStokes.Comparator.navier_stokes_breakdown_periodic"
  ],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

其 manifest 固定 Comparator **`19e111e2141cf333c7daff0f64c5f24acc91dd2e`**。本轮另取回该版本的 README、Main、Compare、Axioms 四个文件，也全部通过 Git blob 校验。

1. 独立构建并导出 challenge 和 solution 环境，而非让 solution 直接利用 challenge 中的占位 theorem。
2. `Comparator/Compare.lean:67` 检查目标 theorem 的 kind、类型、universe 等 `ConstantVal` 一致；还递归检查类型涉及的定义一致（`:37`）。所以换定义、加隐藏假设或弱化目标，不能仅靠同名 theorem 蒙混通过。
3. `Comparator/Axioms.lean:23` 遍历 solution 的传递依赖；`:43` 拒绝非白名单 axiom。challenge 里的 `sorryAx` 因而不能进入已接受 solution 的证明依赖。
4. `Main.lean:279` 先比较声明、检查 axioms，然后调用外部核与内置 Lean 核。`runBuiltinKernel`（`:211`）由导出的常量重新 replay 环境，并检查 quotient primitives；不是只相信一个现成 `.olean`。
5. NS 配置 `enable_nanoda=true` 还要求 nanoda 独立核核验。源配置没有定义洞 `definition_names`，目标定义必须与参考环境相符。

这是一套指定信任边界的核验方法，不能由配置文件本身推断已成功执行。Comparator README 还要求可信 reference/config、适用的隔离工具和导出器，以及未受解答构建污染的核验环境；本轮没有模拟绕过这些要求的检查。

## 对 A/B 形式化的可用方法

可直接参考的是**证明装配方法**，不是 PDE 专用定理：

- 用真实数学对象定义最终 A/B 命题。曲线、局部 ideal、global sections、formal coefficients、实际有理近似应有确定类型，不能用一个未证明的接口常量取代主结论。
- 中间 theorem 可以接受明确的局部/几何假设；最终无条件主 theorem 必须从具体构造和已验证性质逐项消去它们。NS 的 `selected_witness → selected_candidate → theorem_1_1 → ComparatorSolution` 正是这种装配。
- 接口转换必须证明：NS 证明时空变量交换、黏性缩放、initial-boundary 光滑性、全阶 force 衰减；我们的对应义务是 arbitrary-y 局部 compact ideal、CRT packets、weighted global sections、支撑度控制、真实 translated matrix 与渐近 determinant 估计之间的类型和数值等式。
- 对剩余主命题使用独立 reference 声明，核验完整的命题类型及其传递 axioms。仅给一个 `of_geometry` / `of_interpolation` theorem 的 `#print axioms`，只能证明该条件定理；不能表明其几何输入已经构造。
- 审查主定理前实际展开它的定义。尤其需查是否多了 weight separation、统一曲线 margin、jet compatibility、或因 `autoImplicit` 创建的额外参数。当前新代码保持 `autoImplicit=false`，逐模块严格检查。

本轮没有发现应移植到代数几何/Diophantine 核心的 NS 专用 lemma。通用的滤子极限、求和、导数与估计基础应使用我们已固定的 mathlib；PDE 的 candidate/viscosity/periodization/energy 比较 theorem 的类型与 A/B 不相符，不能硬套。

## 如需独立复查 NS 的精确环境

`lean-toolchain` 固定 `leanprover/lean4:v4.34.0-rc2`；manifest 固定 mathlib **`85e3a25e006c35636f0e53b0e9296caca2685bc0`**、Comparator 上述 SHA、lean4export **`cacf989bd75f608700820f6afc595f32e7a99a4d`**。不与目前 OAI017 的 4.34.1 oleans 混用。

可信的新 checkout 固定 NS SHA 后，官方 README 的流程是 `lake exe cache get`、`lake build`，随后按 Comparator README 安装合适的 `landrun`、`lean4export`、`nanoda_bin` 并运行 `lake exe comparator ComparatorChallenges/NavierStokes.json`。Comparator 本身 README 进一步说明可信检查所需的系统隔离调用方式。这里记录流程，未执行整库重检。

## 固定 primary source 链接

- [NS 仓库固定版本](https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd)
- [最终提交命题](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ComparatorSolution.lean)
- [全空间真实主定理](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/Theorem.lean)
- [实际 candidate 装配](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ActualCandidateAssembly.lean)
- [独立参考挑战](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/NavierStokes.lean)
- [Comparator 固定版本的可信核验说明](https://github.com/leanprover/comparator/blob/19e111e2141cf333c7daff0f64c5f24acc91dd2e/README.md)
- [Comparator 实际校验程序](https://github.com/leanprover/comparator/blob/19e111e2141cf333c7daff0f64c5f24acc91dd2e/Main.lean)

本地可审计材料在 `ns_millennium_source/`、`ns_comparator_source/`、`ns_millennium_meta/`。原始 source bytes 保留；`source-provenance.json` 逐文件列出 SHA-256 与固定 tree 的 Git blob SHA-1。

## 本轮已执行的对应检查

没有重建 NS；我们建立了 `../oai017/Round2MainReference.lean`、
`Round2MainTypeChecker.lean` 与 `verify_round2_main.py`。参考命题单独从 stock
mathlib 对象定义，无 solution import、无主命题证明占位。检查器另加载仅 reference
的环境，比对声明定义图，再拒绝任何仍需 geometry 假设的主 theorem。

已经实际对一个已证明的 rational exact-representation theorem 执行空 Lean kernel
environment 重放，16,341 constants 全部 ACCEPTED，Quot postcheck 通过。
条件 B 的 `rational_log_endpoint_of_cofinal_interpolation` 经独立 reference 图比对
后明确被 FINAL_TYPE_MISMATCH 拒绝，原因是仍有 CofinalActualInterpolation 输入。
这项成功拒绝不是 B 无条件主定理已证明的证据。

之后完成的无条件 `RationalLogReview.Main.strict_rational_log_main` 已实际通过
完整流程，guard 与独立 statement certificate 均 EXIT 0：reference 定义图
16,343 常量匹配；实际证明/类型闭包 114,072 常量在新建空 stock kernel
environment 重放 ACCEPTED；Quot primitives postcheck 通过；完整类型没有
额外 geometry/interpolation 输入，传递 axioms 仅标准三个。最终 receipt 与
固定源码/log hashes 在 `../oai017/final-main-receipt.json`。这仍不是已运行
完整 sandbox/export Comparator 或 Nanoda 的声明。

完整 commands、范围与 receipts 见 `../oai017/ROUND2_INDEPENDENT_CHECK.md`。
它使用真实的 stock kernel replay，但不声称运行了 unavailable nanoda 或完整
sandbox/export Comparator。
