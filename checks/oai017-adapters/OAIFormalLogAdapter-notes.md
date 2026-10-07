# OAI017 实际矩阵系数与有理底数适配

适配文件：`OAIFormalLogAdapter.lean`。

工具链：原项目 Lean 4.34.1；mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。

原始 OAI 源码保存在 `source/`，另在 `working/` 建立构建副本。构建副本只把原来的 `import Mathlib` 全库头替换为所需模块集合 `SupportCore`；原有定理正文未改。这减少每个 Lean 进程的内存占用。完整原文与来源校验记录独立保留。

本文件直接导入原始 `OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation` 和 `MatrixArithmetic`，并使用其 `InterpolationMatrix`、`RowTranslation`、`Arithmetic` 原始定义和定理。没有把行公式、尾项预算或算术下界作为新公理。

## 实际复用对应

| 原始 OAI 定义或定理 | 本适配的实际用途 |
|---|---|
| `InterpolationMatrix.monomialImage`、`entry` | 给原矩阵加入逐行、逐列指数相关的乘法中心因子，证明实际多项式系数等于 `y^h * entry` |
| `MatrixTranslation.periodMonomial_shift` | 证明 `Y=y(1+t)` 的真对数单项式经过原平移后，恰好成为截断对数单项式 |
| `RowTranslation.exact_row_identity` | 证明 Theorem B 式 (5) 的有限系数展开 |
| `MatrixTranslation.det_dependent_row_sum` | 证明实际有理底数矩阵的行列式展开，保留所有 `y(row)^h(column)` |
| `MatrixTranslation.periodMonomial_support_subset` | 证明同一个权重单纯形控制新增乘法中心后的横向单项式支集 |
| `RowTranslation.rowScalar_ne_zero_le`、`tail_budget_nat` | 非零展开项必满足 `β ≤ A` 和 `∑ d_i T_i ≤ k` |
| `Arithmetic.shifted_truncation_product_coeff_gaussian` | 把原稿的虚有理中心改成实际实有理中心 `j*p_i/q_i`，完成实际矩阵项的分母清除 |
| `Arithmetic.cleared_det_log_bound_with_denominator` | 对字面实现的 `centeredRationalMatrix`，从上述清除定理推出原始形式的 `log‖det‖` 算术下界 |

## 与 Theorem B 的对应

`centeredMonomialImage` 是以下替换的字面实现：

\[
Y^h X^a\mapsto[y(1+t)]^h\prod_i[jr_i+G_i(t)+u_i]^{a_i}.
\]

`centeredEntry` 就是其 \([t^s u^\beta]\) 系数。`rational_power_entry`、`rational_power_entry_translation` 取 \(y=R^j\)、\(R,r_i\in\mathbb Q\)，给出稿件采用的实际中心。

`rational_base_column_scale` 对 \(R=A/B\) 及 \(j<K\) 证明：

\[
B^{(K-1)h}\cdot\mathrm{centeredEntry}
=A^{jh}B^{(K-1-j)h}\cdot\mathrm{OAIEntry}.
\]

这证明了新增底数的分母高度因子确实作用于实际矩阵系数。

`real_rational_entry_cleared_gaussian` 证明实有理近似中心的原项在共同对数截断分母和 `q_i` 行列缩放后属于高斯整数的复嵌入。`centered_real_rational_entry_cleared_gaussian` 再纳入 `A/B` 底数因子。

`centeredRationalMatrix_arithmetic_lower_bound` 由这些实际系数清除定理，推出

\[
-M\log D-\sum_{\mathrm{rows}}\log(\mathrm{rowScale})
-\sum_{\mathrm{columns}}\log(\mathrm{baseColumnScale})
\le\log\lVert\det\rVert.
\]

这里 `baseColumnScale` 明确保留 `B^((K-1)h)`，`D` 使用原 OAI 的 `Nat.lcmUpto(T_i)`（包含 `T_i`，比稿件列到 `T_i-1` 的分母更宽）。因此这是完整的原始矩阵算术下界，但尚未进一步证明稿件中归一化误差常数的具体界。

## 假设和范围

- 系数、行展开、行列式展开都是有限代数恒等式，不需要底数为正，也不需要底数或中心互异。
- 有理底数分母恒等式只要求分母非零、`j<K`。
- 用原权重单纯形限制支集时，要求每个横向权重为正、源单项式的横向权重不超过 `H`。
- 算术行列式下界另要求分母为正、每个选中源指数不超过共同清除指数，以及实际行列式非零；没有把算术下界自身当作假设。
- 本适配没有证明 Theorem A 的一般插值满射，没有证明 B 的解析行列式上界、归一化误差常数、参数选择或无理性指数结论。
- 解析解释中 `ω=log R` 与指数映射的匹配另由解析层处理；本文件中的 `ω` 可以是任意复数，行展开仍是精确恒等式。

## 编译审计

已执行：

```sh
./proof_review/oai017/check.sh --adapter adapters/OAIFormalLogAdapter.lean
```

编译退出码为 0，使用 `-DautoImplicit=false`，无警告。16 个定理的 `#print axioms` 全部只列出 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx` 或项目自定义公理。实际 `.olean` 已生成，完整输出保存在同目录 `OAIFormalLogAdapter.check.log`。
