# 直接复用 OAI017 的无理性指数末端证明

`OAIApproximationAdapter.lean` 已在 Lean 4.34.1、mathlib 提交 `d13f23b723b8a846827a245b89c10fc7d3f11612` 下成功编译。它直接导入原项目 `OAI.NumberTheory.PiExponent.Approximation.Exponent`，调用原有定理；没有重新定义无理性指数，也没有用 π 的专门结论替代对数结论。

原始代码来自 [openai/math](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent)，固定提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。原始文件、内容哈希及来源保存在上级目录的 `source/` 与 `source-provenance.json`。

| 原项目代码 | 本适配器的具体复用 |
|---|---|
| `EventualLowerBound` | 直接使用原有最终弱下界接口；它对所有整数分子、足够大的自然数分母成立。 |
| `irrationalityExponent_eq_two_of_eventualLowerBound` | 直接调用原有上确界证明，得到原项目定义下的 μ(x)=2。 |
| `eventualLowerBound_iff_integer` | 将原有整数分母接口转换为自然数分母接口。 |
| `eventualLowerBound_of_not_unbounded_approximations` | 将排除无界逼近的反证结果送入原有下界接口。 |

原项目的 μ(x) 是实数上确界：正指数 ν 对应无穷多个不同的既约有理数，分母至少为 2，且满足 `0 < |x-r| < den(r)^(-ν)`。它与第一轮独立代码使用的扩充实数、任意大未约分分母定义有所区别。本文件的最终结论使用原项目的定义。

新增的关键证明是：原有 `EventualLowerBound x` 自身已经蕴含 `Irrational x`。取 ν=3；若 x 是有理数，将其分子、分母同时乘以大整数，会得到超过任何分母阈值的精确表示，与正的 `q^(-3)` 下界矛盾。这满足了原项目通用指数定理所要求的无理性前提。

稿件 B 的严格下界通过把阈值增大为 `max Q 2`、将严格不等式减弱为非严格不等式，转换到原有接口。因此可以得到：

```lean
(hbound : ManuscriptStrictBound (Real.log (r : ℝ))) →
  Irrational (Real.log (r : ℝ)) ∧
  OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2
```

这里的 `hbound` 是明确保留的尚待完成输入。本适配器没有证明新稿件的几何插值定理、含有理底数分母高度的行列式下界或全部解析估计，不能据此宣布 μ(log 2)=2 已获无条件 Lean 证明。

运行环境为控制内存，在编译副本中将部分上游 `import Mathlib` 缩减为 `import SupportCore`。数学定义和证明正文未改动；原文件保留，导入头部修改及两份文件哈希详见上级 `import-header-patches.json`。`SupportCore` 只显式导入同一版本 mathlib 中所需模块。

在上级 `oai017` 目录运行：

```bash
bash check.sh adapters/OAIApproximationAdapter.lean
```

原始成功输出保存于 `OAIApproximationAdapter.check.log`；结构化记录为 `OAIApproximationAdapter.axioms.json`。记录覆盖 4 个被复用的原定理和 7 个新增适配器定理，全部只依赖 `propext`、`Classical.choice`、`Quot.sound`，未出现 `sorryAx` 或新增公理。
