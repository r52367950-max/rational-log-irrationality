# 正有理数对数：完整 Lean 主定理与常规证明

本包包含原稿、完整常规证明、复核记录及无条件 Lean 主定理。对每个正有理数 r≠1，证明所有 ν>2 的最终严格逼近下界、log r 无理，以及原 OAI017 定义下 μ(log r)=2。

先阅读 `复核与重要性评估.md`，常规主证明在 `round2/完整常规主定理证明.md`。`audits/` 中其他迁移审查保留上一轮记录，本轮完成状态以当前报告和 `round2/` 为准。

| 内容 | 位置 |
|---|---|
| 无条件主定理 | `lean-oai017/portable_project/RationalLogMain.lean` |
| A 的完整 successive 存在性 | 同目录 `DistinctMultiplicativeExistence.lean` |
| 独立目标与核重放程序 | 同目录 `Round2MainReference.lean`、`Round2MainTypeChecker.lean`、`verify_round2_main.py` |
| 成功主定理核验 receipt | `checks/final-main-receipt.json`、`checks/final-main/` |
| 全部 {{OAI_THEOREM_COUNT}} 个新增定理声明的公理审计 | `checks/lean-oai017-theorem-axioms.json` |
| 前一轮 {{LOCAL_THEOREM_COUNT}} 个具名局部定理 | `lean-local/portable_project/` |
| 原稿及哈希 | `manuscript/`、`checks/source_sha256.json` |
| 常规完整证明与 A/B 审查 | `round2/` |
| OAI017 869 份原始源码及许可证 | `oai017-upstream/` |
| NS 方法参考及固定源码/许可证 | `round2/NS_source_review.md` 及其来源子目录 |

唯一未形式化的稿件细化是较小阶乘 C* 的具体显示阈值，以及较小 LCM 常数。Lean 使用已验证的较大常数，其参数构造足够推出完整主定理；最终 theorem 没有残留插值、几何或估计假设。

先运行完整性核对：

```bash
python helpers/verify_delivery.py .
```

两个 Lean 工程版本不同，须分别构建。完整主证明使用 Lean 4.34.1、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`：

```bash
cd lean-oai017/portable_project
lake update
lake exe cache get
lake build OAI017Review
python verify_round2_main.py --runner lake --project-dir . \
  --module RationalLogMain \
  --theorem RationalLogReview.Main.strict_rational_log_main
```

最终核验执行独立 reference 定义图和整个 theorem 类型比对、公理审计及新建空 stock Lean 内核的证明项重放，随后生成 statement certificate。没有声称运行 Nanoda 或完整隔离/export Comparator。

旧局部工程使用 Lean 4.24.0、mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`：

```bash
cd lean-local/portable_project
lake update
lake exe cache get
lake build
```

上游固定为 OpenAI/math `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。工作副本仅缩减/补充 stock import，数学定义和证明正文保持不变；原始 Git blob、导入修改清单及实际依赖构建 receipt 已保留。完整原上游 Main 不是本次构建目标。

所审计传递公理仅 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或新增公理。归档的 NS challenge 含原始待解占位，但不会由我们的 proof 工程导入；不应对所有档案文本声称不存在 `sorry`。

有限精确复核需 SymPy 1.14.0：

```bash
python -m pip install sympy==1.14.0
python checks/exact_checks.py
python checks/cech_contraction_check.py
```

有限检查不是主定理证书。压缩包不含工具链、mathlib 下载副本、编译缓存；依赖由固定版本配置获取。
