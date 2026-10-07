# OAI017 reuse build environment

This directory reviews the actual OAI017 PiExponent development at OpenAI/math
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
It uses Lean **4.34.1**, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, matching the upstream configuration.
The earlier independent review project uses Lean4.24.0 and is kept separate.

## Original source and compile copy

`source/OAI/NumberTheory/PiExponent` contains all 869 original Lean modules.
`source-provenance.json` records and checks their exact Git blob hashes and
SHA256 hashes against the pinned upstream tree. No archival source was changed.

`working/OAI/...` is the actual build source. It changes only import lines:
101 upstream `import Mathlib` lines become `import SupportCore`; a few files
receive explicit stock mathlib imports for declarations formerly exported by the
umbrella. `SupportCore.lean` contains imports only, and no declarations.
`import-header-patches.json` lists every header delta. Run:

```bash
python3 audit_import_headers.py
```

This checks all 869 files and rejects any difference outside complete import
lines, then regenerates the exact manifest. Declaration statements and proof
bodies therefore remain byte-identical after removal of import lines.
The narrowing reduces imported state and compiler memory pressure. It does not
replace the original arguments with hypotheses or add axioms.

## Session build commands

The minimal Lake package is **project/**, not the original repository-level
lakefile. Its OAI library uses `srcDir := "../working"`, and its mathlib path
is `../mathlib4`. The archived upstream lakefile requires many other unrelated
projects; it is preserved as metadata and is not used for this review.

```bash
./check.sh --build OAI.NumberTheory.PiExponent.Approximation.Exponent
./check.sh --build OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision
./check.sh --adapter DistinctMultiplicativeJets.lean
./check.sh --adapter adapters/OAIFormalLogAdapter.lean
```

`--build` uses Lake's dependency graph and produces genuine `.olean` files.
`--adapter` checks the named source with `-DautoImplicit=false`, sets its root
to its containing directory, and emits a flat basename `.olean` into the
project build library. This permits imports between the new adapter modules.
A plain filename checks without emission. These direct checks use the same
strict autoImplicit setting as the package builds.

The actual stock Lean executable is `toolchain/lean-4.34.1-linux/bin/lean-original`.
A wrapper at `bin/lean` currently serializes compiler invocations with one shared `flock` slot, profiles
peak RSS, and invokes that unchanged executable with the same arguments. The
bounded limit prevents excessive simultaneous import workers from exhausting
this session's 8GiB cgroup. No proof output or kernel behavior is changed.

The managed container exposes `/proc/self/exe` but not the corresponding numeric
PID path. `check.sh` loads the narrow `proc_self_compat.so` shim from the older
review project; its source only redirects a readlink request for this process's
own numeric exe path to `/proc/self/exe`. The shim changes no Lean functions,
proof terms, or checking operations. Normal Linux machines need neither this
shim nor the bounded wrapper; use the official pinned toolchain directly.

## Scope of evidence

Successful adapter logs include `#print axioms`. The final adapter audit also
checks every theorem in the new namespaces transitively and permits only
`propext`, `Classical.choice`, and `Quot.sound`. A successful subset build should
not be described as a recheck of the complete upstream `Main` unless that
specific target is built. The new adapters expose actual reusable upstream
lemmas, with their stated geometric and analytic hypotheses; they do not by
mere import establish the complete distinct-center interpolation theorem or
an unconditional irrationality-exponent theorem for every rational logarithm.


## Completed first-round evidence

All nine new adapter modules have been checked with `autoImplicit=false` and
emitted into the project import path. Their required original OAI dependency
closure contains exactly **712** modules, and every one is emitted. The
successful original-source build logs are:

- `toolchain/oai-core-final-build.log` (exit0);
- `toolchain/oai-curve-priority-retry2.log` (exit0);
- `toolchain/oai-ag-complete-build.log` (exit0, 5288 Lake jobs).

`compiled-upstream-receipt.json` records the exact roots, dependency closure,
adapter source hashes and emitted module sizes. All 869 archival Git blobs
were reverified. The first-round header ledger recorded 114 changed import headers,
with zero changes to the remaining statement/proof bytes. The exact SupportCore
imports reach 4038 stock mathlib modules; all working supplemental imports
brought that first-round stock dependency superset to 4303. The complete original Main
remains outside this checked target scope.

## Second-round dependency integration

`toolchain/round2-required-retry1.log` completed successfully (exit0, 5060 Lake
jobs) for AdmissibleParameters, Comparison, AffineJetPolynomial,
AffineJetCoefficientInterface, AffineJetPackets, WeightedGlobalSectionBound,
WeightedProjectiveAmple, WeightedAffineFrame, MatrixCounting,
TranslationCountLimit and LogarithmicContactIdeal.
`toolchain/round2-formalmatrix-build.log` then completed successfully (exit0,
4347 jobs) for FormalMatrixSurjectivity and its FormalMatrixBridge dependencies.
The existing first-round modules were retained. Current emitted original OAI
module count is 845, while complete original Main remains unchecked.

Two newly required working headers receive stock imports only:
BranchContactIdeal imports Mathlib.Analysis.Complex.Polynomial.Basic;
WeightedCompactificationImmersion imports
Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor. The regenerated ledger
checks all 869 bodies equal and lists 117 changed headers. SupportCore remains
218 roots / 4038 stock dependencies; all current working supplemental imports
reach 248 roots / 4305 dependencies, with no missing stock modules.
`round2-upstream-receipt.json` records root presence and the successful log hash.

After concurrent heavy adapter checks increased memory pressure without OOM,
the runtime wrapper was reduced to one shared compiler slot. Session statistics
and scheduling affect performance only; the stock checking executable and
proof terms are unchanged.

The September Navier–Stokes source/workflow review is separate, in
`../round2/NS_source_review.md`. Its pinned repository uses Lean4.34.0-rc2 and a
different mathlib commit. No NS oleans were mixed into this environment, and no
local whole-NS/Comparator/nanoda run is claimed.

The degree integration additionally succeeded in
`toolchain/round2-degree-retry3.log` (exit0, 5198 jobs) for ExceptionalCurveDegree,
CurveNormalizedDegreeTransfer, AdmissibleCurveCoordinates, AdmissibleBlowupMargin
and CurveNormalizationMorphism. Local headers also supply the stock Away,
Flasque, SpreadingOut and Grp.Zero APIs; no original proof body changes.

`ROUND2_INDEPENDENT_CHECK.md` documents the separately defined final reference
proposition and actual fresh stock-kernel proof replay. The 16,341-constant
replay smoke passed. The current conditional B theorem was deliberately rejected
as a final unconditional theorem after independent reference/primitives graph
comparison (16,343 constants). This is not a final Main acceptance or a nanoda run.

## Completed second-round main theorem

The full theorem is now assembled in RationalLogMain.lean. Its only inputs are
a positive rational r and r≠1; it proves the strict ν>2 eventual approximation
bound, irrationality of log(r), and the original irrationalityExponent=2.
DistinctMultiplicativeExistence.lean proves A's complete successive-bounds
existence statement and its R-before-centers quantifiers. This uses the larger
upstream rectangular comparison constant, not the manuscript's smaller C*.

The second-round upstream closure has 845 emitted original OAI modules. The
current import-header ledger has 117 modified files, with zero differences to
non-import bytes across all 869 archival originals. See round2-upstream-receipt.json.
Full original PiExponent.Main is still not this review's build target.

The final strict theorem is also subjected to an independently loaded reference
constant graph, whole-type comparison, transitive axiom whitelist and replay
of its proof dependency closure in a fresh stock Lean kernel environment.
See ROUND2_INDEPENDENT_CHECK.md and final-main-receipt.json for actual results.
No nanoda or sandbox/export Comparator result is claimed.
# 最终主 theorem 独立核验

`RationalLogReview.Main.strict_rational_log_main` 最终实际通过独立 reference
图比较（16,343 常量）、完整类型匹配、传递 axioms 检查、新建空 kernel
重放（114,072 常量）、Quot postcheck，以及独立 statement certificate
严格编译。成功 receipt 为 `final-main-receipt.json`（status accepted，EXIT 0）。
最终 19 个新数学证明模块的原 OAI source import 闭包为 845 modules，全部
编译产物已存在；`compiled-upstream-receipt.json` 已更新该范围。869 个原始
module bodies 逐字节不变，只有 117 个工作副本 import headers 修改。
这里只复用了 NS 的核验装配方法，没有重建 NS，也没有运行 Nanoda。
