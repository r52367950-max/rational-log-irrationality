# External reference for proof assembly and checking

The methodological reference is the original [OpenAI NavierStokesAndEuler repository](https://github.com/openai/NavierStokesAndEuler), reviewed at commit `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.

This project takes inspiration from its separation of a reference proposition, concrete proof assembly, complete statement comparison, and transitive axiom checking. It does not depend on its PDE theorems and does not vendor its source, Comparator source, or repository metadata.

The checks actually performed on this project's rational-logarithm candidate are documented in `../checks/final-main-receipt.json` and `../audits/oai017/ROUND2_INDEPENDENT_CHECK.md`. The supplied records do not claim a local rebuild of the NS repository, a Nanoda run, or a full isolated/export Comparator run.
