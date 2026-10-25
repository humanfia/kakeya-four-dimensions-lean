# Task: Every four-dimensional Kakeya set has full Hausdorff dimension (Lean-Eval `oai_074_kakeya_four_dimensions`)

Fill the one hole of the Lean-Eval problem `oai_074_kakeya_four_dimensions` in `Submission.lean`.
The frozen statement is in `Challenge.lean`, its vocabulary in `ChallengeDeps.lean`. Read
`README.md`, `Challenge.lean`, `ChallengeDeps.lean` and `holes.json` first.

Source: OpenAI, `Every four-dimensional Kakeya set has full Hausdorff dimension`, OpenAI math
release (paper family 074). Statement formalised

## Holes

| # | Kind | Challenge name | Fill in `Submission.lean` as | Starter line |
|---|---|---|---|---|
| 1 | theorem | `kakeya_four_dimensions` | `Submission.kakeya_four_dimensions` | 6 |

`config.json` lists the theorems (`theorem_names`) the comparator checks. The starter
`Submission.lean` already declares every hole under `namespace Submission`, with `sorry`: replace
each `sorry` with a proof. Keep every hole's name, binders (in this order) and type exactly as
written: `Solution.lean` restates the challenge and takes each hole from `Submission`, and the
comparator checks that its statements are the challenge's. Helper modules go in `Submission/*.lean`
(for example the existing `Submission/Helpers.lean`).

Imports: the Submission sources may import more of Mathlib and the modules of lean-pool
(`LeanPool.*`, prebuilt; browse `.lake/packages/lean-pool/LeanPool/`). The statement side
(`Challenge.lean`, `ChallengeDeps.lean`) may not import lean-pool, and is protected. A broader
import can change how the fixed statement elaborates: `lake build Solution` must stay green.

## Rules

- Toolchain and packages are pinned: Lean `v4.35.0-rc3`, mathlib
  `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`, lean-pool `e9d53e9cbcff8dfd0cc816ba94db7a26b082929f`
  (lean-eval `38361be884302c7edce1908c4aef8296eb2cb27e`). Do not change `lean-toolchain`,
  `lakefile.toml` or `lake-manifest.json`, and do not run `lake update` or `lake exe cache get`.
- Everything except `Submission.lean` and `Submission/` is protected and must stay byte-identical
  (`Challenge.lean`, `ChallengeDeps.lean`, `Solution.lean`, `config.json`, `holes.json`, the build
  files, `WorkspaceTest.lean`, `README.md`, this file, `.gitignore`). Do not add `.lean` files
  anywhere else.
- Only `Submission.lean` and `.lean` files under `Submission/` with plain names (letters, digits,
  `_`) are taken from your checkout; the checker rebuilds everything else from the pristine
  workspace. No symbolic links anywhere in the repository (`.lake/` excepted).
- No `sorry`, `admit`, `axiom` declarations, `native_decide`, or other unsafe mechanisms. Only
  `propext`, `Quot.sound`, `Classical.choice` are permitted, checked transitively (through imported
  lean-pool modules too). For the root check no `sorry` may remain anywhere in the Submission
  sources.
- Submissions may not use IO, compile-time evaluation or command elaboration from text (`#eval`,
  `run_cmd`, `include_str`, `elabCommand`, ...), nor `unsafe`, `implemented_by` or `extern`.
- A fresh checkout has no `.lake/`. Before building in one, link the prebuilt packages (Mathlib,
  lean-pool) instead of downloading them:
  `mkdir -p .lake && ln -s /home/ubuntu/lean-runs/lean-gap/deps/mathlib-5e0c4e5/.lake/packages .lake/packages`
  (read-only), then `lake build Submission` / `lake build Solution`.
- Child theorems of a decomposition are checked as `Submission.<lean_name>` against their frozen
  type, elaborated in a file that imports exactly `Mathlib` and what
  `/home/ubuntu/lean-runs/lean-gap/trusted/oai_074_kakeya_four_dimensions/imports.txt` lists
  (`import ChallengeDeps`), with no `open` or `namespace`, and with `autoImplicit` off. Write fully
  qualified names and bind every variable; do not mention `Submission` declarations (your own
  definitions, the filled holes included, are not visible to a frozen type), nor lean-pool ones. A
  lemma declared as `Submission.foo` has `lean_name` `foo`; one declared as `Submission.Foo.bar` has
  `lean_name` `Foo.bar`.

## Acceptance

`bash /home/ubuntu/lean-runs/lean-gap/trusted/oai_074_kakeya_four_dimensions/check.sh <node_id>`
(the configured comparator command) exits 0 and prints `Your solution is okay!`. For `root` it
verifies the protected files, scans the Submission sources for forbidden constructs, then runs the
official comparator with `config.json` (theorem `kakeya_four_dimensions`; no required definitions)
and the nanoda kernel forced on, exactly as Lean-Eval's `lake test` does: statement equality,
transitive axioms, and kernel replay.
