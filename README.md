---
pretty_name: "Four-dimensional Kakeya sets have full Hausdorff dimension: a Lean 4 proof"
license: apache-2.0
tags:
- lean4
- mathlib
- formal-proof
- kakeya
---

# Four-dimensional Kakeya sets have full Hausdorff dimension: a Lean 4 proof

This is a complete, machine-checked Lean 4 proof of the following theorem:

```lean
theorem kakeya_four_dimensions (K : Set (EuclideanSpace ℝ (Fin 4)))
    (hK : ∀ e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      ∃ a : EuclideanSpace ℝ (Fin 4), segment ℝ a (a + e) ⊆ K) :
    dimH K = 4
```

In words: every subset of ℝ⁴ that contains a unit line segment in every direction has Hausdorff
dimension 4. This is Theorem 1.1 of OpenAI, *Every four-dimensional Kakeya set has full Hausdorff
dimension* (OpenAI math release, paper family 074, September 24, 2026)
<sup>[[1]](#references)</sup>. The statement is the problem `oai_074_kakeya_four_dimensions`;
`Challenge.lean` and `ChallengeDeps.lean` are used unchanged.

The proof was produced by LOT, our multi-agent proof-tree system. The tree is `g-oai-074`. It started
on 2026-10-21 at 01:44Z and its root was accepted on 2026-10-22 at 20:30Z, 42.8 h of wall clock with
1,100 agent sessions. The proof does not depend on the paper being correct: if the Lean kernel accepts
it, the stated theorem holds.

## Contents

- `proof/` is the judged export, commit `71391e12db6f5956b54bcdb01a6b1ceeba11604d` of the tree's repository,
  byte for byte. It is a self-contained Lean project:
  - 10,629 `.lean` files, 1,381,761 lines, holding only the modules the proof imports.
  - `Submission/Obl/` and `Submission/Lib/` (7,750 files, about 1.01 M lines) are the proof written in the tree.
  - `Submission/WZ/` (2,872 files, 370,727 lines) is our own earlier Lean proof of the three-dimensional
    Kakeya theorem (Wang–Zahl), Lean-Eval #2121, inlined as a library.
  - `NOTICE` and `LICENSES/` are the attribution files that LOT generated for the export. They are
    kept byte for byte, so they still verify against `SHA256SUMS.proof`. The top-level `NOTICE`
    supersedes them for attribution.
- `LICENSE` is the Apache License 2.0, and `NOTICE` is the dataset's attribution notice.
- `SHA256SUMS.proof` holds the sha256 of every file under `proof/`.
- `verification/` holds the final-check record and the fidelity reviews summarised below.

## Verification record

All checks ran on the judged commit above, each in a fresh container.

| Check | Verdict |
|---|---|
| Official trusted check: comparator with both kernels, Lean's and nanoda | **ACCEPTED** (8,971 s, 16 CPUs) |
| `trusted-v10wz` root check together with the official `trusted-v10` check on the same files | **ACCEPTED** (both) |
| Independent recompile + byte comparison + `#print axioms` | **PASS** |

- **Axioms.** `kakeya_four_dimensions` depends only on `[propext, Classical.choice, Quot.sound]`:
  no `sorry`, no extra axioms.
- **Fidelity.** Two independent audits and a reconciliation review compared the Lean statement with the
  paper's Theorem 1.1. Both audits included Lean witnesses that the sphere, the segments and `dimH` mean
  what the paper means. The verdict is **FAITHFUL**: there is no measurability, compactness or boundedness
  assumption, and the content is the full four-dimensional Hausdorff Kakeya statement. See
  `verification/FIDELITY-VERDICT.md`.

## Building

- **Pinned toolchain and dependencies.** Lean `leanprover/lean4:v4.35.0-rc3`, Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`
  and lean-pool `e9d53e9cbcff8dfd0cc816ba94db7a26b082929f`, all pinned in `proof/lake-manifest.json`.
- **Commands.** In `proof/`, run `lake exe cache get` and then `lake build Solution`. A full build needs
  several hours on 16 cores and about 64 GB of memory.
- **Checking with the official comparator.** Use `config.json` in this directory.

## Credits

- **Mathematics:** OpenAI's paper (family 074) <sup>[[1]](#references)</sup>.
- **Formal statement:** the `oai_074_kakeya_four_dimensions` problem files by Zhengyang Zhang, used
  byte for byte.
- **Libraries:** Mathlib, and lean-pool with three of its projects:
  - NavierStokesAndEuler (OpenAI);
  - SardMoreira (Yury G. Kudryashov);
  - Zhang–Yeung (Christopher Boone), with the PFR code it vendors (PFR contributors).
- **Adapted code:** two `ConicKernels.lean` files adapt a dimension argument from lean-pool's
  MetricCodes (openai/ten-proofs; OpenAI, Dean Cureton).
- **Our own earlier work:**
  - the inlined Wang–Zahl three-dimensional library (`Submission/WZ/`);
  - three Plancherel lemmas from our `annals_bose_gases` tree.

`NOTICE` gives the exact sources, revisions and changes.

## License

This dataset is licensed under the [Apache License 2.0](LICENSE).

- Attribution: see the top-level [`NOTICE`](NOTICE). It supersedes `proof/NOTICE`, which is kept byte
  for byte for verification.
- Third-party code: the code included from others is Apache-2.0, and `NOTICE` lists it.
- Exception: the license of the formal statement files (`proof/Challenge.lean`,
  `proof/ChallengeDeps.lean`, `proof/Solution.lean` and the other problem files listed in `NOTICE`
  §4.1) is still to be confirmed by their author.

This repository is private.

## References

1. OpenAI. *Every four-dimensional Kakeya set has full Hausdorff dimension.* OpenAI mathematics release,
   paper family 074, September 24, 2026.
   <https://github.com/openai/math/tree/main/preprints/Every-four-dimensional-Kakeya-set-has-full-Hausdorff-dimension-September-24-2026>

```bibtex
@misc{openai2026kakeya4d,
  author       = {{OpenAI}},
  title        = {Every four-dimensional {K}akeya set has full {H}ausdorff dimension},
  year         = {2026},
  month        = sep,
  note         = {OpenAI mathematics release, paper family 074, September 24, 2026},
  howpublished = {\url{https://github.com/openai/math/tree/main/preprints/Every-four-dimensional-Kakeya-set-has-full-Hausdorff-dimension-September-24-2026}}
}
```
