---
pretty_name: "Four-dimensional Kakeya sets have full Hausdorff dimension: a Lean 4 proof"
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
dimension* (OpenAI math release, paper family 074, September 2026). The statement is the problem
`oai_074_kakeya_four_dimensions`; `Challenge.lean` and `ChallengeDeps.lean` are used unchanged.

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
  - `NOTICE` and `LICENSES/` list the imported libraries and the copied code, with their licenses.
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

- **Mathematics:** OpenAI's paper (family 074).
- **Formal statement:** the `oai_074_kakeya_four_dimensions` problem files.
- **Libraries:** Mathlib, and lean-pool together with the projects listed in `proof/NOTICE`.
- **Inlined library:** the Wang–Zahl three-dimensional library comes from our own earlier proof tree.

This repository is private. Its license has not been decided yet.
