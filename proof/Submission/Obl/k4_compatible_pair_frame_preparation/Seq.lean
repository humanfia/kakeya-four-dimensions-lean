-- Adapted from this LOT tree, o206 (`k4_coarse_pair_frame_preparation`), session x0713
-- (commit 9fd2383c, carried on by x0753), file
-- Submission/Obl/k4_coarse_pair_frame_preparation/Wrapper.lean: `TestedAt`, `tested_iff`,
-- `TestedSample`, `testedAt_iff` and the frequently-and-eventually step of its wrapper. Its
-- record `TestedSample` follows session x0524's `TestedSample.lean` (o156 repository, branch
-- x0524, commit c7cfd90) as adapted by x0472 (o104, `PrepInterface.lean`).

-- The finite tested record and its equivalence are imported from accepted o207.

import Submission.Obl.k4_compatible_pair_frame_preparation.SplitStatements
import Submission.Obl.k4_paired_test_normalization.TestedSample

/-!
# The sequence-level wrapper of o221

`tested` is a cofinal predicate: eight global clauses and `∃ M D, ∀ ε > 0, ∃ᶠ k, (one sample
at k)`.  The eight global clauses are clauses of `FrameData`.

* `TestedAt`: one sample of `tested` at index `k`, with the exact body of the frozen
  definition (`tested_iff` is `Iff.rfl`); `TestedSample` is the same as a record over the
  `k`-th slices (`testedAt_iff`).
* `FrameStep`: the per-sample construction.  A universal `Cf > 0`; for every global datum
  with `FrameData`, every `a, e > 0` and every native format `M D` with its depth grid, output
  formats `M' D'`; for every output slack `ε > 0` a native slack `ε₀ > 0` and a size `N₀`
  such that a native sample `NativeAt True 4 … ε₀` at an index with `N₀ ≤ N k` gives a
  sample `TestedAt False 4 … (Cf * (a + e)) h M' D' ε` at that index.
* `statement_of_frameStep : FrameStep → FramePreparationStatement`.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Filter

set_option linter.unusedVariables false

/-! ### One sample of `tested` -/

/-- One sample of `tested` at index `k`: the body of the frozen `tested` after `∃ᶠ k`. -/
noncomputable def TestedAt (cv : Prop) (lam : ℝ) (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L dc a h : ℝ) (M D : ℕ) (ε : ℝ) (k : ℕ) : Prop :=
  Submission.Obl.k4_paired_test_normalization.NormalizationStep.TestedAt
    cv lam (N k) (W k) (ω k) (ν k) (E k) (B k) L dc a h M D ε

theorem tested_iff (cv : Prop) (lam : ℝ) (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L dc a h : ℝ) :
    tested cv lam N W ω ν E B L dc a h ↔
      ((∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ 0 < L ∧ (∀ k γ, 0 ≤ ω k γ) ∧ (∀ k, (∑ γ, ω k γ) = 1) ∧ (∀ k γ, MeasureTheory.IsProbabilityMeasure (ν k γ)) ∧ (∃ Mb : ℕ, ∀ k γ, 0 < B k γ ∧ B k γ ≤ N k ^ Mb ∧ (B k γ)⁻¹ ≤ N k ^ Mb) ∧ (∃ Me De : ℕ, ∀ k γ, MeasurableSet (E k γ) ∧ ∀ i, fmt 7 (N k ^ Me) De {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ E k γ}) ∧∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
        TestedAt cv lam N W ω ν E B L dc a h M D ε k) :=
  Iff.rfl

/-- One sample of `tested` as a record over the `k`-th slices. -/
noncomputable abbrev TestedSample :=
  Submission.Obl.k4_paired_test_normalization.NormalizationStep.TestedSample

theorem testedAt_iff (cv : Prop) (lam : ℝ) (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L dc a h : ℝ) (M D : ℕ) (ε : ℝ) (k : ℕ) :
    TestedAt cv lam N W ω ν E B L dc a h M D ε k ↔
      Nonempty (TestedSample cv lam (N k) (W k) (ω k) (ν k) (E k) (B k) L dc a h M D ε) := by
  exact (Submission.Obl.k4_paired_test_normalization.NormalizationStep.sample_nonempty_iff
    cv lam (N k) (W k) (ω k) (ν k) (E k) (B k) L dc a h M D ε).symm

/-! ### The per-sample step -/

/-- **The per-sample step** of the frame preparation (see the module doc). -/
def FrameStep : Prop :=
  ∃ Cf : ℝ, 0 < Cf ∧
    ∀ N W ω ν E P B f g
      (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
      L d, FrameData N W ω ν E P B f g L d →
    ∀ S a e u h : ℝ, 0 < a → 0 < e →
    ∀ (M D : ℕ) (depths : Finset ℝ), (0 : ℝ) ∈ depths → L ∈ depths →
      (∀ r ∈ depths, 0 ≤ r ∧ r ≤ L) →
      (∀ r ∈ Set.Icc (0 : ℝ) L, ∃ r' ∈ depths, r' ≤ r ∧ r ≤ r' + e) →
    ∃ M' D' : ℕ, ∀ ε : ℝ, 0 < ε → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℝ, ∀ k : ℕ, N₀ ≤ N k →
      NativeAt True 4 (N k) (W k) (ω k) (ν k) (E k) (P k) (B k) f (g k) (G k)
        L S a e u h M D depths ε₀ →
      TestedAt False 4 N W ω ν E B L d (Cf * (a + e)) h M' D' ε k

/-! ### The wrapper -/

/-- **The frozen o221 statement from the per-sample step.** -/
theorem statement_of_frameStep (hstep : FrameStep) : FramePreparationStatement := by
  obtain ⟨Cf, hCf, hstep⟩ := hstep
  refine ⟨Cf, hCf, ?_⟩
  intro N W ω ν E P B f g G L d hFD S a e u h ha he hnat
  obtain ⟨M, D, depths, h0, hL, hdep, hcov, hfreq⟩ := hnat
  obtain ⟨M', D', hMD⟩ := hstep N W ω ν E P B f g G L d hFD S a e u h ha he M D depths h0 hL
    hdep hcov
  obtain ⟨hN2, hNt, hL0, hω0, hω1, hν, hB, hE, -, -, -, -, -⟩ := hFD
  refine (tested_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr
    ⟨hN2, hNt, hL0, hω0, hω1, hν, hB, hE, M', D', ?_⟩
  intro ε hε
  obtain ⟨ε₀, hε₀, N₀, hsample⟩ := hMD ε hε
  refine ((hfreq ε₀ hε₀).and_eventually (hNt.eventually_ge_atTop N₀)).mono ?_
  rintro k ⟨hk, hNk⟩
  exact hsample k hNk hk

end Submission.Obl.k4_compatible_pair_frame_preparation
