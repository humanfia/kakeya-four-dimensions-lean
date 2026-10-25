/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/RemainderData.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.SampleBridge
import Submission.Obl.k4_remainder_pure_profile_normalization.SequenceBounds
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

/-! The remaining problem retains the full normalized assignment priors. -/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory Filter

/-- Data obtained from full assignment conditioning, with a further selected event. -/
noncomputable def KnownSequence.remainingData {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) (cap : ℝ) (K : ℕ → ℝ)
    (E : (k : ℕ) → Fin (s.atlas k).C → Set Incidence) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (s.atlas k).C → ℝ → Observation → ENNReal)
    (G : (k : ℕ) → Fin (s.atlas k).C → ℝ → JointObservation → ENNReal) : Data where
  N := p.N ∘ s.index
  K := K
  L := p.L - r
  d := cap
  S := p.S
  η := p.η
  W := fun k => (s.atlas k).C
  ω := fun k => (s.atlas k).system.normWeight (p.ω (s.index k)) (p.ν (s.index k))
  ν := fun k => (s.atlas k).system.normPrior (p.ν (s.index k))
  E := E
  P := fun k => (s.atlas k).system.normNative (δ (p.N (s.index k)) r)
  B := fun k => (s.atlas k).system.normScale (p.B (s.index k)) (δ (p.N (s.index k)) r)
  f := f
  g := g
  G := G

/-- The complete analytic output needed from normalization. All maps and priors
are fixed by the actual chosen charts; the terminal comparison controls true floors. -/
structure NormalizedRemainder {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) (cap : ℝ) where
  K : ℕ → ℝ
  E : (k : ℕ) → Fin (s.atlas k).C → Set Incidence
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (s.atlas k).C → ℝ → Observation → ENNReal
  G : (k : ℕ) → Fin (s.atlas k).C → ℝ → JointObservation → ENNReal
  valid : (s.remainingData cap K E f g G).Valid
  event_subset : ∀ k c, E k c ⊆ (s.atlas k).system.normEventOf c
  prior_positive : ∀ k c,
    0 < (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal
  normalizer_subpower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
    ((s.atlas k).system.normZ (p.ω (s.index k)) (p.ν (s.index k)))⁻¹ ≤
      p.N (s.index k) ^ ε
  terminal_comparison : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ c,
    p.N (s.index k) ^ (-p.f p.L) * |((s.atlas k).Q c).det| ≤
      p.N (s.index k) ^ ε *
        (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal *
        p.N (s.index k) ^ (-f (p.L - r))

noncomputable def NormalizedRemainder.data {p : Data} {M D : ℕ} {r h cap : ℝ}
    {s : KnownSequence p M D r h} (q : NormalizedRemainder s cap) : Data :=
  s.remainingData cap q.K q.E q.f q.g q.G

/-- Fixed dyadic rounding errors in the composed fitting depth. -/
theorem delta_product_compare {N : ℝ} (hN : 0 < N) (r s : ℝ) :
    δ N r * δ N s ≤ 4 * δ N (r + s) ∧
      δ N (r + s) ≤ 4 * (δ N r * δ N s) := by
  have hr := Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN r
  have hs := Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN s
  have hrs := Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN (r + s)
  have hp : N ^ (-r) * N ^ (-s) = N ^ (-(r + s)) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hl : N ^ (-(r + s)) ≤ δ N r * δ N s := by
    rw [← hp]
    exact mul_le_mul hr.1 hs.1 (by positivity) (by unfold δ; positivity)
  have hu : δ N r * δ N s ≤ 4 * N ^ (-(r + s)) := by
    calc δ N r * δ N s ≤ (2 * N ^ (-r)) * (2 * N ^ (-s)) :=
          mul_le_mul hr.2 hs.2 (by unfold δ; positivity) (by positivity)
      _ = _ := by rw [show (2 * N ^ (-r)) * (2 * N ^ (-s)) =
          4 * (N ^ (-r) * N ^ (-s)) by ring, hp]
  exact ⟨hu.trans (mul_le_mul_of_nonneg_left hrs.1 (by norm_num)),
    hrs.2.trans (by nlinarith [show 0 ≤ δ N r * δ N s by unfold δ; positivity])⟩

end Submission.Obl.k4_remainder_pure_profile_normalization
