/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/NormalizedGeometry.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.NormalizeSamples
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

/-! Pointwise event bounds and the subpower slack of normalized worlds. -/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Filter

/-- The line of every retained normalized incidence stays bounded for the whole unit
interval; this strengthens the prior-almost-everywhere sample condition. -/
theorem Atlas.KnownAt.normEvent_planar_bound {p : Data} {k M D : ℕ} {a : Atlas p k} {r : ℝ}
    (ha : a.KnownAt M D r) (c : Fin a.C) {q : Incidence}
    (hq : q ∈ a.system.normEventOf c) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ‖y q.1 τ‖ + ‖v q.1‖ ≤ 3 * a.κ := by
  obtain ⟨_, _, _, _, hchart, _⟩ := ha
  have hD : IsUnit (a.system.frame c).det := isUnit_iff_ne_zero.mpr (hchart c).1
  have hδ : 0 < δ (p.N k) r := by unfold δ; positivity
  have hwhole := fun l hl t ht => ((hchart c).2.2.2.2.2.2.2.2.2.1 l hl).2.2 t ht
  have hl : (a.system.frameOf c).denormTraj q.1 ∈ a.system.assignment c := hq.1
  have hbound := a.system.norm_native_bounds c hδ hD hwhole _ hl τ hτ
  rw [a.system.normTraj_denormTraj c hD q.1] at hbound
  exact hbound.1

theorem NormalizedSamples.subpower {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) :
    (∀ k, 1 ≤ 3 * (t.sequence.atlas k).κ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        3 * (t.sequence.atlas k).κ ≤ p.N (t.sequence.index k) ^ ε := by
  simpa only [Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower, pow_one] using
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
      (fun k => (show (1 : ℝ) ≤ 2 by norm_num).trans (hp.1 (t.sequence.index k)))
      (hp.2.1.comp t.sequence.strictMono.tendsto_atTop)
      ⟨t.sequence.slack_one, t.sequence.slack_subpower⟩ (A := 3) (by norm_num) 1

end Submission.Obl.k4_remainder_pure_profile_normalization
