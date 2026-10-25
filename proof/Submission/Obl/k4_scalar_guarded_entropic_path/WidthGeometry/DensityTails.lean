/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/DensityTails.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.ExactLaw

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

open MeasureTheory Set Filter

/-- The simultaneous pure/angular deletion is power-small in the original
mixture, before any path restriction or later successful-label choice. -/
theorem Exact.eventually_originalDensityException_le {p : RawData} (hp : Exact p)
    {a τ : ℝ} (ha : 0 < a) (haU : a ≤ p.U) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ g, ENNReal.ofReal (p.weight k g) *
        mu p k g (originalDensityException p k g a τ)) ≤
          2 * ENNReal.ofReal (p.N k ^ (-c)) := by
  have hL : 0 ≤ p.L := le_of_lt hp.1.2.2.2.2.2.1
  obtain ⟨cp, hcp, hpure⟩ := hp.2.2.2.2.2.1 p.L τ hL le_rfl hτ
  obtain ⟨ca, hca, hang⟩ := hp.2.2.2.2.2.2.2 a τ ha haU hτ
  change ∀ᶠ k in atTop, (∑ g, ENNReal.ofReal (p.weight k g) *
    mu p k g (originalPureException p k g τ)) ≤ ENNReal.ofReal (p.N k ^ (-cp)) at hpure
  change ∀ᶠ k in atTop, (∑ g, ENNReal.ofReal (p.weight k g) *
    mu p k g (originalAngularException p k g a τ)) ≤ ENNReal.ofReal (p.N k ^ (-ca)) at hang
  refine ⟨min cp ca, lt_min hcp hca, ?_⟩
  filter_upwards [hpure, hang] with k hpk hak
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (hp.1.1 k)
  have hsub (g : Fin (p.1 k)) : originalDensityException p k g a τ ⊆
      originalPureException p k g τ ∪ originalAngularException p k g a τ := by
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl (Or.inl hz)
    · exact Or.inr hz
  have hμ (g : Fin (p.1 k)) : mu p k g (originalDensityException p k g a τ) ≤
      mu p k g (originalPureException p k g τ) +
        mu p k g (originalAngularException p k g a τ) :=
    (measure_mono (hsub g)).trans (measure_union_le _ _)
  have hrp : ENNReal.ofReal (p.N k ^ (-cp)) ≤
      ENNReal.ofReal (p.N k ^ (-min cp ca)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_left _ _)))
  have hra : ENNReal.ofReal (p.N k ^ (-ca)) ≤
      ENNReal.ofReal (p.N k ^ (-min cp ca)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_right _ _)))
  calc
    _ ≤ ∑ g, ENNReal.ofReal (p.weight k g) *
        (mu p k g (originalPureException p k g τ) +
          mu p k g (originalAngularException p k g a τ)) := by
      apply Finset.sum_le_sum
      intro g _
      gcongr
      exact hμ g
    _ = (∑ g, ENNReal.ofReal (p.weight k g) * mu p k g (originalPureException p k g τ)) +
        ∑ g, ENNReal.ofReal (p.weight k g) * mu p k g (originalAngularException p k g a τ) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ ENNReal.ofReal (p.N k ^ (-cp)) + ENNReal.ofReal (p.N k ^ (-ca)) := add_le_add hpk hak
    _ ≤ ENNReal.ofReal (p.N k ^ (-min cp ca)) +
        ENNReal.ofReal (p.N k ^ (-min cp ca)) := add_le_add hrp hra
    _ = _ := (two_mul _).symm

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
