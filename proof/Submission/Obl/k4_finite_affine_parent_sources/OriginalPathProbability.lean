-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PathMass
import Submission.Obl.k4_finite_affine_parent_sources.WorldPathProbability

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- A residual of the actual terminal path lies in the original unit
time interval, including the true closed dyadic endpoints. -/
theorem PathData.Valid.terminal_residual_time_support
    (H : Fin W → Set Incidence)
    (hH : ∀ w, H w ⊆ TerminalInc W p.C m p.lev p.world p.counted w) :
    ∀ w, H w ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  intro w z hz
  obtain ⟨b, -, -, hzb⟩ := hH w hz
  have ht := (hp.counted_support b z hzb).2.2.1
  have hj : (p.bin b : ℝ) + 1 ≤ (2 : ℝ) ^ p.T (p.lev b) := by
    exact_mod_cast Nat.succ_le_of_lt (hp.label_bin b)
  refine ⟨mem_univ _, ?_, ?_⟩
  · exact (div_nonneg (Nat.cast_nonneg _) (by positivity)).trans ht.1
  · exact ht.2.trans ((div_le_one (by positivity)).mpr hj)

/-- Normalize the supplied half-terminal residual once. Its original
mass floor pays exactly `2*pathSlack`; every world slice retains its
original weight and its original trajectory prior. -/
theorem PathData.Valid.half_terminal_probability
    (hm : 0 < m) (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (H : Fin W → Set Incidence)
    (hH : ∀ w, H w ⊆ TerminalInc W p.C m p.lev p.world p.counted w)
    (hmass : (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω w) *
        (ν w).prod volume (TerminalInc W p.C m p.lev p.world p.counted w)) ≤
      ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w)) :
    IsProbabilityMeasure (WorldPath.probability ν ω H) ∧
      WorldPath.probability ν ω H ≤ ENNReal.ofReal (2 * p.κ) • WorldPath.original ν ω H ∧
      ∀ (w : Fin W) (A : Set Incidence), MeasurableSet A →
        WorldPath.probability ν ω H ({w} ×ˢ A) =
          (WorldPath.original ν ω H univ)⁻¹ * ENNReal.ofReal (ω w) *
            (ν w).prod volume (A ∩ H w) := by
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  have hκ : 0 < 2 * p.κ := by linarith [hp.one_le_slack]
  have hunit := hp.terminal_residual_time_support H hH
  have hfloor : ENNReal.ofReal ((2 * p.κ)⁻¹) ≤ WorldPath.original ν ω H univ := by
    rw [WorldPath.original_mass]
    exact hp.residual_mass_lower hm H hmass
  have hpositive : WorldPath.original ν ω H univ ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr (inv_pos.mpr hκ)).trans_le hfloor)
  obtain ⟨hprob, hslices⟩ := WorldPath.probability_spec ν ω hω hω1 H hunit hpositive
  exact ⟨hprob, WorldPath.probability_le_original ν ω hω hω1 H hunit
    (2 * p.κ) hκ hfloor, hslices⟩

end
end
end Submission.Obl.k4_finite_affine_parent_sources
