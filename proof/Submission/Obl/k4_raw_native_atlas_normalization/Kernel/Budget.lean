/- Adapted from this LOT tree, o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
   Submission/Lib/K4ChartLifting/NormMass.lean. -/
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.SampleNormalize
namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MeasureTheory
namespace ChartSystem
variable {W T₀ : ℕ} (s : ChartSystem W T₀)

/-- The selected mass of the charts bounds the normalizing constant from below. -/
theorem mass_le_normZ (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ)
    (hsub : ∀ c, ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c)) :
    ∑ c, ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c) ≤
      ENNReal.ofReal (s.normZ ω ν) := by
  unfold normZ
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (hω _) (by positivity))]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [ENNReal.ofReal_mul (hω _)]
  refine mul_le_mul_right ?_ _
  have hsubset : s.event c ⊆ s.assignment c ×ˢ timeBlock T₀ (s.block c) :=
    fun p hp => hsub c p hp
  have hT : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  calc ((ν (s.world c)).prod volume) (s.event c)
      ≤ ((ν (s.world c)).prod volume) (s.assignment c ×ˢ timeBlock T₀ (s.block c)) :=
        measure_mono hsubset
    _ = ν (s.world c) (s.assignment c) * ENNReal.ofReal (1 / (2 : ℝ) ^ T₀) := by
        rw [Measure.prod_prod, timeBlock, Real.volume_Icc]
        congr 2
        field_simp
        ring
    _ = ENNReal.ofReal ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀) := by
        rw [show (ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀ =
          (ν (s.world c) (s.assignment c)).toReal * (1 / (2 : ℝ) ^ T₀) by ring,
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The inverse normalizing constant is at most the slack of the atlas mass condition. -/
theorem normZ_inv_le (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ)
    (hsub : ∀ c, ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c))
    {κ : ℝ} (hκ : 0 < κ)
    (htotal : ENNReal.ofReal κ⁻¹ ≤
      ∑ c, ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c)) :
    0 < s.normZ ω ν ∧ (s.normZ ω ν)⁻¹ ≤ κ := by
  have h := htotal.trans (s.mass_le_normZ ω ν hω hsub)
  have hZ : κ⁻¹ ≤ s.normZ ω ν := by
    rw [ENNReal.ofReal_le_ofReal_iff'] at h
    rcases h with h | h
    · exact h
    · exact absurd h (not_le.mpr (inv_pos.mpr hκ))
  have hZpos : 0 < s.normZ ω ν := lt_of_lt_of_le (inv_pos.mpr hκ) hZ
  exact ⟨hZpos, by rw [inv_le_comm₀ hZpos hκ]; exact hZ⟩

end ChartSystem
end Submission.Obl.k4_raw_native_atlas_normalization.Kernel
