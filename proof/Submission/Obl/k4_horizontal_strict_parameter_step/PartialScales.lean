import Submission.Obl.k4_horizontal_strict_parameter_step.StepScales

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/PartialScales.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

/-- Every smaller positive gain reaches its prescribed depth without regridding. -/
theorem partial_old_depth_bounds {θ s sMax : ℝ} (hθ : 0 < θ)
    (hs : 0 < s) (hsMax : s < sMax) :
    0 < s / (1 + θ) ∧ s / (1 + θ) < s ∧ s / (1 + θ) < sMax := by
  have hp : 0 < 1 + θ := by linarith
  have hlt : s / (1 + θ) < s := (div_lt_iff₀ hp).mpr (by nlinarith)
  exact ⟨div_pos hs hp, hlt, hlt.trans hsMax⟩

/-- The old square and the jet readout have exactly the new requested scales. -/
theorem partial_scale_identities {N u θ s : ℝ} (hN : 0 < N) (hθ : 0 < 1 + θ) :
    N ^ (-(s / (1 + θ))) * N ^ (-θ * (s / (1 + θ))) = N ^ (-s) ∧
      N ^ (-u * (s / (1 + θ))) = N ^ (-(u / (1 + θ)) * s) := by
  constructor
  · rw [← Real.rpow_add hN]
    congr 1
    field_simp
    ring
  · congr 1
    ring

/-- Reducing the gain only coarsens the required normalized preparation floor. -/
theorem partial_jet_depth_bounds {d κ u θ s₀ : ℝ} (hd1 : d < 1)
    (hθ : 0 < θ) (hθmax : θ ≤ gain d κ u) (hs : 0 < s₀) :
    0 < θ * s₀ * (1000 / (1 - d)) ∧
      θ * s₀ * (1000 / (1 - d)) ≤ jetDepth κ u s₀ := by
  have hden : 0 < 1 - d := by linarith
  constructor
  · positivity
  · have hh := mul_le_mul_of_nonneg_right hθmax
      (show 0 ≤ s₀ * (1000 / (1 - d)) by positivity)
    convert hh using 1
    · ring
    · dsimp [gain, jetDepth]
      field_simp
      ring

/-- The original parameter square lies within the transverse width at every
child depth needed by a partial readout, with eight powers of preparation room. -/
theorem partial_transverse_room {κ u s₀ E : ℝ} (hκ : κ ≤ 1)
    (hE : 0 ≤ E) (hread : E ≤ jetDepth κ u s₀) :
    -u * s₀ + 2 * κ * (s₀ + E) ≤ -8 * E := by
  have hh : 10 * E ≤ (u - 2 * κ) * s₀ := by
    dsimp [jetDepth] at hread
    linarith
  have hkE := mul_le_mul_of_nonneg_right hκ hE
  nlinarith

end Submission.Obl.k4_horizontal_strict_parameter_step
