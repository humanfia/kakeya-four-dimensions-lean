import Mathlib

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/StepScales.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

noncomputable section

/-- The gain used in the strict bootstrap step. -/
def gain (d κ u : ℝ) : ℝ := (1 - d) * (u - 2 * κ) / 10000

/-- The old depth associated with the prescribed new depth. -/
def oldDepth (d κ u s : ℝ) : ℝ := s / (1 + gain d κ u)

/-- The accuracy exponent used to prepare the normalized first jet. -/
def jetDepth (κ u s₀ : ℝ) : ℝ := (u - 2 * κ) * s₀ / 10

theorem gain_bounds {d κ u : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hκ : 0 < κ) (hu : 2 * κ < u) (hu1 : u ≤ 1) :
    0 < gain d κ u ∧ gain d κ u ≤ 1 / 10000 := by
  dsimp [gain]
  have hg : 0 < u - 2 * κ := by linarith
  constructor
  · positivity
  · have : (1 - d) * (u - 2 * κ) ≤ 1 := by
      calc (1 - d) * (u - 2 * κ) ≤ 1 * 1 :=
            mul_le_mul (by linarith) (by linarith) hg.le (by norm_num)
           _ = 1 := by norm_num
    linarith

theorem oldDepth_bounds {d κ u s sMax : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hκ : 0 < κ) (hu : 2 * κ < u) (hu1 : u ≤ 1) (hs : 0 < s) (hsMax : s < sMax) :
    0 < oldDepth d κ u s ∧ oldDepth d κ u s < s ∧ oldDepth d κ u s < sMax := by
  have hg := (gain_bounds hd0 hd1 hκ hu hu1).1
  have hden : 0 < 1 + gain d κ u := by linarith
  have hpos : 0 < oldDepth d κ u s := div_pos hs hden
  have hlt : oldDepth d κ u s < s := by
    rw [oldDepth, div_lt_iff₀ hden]
    nlinarith
  exact ⟨hpos, hlt, hlt.trans hsMax⟩

theorem jetDepth_bounds {κ u s₀ sMax : ℝ} (hκ : 0 < κ)
    (hu : 2 * κ < u) (hu1 : u ≤ 1) (hs : 0 < s₀) (hsMax : s₀ < sMax) :
    0 < jetDepth κ u s₀ ∧ jetDepth κ u s₀ < sMax / 10 := by
  have hg : 0 < u - 2 * κ := by linarith
  dsimp [jetDepth]
  constructor
  · positivity
  · nlinarith [mul_pos hs (show 0 < 1 - (u - 2 * κ) by linarith)]

/-- The scalar reading width lies strictly above the finest scale demanded by the first jet. -/
theorem jet_reading_gap {d κ u s₀ : ℝ} (hd1 : d < 1) (hκ : 0 < κ)
    (hu : 2 * κ < u) (hs : 0 < s₀) :
    gain d κ u * s₀ = (1 - d) * jetDepth κ u s₀ / 1000 ∧
    gain d κ u * s₀ < (1 - d) * jetDepth κ u s₀ / 256 := by
  have hprod : 0 < (1 - d) * (u - 2 * κ) * s₀ := by positivity
  dsimp [gain, jetDepth]
  constructor
  · ring
  · nlinarith

/-- The normalized floor is finer than the cube of the finest fitting time scale. -/
theorem jet_floor_gap {κ u s₀ : ℝ} (hκ : 0 < κ) (hu : 2 * κ < u)
    (hs : 0 < s₀) : 3 * (jetDepth κ u s₀ / 4) < jetDepth κ u s₀ := by
  have : 0 < jetDepth κ u s₀ := by dsimp [jetDepth]; positivity
  linarith

/-- The parameter width remains strictly within the nearby true transverse width. -/
theorem transverse_exponent_identity (κ u s₀ : ℝ) :
    -u * s₀ + 2 * κ * (s₀ + jetDepth κ u s₀) =
      -(10 - 2 * κ) * jetDepth κ u s₀ := by
  dsimp [jetDepth]
  ring

/-- The new error thickness is the product of the old thickness and the jet accuracy. -/
theorem thickness_identity {N d κ u s : ℝ} (hN : 0 < N)
    (hg : 0 < 1 + gain d κ u) :
    N ^ (-oldDepth d κ u s) * N ^ (-gain d κ u * oldDepth d κ u s) = N ^ (-s) := by
  rw [← Real.rpow_add hN]
  congr 1
  dsimp [oldDepth]
  field_simp
  ring

/-- Keeping the old parameter square gives precisely the improved rate at the new depth. -/
theorem parameter_width_identity (N d κ u s : ℝ) :
    N ^ (-u * oldDepth d κ u s) =
      N ^ (-(u / (1 + gain d κ u)) * s) := by
  congr 1
  dsimp [oldDepth]
  ring

/-- Returning from normalized parameter coordinates has one rate-independent exponent. -/
theorem reconstruction_amplification {N u s₀ sMax : ℝ} (hN : 1 ≤ N)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hs : 0 ≤ s₀) (hsMax : s₀ ≤ sMax) :
    (N ^ (-u * s₀) * N ^ (-s₀))⁻¹ ≤ N ^ (2 * sMax) := by
  have hN0 : 0 < N := by linarith
  rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]
  apply Real.rpow_le_rpow_of_exponent_le hN
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hu1)]

/-- One positive buffer meets any fixed finite reconstruction exponent. -/
theorem exists_reconstruction_buffer {U e₀ C : ℝ} (hU : 0 < U) (he : 0 < e₀)
    (hC : 0 < C) :
    ∃ sMax : ℝ, 0 < sMax ∧ 2 * sMax < U ∧ 100 * sMax < e₀ ∧
      C * sMax < e₀ / 2 ∧ sMax ≤ 1 / 100 := by
  let sMax : ℝ := min (U / 4) (min (e₀ / 200) (min (e₀ / (4 * C)) (1 / 100)))
  have hs : 0 < sMax := by dsimp [sMax]; positivity
  have h1 : sMax ≤ U / 4 := min_le_left _ _
  have h2 : sMax ≤ e₀ / 200 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : sMax ≤ e₀ / (4 * C) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : sMax ≤ 1 / 100 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨sMax, hs, by linarith, by linarith, ?_, h4⟩
  have h3' : sMax * (4 * C) ≤ e₀ := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp h3
  nlinarith

end

end Submission.Obl.k4_horizontal_strict_parameter_step
