import Mathlib
import ChallengeDeps
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration.RawGridCalibration
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration.Constants
set_option linter.unusedVariables false

/-!
# `Submission.k4_quadratic_mesh_coefficient_calibration`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_quadratic_mesh_coefficient_calibration`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_quadratic_mesh_coefficient_calibration/`
belong to this obligation.

The proof applies the original-grid Remez kernel
`exists_raw_coefficient_bound_from_original_grid` (adapted from o200, see
`RawGridCalibration.lean`) with degree two, the identity base map, base bound
`K` and mesh `δ`, at the truncated mass `min m (β (8K)^3)`. The fixed-power
mesh hypothesis gives `δ ≤ K` and the kernel's absorption condition.
-/

theorem Submission.k4_quadratic_mesh_coefficient_calibration : ∃ C:ℝ,1 ≤ C ∧ ∀ K β m E δ:ℝ,1 ≤ K → 0 < β → 0 < m → 0 ≤ E → 0 < δ → C * (1 + K) ^ C * (1 + β / m) ^ (6:ℕ) * δ ≤ (1:ℝ) / 2 → ∀ μ:MeasureTheory.Measure (Fin 3 → ℝ),MeasureTheory.IsFiniteMeasure μ → ENNReal.ofReal m ≤ μ Set.univ → (∀ q:Fin 3 → ℤ,μ {z | (fun i:Fin 3 => ⌊z i / δ⌋) = q} ≤ ENNReal.ofReal (β * δ ^ (3:ℕ))) → ∀ G:MvPolynomial (Fin 3) ℝ,G.totalDegree ≤ 2 → (∀ᵐ z ∂μ,(∀ i,|z i| ≤ K) ∧ |MvPolynomial.eval z G| ≤ E) → ∀ e,|G.coeff e| ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6:ℕ) * E := by
  obtain ⟨C₀, L, hC₀, hL, hcal⟩ :=
    Submission.Obl.k4_quadratic_mesh_coefficient_calibration.exists_raw_coefficient_bound_from_original_grid 2
  have hW : (0 : ℝ) < 96 ^ 6 * 8 ^ 18 := by positivity
  refine ⟨18 + 1458 * C₀ * (96 ^ 6 * 8 ^ 18) + 54 * L * C₀ * (96 ^ 6 * 8 ^ 18), ?_, ?_⟩
  · have h1 : 0 ≤ 1458 * C₀ * (96 ^ 6 * 8 ^ 18 : ℝ) := by positivity
    have h2 : 0 ≤ 54 * L * C₀ * (96 ^ 6 * 8 ^ 18 : ℝ) := by positivity
    linarith
  intro K β m E δ hK hβ hm hE hδ hsmall μ hfin hmass hcap G hG hae e
  set W : ℝ := 96 ^ 6 * 8 ^ 18 with hWdef
  set C : ℝ := 18 + 1458 * C₀ * W + 54 * L * C₀ * W with hCdef
  have hA : 0 ≤ 1458 * C₀ * W := by positivity
  have hB : 0 ≤ 54 * L * C₀ * W := by positivity
  have hC18 : (18 : ℝ) ≤ C := by linarith
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hK1 : (1 : ℝ) ≤ 1 + K := by linarith
  have hβm : 0 < β / m := div_pos hβ hm
  have hP : (1 : ℝ) ≤ (1 + β / m) ^ 6 := one_le_pow₀ (by linarith)
  have hKC : (1 : ℝ) ≤ (1 + K) ^ C := Real.one_le_rpow hK1 (by linarith)
  have hK18 : (1 + K) ^ (18 : ℕ) ≤ (1 + K) ^ C := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hK1 (by push_cast; linarith)
  have hK18' : (1 : ℝ) ≤ (1 + K) ^ (18 : ℕ) := one_le_pow₀ hK1
  -- the common factor of both conclusions
  have hfac : 1 ≤ C * (1 + K) ^ C * (1 + β / m) ^ 6 := by
    have h1 : (1 : ℝ) ≤ C * (1 + K) ^ C := by nlinarith
    nlinarith
  have hδhalf : δ ≤ 1 / 2 := by nlinarith
  have hδK : δ ≤ K := by linarith
  -- the truncated mass
  have hBpos : 0 < β * (8 * K) ^ 3 := by positivity
  have hm' : 0 < min m (β * (8 * K) ^ 3) := lt_min hm hBpos
  have hloss :=
    Submission.Obl.k4_quadratic_mesh_coefficient_calibration.truncated_remez_loss_le hK hβ hm
  set X : ℝ := (32 * (((2 : ℕ) : ℝ) + 1) /
    (min m (β * (8 * K) ^ 3) / (β * (8 * K) ^ 3))) ^ (3 * 2) with hXdef
  have hX0 : 0 ≤ X := by positivity
  -- `Y` is the fixed-power loss in the frozen form
  have hY : W * (1 + K) ^ 18 * (1 + β / m) ^ 6 ≤ W * (1 + K) ^ C * (1 + β / m) ^ 6 := by
    gcongr
  have hXY : X ≤ W * (1 + K) ^ C * (1 + β / m) ^ 6 := by
    refine le_trans ?_ hY
    simpa only [hWdef, mul_assoc] using hloss
  have hδ8 : δ / (8 * K) ≤ δ := by
    apply div_le_self hδ.le
    linarith
  have habs : 2 * L * (((2 + 1) ^ 3 : ℕ) : ℝ) * C₀ * X * (δ / (8 * K)) ≤ 1 / 2 := by
    have hcast : (((2 + 1) ^ 3 : ℕ) : ℝ) = 27 := by norm_num
    rw [hcast]
    calc
      2 * L * 27 * C₀ * X * (δ / (8 * K)) ≤
          2 * L * 27 * C₀ * (W * (1 + K) ^ C * (1 + β / m) ^ 6) * δ := by
        gcongr
      _ = (54 * L * C₀ * W) * ((1 + K) ^ C * (1 + β / m) ^ 6 * δ) := by ring
      _ ≤ C * ((1 + K) ^ C * (1 + β / m) ^ 6 * δ) := by
        gcongr
        linarith
      _ = C * (1 + K) ^ C * (1 + β / m) ^ 6 * δ := by ring
      _ ≤ 1 / 2 := hsmall
  have hcoeff := hcal (Fin 3 → ℝ) μ (fun z => z) G hG K δ (min m (β * (8 * K) ^ 3)) β E
    hK hδ hδK hm' hβ (min_le_right _ _) hE
    ((ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans hmass) hcap hae habs e
  have hcast : (((2 + 1) ^ 3 : ℕ) : ℝ) = 27 := by norm_num
  rw [hcast] at hcoeff
  calc
    |G.coeff e| ≤ 27 * (2 * 27 * C₀ * X * E) := hcoeff
    _ = (1458 * C₀ * W) * (X * E) / W := by field_simp; ring
    _ ≤ (1458 * C₀ * W) * ((W * (1 + K) ^ C * (1 + β / m) ^ 6) * E) / W := by
        gcongr
    _ = (1458 * C₀ * W) * ((1 + K) ^ C * (1 + β / m) ^ 6 * E) := by field_simp
    _ ≤ C * ((1 + K) ^ C * (1 + β / m) ^ 6 * E) := by
        gcongr
        linarith
    _ = C * (1 + K) ^ C * (1 + β / m) ^ 6 * E := by ring
