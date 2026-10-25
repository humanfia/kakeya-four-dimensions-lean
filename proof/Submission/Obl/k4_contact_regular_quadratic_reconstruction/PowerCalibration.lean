import Submission.Obl.k4_contact_regular_quadratic_reconstruction.HomogeneousCalibration

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ContactNormalization Submission.Lib.K4ChartLifting

noncomputable section

/-- A fixed exponent for the mesh-calibration loss at power-bounded mass. -/
def calibrationPower (C B : ℝ) : ℝ := (B + 1) * C + 12 * B + 7

theorem calibrationPower_pos {C B : ℝ} (hC : 1 ≤ C) (hB : 1 ≤ B) :
    0 < calibrationPower C B := by
  unfold calibrationPower
  nlinarith

/-- The calibration cost is a fixed power, uniformly in the original law. -/
theorem calibration_loss_le_power {N C B : ℝ}
    (hN : 2 ≤ N) (hC : 1 ≤ C) (hCN : C ≤ N) (hB : 1 ≤ B) :
    C * (1 + N ^ B) ^ C * (1 + N ^ B / N ^ (-B)) ^ (6 : ℕ) ≤
      N ^ calibrationPower C B := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hNB : 1 ≤ N ^ B := Real.one_le_rpow hN1 (by linarith)
  have hNBB : 1 ≤ N ^ (2 * B) := Real.one_le_rpow hN1 (by linarith)
  have hsum : 1 + N ^ B ≤ N ^ (B + 1) := by
    rw [Real.rpow_add hN0, Real.rpow_one]
    nlinarith [Real.rpow_pos_of_pos hN0 B]
  have hratio : N ^ B / N ^ (-B) = N ^ (2 * B) := by
    rw [← Real.rpow_sub hN0]
    congr 1
    ring
  have hsum2 : 1 + N ^ B / N ^ (-B) ≤ N ^ (2 * B + 1) := by
    rw [hratio, Real.rpow_add hN0, Real.rpow_one]
    nlinarith [Real.rpow_pos_of_pos hN0 (2 * B)]
  calc
    _ ≤ N * (N ^ (B + 1)) ^ C * (N ^ (2 * B + 1)) ^ (6 : ℕ) := by
      gcongr
    _ = N ^ calibrationPower C B := by
      rw [← Real.rpow_mul hN0.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hN0.le]
      norm_num only [Nat.cast_ofNat]
      have hprod : N * N ^ ((B + 1) * C) * N ^ ((2 * B + 1) * (6 : ℝ)) =
          N ^ (1 + (B + 1) * C + (2 * B + 1) * 6) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
      rw [hprod]
      congr 1
      unfold calibrationPower
      ring

/-- A mesh chosen one fixed power finer absorbs the calibration error. -/
theorem calibration_power_mesh_small {N C B : ℝ}
    (hN : 2 ≤ N) (hC : 1 ≤ C) (hCN : C ≤ N) (hB : 1 ≤ B) :
    C * (1 + N ^ B) ^ C * (1 + N ^ B / N ^ (-B)) ^ (6 : ℕ) *
        N ^ (-(calibrationPower C B + 1)) ≤ (1 : ℝ) / 2 := by
  have hN0 : 0 < N := by linarith
  calc
    _ ≤ N ^ calibrationPower C B * N ^ (-(calibrationPower C B + 1)) :=
      mul_le_mul_of_nonneg_right (calibration_loss_le_power hN hC hCN hB) (by positivity)
    _ = N⁻¹ := by
      rw [← Real.rpow_add hN0]
      rw [show calibrationPower C B + -(calibrationPower C B + 1) = (-1 : ℝ) by ring,
        Real.rpow_neg_one]
    _ ≤ (1 : ℝ) / 2 := by
      simpa only [one_div] using (inv_le_inv₀ hN0 (by norm_num : (0 : ℝ) < 2)).mpr hN

/-- Fixed-power original witness mass and fixed-power mesh ceilings yield a
fixed-power coefficient bound. The exponent is independent of all tolerances. -/
theorem MeshCalibration.coefficients_of_power_caps {C : ℝ}
    (hcal : MeshCalibration C) (hC : 1 ≤ C)
    {N B : ℝ} (hN : 2 ≤ N) (hCN : C ≤ N) (hB : 1 ≤ B)
    {Ω : Type*} [MeasurableSpace Ω] (σ : Measure Ω) [IsFiniteMeasure σ]
    (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z)
    (G : MvPolynomial (Fin 3) ℝ) (hG : G.totalDegree ≤ 2)
    (hmass : ENNReal.ofReal (N ^ (-B)) ≤ σ univ)
    (hcap : ∀ q : Fin 3 → ℤ,
      σ {p | (fun i : Fin 3 => ⌊Z p i / N ^ (-(calibrationPower C B + 1))⌋) = q} ≤
        ENNReal.ofReal (N ^ B * (N ^ (-(calibrationPower C B + 1))) ^ (3 : ℕ)))
    (htrace : ∀ᵐ p ∂σ, (∀ i, |Z p i| ≤ N ^ B) ∧ |eval (Z p) G| ≤ N ^ B) :
    ∀ e, |G.coeff e| ≤ N ^ (calibrationPower C B + B) := by
  have hN0 : 0 < N := by linarith
  have hb := hcal.observation_bound σ Z hZ G hG
    (Real.one_le_rpow (by linarith : 1 ≤ N) (by linarith : 0 ≤ B))
    (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hN0 _)
    (by positivity) (Real.rpow_pos_of_pos hN0 _)
    (calibration_power_mesh_small hN hC hCN hB) hmass hcap htrace
  intro e
  calc
    |G.coeff e| ≤ C * (1 + N ^ B) ^ C * (1 + N ^ B / N ^ (-B)) ^ (6 : ℕ) * N ^ B := hb e
    _ ≤ N ^ calibrationPower C B * N ^ B :=
      mul_le_mul_of_nonneg_right (calibration_loss_le_power hN hC hCN hB) (by positivity)
    _ = _ := (Real.rpow_add hN0 _ _).symm

/-- Adding the original polynomial's coefficient to a power-bounded correction
has exactly the homogeneous shape required by the original candidate. -/
theorem homogeneous_coeff_add_power {N r : ℝ} (hN : 2 ≤ N) (hr : 0 ≤ r)
    (F P : MvPolynomial (Fin 4) ℝ) (e : Fin 4 →₀ ℕ) :
    |F.coeff e| + N ^ r ≤
      N ^ (r + 1) * ((1 + ∑ f ∈ F.support, |F.coeff f|) +
        ∑ f ∈ P.support, |P.coeff f|) ^ (r + 1) := by
  let A : ℝ := (1 + coeffL1 F) + coeffL1 P
  have hF0 : 0 ≤ coeffL1 F := coeffL1_nonneg F
  have hP0 : 0 ≤ coeffL1 P := coeffL1_nonneg P
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hcoef : |F.coeff e| ≤ A := by
    exact (abs_coeff_le_coeffL1 F e).trans (by dsimp [A]; linarith)
  have hApow : A ≤ A ^ (r + 1) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hA1 (show (1 : ℝ) ≤ r + 1 by linarith)
  have hN0 : 0 < N := by linarith
  have hNr : 1 ≤ N ^ r := Real.one_le_rpow (by linarith) hr
  change _ ≤ N ^ (r + 1) * A ^ (r + 1)
  calc
    |F.coeff e| + N ^ r ≤ A + N ^ r := add_le_add hcoef le_rfl
    _ ≤ 2 * N ^ r * A := by nlinarith
    _ ≤ N * N ^ r * A := by gcongr
    _ = N ^ (r + 1) * A := by rw [Real.rpow_add hN0, Real.rpow_one]; ring
    _ ≤ N ^ (r + 1) * A ^ (r + 1) := mul_le_mul_of_nonneg_left hApow (by positivity)

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
