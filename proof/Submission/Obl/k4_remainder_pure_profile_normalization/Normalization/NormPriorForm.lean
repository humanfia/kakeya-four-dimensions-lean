/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/Normalization/NormPriorForm.lean.
Earlier provenance is preserved below.
-/
/-
Adapted from this LOT tree, o064, session x0214, commit 1213d02,
Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/NormPriorForm.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.SampleNormalize

/-!
# The normalized prior in frozen form, and size bounds

`ChartSystem.normPrior_form`: the normalized prior is `Σ_j ofReal (c_j |det|⁻¹ / ν(A_c)) •`
Lebesgue on the normalized pieces; bounds for the Jacobian factor (`≤ N^(7 M₀)`) and for the
normalization bound (`≤ 16 N^(2 M₀)`).
-/
namespace Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open MeasureTheory MvPolynomial

namespace ChartSystem
variable {W T₀ : ℕ} (s : ChartSystem W T₀)

/-- The normalized prior in the frozen piecewise-Lebesgue form. -/
theorem normPrior_form (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (c : Fin s.count) (hD : IsUnit (s.frame c).det) (hA : MeasurableSet (s.assignment c))
    {m : ℕ} (cc : Fin m → ℝ) (hcc : ∀ j, 0 ≤ cc j) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ))
    (hν : ν (s.world c) = ∑ j, ENNReal.ofReal (cc j) •
      Measure.map (fun x => (i j, x)) (volume.restrict (A j)))
    (hpos : ν (s.world c) (s.assignment c) ≠ 0) :
    s.normPrior ν c = ∑ j, ENNReal.ofReal (cc j * |(s.frameOf c).normMatrix.det|⁻¹ /
        (ν (s.world c) (s.assignment c)).toReal) •
      Measure.map (fun x => (i j, x)) (volume.restrict
        ((s.frameOf c).denormCoeff ⁻¹' (A j ∩ {x | (i j, x) ∈ s.assignment c}))) := by
  have hq := s.frameOf_q_pos c
  have hfin : ν (s.world c) (s.assignment c) ≠ ⊤ := measure_ne_top _ _
  have hposR : 0 < (ν (s.world c) (s.assignment c)).toReal := ENNReal.toReal_pos hpos hfin
  have key : Measure.map (s.frameOf c).normTraj ((ν (s.world c)).restrict (s.assignment c)) =
      ∑ j, (ENNReal.ofReal (cc j) * ENNReal.ofReal |(s.frameOf c).normMatrix.det|⁻¹) •
        Measure.map (fun x => (i j, x)) (volume.restrict
          ((s.frameOf c).denormCoeff ⁻¹' (A j ∩ {x | (i j, x) ∈ s.assignment c}))) := by
    rw [hν]; exact (s.frameOf c).map_normTraj_prior hq.ne' hD cc i A _ hA
  rw [normPrior, key, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (mul_nonneg (hcc j) (inv_nonneg.mpr (abs_nonneg _))),
    ENNReal.ofReal_mul (hcc j), ENNReal.ofReal_inv_of_pos hposR, ENNReal.ofReal_toReal hfin]
  ring

theorem frameOf_t₀_le_one (c : Fin s.count) : |(s.frameOf c).t₀| ≤ 1 := by
  have hT : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  simp only [frameOf]
  rw [abs_of_nonneg (by positivity), div_le_one hT]
  exact block_lt_two_pow (s.block c)

theorem frameOf_q_le_one (c : Fin s.count) : |(s.frameOf c).q| ≤ 1 := by
  simp only [frameOf]
  rw [abs_of_pos (by positivity), div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

/-- Size of the normalization bound in terms of the atlas sizes. -/
theorem normBound_le (c : Fin s.count) {N : ℝ} {M₀ : ℕ} (hN : 1 ≤ N)
    (hcu : ‖s.center c‖ + ‖s.speed c‖ ≤ N ^ M₀)
    (hDi : (∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'|) ≤ N ^ M₀) :
    (s.frameOf c).normBound ≤ 16 * N ^ (2 * M₀) := by
  have h1 : 1 ≤ N ^ M₀ := one_le_pow₀ hN
  have ht := s.frameOf_t₀_le_one c
  have hq := s.frameOf_q_le_one c
  have h2M : N ^ (2 * M₀) = N ^ M₀ * N ^ M₀ := by rw [two_mul, pow_add]
  unfold Frame.normBound
  have a : 1 + ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frameOf c).D⁻¹ e e'| ≤ 2 * N ^ M₀ := by
    show 1 + ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'| ≤ 2 * N ^ M₀
    linarith
  have b : 1 + ‖(s.frameOf c).c‖ + ‖(s.frameOf c).u‖ ≤ 2 * N ^ M₀ := by
    show 1 + ‖s.center c‖ + ‖s.speed c‖ ≤ 2 * N ^ M₀
    linarith
  have hS0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frameOf c).D⁻¹ e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc (1 + ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frameOf c).D⁻¹ e e'|) * (1 + |(s.frameOf c).t₀|) *
        (1 + |(s.frameOf c).q|) * (1 + ‖(s.frameOf c).c‖ + ‖(s.frameOf c).u‖)
      ≤ (2 * N ^ M₀) * 2 * 2 * (2 * N ^ M₀) := by
        gcongr
        · linarith
        · linarith
    _ = 16 * N ^ (2 * M₀) := by rw [h2M]; ring

/-- Size of the Jacobian factor of the normalized prior. -/
theorem abs_det_normMatrix_inv_le (c : Fin s.count) (hD : IsUnit (s.frame c).det) {N : ℝ}
    {M₀ : ℕ} (hN : 1 ≤ N) (hT₀ : (2 : ℝ) ^ T₀ ≤ N ^ M₀)
    (hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) ≤ N ^ M₀) :
    |(s.frameOf c).normMatrix.det|⁻¹ ≤ N ^ (7 * M₀) := by
  have hdet : (s.frameOf c).normMatrix.det = (1 / (2 : ℝ) ^ T₀) ^ 3 * ((s.frame c).det)⁻¹ ^ 2 := by
    rw [Frame.det_normMatrix, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; rfl
  have hd0 : (s.frame c).det ≠ 0 := hD.ne_zero
  rw [hdet, abs_mul, abs_pow, abs_pow, abs_inv, mul_inv, ← inv_pow, ← inv_pow, inv_inv]
  have hT : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ T₀), one_div, inv_inv]
  have hdetle : |(s.frame c).det| ≤ N ^ (2 * M₀) := by
    rw [Matrix.det_fin_two]
    have hsum : ∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'| =
        |s.frame c 0 0| + |s.frame c 0 1| + (|s.frame c 1 0| + |s.frame c 1 1|) := by
      simp [Fin.sum_univ_two]
    have h2M : N ^ (2 * M₀) = N ^ M₀ * N ^ M₀ := by rw [two_mul, pow_add]
    rw [h2M]
    calc |s.frame c 0 0 * s.frame c 1 1 - s.frame c 0 1 * s.frame c 1 0|
        ≤ |s.frame c 0 0| * |s.frame c 1 1| + |s.frame c 0 1| * |s.frame c 1 0| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) *
          (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) := by
          rw [hsum]
          nlinarith [abs_nonneg (s.frame c 0 0), abs_nonneg (s.frame c 0 1),
            abs_nonneg (s.frame c 1 0), abs_nonneg (s.frame c 1 1)]
      _ ≤ N ^ M₀ * N ^ M₀ := by
          have h0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'| :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
          exact mul_le_mul hDs hDs h0 (by positivity)
  have h7 : N ^ (7 * M₀) = (N ^ M₀) ^ 3 * (N ^ (2 * M₀)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  rw [h7]
  apply mul_le_mul (pow_le_pow_left₀ hT.le hT₀ 3) (pow_le_pow_left₀ (abs_nonneg _) hdetle 2)
    (by positivity) (by positivity)

end ChartSystem
end Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
