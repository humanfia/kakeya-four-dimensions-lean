import Submission.Obl.k4_prescribed_polynomial_visibility.VolumeShrink

namespace Submission.Obl.k4_prescribed_polynomial_visibility

open MeasureTheory
open scoped ENNReal

/-- A Euclidean unit ball lies in the coordinate cube of side two. -/
theorem volume_unitBody_norm_le {n : ℕ} :
    volume (unitBody (normSeminorm ℝ (EuclideanSpace ℝ (Fin n)))) ≤ (2 : ℝ≥0∞) ^ n := by
  let K : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)
  have hK : MeasurableSet K := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hsub : unitBody (normSeminorm ℝ (EuclideanSpace ℝ (Fin n))) ⊆
      WithLp.ofLp ⁻¹' K := by
    intro x hx
    change ‖x‖ ≤ 1 at hx
    simp only [K, Set.mem_preimage, Set.mem_univ_pi]
    intro j
    have hj : ‖x j‖ ≤ 1 := (PiLp.norm_apply_le x j).trans hx
    simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using hj
  calc
    volume (unitBody (normSeminorm ℝ (EuclideanSpace ℝ (Fin n)))) ≤
        volume (WithLp.ofLp ⁻¹' K) := measure_mono hsub
    _ = volume K := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hK.nullMeasurableSet
    _ = (2 : ℝ≥0∞) ^ n := by
      rw [show volume K = ∏ _j : Fin n, volume (Set.Icc (-1 : ℝ) 1) from volume_pi_pi _]
      norm_num

theorem probability_mass_le_one {m : ℕ} (M : Fin m → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hsum : ∑ q, M q = 1) (q : Fin m) : M q ≤ 1 := by
  rw [← hsum]
  exact Finset.single_le_sum (fun i _ => hM i) (Finset.mem_univ q)

/-- Doubling the scale cancels the factor coming from a doubled unit body. -/
theorem two_pow_mul_reciprocal {n : ℕ} (a M : ℝ) (ha : 0 < a) (hM : 0 < M) :
    (2 : ℝ≥0∞) ^ n * ENNReal.ofReal (((2 * a) ^ n * M)⁻¹) =
      ENNReal.ofReal ((a ^ n * M)⁻¹) := by
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hap : a ^ n ≠ 0 := pow_ne_zero n ha.ne'
  rw [← show ENNReal.ofReal ((2 : ℝ) ^ n) = (2 : ℝ≥0∞) ^ n by simp,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  congr 1
  rw [mul_pow]
  field_simp [ha.ne', hM.ne', htwo, hap]

/-- The norm alone supplies the initial demand at scale one half. -/
theorem initial_volume_bound {n m : ℕ} (M : Fin m → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hsum : ∑ q, M q = 1) (q : Fin m) (hq : 0 < M q) :
    volume (unitBody (normSeminorm ℝ (EuclideanSpace ℝ (Fin n)))) ≤
      ENNReal.ofReal (((1 / 2 : ℝ) ^ n * M q)⁻¹) := by
  calc
    volume (unitBody (normSeminorm ℝ (EuclideanSpace ℝ (Fin n)))) ≤ (2 : ℝ≥0∞) ^ n :=
      volume_unitBody_norm_le
    _ ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ n * M q)⁻¹) := by
      rw [← show ENNReal.ofReal ((2 : ℝ) ^ n) = (2 : ℝ≥0∞) ^ n by simp]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_eq_one_div,
        le_div_iff₀ (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n * M q)]
      calc
        (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n * M q) = M q := by
          rw [← mul_assoc, ← mul_pow]
          norm_num
        _ ≤ 1 := probability_mass_le_one M hM hsum q

end Submission.Obl.k4_prescribed_polynomial_visibility
