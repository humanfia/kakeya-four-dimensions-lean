import Mathlib
import Submission.Lib.K4FinitePlankAtlases
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat
import Submission.Obl.k4_eligibility_sign_description.Descriptions
import Submission.Obl.k4_eligibility_sign_description.Families
import Submission.Obl.k4_eligibility_sign_description.Signs
import Submission.Obl.k4_horizon_chart_assembly.Defs
import Submission.Obl.k4_matching_homogeneous_records.Offsets
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation
import Submission.Obl.k4_scalar_coefficient_clustering.Geometry

namespace Submission.Obl.k4_horizon_chart_assembly
open Set MeasureTheory
open scoped BigOperators
abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def graphPoint (l : Trajectory) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]
def planarPoint (l : Trajectory) (t : ℝ) : Plane :=
  WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4]
def timeBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)
def PolynomialFormat {n : ℕ} (N : ℝ) (M D : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  Fmt n (N ^ M) D S
open Submission.Lib.K4FinitePlankAtlases (fullTracePlank_iff_endpoints)
end Submission.Obl.k4_horizon_chart_assembly
/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/Variation.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set
open Submission.Obl.k4_eligibility_sign_description (Quadratic)
open Submission.Obl.k4_scalar_coefficient_clustering
  (quadratic quadratic_time_lipschitz coeff_norm_le_abs_add floor_scaled_error)

/-- Quadratic coefficients recovered from the three unit-interval sample times. -/
noncomputable def quadraticCoefficients (q : ℝ → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![q 0, -q 1 + 4 * q (1 / 2) - 3 * q 0,
    2 * q 1 - 4 * q (1 / 2) + 2 * q 0]

theorem quadraticCoefficients_eval {q : ℝ → ℝ} (hq : Quadratic q) (t : ℝ) :
    quadratic (quadraticCoefficients q) t = q t := by
  obtain ⟨a, b, c, h⟩ := hq
  change q 0 + t * (-q 1 + 4 * q (1 / 2) - 3 * q 0) +
    t ^ 2 * (2 * q 1 - 4 * q (1 / 2) + 2 * q 0) = q t
  simp only [h]
  ring

/-- A uniform bound on a unit interval controls all three quadratic coefficients. -/
theorem quadraticCoefficients_norm_le {q : ℝ → ℝ} {K : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |q t| ≤ K) :
    ‖quadraticCoefficients q‖ ≤ 17 * K := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have hh := h (1 / 2) (by norm_num)
  have ha : |2 * q 1 - 4 * q (1 / 2) + 2 * q 0| ≤ 8 * K := by
    rw [abs_le] at h0 h1 hh ⊢
    constructor <;> linarith
  have hb : |-q 1 + 4 * q (1 / 2) - 3 * q 0| ≤ 8 * K := by
    rw [abs_le] at h0 h1 hh ⊢
    constructor <;> linarith
  calc
    ‖quadraticCoefficients q‖ ≤ |q 0| + |-q 1 + 4 * q (1 / 2) - 3 * q 0| +
        |2 * q 1 - 4 * q (1 / 2) + 2 * q 0| := by
      simpa [quadraticCoefficients] using coeff_norm_le_abs_add (quadraticCoefficients q)
    _ ≤ 17 * K := by linarith

/-- Native bounded quadratics move only a subpower multiple of the elapsed time. -/
theorem bounded_quadratic_variation {q : ℝ → ℝ} (hq : Quadratic q) {K t s : ℝ}
    (h : ∀ u ∈ Icc (0 : ℝ) 1, |q u| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    |q t - q s| ≤ 51 * K * |t - s| := by
  have hvar := quadratic_time_lipschitz (quadraticCoefficients_norm_le h) ht hs
  simpa only [quadraticCoefficients_eval hq, show 3 * (17 * K) = 51 * K by ring] using hvar

/-- The native polynomial evaluated along a frozen trajectory is quadratic in time. -/
theorem native_quadratic (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (l : Trajectory) : Quadratic (fun t => MvPolynomial.eval (graphPoint l t) P) := by
  have h := Quadratic.mv_line P hP ![0, l.2 0, l.2 1, l.2 2] ![1, l.2 3, l.2 4, l.2 5]
  have heq (t : ℝ) : graphPoint l t =
      (fun i => ![0, l.2 0, l.2 1, l.2 2] i + t * ![1, l.2 3, l.2 4, l.2 5] i) := by
    ext j
    fin_cases j <;> simp [graphPoint]
  simpa only [← heq] using h

/-- Midpoint signal bins give a full-block small-value test on blocks comparable
to the terminal hidden resolution. -/
theorem native_signal_bin_bound (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (l : Trajectory) {K δ q t s : ℝ} (hδ : 0 < δ)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (graphPoint l u) P| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (hdt : |t - s| ≤ q) :
    |MvPolynomial.eval (graphPoint l t) P -
      δ * (⌊MvPolynomial.eval (graphPoint l s) P / δ⌋ : ℝ)| ≤ 51 * K * q + δ := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hbound s hs)
  have hvar := bounded_quadratic_variation (native_quadratic P hP l) hbound ht hs
  have hbin := floor_scaled_error hδ (MvPolynomial.eval (graphPoint l s) P)
  have htri := abs_sub_le (MvPolynomial.eval (graphPoint l t) P)
    (MvPolynomial.eval (graphPoint l s) P)
    (δ * (⌊MvPolynomial.eval (graphPoint l s) P / δ⌋ : ℝ))
  have hvar' := mul_le_mul_of_nonneg_left hdt (show 0 ≤ 51 * K by positivity)
  linarith

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/NativeTest.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set
open Submission.Obl.k4_eligibility_sign_description (degree_sub_le)
open Submission.Obl.k4_scalar_coefficient_clustering (floor_scaled_error)

/-- The initial terminal candidate subtracts its native-signal bin center. -/
noncomputable def shiftedTest (P : MvPolynomial (Fin 4) ℝ) (b : ℝ) :
    MvPolynomial (Fin 4) ℝ := P - MvPolynomial.C b

theorem shiftedTest_degree {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (b : ℝ) : (shiftedTest P b).totalDegree ≤ 2 :=
  degree_sub_le hP (by simp)

theorem pderiv_shiftedTest (P : MvPolynomial (Fin 4) ℝ) (b : ℝ) (i : Fin 4) :
    MvPolynomial.pderiv i (shiftedTest P b) = MvPolynomial.pderiv i P := by
  simp [shiftedTest]

/-- Subtracting a signal bin changes no nonconstant coefficient. -/
theorem shiftedTest_coeff_le {P : MvPolynomial (Fin 4) ℝ} {C : ℝ}
    (hP : ∀ e, |P.coeff e| ≤ C) (b : ℝ) (e : Fin 4 →₀ ℕ) :
    |(shiftedTest P b).coeff e| ≤ C + |b| := by
  classical
  have hC : |(MvPolynomial.C b : MvPolynomial (Fin 4) ℝ).coeff e| ≤ |b| := by
    simp only [MvPolynomial.coeff_C]
    split_ifs <;> simp
  calc
    _ = |P.coeff e - (MvPolynomial.C b : MvPolynomial (Fin 4) ℝ).coeff e| := by
      rw [shiftedTest, MvPolynomial.coeff_sub]
    _ ≤ |P.coeff e| + |(MvPolynomial.C b : MvPolynomial (Fin 4) ℝ).coeff e| := abs_sub _ _
    _ ≤ C + |b| := add_le_add (hP e) hC

/-- A bin center remains bounded by the original signal bound plus one bin width. -/
theorem signal_bin_center_bound {x K δ : ℝ} (hx : |x| ≤ K) (hδ : 0 < δ) :
    |δ * (⌊x / δ⌋ : ℝ)| ≤ K + δ := by
  have h := floor_scaled_error hδ x
  rw [abs_le] at hx h ⊢
  constructor <;> linarith

/-- The centered native test has the terminal small-value fit on a short block.
Its first and second hidden derivatives are exactly the original ones. -/
theorem shifted_native_signal_bound (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (l : Trajectory) {K δ q t s : ℝ} (hδ : 0 < δ)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (graphPoint l u) P| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (hdt : |t - s| ≤ q) :
    |MvPolynomial.eval (graphPoint l t)
      (shiftedTest P (δ * (⌊MvPolynomial.eval (graphPoint l s) P / δ⌋ : ℝ)))| ≤
        51 * K * q + δ := by
  simpa only [shiftedTest, map_sub, MvPolynomial.eval_C] using
    native_signal_bin_bound P hP l hδ hbound ht hs hdt

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/InitialGeometry.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Submission.Obl.k4_scalar_coefficient_clustering (floor_scaled_error plane_norm_le_abs_add)

noncomputable def isotropicFrame (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun _ => q)

theorem isotropicFrame_det (q : ℝ) : Matrix.det (isotropicFrame q) = q ^ 2 := by
  simp [isotropicFrame, Matrix.det_diagonal, pow_two]

theorem isotropicFrame_entry_sum {q : ℝ} (hq : 0 ≤ q) :
    (∑ i : Fin 2, ∑ j : Fin 2, |isotropicFrame q i j|) = 2 * q := by
  simp [isotropicFrame, Fin.sum_univ_two, abs_of_nonneg hq]
  ring

theorem isotropicFrame_inverse (q : ℝ) :
    (isotropicFrame q)⁻¹ = isotropicFrame q⁻¹ := by
  by_cases hq : q = 0
  · simp [hq, isotropicFrame]
  apply Matrix.inv_eq_right_inv
  simp [isotropicFrame, Matrix.diagonal_mul_diagonal, hq]

theorem isotropicFrame_inverse_action (q : ℝ) (z : Plane) :
    Matrix.toEuclideanLin ((isotropicFrame q)⁻¹) z = q⁻¹ • z := by
  rw [isotropicFrame_inverse]
  ext i
  fin_cases i <;> simp [isotropicFrame, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

theorem isotropicFrame_inverse_sum {q : ℝ} (hq : 0 ≤ q) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|isotropicFrame q i j| + |(isotropicFrame q)⁻¹ i j|)) = 2 * (q + q⁻¹) := by
  rw [isotropicFrame_inverse]
  simp [isotropicFrame, Fin.sum_univ_two, abs_of_nonneg hq,
    abs_of_nonneg (inv_nonneg.mpr hq)]
  ring

noncomputable def planeBinCenter (q : ℝ) (z : Plane) : Plane :=
  WithLp.toLp 2 (fun i => q * (⌊z i / q⌋ : ℝ))

theorem planeBinCenter_error {q : ℝ} (hq : 0 < q) (z : Plane) :
    ‖z - planeBinCenter q z‖ ≤ 2 * q := by
  have h0 := floor_scaled_error hq (z 0)
  have h1 := floor_scaled_error hq (z 1)
  calc
    ‖z - planeBinCenter q z‖ ≤ |z 0 - q * (⌊z 0 / q⌋ : ℝ)| +
        |z 1 - q * (⌊z 1 / q⌋ : ℝ)| := by
      simpa only [PiLp.sub_apply, planeBinCenter] using
        plane_norm_le_abs_add (z - planeBinCenter q z)
    _ ≤ 2 * q := by linarith

def planarVelocity (l : Trajectory) : Plane := WithLp.toLp 2 ![l.2 3, l.2 4]

theorem planarPoint_sub (l : Trajectory) (t s : ℝ) :
    planarPoint l t - planarPoint l s = (t - s) • planarVelocity l := by
  ext i
  fin_cases i <;> simp [planarPoint, planarVelocity, PiLp.sub_apply, PiLp.smul_apply] <;> ring

theorem planarPoint_variation {l : Trajectory} {K t s q : ℝ}
    (hK : ‖planarVelocity l‖ ≤ K) (hdt : |t - s| ≤ q) :
    ‖planarPoint l t - planarPoint l s‖ ≤ K * q := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  rw [planarPoint_sub, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hK (abs_nonneg _)).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hdt hK0])

/-- A midpoint position bin and a q-isotropic frame contain the whole affine
trace for a time block of length at most q, with subpower geometric slack. -/
theorem initial_planar_fit {l : Trajectory} {K t s q : ℝ} (hq : 0 < q)
    (hK : ‖planarVelocity l‖ ≤ K) (hdt : |t - s| ≤ q) :
    ‖Matrix.toEuclideanLin ((isotropicFrame q)⁻¹)
      (planarPoint l t - planeBinCenter q (planarPoint l s))‖ ≤ K + 2 := by
  have htri := norm_sub_le_norm_sub_add_norm_sub (planarPoint l t) (planarPoint l s)
    (planeBinCenter q (planarPoint l s))
  have hfit : ‖planarPoint l t - planeBinCenter q (planarPoint l s)‖ ≤ (K + 2) * q := by
    linarith [planarPoint_variation hK hdt, planeBinCenter_error hq (planarPoint l s)]
  calc
    _ = q⁻¹ * ‖planarPoint l t - planeBinCenter q (planarPoint l s)‖ := by
      rw [isotropicFrame_inverse_action, norm_smul_of_nonneg (inv_nonneg.mpr hq.le)]
    _ ≤ q⁻¹ * ((K + 2) * q) := mul_le_mul_of_nonneg_left hfit (inv_nonneg.mpr hq.le)
    _ = K + 2 := by field_simp

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/HiddenPrediction.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Submission.Obl.k4_quadratic_slope_volume
  (coordinatePolynomialHom natDegree_eval₂_affine_le derivative_coordinatePolynomialHom
    eval_coordinatePolynomialHom)
open Submission.Obl.k4_scalar_coefficient_clustering (floor_scaled_error)

/-- The exact second-order Taylor identity for a quadratic. -/
theorem quadratic_taylor_exact (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) (x y : ℝ) :
    p.eval y - p.eval x = p.derivative.eval x * (y - x) +
      p.derivative.derivative.eval x * (y - x) ^ 2 / 2 := by
  obtain ⟨a, b, c, rfl⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients p hp
  simp
  ring

/-- Freezing the other coordinates retains the exact quadratic Taylor formula,
with the original first and second partial derivatives. -/
theorem quadratic_coordinate_taylor {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2) (v : σ → ℝ) (i : σ) (w : ℝ) :
    MvPolynomial.eval (Function.update v i w) P - MvPolynomial.eval v P =
      MvPolynomial.eval v (MvPolynomial.pderiv i P) * (w - v i) +
      MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) * (w - v i) ^ 2 / 2 := by
  have hdeg : (coordinatePolynomialHom v i P).natDegree ≤ 2 := by
    apply (natDegree_eval₂_affine_le P _ ?_).trans hP
    intro j
    split_ifs <;> simp
  have h := quadratic_taylor_exact (coordinatePolynomialHom v i P) hdeg (v i) w
  simpa only [derivative_coordinatePolynomialHom, eval_coordinatePolynomialHom,
    Function.update_eq_self] using h

/-- One native hidden bin changes the signal by at most a constant times its
terminal resolution, even when the native derivative scale is arbitrarily small. -/
theorem quadratic_hidden_bin_error {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 2) (v : σ → ℝ) (i : σ)
    {K B δ w : ℝ} (hK : 0 ≤ K) (hB : 0 < B) (hδ : 0 < δ)
    (hfirst : |MvPolynomial.eval v (MvPolynomial.pderiv i P)| ≤ K * B)
    (hsecond : |MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i P))| ≤ K * B ^ 2 / δ)
    (hdist : |w - v i| ≤ δ / B) :
    |MvPolynomial.eval (Function.update v i w) P - MvPolynomial.eval v P| ≤ 2 * K * δ := by
  have h1 : |MvPolynomial.eval v (MvPolynomial.pderiv i P) * (w - v i)| ≤ K * δ := by
    rw [abs_mul]
    calc
      _ ≤ (K * B) * (δ / B) := mul_le_mul hfirst hdist (abs_nonneg _) (mul_nonneg hK hB.le)
      _ = _ := by field_simp
  have h2 : |MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) *
      (w - v i) ^ 2| ≤ K * δ := by
    rw [abs_mul, abs_pow]
    calc
      _ ≤ (K * B ^ 2 / δ) * (δ / B) ^ 2 :=
        mul_le_mul hsecond (pow_le_pow_left₀ (abs_nonneg _) hdist 2) (sq_nonneg _)
          (by positivity)
      _ = _ := by field_simp
  rw [quadratic_coordinate_taylor P hP v i w]
  apply (abs_add_le _ _).trans
  have hhalf : |MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) *
      (w - v i) ^ 2 / 2| ≤ K * δ / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right h2 (by norm_num)
  linarith [mul_nonneg hK hδ.le]

/-- The observed hidden-bin center supplies a deterministic prediction of the
native signal at exact observed time and planar position. -/
theorem native_hidden_bin_prediction (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (v : Fin 4 → ℝ) {K B δ : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B) (hδ : 0 < δ)
    (hfirst : |MvPolynomial.eval v (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B)
    (hsecond : |MvPolynomial.eval v
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2 / δ) :
    |MvPolynomial.eval v P - MvPolynomial.eval
      (Function.update v (3 : Fin 4) (δ * (⌊B * v 3 / δ⌋ : ℝ) / B)) P| ≤ 2 * K * δ := by
  have hbin := floor_scaled_error hδ (B * v 3)
  have hdist : |δ * (⌊B * v 3 / δ⌋ : ℝ) / B - v 3| ≤ δ / B := by
    have heq : δ * (⌊B * v 3 / δ⌋ : ℝ) / B - v 3 =
        -(B * v 3 - δ * (⌊B * v 3 / δ⌋ : ℝ)) / B := by field_simp; ring
    rw [heq, abs_div, abs_neg, abs_of_pos hB]
    exact div_le_div_of_nonneg_right hbin hB.le
  simpa only [abs_sub_comm] using
    quadratic_hidden_bin_error P hP v (3 : Fin 4) hK hB hδ hfirst hsecond hdist

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/SignalLabels.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set
open Submission.Obl.k4_matching_homogeneous_records (floor_sub_bound)

/-- Predict the signal using only the exact base coordinates and the native
hidden-bin index. -/
noncomputable def hiddenSignalPrediction (P : MvPolynomial (Fin 4) ℝ) (B δ : ℝ)
    (v : Fin 4 → ℝ) : ℝ :=
  MvPolynomial.eval (Function.update v (3 : Fin 4) (δ * (⌊B * v 3 / δ⌋ : ℝ) / B)) P

/-- Equal observed bases and hidden bins give exactly the same prediction. -/
theorem hiddenSignalPrediction_eq_of_observation (P : MvPolynomial (Fin 4) ℝ)
    (B δ : ℝ) {v v' : Fin 4 → ℝ} (h₀ : v 0 = v' 0)
    (h₁ : v 1 = v' 1) (h₂ : v 2 = v' 2)
    (hbin : ⌊B * v 3 / δ⌋ = ⌊B * v' 3 / δ⌋) :
    hiddenSignalPrediction P B δ v = hiddenSignalPrediction P B δ v' := by
  apply congrArg (fun z : Fin 4 → ℝ => MvPolynomial.eval z P)
  funext j
  fin_cases j <;> simp [h₀, h₁, h₂, hbin]

/-- A deterministic finite list around the predicted signal-bin index. -/
noncomputable def signalBinList (prediction δ R : ℝ) : Finset ℤ :=
  Finset.Icc (⌊prediction / δ⌋ - ⌈R⌉) (⌊prediction / δ⌋ + ⌈R⌉)

theorem signalBinList_card (prediction δ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((signalBinList prediction δ R).card : ℝ) ≤ 2 * R + 3 := by
  have hceil : 0 ≤ ⌈R⌉ := Int.ceil_nonneg hR
  have hnat : ((2 * ⌈R⌉ + 1).toNat : ℤ) = 2 * ⌈R⌉ + 1 := Int.toNat_of_nonneg (by omega)
  have hcard : ((signalBinList prediction δ R).card : ℤ) = 2 * ⌈R⌉ + 1 := by
    simp only [signalBinList, Int.card_Icc]
    convert hnat using 1 <;> congr 1 <;> omega
  have hcard' : ((signalBinList prediction δ R).card : ℝ) = 2 * (⌈R⌉ : ℝ) + 1 := by
    exact_mod_cast hcard
  rw [hcard']
  linarith [Int.ceil_lt_add_one R]

/-- An error of `A` cell widths leaves at most a linear number of possible bins. -/
theorem floor_mem_signalBinList {x prediction δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (herror : |x - prediction| ≤ A * δ) :
    ⌊x / δ⌋ ∈ signalBinList prediction δ (A + 1) := by
  have hd : |x / δ - prediction / δ| ≤ A := by
    rw [← sub_div, abs_div, abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr herror
  have hfloor : |(((⌊x / δ⌋ - ⌊prediction / δ⌋ : ℤ) : ℝ))| ≤ A + 1 :=
    (floor_sub_bound _ _).trans (by linarith)
  have hR := Int.le_ceil (A + 1)
  have h := abs_le.mp (hfloor.trans hR)
  have hlo : -⌈A + 1⌉ ≤ ⌊x / δ⌋ - ⌊prediction / δ⌋ := by exact_mod_cast h.1
  have hhi : ⌊x / δ⌋ - ⌊prediction / δ⌋ ≤ ⌈A + 1⌉ := by exact_mod_cast h.2
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- The midpoint signal can be predicted at any observed incidence in its short
block, with an error independent of the reciprocal native derivative scale. -/
theorem native_midpoint_prediction_error (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (l : Trajectory) {K B δ q s t : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B) (hδ : 0 < δ)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (graphPoint l u) P| ≤ K)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hdt : |s - t| ≤ q)
    (hfirst : |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B)
    (hsecond : |MvPolynomial.eval (graphPoint l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2 / δ) :
    |MvPolynomial.eval (graphPoint l s) P - hiddenSignalPrediction P B δ (graphPoint l t)| ≤
      51 * K * q + 2 * K * δ := by
  have hv := bounded_quadratic_variation (native_quadratic P hP l) hbound hs ht
  have hv' := mul_le_mul_of_nonneg_left hdt (show 0 ≤ 51 * K by positivity)
  have hp := native_hidden_bin_prediction P hP (graphPoint l t) hK hB hδ hfirst hsecond
  have htri := abs_sub_le (MvPolynomial.eval (graphPoint l s) P)
    (MvPolynomial.eval (graphPoint l t) P) (hiddenSignalPrediction P B δ (graphPoint l t))
  change |MvPolynomial.eval (graphPoint l t) P - hiddenSignalPrediction P B δ (graphPoint l t)| ≤ _ at hp
  linarith

/-- The initial midpoint native label is known from the observation up to a
linear-size list in the common slack. -/
theorem native_midpoint_signal_list (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (l : Trajectory) {K B δ q s t : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B) (hδ : 0 < δ) (hq : q ≤ δ)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (graphPoint l u) P| ≤ K)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hdt : |s - t| ≤ q)
    (hfirst : |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B)
    (hsecond : |MvPolynomial.eval (graphPoint l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2 / δ) :
    ⌊MvPolynomial.eval (graphPoint l s) P / δ⌋ ∈
      signalBinList (hiddenSignalPrediction P B δ (graphPoint l t)) δ (53 * K + 1) ∧
    ((signalBinList (hiddenSignalPrediction P B δ (graphPoint l t)) δ (53 * K + 1)).card : ℝ) ≤
      106 * K + 5 := by
  have herror := native_midpoint_prediction_error P hP l hK hB hδ hbound hs ht hdt hfirst hsecond
  have hscale := mul_le_mul_of_nonneg_left hq (show 0 ≤ 51 * K by positivity)
  constructor
  · apply floor_mem_signalBinList hδ (by positivity)
    nlinarith
  · apply (signalBinList_card _ _ (show 0 ≤ 53 * K + 1 by positivity)).trans_eq
    ring

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/MidpointLabels.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set

noncomputable def positionBinList (y : Plane) (q K : ℝ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun i => signalBinList (y i) q (K + 1))

theorem positionBinList_card (y : Plane) (q : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ((positionBinList y q K).card : ℝ) ≤ (2 * K + 5) ^ 2 := by
  have hcard (i : Fin 2) : ((signalBinList (y i) q (K + 1)).card : ℝ) ≤ 2 * K + 5 := by
    apply (signalBinList_card _ _ (show 0 ≤ K + 1 by positivity)).trans_eq
    ring
  rw [positionBinList, Fintype.card_piFinset, Fin.prod_univ_two, Nat.cast_mul]
  simpa only [pow_two] using mul_le_mul (hcard 0) (hcard 1) (Nat.cast_nonneg _)
    (show 0 ≤ 2 * K + 5 by positivity)

theorem midpoint_position_mem_list (l : Trajectory) {K q s t : ℝ}
    (hq : 0 < q) (hK : ‖planarVelocity l‖ ≤ K) (hdt : |s - t| ≤ q) :
    (fun i : Fin 2 => ⌊planarPoint l s i / q⌋) ∈ positionBinList (planarPoint l t) q K := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hK₀ : 0 ≤ K := (norm_nonneg _).trans hK
  apply floor_mem_signalBinList hq hK₀
  have h := (PiLp.norm_apply_le (planarPoint l s - planarPoint l t) i).trans
    (planarPoint_variation hK hdt)
  simpa only [PiLp.sub_apply, Real.norm_eq_abs] using h

/-- The joint midpoint group is predicted entirely by the exact observed base
and the native hidden-bin code. -/
noncomputable def midpointLabelList (P : MvPolynomial (Fin 4) ℝ) (B δ q K : ℝ)
    (v : Fin 4 → ℝ) : Finset ((Fin 2 → ℤ) × ℤ) :=
  (positionBinList (WithLp.toLp 2 ![v 1, v 2]) q K) ×ˢ
    (signalBinList (hiddenSignalPrediction P B δ v) δ (53 * K + 1))

/-- An explicit decoder on the actual observed base and integer hidden bin. -/
noncomputable def midpointObservedDecoder (P : MvPolynomial (Fin 4) ℝ) (B δ q K : ℝ)
    (base : Fin 3 → ℝ) (j : ℤ) : Finset ((Fin 2 → ℤ) × ℤ) :=
  (positionBinList (WithLp.toLp 2 ![base 1, base 2]) q K) ×ˢ
    (signalBinList (MvPolynomial.eval ![base 0, base 1, base 2, δ * (j : ℝ) / B] P)
      δ (53 * K + 1))

theorem midpointLabelList_eq_decoder (P : MvPolynomial (Fin 4) ℝ) (B δ q K : ℝ)
    (v : Fin 4 → ℝ) :
    midpointLabelList P B δ q K v =
      midpointObservedDecoder P B δ q K (fun i : Fin 3 => v i.castSucc) ⌊B * v 3 / δ⌋ := by
  have hpredict : hiddenSignalPrediction P B δ v =
      MvPolynomial.eval ![v 0, v 1, v 2, δ * (⌊B * v 3 / δ⌋ : ℝ) / B] P := by
    apply congrArg (fun z : Fin 4 → ℝ => MvPolynomial.eval z P)
    ext i
    fin_cases i <;> simp
  unfold midpointLabelList midpointObservedDecoder
  rw [hpredict]
  rfl

/-- Every fixed-label membership predicate of the observation decoder is
measurable, as required when taking its original joint density. -/
theorem measurableSet_midpointObservedDecoder (P : MvPolynomial (Fin 4) ℝ)
    (B δ q K : ℝ) (code : (Fin 2 → ℤ) × ℤ) :
    MeasurableSet {z : (Fin 3 → ℝ) × ℤ | code ∈ midpointObservedDecoder P B δ q K z.1 z.2} := by
  have hpred : Measurable (fun z : (Fin 3 → ℝ) × ℤ =>
      MvPolynomial.eval ![z.1 0, z.1 1, z.1 2, δ * (z.2 : ℝ) / B] P) :=
    (MvPolynomial.continuous_eval P).measurable.comp (by fun_prop)
  have hfloor := Int.measurable_floor.comp (hpred.div_const δ)
  have hy (i : Fin 2) : Measurable (fun z : (Fin 3 → ℝ) × ℤ =>
      ⌊(WithLp.toLp 2 ![z.1 1, z.1 2] : Plane) i / q⌋) := by fun_prop
  let S : Fin 2 → Set ((Fin 3 → ℝ) × ℤ) := fun i =>
    {z | ⌊(WithLp.toLp 2 ![z.1 1, z.1 2] : Plane) i / q⌋ - ⌈K + 1⌉ ≤ code.1 i ∧
      code.1 i ≤ ⌊(WithLp.toLp 2 ![z.1 1, z.1 2] : Plane) i / q⌋ + ⌈K + 1⌉}
  let T : Set ((Fin 3 → ℝ) × ℤ) :=
    {z | ⌊MvPolynomial.eval ![z.1 0, z.1 1, z.1 2, δ * (z.2 : ℝ) / B] P / δ⌋ - ⌈53 * K + 1⌉ ≤ code.2 ∧
      code.2 ≤ ⌊MvPolynomial.eval ![z.1 0, z.1 1, z.1 2, δ * (z.2 : ℝ) / B] P / δ⌋ + ⌈53 * K + 1⌉}
  have heq : {z : (Fin 3 → ℝ) × ℤ | code ∈ midpointObservedDecoder P B δ q K z.1 z.2} =
      (⋂ i, S i) ∩ T := by
    ext z
    simp only [midpointObservedDecoder, Finset.mem_product, positionBinList,
      Fintype.mem_piFinset, signalBinList, Finset.mem_Icc, S, T,
      mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [heq]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (measurableSet_le ((hy i).sub_const _) measurable_const).inter
      (measurableSet_le measurable_const ((hy i).add_const _))
  · exact (measurableSet_le (hfloor.sub_const _) measurable_const).inter
      (measurableSet_le measurable_const (hfloor.add_const _))

theorem midpointLabelList_card (P : MvPolynomial (Fin 4) ℝ) (B δ q : ℝ)
    {K : ℝ} (hK : 0 ≤ K) (v : Fin 4 → ℝ) :
    ((midpointLabelList P B δ q K v).card : ℝ) ≤
      (2 * K + 5) ^ 2 * (106 * K + 5) := by
  rw [midpointLabelList, Finset.card_product, Nat.cast_mul]
  have hs : ((signalBinList (hiddenSignalPrediction P B δ v) δ (53 * K + 1)).card : ℝ) ≤
      106 * K + 5 := by
    apply (signalBinList_card _ _ (show 0 ≤ 53 * K + 1 by positivity)).trans_eq
    ring
  exact mul_le_mul (positionBinList_card _ _ hK) hs (Nat.cast_nonneg _) (sq_nonneg _)

theorem midpointLabelList_eq_of_observation (P : MvPolynomial (Fin 4) ℝ)
    (B δ q K : ℝ) {v v' : Fin 4 → ℝ} (h₀ : v 0 = v' 0)
    (h₁ : v 1 = v' 1) (h₂ : v 2 = v' 2)
    (hbin : ⌊B * v 3 / δ⌋ = ⌊B * v' 3 / δ⌋) :
    midpointLabelList P B δ q K v = midpointLabelList P B δ q K v' := by
  have hy : (WithLp.toLp 2 ![v 1, v 2] : Plane) = WithLp.toLp 2 ![v' 1, v' 2] := by
    ext i
    fin_cases i <;> simp [h₁, h₂]
  unfold midpointLabelList
  rw [hy, hiddenSignalPrediction_eq_of_observation P B δ h₀ h₁ h₂ hbin]

/-- The label-list bound uses the exact model's original curvature bound. Its
size is polynomial only in the common slack, independent of hidden-bin scale. -/
theorem native_midpoint_joint_list (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (l : Trajectory) {K B δ q s t : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hq : 0 < q) (hqδ : q ≤ δ) (hV : ‖planarVelocity l‖ ≤ K)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (graphPoint l u) P| ≤ K)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hdt : |s - t| ≤ q)
    (hfirst : |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B)
    (hsecond : |MvPolynomial.eval (graphPoint l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2) :
    ((fun i : Fin 2 => ⌊planarPoint l s i / q⌋),
      ⌊MvPolynomial.eval (graphPoint l s) P / δ⌋) ∈
        midpointLabelList P B δ q K (graphPoint l t) := by
  have hsecond' : |MvPolynomial.eval (graphPoint l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2 / δ := by
    apply hsecond.trans
    apply (le_div_iff₀ hδ).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ₁ (mul_nonneg hK (sq_nonneg B))
  have hsig := (native_midpoint_signal_list P hP l hK hB hδ hqδ hbound hs ht hdt hfirst hsecond').1
  have hy : (WithLp.toLp 2 ![(graphPoint l t) 1, (graphPoint l t) 2] : Plane) =
      planarPoint l t := by ext i; fin_cases i <;> rfl
  apply Finset.mem_product.mpr
  constructor
  · rw [hy]
    exact midpoint_position_mem_list l hq hV hdt
  · exact hsig

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/BooleanFormat.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Submission.Obl.k4_eligibility_sign_description

/-- Two nonnegative predicates recover all three possible signs. -/
def signOfBits (a b : Bool) : SignType :=
  if a then (if b then 0 else 1) else -1

lemma signOfBits_nonneg (x : ℝ) :
    signOfBits (decide (0 ≤ x)) (decide (0 ≤ -x)) = SignType.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [signOfBits, not_le.mpr hx, sign_neg hx]
  · simp [hx, signOfBits]
  · simp [signOfBits, hx.le, not_le.mpr (neg_neg_of_pos hx), sign_pos hx]

/-- A polynomial sign description is expressible using the frozen Boolean
nonnegative format with twice as many polynomials and the same degree bound. -/
theorem polynomialFormat_of_signRep {n m d : ℕ} {N : ℝ} {M : ℕ}
    {S : Set (Fin n → ℝ)}
    (h : SignRep (fun x : Fin n → ℝ => x) m d (fun x => x ∈ S))
    (hcount : ((m + m : ℕ) : ℝ) ≤ N ^ M) : PolynomialFormat N M d S := by
  classical
  obtain ⟨p, B, hp, hB⟩ := h
  let q : Fin (m + m) → MvPolynomial (Fin n) ℝ := Fin.addCases p (fun i => -p i)
  let b : (Fin (m + m) → Bool) → Bool := fun v =>
    decide ((fun i => signOfBits (v (Fin.castAdd m i)) (v (Fin.natAdd m i))) ∈ B)
  refine ⟨m + m, hcount, q, ?_, b, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [q, Fin.addCases_left] using hp j
    · simpa only [q, Fin.addCases_right, MvPolynomial.totalDegree_neg] using hp j
  · intro x
    change x ∈ S ↔ decide ((fun i => signOfBits
      (decide (0 ≤ MvPolynomial.eval x (q (Fin.castAdd m i))))
      (decide (0 ≤ MvPolynomial.eval x (q (Fin.natAdd m i))))) ∈ B) = true
    simp only [q, Fin.addCases_left, Fin.addCases_right, map_neg, signOfBits_nonneg,
      decide_eq_true_eq]
    exact (hB x).symm

/-- Every predicate in the frozen Boolean polynomial format is measurable. -/
theorem PolynomialFormat.measurableSet {n : ℕ} {N : ℝ} {M D : ℕ}
    {S : Set (Fin n → ℝ)} (h : PolynomialFormat N M D S) : MeasurableSet S := by
  classical
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  have heval : Measurable (fun x : Fin n → ℝ =>
      fun i : Fin m => decide (0 ≤ MvPolynomial.eval x (p i))) := by
    apply Measurable.of_eval
    intro i
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      (measurableSet_le measurable_const (MvPolynomial.continuous_eval (p i)).measurable)
  have hmeas := (measurable_of_countable b).comp heval
  have heq : S = (fun x : Fin n → ℝ => b
      (fun i : Fin m => decide (0 ≤ MvPolynomial.eval x (p i)))) ⁻¹' {true} := by
    ext x
    exact hb x
  rw [heq]
  exact hmeas (measurableSet_singleton true)

/-- Countably many indexed polynomial-format coefficient sets give a measurable
trajectory assignment, without imposing a global finite bound on the unused indices. -/
theorem measurableSet_indexed_polynomialFormat {n : ℕ} {N : ℝ} {M D : ℕ}
    {S : Set (ℕ × (Fin n → ℝ))}
    (h : ∀ i, PolynomialFormat N M D {x | (i, x) ∈ S}) : MeasurableSet S := by
  have heq : S = ⋃ i : ℕ, ({i} : Set ℕ) ×ˢ {x | (i, x) ∈ S} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf]
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun i => (measurableSet_singleton i).prod ((h i).measurableSet))

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/WholeBlock.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set
open Submission.Obl.k4_eligibility_sign_description

/-- A coordinate pullback by a permutation (or any coordinate map) preserves
the number and degree of polynomial sign tests. -/
theorem signRep_pullback {σ X : Type*} {n m d : ℕ} {v : X → σ → ℝ}
    {P : X → Prop} (h : SignRep v m d P) (F : (Fin n → ℝ) → X)
    (ρ : σ → Fin n) (hρ : ∀ x i, v (F x) i = x (ρ i)) :
    SignRep (fun x : Fin n → ℝ => x) m d (fun x => P (F x)) := by
  obtain ⟨p, A, hp, hA⟩ := h
  refine ⟨fun i => MvPolynomial.rename ρ (p i), A,
    fun i => (MvPolynomial.totalDegree_rename_le ρ (p i)).trans (hp i), ?_⟩
  intro x
  have hcoords : x ∘ ρ = v (F x) := funext (fun i => (hρ x i).symm)
  simpa only [MvPolynomial.eval_rename, hcoords] using hA (F x)

/-- The paper's slope/intercept pair in the frozen trajectory coordinate order. -/
def coefficientPair (x : Fin 6 → ℝ) : E3 × E3 :=
  (WithLp.toLp 2 (fun i : Fin 3 => x (Fin.natAdd 3 i)),
    WithLp.toLp 2 (fun i : Fin 3 => x (Fin.castAdd 3 i)))

/-- A geometric fit asks for all four terminal bounds on the complete time block. -/
def WholeBlockFit (P : MvPolynomial (Fin 4) ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (c u : Plane) (K B δ l r : ℝ) (x : Fin 6 → ℝ) : Prop :=
  ∀ t ∈ Icc l r,
    ‖Matrix.toEuclideanLin (Q⁻¹) (planarPoint (0, x) t - c - t • u)‖ ≤ K ∧
    |MvPolynomial.eval (graphPoint (0, x) t) P| ≤ K * δ ∧
    |MvPolynomial.eval (graphPoint (0, x) t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B ∧
    |MvPolynomial.eval (graphPoint (0, x) t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2 / δ

/-- Uniform semialgebraic complexity of a whole-block geometric fit, including
both derivative upper bounds. No time discretization or measurable search is used. -/
theorem wholeBlockFit_signRep (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : Plane)
    (K B δ l r : ℝ) (hK : 0 ≤ K) (hlr : l ≤ r) :
    SignRep (fun x : Fin 6 → ℝ => x) 42 4 (WholeBlockFit P Q c u K B δ l r) := by
  let P₁ := MvPolynomial.pderiv (3 : Fin 4) P
  let P₂ := MvPolynomial.pderiv (3 : Fin 4) P₁
  have hP₁ : P₁.totalDegree ≤ 2 := (degree_pderiv_le P _).trans hP
  have hP₂ : P₂.totalDegree ≤ 2 := (degree_pderiv_le P₁ _).trans hP₁
  have hnorm := SignRep.transverse_norm (Q⁻¹) c u K l r hK hlr
  have hvalue := SignRep.trace_abs P hP (K * δ) l r hlr
  have hfirst := SignRep.trace_abs P₁ hP₁ (K * B) l r hlr
  have hsecond := SignRep.trace_abs P₂ hP₂ (K * B ^ 2 / δ) l r hlr
  have h := signRep_pullback (((hnorm.and hvalue).and hfirst).and hsecond)
    coefficientPair
    (Sum.elim (fun i : Fin 3 => Fin.natAdd 3 i) (fun i : Fin 3 => Fin.castAdd 3 i))
    (by intro x i; cases i <;> rfl)
  apply h.congr
  intro x
  have hplanar (t : ℝ) :
      WithLp.toLp 2 (fun j : Fin 2 =>
        ((coefficientPair x).2 + t • (coefficientPair x).1) j.castSucc - c j - t * u j) =
      planarPoint (0, x) t - c - t • u := by
    ext j
    fin_cases j <;> rfl
  have hgraph (t : ℝ) :
      ![t, ((coefficientPair x).2 + t • (coefficientPair x).1) 0,
        ((coefficientPair x).2 + t • (coefficientPair x).1) 1,
        ((coefficientPair x).2 + t • (coefficientPair x).1) 2] = graphPoint (0, x) t := by
    ext j
    fin_cases j <;> rfl
  simp only [hplanar, hgraph, WholeBlockFit, forall_and, P₁, P₂]
  tauto

/-- Whole-block fits have a Boolean nonnegative description with 84 polynomial
conditions, each of total degree at most four. -/
theorem wholeBlockFit_polynomialFormat (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : Plane)
    (K B δ l r N : ℝ) (M : ℕ) (hK : 0 ≤ K) (hlr : l ≤ r)
    (hcount : (84 : ℝ) ≤ N ^ M) :
    PolynomialFormat N M 4 {x | WholeBlockFit P Q c u K B δ l r x} := by
  exact polynomialFormat_of_signRep (wholeBlockFit_signRep P hP Q c u K B δ l r hK hlr)
    (by norm_num; exact hcount)

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/MidpointGroupFormat.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set
open Submission.Obl.k4_eligibility_sign_description

/-- A half-open polynomial value bin uses two sign tests and preserves degree. -/
theorem polynomial_bin_signRep {σ X : Type*} (v : X → σ → ℝ)
    (p : MvPolynomial σ ℝ) {d : ℕ} (hp : p.totalDegree ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    SignRep v 2 d (fun x => ⌊MvPolynomial.eval (v x) p / δ⌋ = k) := by
  have hlo := SignRep.nonneg v (p - MvPolynomial.C (δ * (k : ℝ))) d
    (degree_sub_le hp (by simp only [MvPolynomial.totalDegree_C]; omega))
  have hhi := SignRep.nonneg v (p - MvPolynomial.C (δ * ((k : ℝ) + 1))) d
    (degree_sub_le hp (by simp only [MvPolynomial.totalDegree_C]; omega))
  have h := hlo.and hhi.not
  simp only [max_self] at h
  apply h.congr
  intro x
  simp only [map_sub, MvPolynomial.eval_C, not_le]
  rw [Int.floor_eq_iff]
  rw [le_div_iff₀ hδ, div_lt_iff₀ hδ]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- The actual midpoint code of a trajectory, in the frozen coordinate order. -/
noncomputable def midpointGroupCode (P : MvPolynomial (Fin 4) ℝ) (s q δ : ℝ)
    (x : Fin 6 → ℝ) : (Fin 2 → ℤ) × ℤ :=
  ((fun i => ⌊planarPoint (0, x) s i / q⌋),
    ⌊MvPolynomial.eval (graphPoint (0, x) s) P / δ⌋)

theorem midpoint_position_bin_signRep (s : ℝ) {q : ℝ} (hq : 0 < q)
    (i : Fin 2) (k : ℤ) :
    SignRep (fun x : Fin 6 → ℝ => x) 2 2
      (fun x => ⌊planarPoint (0, x) s i / q⌋ = k) := by
  let p : MvPolynomial (Fin 6) ℝ :=
    MvPolynomial.X i.castSucc.castSucc.castSucc.castSucc +
      MvPolynomial.C s * MvPolynomial.X (Fin.natAdd 3 i.castSucc)
  have hp : p.totalDegree ≤ 2 := by
    apply degree_add_le
    · simp
    · exact (degree_C_mul_le _ _).trans (by simp)
  apply (polynomial_bin_signRep (fun x : Fin 6 → ℝ => x) p hp hq k).congr
  intro x
  have heval : MvPolynomial.eval x p = planarPoint (0, x) s i := by
    fin_cases i <;> simp [p, planarPoint]
  rw [heval]

theorem midpoint_native_bin_signRep (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (s : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    SignRep (fun x : Fin 6 → ℝ => x) 2 2
      (fun x => ⌊MvPolynomial.eval (graphPoint (0, x) s) P / δ⌋ = k) := by
  have h := polynomial_bin_signRep coords (tracePoly P s)
    ((degree_tracePoly P s).trans hP) hδ k
  have h' := signRep_pullback h coefficientPair
    (Sum.elim (fun i : Fin 3 => Fin.natAdd 3 i) (fun i : Fin 3 => Fin.castAdd 3 i))
    (by intro x i; cases i <;> rfl)
  apply h'.congr
  intro x
  rw [eval_tracePoly]
  have hgraph :
      ![s, ((coefficientPair x).2 + s • (coefficientPair x).1) 0,
        ((coefficientPair x).2 + s • (coefficientPair x).1) 1,
        ((coefficientPair x).2 + s • (coefficientPair x).1) 2] = graphPoint (0, x) s := by
    ext j
    fin_cases j <;> rfl
  rw [hgraph]

/-- Grouping by the two spatial bins and the native signal bin is uniformly
semialgebraic, regardless of the number of groups actually used. -/
theorem midpointGroupCode_signRep (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (s : ℝ) {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (Γ : (Fin 2 → ℤ) × ℤ) :
    SignRep (fun x : Fin 6 → ℝ => x) 6 2 (fun x => midpointGroupCode P s q δ x = Γ) := by
  rcases Γ with ⟨γ, k⟩
  have h := ((midpoint_position_bin_signRep s hq 0 (γ 0)).and
    (midpoint_position_bin_signRep s hq 1 (γ 1))).and
    (midpoint_native_bin_signRep P hP s hδ k)
  apply h.congr
  intro x
  simp only [midpointGroupCode, Prod.mk.injEq, funext_iff, Fin.forall_fin_two]

theorem midpointGroupCode_polynomialFormat (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (s : ℝ) {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (Γ : (Fin 2 → ℤ) × ℤ) {N : ℝ} {M : ℕ} (hcount : (12 : ℝ) ≤ N ^ M) :
    PolynomialFormat N M 2 {x | midpointGroupCode P s q δ x = Γ} := by
  exact polynomialFormat_of_signRep (midpointGroupCode_signRep P hP s hq hδ Γ)
    (by norm_num; exact hcount)

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/MidpointGroupBounds.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set

/-- A finite universe for every midpoint group on the original bounded support. -/
noncomputable def midpointGroupUniverse (q δ K : ℝ) : Finset ((Fin 2 → ℤ) × ℤ) :=
  positionBinList 0 q (2 * K / q) ×ˢ signalBinList 0 δ (K / δ + 1)

theorem midpointGroupUniverse_card {q δ K : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (hK : 0 ≤ K) :
    ((midpointGroupUniverse q δ K).card : ℝ) ≤
      (4 * K / q + 5) ^ 2 * (2 * K / δ + 5) := by
  have hp := positionBinList_card (0 : Plane) q
    (show 0 ≤ 2 * K / q by positivity)
  have hs := signalBinList_card 0 δ (show 0 ≤ K / δ + 1 by positivity)
  have hp' : ((positionBinList 0 q (2 * K / q)).card : ℝ) ≤ (4 * K / q + 5) ^ 2 := by
    convert hp using 1 <;> congr 1 <;> ring
  have hs' : ((signalBinList 0 δ (K / δ + 1)).card : ℝ) ≤ 2 * K / δ + 5 := by
    convert hs using 1 <;> ring
  rw [midpointGroupUniverse, Finset.card_product, Nat.cast_mul]
  exact mul_le_mul hp' hs' (Nat.cast_nonneg _) (sq_nonneg _)

theorem midpointGroupCode_mem_universe (P : MvPolynomial (Fin 4) ℝ)
    (s : ℝ) {q δ K : ℝ} (hq : 0 < q) (hδ : 0 < δ) (hK : 0 ≤ K)
    (x : Fin 6 → ℝ) (hy : ‖planarPoint (0, x) s‖ ≤ 2 * K)
    (hnative : |MvPolynomial.eval (graphPoint (0, x) s) P| ≤ K) :
    midpointGroupCode P s q δ x ∈ midpointGroupUniverse q δ K := by
  apply Finset.mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro i
    apply floor_mem_signalBinList hq (show 0 ≤ 2 * K / q by positivity)
    have hi := (PiLp.norm_apply_le (planarPoint (0, x) s) i).trans hy
    simpa only [PiLp.zero_apply, sub_zero, Real.norm_eq_abs,
      div_mul_cancel₀ _ hq.ne'] using hi
  · apply floor_mem_signalBinList hδ (show 0 ≤ K / δ by positivity)
    simpa only [sub_zero, div_mul_cancel₀ _ hδ.ne'] using hnative

/-- The full group count is polynomial in inverse scales and the old support
bound. The compatible decoder lists remain much smaller. -/
theorem midpointGroupUniverse_card_coarse {q δ K : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (hq1 : q ≤ 1) (hδ1 : δ ≤ 1) (hK : 1 ≤ K) :
    ((midpointGroupUniverse q δ K).card : ℝ) ≤ 567 * K ^ 3 / (q ^ 2 * δ) := by
  have hK₀ : 0 ≤ K := le_trans zero_le_one hK
  have hqK : q ≤ K := hq1.trans hK
  have hδK : δ ≤ K := hδ1.trans hK
  have hp : 4 * K / q + 5 ≤ 9 * K / q := by
    apply (le_div_iff₀ hq).mpr
    field_simp
    nlinarith
  have hs : 2 * K / δ + 5 ≤ 7 * K / δ := by
    apply (le_div_iff₀ hδ).mpr
    field_simp
    nlinarith
  calc
    ((midpointGroupUniverse q δ K).card : ℝ) ≤
        (4 * K / q + 5) ^ 2 * (2 * K / δ + 5) := midpointGroupUniverse_card hq hδ hK₀
    _ ≤ (9 * K / q) ^ 2 * (7 * K / δ) := by
      apply mul_le_mul _ hs (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hp 2
    _ = 567 * K ^ 3 / (q ^ 2 * δ) := by ring

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/AffineRescale.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set
open scoped BigOperators

/-- Scaling a nonsingular planar frame scales its inverse reciprocally. -/
theorem scaled_frame_inverse {r : ℝ} (hr : r ≠ 0) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Matrix.det Q ≠ 0) : (r • Q)⁻¹ = r⁻¹ • Q⁻¹ := by
  letI : Invertible r := invertibleOfNonzero hr
  simpa only [invOf_eq_inv] using Matrix.inv_smul Q r (isUnit_iff_ne_zero.mpr hQ)

theorem scaled_frame_inverse_action {r : ℝ} (hr : r ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Matrix.det Q ≠ 0) (z : Plane) :
    Matrix.toEuclideanLin ((r • Q)⁻¹) (r • z) = Matrix.toEuclideanLin (Q⁻¹) z := by
  rw [scaled_frame_inverse hr Q hQ]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hr, one_smul]

theorem scaled_frame_abs_det {r : ℝ} (hr : 0 ≤ r) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    |Matrix.det (r • Q)| = r ^ 2 * |Matrix.det Q| := by
  rw [Matrix.det_smul, Fintype.card_fin, abs_mul, abs_pow, abs_of_nonneg hr]

theorem scaled_frame_entries {r : ℝ} (hr : 0 ≤ r) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, |(r • Q) i j|) =
      r * (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) := by
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hr, Finset.mul_sum]

theorem scaled_frame_entry_budget {r : ℝ} (hr : 0 < r)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Matrix.det Q ≠ 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, (|(r • Q) i j| + |(r • Q)⁻¹ i j|)) =
      r * (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) +
      r⁻¹ * (∑ i : Fin 2, ∑ j : Fin 2, |(Q⁻¹) i j|) := by
  rw [scaled_frame_inverse hr.ne' Q hQ]
  simp only [Finset.sum_add_distrib, scaled_frame_entries hr.le,
    scaled_frame_entries (inv_nonneg.mpr hr.le)]

noncomputable def normalizedBlockIntercept (b u origin : Plane) (s r : ℝ) : Plane :=
  r⁻¹ • (b + s • u - origin)

noncomputable def normalizedBlockVelocity (u : Plane) (q r : ℝ) : Plane := (q / r) • u

noncomputable def liftedBlockCenter (origin c w : Plane) (s q r : ℝ) : Plane :=
  origin + r • c - s • ((r / q) • w)

noncomputable def liftedBlockSpeed (w : Plane) (q r : ℝ) : Plane := (r / q) • w

/-- The old-coordinate residual is exactly `r` times the normalized residual at
normalized block time. Native tests remain in their original coordinates. -/
theorem affine_block_residual (b u origin c w : Plane) (s t : ℝ)
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    b + t • u - liftedBlockCenter origin c w s q r - t • liftedBlockSpeed w q r =
      r • (normalizedBlockIntercept b u origin s r +
        ((t - s) / q) • normalizedBlockVelocity u q r - c - ((t - s) / q) • w) := by
  ext i
  simp only [liftedBlockCenter, liftedBlockSpeed, normalizedBlockIntercept,
    normalizedBlockVelocity, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Whole normalized-block confinement lifts with no loss in its norm bound. -/
theorem affine_block_fit (b u origin c w : Plane) (s : ℝ)
    {q r K : ℝ} (hq : 0 < q) (hr : 0 < r)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Matrix.det Q ≠ 0)
    (hfit : ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin (Q⁻¹)
        (normalizedBlockIntercept b u origin s r + τ • normalizedBlockVelocity u q r - c - τ • w)‖ ≤ K) :
    ∀ t ∈ Icc s (s + q),
      ‖Matrix.toEuclideanLin ((r • Q)⁻¹)
        (b + t • u - liftedBlockCenter origin c w s q r - t • liftedBlockSpeed w q r)‖ ≤ K := by
  intro t ht
  rw [affine_block_residual b u origin c w s t hq hr, scaled_frame_inverse_action hr.ne' Q hQ]
  apply hfit
  exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hq.le, (div_le_one hq).mpr (by linarith [ht.2])⟩

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/GroupNormalization.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set

def midpointGroupCenter (q : ℝ) (Γ : (Fin 2 → ℤ) × ℤ) : Plane :=
  WithLp.toLp 2 (fun i => q * (Γ.1 i : ℝ))

theorem midpointGroupCenter_eq (P : MvPolynomial (Fin 4) ℝ) (s q δ : ℝ)
    (x : Fin 6 → ℝ) (Γ : (Fin 2 → ℤ) × ℤ)
    (hΓ : midpointGroupCode P s q δ x = Γ) :
    midpointGroupCenter q Γ = planeBinCenter q (planarPoint (0, x) s) := by
  rw [← hΓ]
  rfl

theorem planarPoint_affine (l : Trajectory) (t : ℝ) :
    planarPoint l t = planarPoint l 0 + t • planarVelocity l := by
  ext i
  fin_cases i <;> simp [planarPoint, planarVelocity, PiLp.add_apply, PiLp.smul_apply]

/-- The grouping radius normalizes both intercept and speed to the unit ball.
The center is constant throughout each whole midpoint group. -/
theorem midpoint_group_normalized_bounds (P : MvPolynomial (Fin 4) ℝ)
    (s a δ : ℝ) {q K : ℝ} (hq : 0 < q) (hK : 0 ≤ K)
    (x : Fin 6 → ℝ) (Γ : (Fin 2 → ℤ) × ℤ)
    (hΓ : midpointGroupCode P s q δ x = Γ)
    (hV : ‖planarVelocity (0, x)‖ ≤ K) (has : |a - s| ≤ q) :
    ‖normalizedBlockIntercept (planarPoint (0, x) 0) (planarVelocity (0, x))
      (midpointGroupCenter q Γ) a ((K + 2) * q)‖ ≤ 1 ∧
    ‖normalizedBlockVelocity (planarVelocity (0, x)) q ((K + 2) * q)‖ ≤ 1 := by
  have hr : 0 < (K + 2) * q := by positivity
  have hb : ‖planarPoint (0, x) a - midpointGroupCenter q Γ‖ ≤ (K + 2) * q := by
    rw [midpointGroupCenter_eq P s q δ x Γ hΓ]
    have htri := norm_sub_le_norm_sub_add_norm_sub (planarPoint (0, x) a)
      (planarPoint (0, x) s) (planeBinCenter q (planarPoint (0, x) s))
    linarith [planarPoint_variation hV has, planeBinCenter_error hq (planarPoint (0, x) s)]
  constructor
  · rw [normalizedBlockIntercept, ← planarPoint_affine]
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hr.le)]
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hr.le)).trans_eq (inv_mul_cancel₀ hr.ne')
  · rw [normalizedBlockVelocity, norm_smul_of_nonneg (div_nonneg hq.le hr.le)]
    apply (mul_le_mul_of_nonneg_left hV (div_nonneg hq.le hr.le)).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_one hr).mpr
    nlinarith

/-- The whole-block native inequalities and the lifted geometric confinement
use one common slack, without loss in a reciprocal derivative scale. -/
theorem initial_group_wholeBlockFit (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Matrix.det Q ≠ 0)
    (c w : Plane) (a s : ℝ) {q δ B K : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hqδ : q ≤ δ) (hB : 0 < B) (hK : 0 ≤ K)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hblock : Icc a (a + q) ⊆ Icc (0 : ℝ) 1)
    (hnear : ∀ t ∈ Icc a (a + q), |t - s| ≤ q)
    (x : Fin 6 → ℝ) (Γ : (Fin 2 → ℤ) × ℤ)
    (hΓ : midpointGroupCode P s q δ x = Γ)
    (hvalue : ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (graphPoint (0, x) t) P| ≤ K)
    (hfirst : ∀ t ∈ Icc (0 : ℝ) 1,
      |MvPolynomial.eval (graphPoint (0, x) t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B)
    (hsecond : ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (graphPoint (0, x) t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2)
    (hfit : ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin (Q⁻¹)
        (normalizedBlockIntercept (planarPoint (0, x) 0) (planarVelocity (0, x))
          (midpointGroupCenter q Γ) a ((K + 2) * q) +
          τ • normalizedBlockVelocity (planarVelocity (0, x)) q ((K + 2) * q) - c - τ • w)‖ ≤ 2) :
    WholeBlockFit (shiftedTest P (δ * (Γ.2 : ℝ))) (((K + 2) * q) • Q)
      (liftedBlockCenter (midpointGroupCenter q Γ) c w a q ((K + 2) * q))
      (liftedBlockSpeed w q ((K + 2) * q)) (51 * K + 3) B δ a (a + q) x := by
  have hr : 0 < (K + 2) * q := by positivity
  have hgeom := affine_block_fit (planarPoint (0, x) 0) (planarVelocity (0, x))
    (midpointGroupCenter q Γ) c w a hq hr Q hQ hfit
  have hnativeCode : ⌊MvPolynomial.eval (graphPoint (0, x) s) P / δ⌋ = Γ.2 :=
    congrArg Prod.snd hΓ
  intro t ht
  have ht01 := hblock ht
  have hcenter := shifted_native_signal_bound P hP (0, x) hδ hvalue ht01 hs (hnear t ht)
  rw [hnativeCode] at hcenter
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hg := hgeom t ht
    rw [← planarPoint_affine] at hg
    exact hg.trans (by linarith)
  · exact hcenter.trans (by nlinarith [mul_le_mul_of_nonneg_left hqδ (show 0 ≤ 51 * K by positivity)])
  · rw [pderiv_shiftedTest]
    exact (hfirst t ht01).trans (by nlinarith)
  · rw [pderiv_shiftedTest]
    apply (hsecond t ht01).trans
    apply (le_div_iff₀ hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδ1 (mul_nonneg hK (sq_nonneg B))]

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/Scales.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

/-- The exact dyadic exponent occurring in the frozen observation maps. -/
noncomputable def scaleIndex (N r : ℝ) : ℤ := ⌊r * Real.log N / Real.log 2⌋

/-- The unnormalized true hidden-bin width, including its dyadic rounding. -/
noncomputable def resolution (N r : ℝ) : ℝ := (2 : ℝ) ^ (-scaleIndex N r)

/-- Rounding an exponent down changes the corresponding power by less than two. -/
theorem scaleIndex_bounds {N : ℝ} (hN : 0 < N) (r : ℝ) :
    (2 : ℝ) ^ scaleIndex N r ≤ N ^ r ∧ N ^ r < 2 * (2 : ℝ) ^ scaleIndex N r := by
  let x := r * Real.log N / Real.log 2
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have heq : (2 : ℝ) ^ x = N ^ r := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hN]
    congr 1
    dsimp [x]
    field_simp
  have hlo : (scaleIndex N r : ℝ) ≤ x := Int.floor_le _
  have hhi : x < (scaleIndex N r : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · calc
      _ = (2 : ℝ) ^ (scaleIndex N r : ℝ) := (Real.rpow_intCast ..).symm
      _ ≤ (2 : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlo
      _ = N ^ r := heq
  · calc
      N ^ r = (2 : ℝ) ^ x := heq.symm
      _ < (2 : ℝ) ^ ((scaleIndex N r : ℝ) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hhi
      _ = 2 * (2 : ℝ) ^ scaleIndex N r := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_intCast]
        ring

theorem resolution_pos (N r : ℝ) : 0 < resolution N r := by
  unfold resolution
  positivity

/-- The frozen dyadic width lies between N^(-r) and twice that width. -/
theorem resolution_bounds {N : ℝ} (hN : 0 < N) (r : ℝ) :
    N ^ (-r) ≤ resolution N r ∧ resolution N r ≤ 2 * N ^ (-r) := by
  obtain ⟨hlo, hhi⟩ := scaleIndex_bounds hN r
  have hD : (0 : ℝ) < (2 : ℝ) ^ scaleIndex N r := by positivity
  have hNr : 0 < N ^ r := Real.rpow_pos_of_pos hN _
  rw [resolution, zpow_neg, Real.rpow_neg hN.le]
  constructor
  · exact (inv_le_inv₀ hNr hD).mpr hlo
  · change ((2 : ℝ) ^ scaleIndex N r)⁻¹ ≤ 2 / N ^ r
    apply (le_div_iff₀ hNr).mpr
    rw [show ((2 : ℝ) ^ scaleIndex N r)⁻¹ * N ^ r =
      N ^ r / ((2 : ℝ) ^ scaleIndex N r) by ring]
    exact (div_le_iff₀ hD).mpr hhi.le

/-- Nonnegative depths over bases at least one have a genuine finite dyadic
partition; its reciprocal length is exactly the frozen hidden resolution. -/
theorem exists_time_partition {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) :
    ∃ T : ℕ, (2 : ℝ) ^ T ≤ N ^ r ∧ resolution N r = ((2 : ℝ) ^ T)⁻¹ := by
  have hi : 0 ≤ scaleIndex N r := Int.floor_nonneg.mpr
    (div_nonneg (mul_nonneg hr (Real.log_nonneg hN)) (Real.log_nonneg (by norm_num)))
  let T := (scaleIndex N r).toNat
  have hT : (T : ℤ) = scaleIndex N r := Int.toNat_of_nonneg hi
  refine ⟨T, ?_, ?_⟩
  · simpa only [← hT, zpow_natCast] using
      (scaleIndex_bounds (lt_of_lt_of_le zero_lt_one hN) r).1
  · rw [resolution, ← hT, zpow_neg, zpow_natCast]

end Submission.Obl.k4_horizon_chart_assembly

/-! Adapted from this LOT tree, o049, session x0147, commit f4fd579,
`Submission/Obl/k4_cap_class_terminal_charts/PlankFormat.lean`. -/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set
open Submission.Lib.K4FinitePlankAtlases (fullTracePlank_iff_endpoints)
open scoped BigOperators
open Submission.Obl.k4_eligibility_sign_description
open Submission.Lib.K4ContinuousPlanks (InFullTracePlank)

noncomputable def polynomialPlane {n : ℕ} (p : Fin 2 → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : Plane := WithLp.toLp 2 (fun k => MvPolynomial.eval x (p k))

/-- An endpoint projection in polynomial coefficient coordinates. -/
noncomputable def endpointPolynomial {n : ℕ} (b u : Fin 2 → MvPolynomial (Fin n) ℝ)
    (c w e : Plane) (t : ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ k : Fin 2, MvPolynomial.C (e k) *
    (b k + MvPolynomial.C t * u k - MvPolynomial.C (c k) - MvPolynomial.C (t * w k))

theorem endpointPolynomial_degree {n d : ℕ} (b u : Fin 2 → MvPolynomial (Fin n) ℝ)
    (hb : ∀ k, (b k).totalDegree ≤ d) (hu : ∀ k, (u k).totalDegree ≤ d)
    (c w e : Plane) (t : ℝ) : (endpointPolynomial b u c w e t).totalDegree ≤ d := by
  apply degree_sum_le
  intro k _
  apply (degree_C_mul_le _ _).trans
  apply degree_sub_le
  · apply degree_sub_le
    · exact degree_add_le (hb k) ((degree_C_mul_le _ _).trans (hu k))
    · simp
  · simpa using (degree_C_mul_le t (MvPolynomial.C (w k))).trans
      (show (MvPolynomial.C (w k) : MvPolynomial (Fin n) ℝ).totalDegree ≤ d by simp)

theorem endpointPolynomial_eval {n : ℕ} (b u : Fin 2 → MvPolynomial (Fin n) ℝ)
    (c w e : Plane) (t : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (endpointPolynomial b u c w e t) =
      inner ℝ (polynomialPlane b x + t • polynomialPlane u x - c - t • w) e := by
  simp [endpointPolynomial, polynomialPlane, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private theorem endpoint_abs_signRep {n d : ℕ} (b u : Fin 2 → MvPolynomial (Fin n) ℝ)
    (hb : ∀ k, (b k).totalDegree ≤ d) (hu : ∀ k, (u k).totalDegree ≤ d)
    (c w e : Plane) (t R : ℝ) :
    SignRep (fun x : Fin n → ℝ => x) 2 d (fun x =>
      |inner ℝ (polynomialPlane b x + t • polynomialPlane u x - c - t • w) e| ≤ R) := by
  let p := endpointPolynomial b u c w e t
  have hp : p.totalDegree ≤ d := endpointPolynomial_degree b u hb hu c w e t
  have hplus := SignRep.nonneg (fun x : Fin n → ℝ => x) (MvPolynomial.C R + p) d
    (degree_add_le (by simp) hp)
  have hminus := SignRep.nonneg (fun x : Fin n → ℝ => x) (MvPolynomial.C R - p) d
    (degree_sub_le (by simp) hp)
  have h : SignRep (fun x : Fin n → ℝ => x) 2 d (fun x =>
      0 ≤ MvPolynomial.eval x (MvPolynomial.C R + p) ∧
      0 ≤ MvPolynomial.eval x (MvPolynomial.C R - p)) := by
    simpa only [max_self] using hplus.and hminus
  apply h.congr
  intro x
  simp only [map_add, map_sub, MvPolynomial.eval_C, p, endpointPolynomial_eval]
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Four endpoint projections give eight sign tests of the original coefficient
degree, independent of the time continuum and of any internal mark table. -/
theorem fullTracePlank_signRep {n d : ℕ} (b u : Fin 2 → MvPolynomial (Fin n) ℝ)
    (hb : ∀ k, (b k).totalDegree ≤ d) (hu : ∀ k, (u k).totalDegree ≤ d)
    (c w e₁ e₂ : Plane) (a β : ℝ) :
    SignRep (fun x : Fin n → ℝ => x) 8 d (fun x =>
      InFullTracePlank (polynomialPlane b x) (polynomialPlane u x) c w e₁ e₂ a β) := by
  have h0 := (endpoint_abs_signRep b u hb hu c w e₁ 0 a).and
    (endpoint_abs_signRep b u hb hu c w e₂ 0 β)
  have h1 := (endpoint_abs_signRep b u hb hu c w e₁ 1 a).and
    (endpoint_abs_signRep b u hb hu c w e₂ 1 β)
  have h := h0.and h1
  simp only [max_self] at h
  apply h.congr
  intro x
  simp only [zero_smul, one_smul, add_zero, sub_zero]
  exact (fullTracePlank_iff_endpoints _ _ _ _ _ _ _ _).symm

/-- The Boolean format costs sixteen nonnegative polynomial tests and preserves
the degree of the original polynomial trace coordinates. -/
theorem fullTracePlank_polynomialFormat {n d M : ℕ} {N : ℝ}
    (b u : Fin 2 → MvPolynomial (Fin n) ℝ)
    (hb : ∀ k, (b k).totalDegree ≤ d) (hu : ∀ k, (u k).totalDegree ≤ d)
    (c w e₁ e₂ : Plane) (a β : ℝ) (hcount : (16 : ℝ) ≤ N ^ M) :
    PolynomialFormat N M d {x | InFullTracePlank
      (polynomialPlane b x) (polynomialPlane u x) c w e₁ e₂ a β} :=
  polynomialFormat_of_signRep (fullTracePlank_signRep b u hb hu c w e₁ e₂ a β)
    (by norm_num; exact hcount)

end Submission.Obl.k4_horizon_chart_assembly
