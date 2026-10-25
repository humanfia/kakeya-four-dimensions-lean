/- Adapted from: here:o223
   (x0927; countable-cell threshold extends x0775). -/
import Submission.Lib.K4ContactAffine.TimeMargins

/-!+# A contact chart with the original times in its interior

The chart sends the extended time interval `[-1,2]` to `[0,1]`, hence sends
the original incidence times `[0,1]` into the middle third. The base is dilated
and translated by a contact transformation. Original velocity bins are retained
by scaling their mesh by the same factor as the actual velocity.
-/

namespace Submission.Lib.K4ContactAffine

open Set MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting

noncomputable section

def interiorCoeff (R : ℝ) (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(b 0 - b 3) / R + 1 / 2,
    (b 1 + b 0 - b 4 - b 3) / (3 * R) + 3 / 4,
    b 2 - b 5,
    3 * b 3 / R,
    (b 4 + b 3) / R - 1 / 2,
    3 * b 5]

def interiorBase (R : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(p 0 + 1) / 3, p 1 / R + 1 / 2,
    (p 2 + p 1) / (3 * R) - (p 0 + 1) / 6 + 3 / 4]

def interiorInverseSubst (R : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C 3 * X 0 - C 1,
    C R * (X 1 - C (1 / 2)),
    C (3 * R) * (X 2 + C (1 / 2) * X 0 - C (3 / 4)) - C R * (X 1 - C (1 / 2)),
    X 3]

def interiorTest (R : ℝ) (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (interiorInverseSubst R) P

theorem interiorCoeff_contact (R : ℝ) (b : Fin 6 → ℝ) :
    interiorCoeff R b 4 + interiorCoeff R b 0 = (b 4 + b 0) / R := by
  simp only [interiorCoeff, Matrix.cons_val]
  ring

theorem interior_velocity_bin (R η : ℝ) (hR : R ≠ 0) (hη : η ≠ 0) (b : Fin 6 → ℝ) :
    ⌊interiorCoeff R b 3 / (3 * η / R)⌋ = ⌊b 3 / η⌋ := by
  congr 1
  simp only [interiorCoeff, Matrix.cons_val]
  field_simp

theorem interiorCoeff_base (R : ℝ) (b : Fin 6 → ℝ) (σ : ℝ) :
    ![σ, interiorCoeff R b 0 + σ * interiorCoeff R b 3,
      interiorCoeff R b 1 + σ * interiorCoeff R b 4] =
      interiorBase R ![3 * σ - 1, b 0 + (3 * σ - 1) * b 3,
        b 1 + (3 * σ - 1) * b 4] := by
  funext i
  fin_cases i <;> simp [interiorCoeff, interiorBase] <;> ring

theorem interiorCoeff_observed_base (R : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    ![(t + 1) / 3, interiorCoeff R b 0 + ((t + 1) / 3) * interiorCoeff R b 3,
      interiorCoeff R b 1 + ((t + 1) / 3) * interiorCoeff R b 4] =
      interiorBase R ![t, b 0 + t * b 3, b 1 + t * b 4] := by
  have h := interiorCoeff_base R b ((t + 1) / 3)
  have ht : 3 * ((t + 1) / 3) - 1 = t := by ring
  simpa only [ht] using h

theorem interiorCoeff_observed_hidden (R : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    interiorCoeff R b 2 + ((t + 1) / 3) * interiorCoeff R b 5 = b 2 + t * b 5 := by
  simp only [interiorCoeff, Matrix.cons_val]
  ring

theorem eval_interiorInverseSubst (R : ℝ) (hR : R ≠ 0) (b : Fin 6 → ℝ) (σ : ℝ) :
    (fun i => eval (point (interiorCoeff R b) σ) (interiorInverseSubst R i)) =
      point b (3 * σ - 1) := by
  funext i
  fin_cases i <;> simp [interiorInverseSubst, interiorCoeff, point] <;> field_simp <;> ring

theorem eval_interiorTest (R : ℝ) (hR : R ≠ 0) (b : Fin 6 → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (σ : ℝ) :
    eval (point (interiorCoeff R b) σ) (interiorTest R P) = eval (point b (3 * σ - 1)) P := by
  rw [interiorTest, eval_bind₁', eval_interiorInverseSubst R hR]

theorem interiorInverseSubst_degree (R : ℝ) (i : Fin 4) :
    (interiorInverseSubst R i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_sub (deg1_C_mul _ (deg1_X _)) (deg1_C _)
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · exact deg1_sub
      (deg1_C_mul _ (deg1_sub (deg1_add (deg1_X _) (deg1_C_mul _ (deg1_X _))) (deg1_C _)))
      (deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _)))
  · exact deg1_X _

theorem interiorTest_degree (R : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    (interiorTest R P).totalDegree ≤ P.totalDegree :=
  totalDegree_bind₁_le_of_le_one _ (interiorInverseSubst_degree R) P

theorem pderiv_interiorInverseSubst (R : ℝ) (i : Fin 4) :
    pderiv (3 : Fin 4) (interiorInverseSubst R i) = if i = 3 then 1 else 0 := by
  fin_cases i <;> simp [interiorInverseSubst, pderiv_X]

theorem pderiv_interiorTest (R : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (interiorTest R P) = interiorTest R (pderiv 3 P) := by
  rw [interiorTest, interiorTest, pderiv_bind₁, Finset.sum_eq_single (3 : Fin 4)]
  · rw [pderiv_interiorInverseSubst, ite_eq_left rfl, mul_one]
  · intro i _ hi
    rw [pderiv_interiorInverseSubst, ite_eq_right hi, mul_zero]
  · simp

theorem interior_observed_derivative (R : ℝ) (hR : R ≠ 0) (P : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (interiorCoeff R b) ((t + 1) / 3)) (pderiv 3 (interiorTest R P)) =
      eval (point b t) (pderiv 3 P) := by
  rw [pderiv_interiorTest, eval_interiorTest R hR]
  congr 2
  ring

/-- Native tests retain the complete unit-time fitting bounds in the new
chart, using polynomial extrapolation to the extended old interval. -/
theorem interior_full_fit (R : ℝ) (hR : R ≠ 0) (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b : Fin 6 → ℝ) {H : ℝ}
    (hfit : ∀ t ∈ Icc (0 : ℝ) 1, |eval (point b t) P| ≤ H ∧
      |eval (point b t) (pderiv 3 P)| ≤ H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 P))| ≤ H) :
    ∀ σ ∈ Icc (0 : ℝ) 1, |eval (point (interiorCoeff R b) σ) (interiorTest R P)| ≤ 432 * H ∧
      |eval (point (interiorCoeff R b) σ) (pderiv 3 (interiorTest R P))| ≤ 432 * H ∧
      |eval (point (interiorCoeff R b) σ) (pderiv 3 (pderiv 3 (interiorTest R P)))| ≤ 432 * H := by
  have hext := unit_native_fit_with_time_margin P hP b hfit
  intro σ hσ
  simp only [pderiv_interiorTest, eval_interiorTest R hR]
  have ht : 3 * σ - 1 ∈ Icc (-1 : ℝ) 2 :=
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  simpa using hext (3 * σ - 1) ht

def interiorAffineCoeff (R c₀ : ℝ) (c : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![c₀ + c 0 / 3 + c 1 / 2 + 7 * c 2 / 12,
    c 0 / 3 - c 2 / 6,
    c 1 / R + c 2 / (3 * R),
    c 2 / (3 * R)]

/-- Affine predictors pull back to affine predictors without imposing any
bound on their coefficients. -/
theorem interior_affine_prediction (R c₀ : ℝ) (c : Fin 3 → ℝ) (p : Fin 3 → ℝ) :
    c₀ + c 0 * interiorBase R p 0 + c 1 * interiorBase R p 1 +
      c 2 * interiorBase R p 2 =
    interiorAffineCoeff R c₀ c 0 + interiorAffineCoeff R c₀ c 1 * p 0 +
      interiorAffineCoeff R c₀ c 2 * p 1 + interiorAffineCoeff R c₀ c 3 * p 2 := by
  simp only [interiorBase, interiorAffineCoeff, Matrix.cons_val]
  ring

/-- Uniform base bounds through the enlarged time interval use only the
original four bounded base coefficients. -/
theorem extended_base_bounds (b : Fin 6 → ℝ) {K t : ℝ}
    (hb : |b 0| + |b 1| + |b 3| + |b 4| ≤ K) (ht : t ∈ Icc (-1 : ℝ) 2) :
    |b 0 + t * b 3| ≤ 2 * K ∧ |b 1 + t * b 4 + (b 0 + t * b 3)| ≤ 2 * K := by
  have ht2 : |t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hZ : |b 0 + t * b 3| ≤ |b 0| + 2 * |b 3| := by
    calc
      _ ≤ |b 0| + |t| * |b 3| := by simpa only [abs_mul] using abs_add_le (b 0) (t * b 3)
      _ ≤ _ := by gcongr
  have hY : |b 1 + t * b 4 + (b 0 + t * b 3)| ≤
      |b 1| + 2 * |b 4| + (|b 0| + 2 * |b 3|) := by
    calc
      _ ≤ |b 1 + t * b 4| + |b 0 + t * b 3| := abs_add_le _ _
      _ ≤ (|b 1| + |t| * |b 4|) + (|b 0| + 2 * |b 3|) := by
        exact add_le_add (by simpa only [abs_mul] using abs_add_le (b 1) (t * b 4)) hZ
      _ ≤ _ := by gcongr
  constructor <;> nlinarith [abs_nonneg (b 0), abs_nonneg (b 1), abs_nonneg (b 3), abs_nonneg (b 4)]

/-- A scale at least `32 K` places every original base incidence in the
quarter cube. This leaves enough room for complete fine mesh cells. -/
theorem interiorBase_margin (b : Fin 6 → ℝ) {K R t : ℝ} (hK : 0 < K)
    (hR : 32 * K ≤ R) (hb : |b 0| + |b 1| + |b 3| + |b 4| ≤ K)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ e, 1 / 4 ≤ interiorBase R ![t, b 0 + t * b 3, b 1 + t * b 4] e ∧
      interiorBase R ![t, b 0 + t * b 3, b 1 + t * b 4] e ≤ 3 / 4 := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hZ, hY⟩ := extended_base_bounds b (t := t) hb ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hZ' : |(b 0 + t * b 3) / R| ≤ 1 / 16 := by
    rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
    linarith
  have hY' : |(b 1 + t * b 4 + (b 0 + t * b 3)) / (3 * R)| ≤ 1 / 48 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 3 * R), div_le_iff₀ (by positivity)]
    linarith
  intro e
  fin_cases e <;> simp [interiorBase]
  all_goals constructor <;> linarith [(abs_le.mp hZ').1, (abs_le.mp hZ').2,
    (abs_le.mp hY').1, (abs_le.mp hY').2, ht.1, ht.2]

/-- The complete extended trajectory remains in the unit cube. -/
theorem interiorBase_extended_cube (b : Fin 6 → ℝ) {K R t : ℝ} (hK : 0 < K)
    (hR : 32 * K ≤ R) (hb : |b 0| + |b 1| + |b 3| + |b 4| ≤ K)
    (ht : t ∈ Icc (-1 : ℝ) 2) :
    interiorBase R ![t, b 0 + t * b 3, b 1 + t * b 4] ∈ Icc (0 : Fin 3 → ℝ) 1 := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hZ, hY⟩ := extended_base_bounds b hb ht
  have hZ' : |(b 0 + t * b 3) / R| ≤ 1 / 16 := by
    rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
    linarith
  have hY' : |(b 1 + t * b 4 + (b 0 + t * b 3)) / (3 * R)| ≤ 1 / 48 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 3 * R), div_le_iff₀ (by positivity)]
    linarith
  constructor
  all_goals
    intro e
    fin_cases e <;> simp [interiorBase]
    all_goals linarith [(abs_le.mp hZ').1, (abs_le.mp hZ').2,
      (abs_le.mp hY').1, (abs_le.mp hY').2, ht.1, ht.2]

theorem interiorCoeff_line_in_cube (b : Fin 6 → ℝ) {K R : ℝ} (hK : 0 < K)
    (hR : 32 * K ≤ R) (hb : |b 0| + |b 1| + |b 3| + |b 4| ≤ K) :
    ∀ σ ∈ Icc (0 : ℝ) 1,
      ![σ, interiorCoeff R b 0 + σ * interiorCoeff R b 3,
        interiorCoeff R b 1 + σ * interiorCoeff R b 4] ∈ Icc (0 : Fin 3 → ℝ) 1 := by
  intro σ hσ
  rw [interiorCoeff_base]
  exact interiorBase_extended_cube b hK hR hb ⟨by linarith [hσ.1], by linarith [hσ.2]⟩

end

end Submission.Lib.K4ContactAffine
