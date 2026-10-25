import Submission.Obl.k4_stable_native_signal_oscillation.Hidden
import Submission.Obl.k4_eligibility_sign_description.Signs

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization

/-- Freeze the hidden variable at zero. -/
noncomputable def restrictBase {R : Type*} [CommSemiring R] {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R) : MvPolynomial (Fin n) R :=
  aeval (Fin.snoc (fun j : Fin n => X j) 0) P

lemma totalDegree_restrictBase {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℝ) :
    (restrictBase P).totalDegree ≤ P.totalDegree := by
  apply Submission.Obl.k4_eligibility_sign_description.degree_aeval_le
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

lemma eval_restrictBase {R : Type*} [CommSemiring R] {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R) (x : Fin n → R) :
    eval x (restrictBase P) = eval (Fin.snoc x 0) P := by
  have he : (eval x).comp (aeval (Fin.snoc (fun j : Fin n => X j) 0)).toRingHom =
      eval (Fin.snoc x 0) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast j => simp
  exact congrArg (fun h : MvPolynomial (Fin (n + 1)) R →+* R => h P) he

lemma update_snoc_hidden {R : Type*} {n : ℕ} (x : Fin n → R) (w t : R) :
    Function.update (Fin.snoc x w : Fin (n + 1) → R) (Fin.last n) t =
      (Fin.snoc x t : Fin (n + 1) → R) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

noncomputable def baseDiscriminant {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ := restrictBase (discriminant P (Fin.last n))

lemma baseDiscriminant_degree {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ 2) : (baseDiscriminant P).totalDegree ≤ 2 :=
  (totalDegree_restrictBase _).trans (discriminant_totalDegree P hP _)

lemma eval_baseDiscriminant {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ 2) (x : Fin n → ℝ) (w : ℝ) :
    eval x (baseDiscriminant P) = eval (Fin.snoc x w) (discriminant P (Fin.last n)) := by
  rw [baseDiscriminant, eval_restrictBase]
  have he := discriminant_update P hP (Fin.last n) (Fin.snoc x w) 0
  rw [update_snoc_hidden] at he
  exact he

/-- The exact hidden-coordinate quadratic expansion, with polynomial base coefficients. -/
lemma eval_snoc_quadratic {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ 2) (x : Fin n → ℝ) (w : ℝ) :
    eval (Fin.snoc x w) P = eval x (restrictBase P) +
      eval x (restrictBase (pderiv (Fin.last n) P)) * w +
      curvature P (Fin.last n) * w ^ 2 / 2 := by
  have ht := quadratic_coordinate_taylor P hP (Fin.snoc x 0) (Fin.last n) w
  simpa only [Fin.snoc_last, zero_add, update_snoc_hidden, eval_restrictBase] using ht

lemma quadratic_decomposition {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ 2) :
    P = rename Fin.castSucc (restrictBase P) +
      rename Fin.castSucc (restrictBase (pderiv (Fin.last n) P)) * X (Fin.last n) +
      C (curvature P (Fin.last n) / 2) * X (Fin.last n) ^ 2 := by
  apply MvPolynomial.funext
  intro v
  have ht := eval_snoc_quadratic P hP (Fin.init v) (v (Fin.last n))
  rw [Fin.snoc_init_self] at ht
  simpa only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_rename,
    Function.comp_def, Fin.init_def, div_mul_eq_mul_div] using ht

/-- The base polynomial of the critical center. -/
noncomputable def centerPoly {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  C (-(curvature P (Fin.last n))⁻¹) * restrictBase (pderiv (Fin.last n) P)

lemma centerPoly_degree {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ 2) : (centerPoly P).totalDegree ≤ 1 := by
  unfold centerPoly
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact (totalDegree_restrictBase _).trans
    ((Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le P _).trans (by omega))

lemma eval_centerPoly {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ 2) (hc : curvature P (Fin.last n) ≠ 0)
    (x : Fin n → ℝ) (w : ℝ) :
    eval x (centerPoly P) = hiddenCenter P (Fin.snoc x w) (Fin.last n) := by
  rw [← hiddenCenter_update P hP (Fin.snoc x w) (Fin.last n) hc 0, update_snoc_hidden]
  simp [centerPoly, hiddenCenter, eval_restrictBase, div_eq_mul_inv, mul_comm]

/-- The native signal evaluated on the affine critical center. -/
noncomputable def centerSignal {n : ℕ} (P S : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin n) ℝ := aeval (Fin.snoc (fun i : Fin n => X i) (centerPoly P)) S

lemma centerSignal_degree {n : ℕ} (P S : MvPolynomial (Fin (n + 1)) ℝ)
    (hP : P.totalDegree ≤ 2) : (centerSignal P S).totalDegree ≤ S.totalDegree := by
  apply Submission.Obl.k4_eligibility_sign_description.degree_aeval_le
  intro i
  induction i using Fin.lastCases with
  | last => simpa using centerPoly_degree P hP
  | cast j => simp

lemma eval_centerSignal {n : ℕ} (P S : MvPolynomial (Fin (n + 1)) ℝ)
    (x : Fin n → ℝ) :
    eval x (centerSignal P S) = eval (Fin.snoc x (eval x (centerPoly P))) S := by
  have he : (eval x).comp (aeval (Fin.snoc (fun j : Fin n => X j) (centerPoly P))).toRingHom =
      eval (Fin.snoc x (eval x (centerPoly P))) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast j => simp
  exact congrArg (fun h : MvPolynomial (Fin (n + 1)) ℝ →+* ℝ => h S) he

end Submission.Obl.k4_stable_native_signal_oscillation
