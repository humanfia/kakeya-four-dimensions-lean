/- Adapted within this LOT tree from o120/x0402, commit 81f800489248f55eaf1c2da13f86ceff0ee98719,
Submission/Obl/k4_unbounded_width_exclusion/ScalarFormat.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates
import Submission.Obl.k4_eligibility_sign_description.Descriptions
import Submission.Obl.k4_dk4_smoothed_problem.NativeFormat
import Submission.Lib.K4FinitePlankAtlases.Assignments

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MvPolynomial Set
open Submission.Obl.k4_eligibility_sign_description
open Submission.Obl.k4_dk4_smoothed_problem

def signFromBooleans (nonnegative nonpositive : Bool) : SignType :=
  if nonnegative then if nonpositive then 0 else 1 else -1

theorem signFromBooleans_eq (r : ℝ) :
    signFromBooleans (decide (0 ≤ r)) (decide (0 ≤ -r)) = SignType.sign r := by
  rcases lt_trichotomy r 0 with h | rfl | h
  · simp [signFromBooleans, not_le.mpr h, sign_neg h]
  · simp [signFromBooleans]
  · simp [signFromBooleans, h.le, show ¬0 ≤ -r by linarith, sign_pos h]

/-- Two weak Boolean tests recover a three-valued polynomial sign. -/
theorem hasBoolFormat_of_signRep {n m D : ℕ} {A : Set (Fin n → ℝ)}
    (h : SignRep id m D (fun x => x ∈ A)) :
    HasBoolPolynomialFormat id A (m + m) D := by
  classical
  obtain ⟨p, B, hp, hB⟩ := h
  refine ⟨Fin.addCases p (fun i => -p i), ?_,
    fun v => decide ((fun i => signFromBooleans (v (Fin.castAdd m i))
      (v (Fin.natAdd m i))) ∈ B), ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hp j
    · simpa only [Fin.addCases_right, totalDegree_neg] using hp j
  · intro x
    simpa only [decide_eq_true_eq, Fin.addCases_left, Fin.addCases_right,
      map_neg, signFromBooleans_eq, id_eq] using (hB x).symm

theorem fmt_of_hasBoolFormat {n m D : ℕ} {A : Set (Fin n → ℝ)}
    (h : HasBoolPolynomialFormat id A m D) : fmt n m D A :=
  ⟨m, le_rfl, h⟩

theorem fmt_of_signRep {n m D : ℕ} {A : Set (Fin n → ℝ)}
    (h : SignRep id m D (fun x => x ∈ A)) : fmt n (2 * m) D A := by
  convert fmt_of_hasBoolFormat (hasBoolFormat_of_signRep h) using 1
  push_cast
  ring

def scalarErrorPolynomial (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    MvPolynomial (Fin 5) ℝ :=
  X 2 + C t * X 3 + C (t ^ 2) * X 4 -
    aeval ![C t, X 0 + C t * X 1] P

theorem scalarErrorPolynomial_degree (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t : ℝ) :
    (scalarErrorPolynomial P t).totalDegree ≤ 2 := by
  apply degree_sub_le
  · apply degree_add_le
    · exact degree_add_le (by simp) ((degree_C_mul_le _ _).trans (by simp))
    · exact (degree_C_mul_le _ _).trans (by simp)
  · apply (degree_aeval_le _ _ ?_).trans hP
    intro i
    fin_cases i
    · change (C t : MvPolynomial (Fin 5) ℝ).totalDegree ≤ 1
      simp
    · apply degree_add_le (by simp) ((degree_C_mul_le _ _).trans (by simp))

theorem eval_scalarErrorPolynomial (P : MvPolynomial (Fin 2) ℝ)
    (t : ℝ) (b : Fin 5 → ℝ) :
    eval b (scalarErrorPolynomial P t) = scalarX b t - eval ![t, scalarY b t] P := by
  simp only [scalarErrorPolynomial, map_sub, map_add, map_mul, eval_X, eval_C,
    eval_aeval_real]
  have hv : (fun i => eval b (![C t, X 0 + C t * X 1] i)) =
      (![t, scalarY b t] : Fin 2 → ℝ) := by
    ext i
    fin_cases i <;> simp [scalarY]
  rw [hv]
  simp only [scalarX]

theorem quadratic_scalarErrorPolynomial (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (b : Fin 5 → ℝ) :
    Quadratic (fun t => eval b (scalarErrorPolynomial P t)) := by
  obtain ⟨A, B, C, h⟩ := Quadratic.mv_line P hP ![0, b 0] ![1, b 1]
  refine ⟨b 4 - A, b 3 - B, b 2 - C, fun t => ?_⟩
  have hv : (fun i => (![0, b 0] : Fin 2 → ℝ) i + t * (![1, b 1] : Fin 2 → ℝ) i) =
      ![t, scalarY b t] := by
    ext i
    fin_cases i <;> simp [scalarY]
  have ht := h t
  dsimp only at ht ⊢
  rw [hv] at ht
  rw [eval_scalarErrorPolynomial, ht]
  simp only [scalarX]
  ring

/-- A whole-time quadratic fit has fixed polynomial format, regardless of
the candidate's coefficients or the fitting error. -/
theorem scalarFit_hasBoolFormat (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (error : ℝ) : HasBoolPolynomialFormat id (scalarFit P error) 24 4 := by
  have hs := SignRep.quadratic_abs_family id false (scalarErrorPolynomial P)
    (scalarErrorPolynomial_degree P hP) (quadratic_scalarErrorPolynomial P hP)
    error 0 1 (by norm_num)
  have hf : SignRep id 12 4 (fun b => b ∈ scalarFit P error) := by
    simpa only [id_eq, Bool.false_eq_true, ↓reduceIte, eval_scalarErrorPolynomial,
      scalarFit, mem_ofPred_eq] using hs
  exact hasBoolFormat_of_signRep hf

theorem scalarFit_format (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (error : ℝ) : fmt 5 24 4 (scalarFit P error) :=
  fmt_of_hasBoolFormat (scalarFit_hasBoolFormat P hP error)

/-- First-fit assignments use the original finite family of polynomial tests. -/
theorem firstAssignment_hasBoolFormat {n C m D : ℕ} (S : Fin C → Set (Fin n → ℝ))
    (hS : ∀ j, HasBoolPolynomialFormat id (S j) m D) (i : Fin C) :
    HasBoolPolynomialFormat id (Submission.Lib.K4FinitePlankAtlases.firstAssignment S i)
      (C * m) D := by
  classical
  choose p hp b hb using hS
  let e : Fin (C * m) ≃ Fin C × Fin m := finProdFinEquiv.symm
  refine ⟨fun a => p (e a).1 (e a).2, fun a => hp (e a).1 (e a).2,
    fun v => decide (b i (fun a => v (e.symm (i, a))) = true ∧
      ∀ j, j < i → ¬ b j (fun a => v (e.symm (j, a))) = true), ?_⟩
  intro x
  simpa only [Submission.Lib.K4FinitePlankAtlases.firstAssignment, mem_ofPred_eq,
    decide_eq_true_eq, Equiv.apply_symm_apply, id_eq] using
    and_congr (hb i x) (forall_congr' fun j => imp_congr_right fun _ => not_congr (hb j x))

theorem scalarFit_firstAssignment_format {C : ℕ}
    (P : Fin C → MvPolynomial (Fin 2) ℝ) (hP : ∀ i, (P i).totalDegree ≤ 2)
    (error : ℝ) (i : Fin C) :
    fmt 5 (C * 24) 4 (Submission.Lib.K4FinitePlankAtlases.firstAssignment
      (fun j => scalarFit (P j) error) i) := by
  convert fmt_of_hasBoolFormat (firstAssignment_hasBoolFormat
    (fun j => scalarFit (P j) error) (fun j => scalarFit_hasBoolFormat (P j) (hP j) error) i)
    using 1
  norm_num

end Submission.Obl.k4_fixed_budget_quadratic_recovery
