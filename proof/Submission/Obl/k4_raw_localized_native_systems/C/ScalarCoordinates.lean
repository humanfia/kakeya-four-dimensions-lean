import Submission.Obl.k4_raw_localized_native_systems.C.NativeCorrection
import Submission.Obl.k4_eligibility_sign_description.Families
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

/-
Adapted from this LOT tree, o178, session x0596, `ScalarCoordinates.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MvPolynomial
open Submission.Lib.K4XInterface
open Submission.Obl.k4_eligibility_sign_description

noncomputable section

/-- The original spacetime point at a fixed time, polynomial in the six line coefficients. -/
abbrev graphAt := Submission.Obl.k4_quadratic_atlas_normalization.fixedSub

theorem graphAt_degree (t : ℝ) (i : Fin 4) : (graphAt t i).totalDegree ≤ 1 := by
  fin_cases i
  · simp [graphAt, Submission.Obl.k4_quadratic_atlas_normalization.fixedSub]
  all_goals
    apply degree_add_le (by simp)
    exact (degree_C_mul_le _ _).trans (by simp)

theorem eval_graphAt (t : ℝ) (l : ℕ × (Fin 6 → ℝ)) (i : Fin 4) :
    eval l.2 (graphAt t i) = gx l t i := by
  fin_cases i <;> simp [graphAt, Submission.Obl.k4_quadratic_atlas_normalization.fixedSub, gx]

abbrev nativeAt := Submission.Obl.k4_quadratic_atlas_normalization.fixedTrace

theorem nativeAt_degree (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    (nativeAt P t).totalDegree ≤ P.totalDegree :=
  Submission.Obl.k4_quadratic_atlas_normalization.fixedTrace_degree P t

theorem eval_nativeAt (P : MvPolynomial (Fin 4) ℝ) (t : ℝ)
    (l : ℕ × (Fin 6 → ℝ)) : eval l.2 (nativeAt P t) = eval (gx l t) P :=
  Submission.Obl.k4_quadratic_atlas_normalization.eval_fixedTrace P t l.1 l.2

/-- An affine tangent coordinate on the original observed base. -/
def tangentBase (a : ℝ) (v : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  C a + ∑ i, C (v i) * X i

theorem tangentBase_degree (a : ℝ) (v : Fin 3 → ℝ) :
    (tangentBase a v).totalDegree ≤ 1 := by
  apply degree_add_le (by simp)
  apply degree_sum_le
  intro i hi
  exact (degree_C_mul_le _ _).trans (by simp)

def tangentAt (a : ℝ) (v : Fin 3 → ℝ) (t : ℝ) : MvPolynomial (Fin 6) ℝ :=
  aeval (fun i : Fin 3 => graphAt t i.castSucc) (tangentBase a v)

theorem tangentAt_degree (a : ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    (tangentAt a v t).totalDegree ≤ 1 := by
  unfold tangentAt
  exact (degree_aeval_le (tangentBase a v)
    (fun i : Fin 3 => graphAt t i.castSucc) (fun i => graphAt_degree t i.castSucc)).trans
      (tangentBase_degree a v)

theorem eval_tangentAt (a : ℝ) (v : Fin 3 → ℝ) (t : ℝ)
    (l : ℕ × (Fin 6 → ℝ)) :
    eval l.2 (tangentAt a v t) = eval (gx l t ∘ Fin.castSucc) (tangentBase a v) := by
  rw [tangentAt, eval_aeval_real]
  apply congrArg (fun z : Fin 3 → ℝ => eval z (tangentBase a v))
  funext i
  exact eval_graphAt t l i.castSucc

/-- The scalar law uses an affine tangent and the quadratic native signal, in
unit block time.  All five coefficients are polynomial in the original line. -/
def scalarCoeffPoly (P : MvPolynomial (Fin 4) ℝ) (t₀ q a : ℝ)
    (v : Fin 3 → ℝ) : Fin 5 → MvPolynomial (Fin 6) ℝ :=
  ![tangentAt a v t₀,
    tangentAt a v (t₀ + q) - tangentAt a v t₀,
    nativeAt P t₀,
    C 4 * nativeAt P (t₀ + q / 2) - C 3 * nativeAt P t₀ - nativeAt P (t₀ + q),
    C 2 * (nativeAt P (t₀ + q) + nativeAt P t₀ - C 2 * nativeAt P (t₀ + q / 2))]

def scalarCoeff (P : MvPolynomial (Fin 4) ℝ) (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    (l : ℕ × (Fin 6 → ℝ)) : Fin 5 → ℝ :=
  fun i => eval l.2 (scalarCoeffPoly P t₀ q a v i)

theorem scalarCoeffPoly_degree (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) (i : Fin 5) :
    (scalarCoeffPoly P t₀ q a v i).totalDegree ≤ 2 := by
  have hn t := (nativeAt_degree P t).trans hP
  have ht t := (tangentAt_degree a v t).trans (by decide : 1 ≤ 2)
  fin_cases i
  · exact ht _
  · exact degree_sub_le (ht _) (ht _)
  · exact hn _
  · exact degree_sub_le (degree_sub_le ((degree_C_mul_le _ _).trans (hn _))
      ((degree_C_mul_le _ _).trans (hn _))) (hn _)
  · exact (degree_C_mul_le _ _).trans (degree_sub_le (degree_add_le (hn _) (hn _))
      ((degree_C_mul_le _ _).trans (hn _)))

theorem scalarCoeff_y (P : MvPolynomial (Fin 4) ℝ) (t₀ q a : ℝ)
    (v : Fin 3 → ℝ) (l : ℕ × (Fin 6 → ℝ)) (s : ℝ) :
    scalarCoeff P t₀ q a v l 0 + s * scalarCoeff P t₀ q a v l 1 =
      eval (gx l (t₀ + q * s) ∘ Fin.castSucc) (tangentBase a v) := by
  simp only [scalarCoeff, scalarCoeffPoly, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_sub, eval_tangentAt]
  simp [tangentBase, Fin.sum_univ_three, gx, Function.comp_def]
  ring

theorem quadratic_native_unit (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q : ℝ) (l : ℕ × (Fin 6 → ℝ)) :
    Quadratic (fun s => eval (gx l (t₀ + q * s)) P) := by
  have hh := Quadratic.mv_line P hP (gx l t₀)
    ![q, q * l.2 3, q * l.2 4, q * l.2 5]
  convert hh using 1
  funext s
  apply congrArg (fun z : Fin 4 → ℝ => eval z P)
  funext i
  fin_cases i <;> simp [gx] <;> ring

theorem scalarCoeff_x (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) (l : ℕ × (Fin 6 → ℝ)) (s : ℝ) :
    scalarCoeff P t₀ q a v l 2 + s * scalarCoeff P t₀ q a v l 3 +
      s ^ 2 * scalarCoeff P t₀ q a v l 4 = eval (gx l (t₀ + q * s)) P := by
  obtain ⟨A, B, C, h⟩ := quadratic_native_unit P hP t₀ q l
  change eval l.2 (nativeAt P t₀) +
    s * eval l.2 (MvPolynomial.C 4 * nativeAt P (t₀ + q / 2) -
      MvPolynomial.C 3 * nativeAt P t₀ - nativeAt P (t₀ + q)) +
    s ^ 2 * eval l.2 (MvPolynomial.C 2 * (nativeAt P (t₀ + q) + nativeAt P t₀ -
      MvPolynomial.C 2 * nativeAt P (t₀ + q / 2))) = _
  simp only [map_sub, map_add, map_mul, eval_C, eval_nativeAt]
  have h₀ := h 0
  have hm := h (1 / 2)
  have h₁ := h 1
  dsimp only at h hm
  simp only [mul_zero, add_zero] at h₀
  simp only [mul_one] at h₁
  have heq : t₀ + q / 2 = t₀ + q * (1 / 2) := by ring
  rw [heq, hm, h₀, h₁, h s]
  ring

/-- Pull a recovered scalar predictor back to the original base coordinates. -/
def scalarPredictor (t₀ q a : ℝ) (v : Fin 3 → ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  aeval ![C q⁻¹ * (X 0 - C t₀), tangentBase a v] P

theorem scalarPredictor_degree (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    (P : MvPolynomial (Fin 2) ℝ) :
    (scalarPredictor t₀ q a v P).totalDegree ≤ P.totalDegree := by
  unfold scalarPredictor
  apply degree_aeval_le P ![C q⁻¹ * (X 0 - C t₀), tangentBase a v]
  intro i
  fin_cases i
  · exact (degree_C_mul_le _ _).trans (degree_sub_le (by simp) (by simp))
  · exact tangentBase_degree a v

theorem eval_scalarPredictor (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (l : ℕ × (Fin 6 → ℝ)) (s : ℝ) (hq : q ≠ 0) :
    eval (gx l (t₀ + q * s) ∘ Fin.castSucc) (scalarPredictor t₀ q a v P) =
      eval ![s, eval (gx l (t₀ + q * s) ∘ Fin.castSucc) (tangentBase a v)] P := by
  rw [scalarPredictor, eval_aeval_real]
  apply congrArg (fun z : Fin 2 → ℝ => eval z P)
  funext i
  fin_cases i
  · simp [gx, Function.comp_def, hq]
  · simp

/-- A whole-unit-interval scalar fit is exactly an improved native test on the
original block.  The block is not replaced by a newly chosen time interval. -/
theorem scalar_fit_nativeCorrection (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    (R : MvPolynomial (Fin 2) ℝ) (l : ℕ × (Fin 6 → ℝ))
    {e : ℝ} (hq : 0 < q)
    (hfit : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |scalarCoeff P t₀ q a v l 2 + s * scalarCoeff P t₀ q a v l 3 +
        s ^ 2 * scalarCoeff P t₀ q a v l 4 -
        eval ![s, scalarCoeff P t₀ q a v l 0 + s * scalarCoeff P t₀ q a v l 1] R| ≤ e)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ (t₀ + q)) :
    |eval (gx l t) (nativeCorrection P (scalarPredictor t₀ q a v R))| ≤ e := by
  let s := (t - t₀) / q
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith [ht.1]) hq.le, ?_⟩
    apply (div_le_one hq).mpr
    linarith [ht.2]
  have heq : t₀ + q * s = t := by dsimp [s]; field_simp; ring
  have hh := hfit s hs
  rw [scalarCoeff_x P hP, scalarCoeff_y] at hh
  rw [eval_nativeCorrection, ← heq, eval_scalarPredictor _ _ _ _ _ _ _ hq.ne']
  exact hh

/-- Bounds at the three native interpolation times and the two tangent
endpoints control every scalar coefficient, independently of the frame's
absolute polynomial complexity. -/
theorem scalarCoeff_bound (P : MvPolynomial (Fin 4) ℝ) (t₀ q a : ℝ)
    (v : Fin 3 → ℝ) (l : ℕ × (Fin 6 → ℝ)) {K : ℝ} (hK : 0 ≤ K)
    (hy₀ : |eval (gx l t₀ ∘ Fin.castSucc) (tangentBase a v)| ≤ K)
    (hy₁ : |eval (gx l (t₀ + q) ∘ Fin.castSucc) (tangentBase a v)| ≤ K)
    (hx₀ : |eval (gx l t₀) P| ≤ K)
    (hxm : |eval (gx l (t₀ + q / 2)) P| ≤ K)
    (hx₁ : |eval (gx l (t₀ + q)) P| ≤ K) (i : Fin 5) :
    |scalarCoeff P t₀ q a v l i| ≤ 8 * K := by
  obtain ⟨hy₀l, hy₀u⟩ := abs_le.mp hy₀
  obtain ⟨hy₁l, hy₁u⟩ := abs_le.mp hy₁
  obtain ⟨hx₀l, hx₀u⟩ := abs_le.mp hx₀
  obtain ⟨hxml, hxmu⟩ := abs_le.mp hxm
  obtain ⟨hx₁l, hx₁u⟩ := abs_le.mp hx₁
  fin_cases i <;>
    simp [scalarCoeff, scalarCoeffPoly, eval_tangentAt, eval_nativeAt]
  all_goals
    first
    | rw [abs_le]; constructor <;> linarith
    | have hh : |eval (gx l (t₀ + q)) P + eval (gx l t₀) P -
          2 * eval (gx l (t₀ + q / 2)) P| ≤ 4 * K := by
        rw [abs_le]; constructor <;> linarith
      linarith

end
end Submission.Obl.k4_raw_localized_native_systems.C
