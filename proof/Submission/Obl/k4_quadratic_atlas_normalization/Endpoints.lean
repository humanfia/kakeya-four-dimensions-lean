import Submission.Obl.k4_quadratic_atlas_normalization.Interface
import Submission.Obl.k4_quadratic_selector_sweep.Quadratic

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set MvPolynomial

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Line × ℝ

/-- Along a trajectory the hidden derivative of a quadratic is affine. -/
theorem derivative_affine (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (l : Line) : ∃ m d : ℝ, ∀ t : ℝ,
      eval (x l t) (pderiv (3 : Fin 4) R) = m * t + d := by
  have hdeg : (pderiv (3 : Fin 4) R).totalDegree ≤ 1 :=
    Submission.Obl.k4_quadratic_selector_sweep.totalDegree_pderiv_le R 3 hR
  obtain ⟨m, d, hmd⟩ :=
    Submission.Obl.k4_quadratic_selector_sweep.eval_affine_of_totalDegree_le_one
      (pderiv (3 : Fin 4) R) hdeg ![0, l.2 0, l.2 1, l.2 2] ![1, l.2 3, l.2 4, l.2 5]
  refine ⟨m, d, fun t => ?_⟩
  have heq : x l t = (fun i =>
      ![0, l.2 0, l.2 1, l.2 2] i + t * ![1, l.2 3, l.2 4, l.2 5] i) := by
    funext i
    fin_cases i <;> simp [x]
  rw [heq]
  exact hmd t

/-- The absolute value of an affine function is bounded by its endpoint maximum. -/
theorem abs_affine_le_endpoint_max (m d s e t : ℝ) (ht : t ∈ Icc s e) :
    |m * t + d| ≤ max |m * s + d| |m * e + d| := by
  apply abs_le.mpr
  by_cases hm : 0 ≤ m
  · have hs := mul_le_mul_of_nonneg_left ht.1 hm
    have he := mul_le_mul_of_nonneg_left ht.2 hm
    constructor
    · have hl := neg_abs_le (m * s + d)
      have hu := le_max_left |m * s + d| |m * e + d|
      linarith
    · exact (by linarith : m * t + d ≤ m * e + d).trans
        ((le_abs_self _).trans (le_max_right _ _))
  · have hm' : m ≤ 0 := le_of_not_ge hm
    have hs := mul_le_mul_of_nonpos_left ht.1 hm'
    have he := mul_le_mul_of_nonpos_left ht.2 hm'
    constructor
    · have hl := neg_abs_le (m * e + d)
      have hu := le_max_right |m * s + d| |m * e + d|
      linarith
    · exact (by linarith : m * t + d ≤ m * s + d).trans
        ((le_abs_self _).trans (le_max_left _ _))

/-- The whole-block maximum of the hidden derivative, in endpoint form. -/
noncomputable def derivativeMax (R : MvPolynomial (Fin 4) ℝ) (s e : ℝ) (l : Line) : ℝ :=
  max |eval (x l s) (pderiv (3 : Fin 4) R)| |eval (x l e) (pderiv (3 : Fin 4) R)|

lemma derivative_le_max (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (l : Line) {s e t : ℝ} (ht : t ∈ Icc s e) :
    |eval (x l t) (pderiv (3 : Fin 4) R)| ≤ derivativeMax R s e l := by
  obtain ⟨m, d, hmd⟩ := derivative_affine R hR l
  simp only [derivativeMax, hmd]
  exact abs_affine_le_endpoint_max m d s e t ht

lemma derivativeMax_attained (R : MvPolynomial (Fin 4) ℝ) (l : Line)
    {s e : ℝ} (hse : s ≤ e) :
    ∃ t ∈ Icc s e, derivativeMax R s e l = |eval (x l t) (pderiv (3 : Fin 4) R)| := by
  by_cases h : |eval (x l s) (pderiv (3 : Fin 4) R)| ≤
      |eval (x l e) (pderiv (3 : Fin 4) R)|
  · exact ⟨e, ⟨hse, le_rfl⟩, max_eq_right h⟩
  · exact ⟨s, ⟨le_rfl, hse⟩, max_eq_left (le_of_not_ge h)⟩

lemma derivativeMax_nonneg (R : MvPolynomial (Fin 4) ℝ) (s e : ℝ) (l : Line) :
    0 ≤ derivativeMax R s e l :=
  (abs_nonneg _).trans (le_max_left _ _)

end Submission.Obl.k4_quadratic_atlas_normalization
