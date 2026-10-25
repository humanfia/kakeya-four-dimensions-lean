import Submission.Lib.K4HiddenQuadratic
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniGraph

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MvPolynomial

noncomputable section

namespace QuadraticTube

def point (u : FubiniBase) (w : ℝ) : Fin 4 → ℝ := Fin.snoc (fun i => u i) w

def ev (Q : MvPolynomial (Fin 4) ℝ) (u : FubiniBase) (w : ℝ) : ℝ := eval (point u w) Q

/-- Exact vertical Taylor identities for a quadratic. -/
theorem vertical_identities (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (u : FubiniBase) (v w : ℝ) :
    ev Q u w = ev Q u v+(w-v)*ev (pderiv (3:Fin 4) Q) u v+
      (w-v)^2/2*ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v ∧
    ev (pderiv (3:Fin 4) Q) u w = ev (pderiv (3:Fin 4) Q) u v+
      (w-v)*ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v := by
  have hp : Function.update (point u v) (3:Fin 4) ((point u v) 3+(w-v)) = point u w := by
    funext i
    fin_cases i <;> norm_num [point, Fin.snoc] <;> simp
  have h0 := Submission.Lib.K4HiddenQuadratic.eval_update_add Q hQ (point u v) (3:Fin 4) (w-v)
  have h1 := Submission.Lib.K4HiddenQuadratic.eval_update_add_pderiv Q hQ (point u v) (3:Fin 4) (w-v)
  rw [hp] at h0 h1
  exact ⟨h0,h1⟩

/-- A signed regular derivative on the graph persists in a small vertical
tube, and the value error grows only linearly with the tube thickness. -/
theorem estimates (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (u : FubiniBase) (v w : ℝ) {A E : ℝ} (hA : 1 ≤ A)
    (hvalue : |ev Q u v| ≤ E)
    (hlower : A⁻¹ ≤ ev (pderiv (3:Fin 4) Q) u v)
    (hupper : ev (pderiv (3:Fin 4) Q) u v ≤ 3*A)
    (hcurv : |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v| ≤ 2*A^2)
    (hsmall : 4*A^3*|w-v| ≤ 1) :
    |ev Q u w| ≤ E+4*A^2*|w-v| ∧
    (2*A)⁻¹ ≤ ev (pderiv (3:Fin 4) Q) u w ∧
    ev (pderiv (3:Fin 4) Q) u w ≤ 4*A ∧
    |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u w| ≤ 2*A^2 := by
  have hA0 : 0 < A := by linarith
  have hA2 : A ≤ A^2 := by simpa using pow_le_pow_right₀ hA (by decide : 1 ≤ 2)
  have hA3 : 1 ≤ A^3 := one_le_pow₀ hA
  have hd : |w-v| ≤ 1 := by nlinarith [abs_nonneg (w-v)]
  have hd2 : |w-v|^2 ≤ |w-v| := by nlinarith [abs_nonneg (w-v)]
  have hderpos : 0 ≤ ev (pderiv (3:Fin 4) Q) u v := (inv_nonneg.mpr hA0.le).trans hlower
  obtain ⟨hvaleq, hdereq⟩ := vertical_identities Q hQ u v w
  have ht1 : |(w-v)*ev (pderiv (3:Fin 4) Q) u v| ≤ 3*A*|w-v| := by
    rw [abs_mul, abs_of_nonneg hderpos]
    convert mul_le_mul_of_nonneg_left hupper (abs_nonneg (w-v)) using 1 <;> ring
  have ht2 : |(w-v)^2/2*ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v| ≤ A^2*|w-v|^2 := by
    rw [abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    convert mul_le_mul_of_nonneg_left hcurv (by positivity : 0 ≤ |w-v|^2/2) using 1 <;> ring
  have hdererr : |(w-v)*ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v| ≤ 2*A^2*|w-v| := by
    rw [abs_mul]
    convert mul_le_mul_of_nonneg_left hcurv (abs_nonneg (w-v)) using 1 <;> ring
  have hdererrsmall : 2*A^2*|w-v| ≤ (2*A)⁻¹ := by
    rw [← one_div (2*A)]
    apply (le_div_iff₀ (by positivity : 0 < 2*A)).mpr
    convert hsmall using 1 <;> ring
  have hinv : A⁻¹ = 2*(2*A)⁻¹ := by field_simp
  have hinvA : (2*A)⁻¹ ≤ A := by
    have hh : (2*A)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    exact hh.trans hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hvaleq]
    have hsum := abs_add_le (ev Q u v+(w-v)*ev (pderiv (3:Fin 4) Q) u v)
      ((w-v)^2/2*ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v)
    have hsum' := abs_add_le (ev Q u v) ((w-v)*ev (pderiv (3:Fin 4) Q) u v)
    nlinarith [mul_le_mul_of_nonneg_left hd2 (sq_nonneg A),
      mul_le_mul_of_nonneg_right hA2 (abs_nonneg (w-v))]
  · rw [hdereq]
    rw [hinv] at hlower
    have hh := neg_abs_le ((w-v)*ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v)
    linarith
  · rw [hdereq]
    have hh := le_abs_self ((w-v)*ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v)
    linarith
  · change |eval (point u w) (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q))| ≤ _
    rw [Submission.Lib.K4HiddenQuadratic.eval_pderiv_pderiv_eq Q hQ (3:Fin 4) (point u w) (point u v)]
    exact hcurv

end QuadraticTube

end

end Submission.Obl.k4_physical_parent_potential_candidates
