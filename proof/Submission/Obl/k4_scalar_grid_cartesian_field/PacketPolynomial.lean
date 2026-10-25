import Submission.Obl.k4_scalar_candidate_original_return.Core.Normalize
import Submission.Obl.k4_scalar_candidate_original_return.Core.Cells
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MvPolynomial
open Submission.Obl.k4_scalar_candidate_original_return

/-- The packet predictor in its time and transverse strip coordinates. -/
noncomputable def packetPolynomial (F : MvPolynomial (Fin 2) ℝ) (a h u v : ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  Normalize.affSubst F ![![h, 0], ![h * v, h]] ![a, u + a * v]

theorem packetPolynomial_degree (F : MvPolynomial (Fin 2) ℝ) (a h u v : ℝ) :
    (packetPolynomial F a h u v).totalDegree ≤ F.totalDegree :=
  Normalize.affSubst_totalDegree_le _ _ _

theorem eval_packetPolynomial (F : MvPolynomial (Fin 2) ℝ) (a h u v τ w : ℝ) :
    eval ![τ, w] (packetPolynomial F a h u v) =
      eval ![a + h * τ, u + (a + h * τ) * v + h * w] F := by
  rw [packetPolynomial, Normalize.eval_affSubst]
  apply congrArg (fun z : Fin 2 → ℝ => eval z F)
  funext e
  fin_cases e <;> simp <;> ring

/-- A bounded quadratic on the unit packet strip has uniformly bounded coefficients. -/
theorem quadratic_strip_coeff_bound (Q : MvPolynomial (Fin 2) ℝ)
    (hQ : Q.totalDegree ≤ 2) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, w] Q| ≤ K) :
    ∀ b, |Q.coeff b| ≤ 48 * K := by
  obtain ⟨a, b, c, d, e, f, hnf⟩ := QuadBounds.quad_normal_form Q hQ
  let coeff : Fin 6 → ℝ := ![a, b, c, d, e, f]
  have heval : ∀ t w, eval ![t, w] Q =
      Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticValue coeff t w := by
    intro t w
    rw [hnf]
    simp [Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticValue, coeff]
    <;> ring
  have hc : ∀ i, |coeff i| ≤ 8 * K :=
    Submission.Obl.k4_fixed_budget_quadratic_recovery.quadratic_coefficients_bound
      (fun t ht w hw => by rw [← heval]; exact hbound t ht w hw)
  rw [Submission.Obl.k4_fixed_budget_quadratic_recovery.polynomial_eq_of_quadratic_values heval]
  intro b
  convert Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticPolynomial_coeff_bound
    (by positivity : 0 ≤ 8 * K) hc b using 1 <;> ring

/-- The frozen strip norm bounds the coefficients after packet normalization. -/
theorem packetPolynomial_coeff_bound (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) {a h u v K : ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc a (a + h), ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + h * w] F| ≤ K) :
    ∀ b, |(packetPolynomial F a h u v).coeff b| ≤ 48 * K := by
  apply quadratic_strip_coeff_bound _ ((packetPolynomial_degree _ _ _ _ _).trans hF) hK
  intro τ hτ w hw
  rw [eval_packetPolynomial]
  apply hbound _ ?_ w hw
  constructor <;> nlinarith [hτ.1, hτ.2]

/-- Undoing packet strip coordinates is exact, including the velocity term. -/
theorem eval_packetPolynomial_normalized (F : MvPolynomial (Fin 2) ℝ)
    (a h u v t y : ℝ) (hh : h ≠ 0) :
    eval ![(t - a) / h, (y - u - t * v) / h] (packetPolynomial F a h u v) =
      eval ![t, y] F := by
  rw [eval_packetPolynomial]
  apply congrArg (fun z : Fin 2 → ℝ => eval z F)
  funext e
  fin_cases e <;> simp <;> field_simp <;> ring

/-- The frozen packet norm gives a quantitative Lipschitz bound on the entire wider packet. -/
theorem packet_polynomial_lipschitz (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) {a h u v K t t' y y' : ℝ}
    (hh : 0 < h) (hK : 1 ≤ K)
    (hbound : ∀ t ∈ Icc a (a + h), ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + h * w] F| ≤ K)
    (ht : t ∈ Icc a (a + h)) (ht' : t' ∈ Icc a (a + h))
    (hy : |y - u - t * v| ≤ K * h) (hy' : |y' - u - t' * v| ≤ K * h) :
    |eval ![t, y] F - eval ![t', y'] F| ≤
      480 * K * (1 + K) / h * ((1 + |v|) * |t - t'| + |y - y'|) := by
  let Q := packetPolynomial F a h u v
  let z : Fin 2 → ℝ := ![(t - a) / h, (y - u - t * v) / h]
  let z' : Fin 2 → ℝ := ![(t' - a) / h, (y' - u - t' * v) / h]
  have hz : ∀ e, |z e| ≤ K := by
    intro e
    fin_cases e
    · change |(t - a) / h| ≤ K
      rw [abs_div, abs_of_pos hh, abs_of_nonneg (by linarith [ht.1])]
      exact ((div_le_one hh).mpr (by linarith [ht.2])).trans hK
    · change |(y - u - t * v) / h| ≤ K
      rw [abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).mpr hy
  have hz' : ∀ e, |z' e| ≤ K := by
    intro e
    fin_cases e
    · change |(t' - a) / h| ≤ K
      rw [abs_div, abs_of_pos hh, abs_of_nonneg (by linarith [ht'.1])]
      exact ((div_le_one hh).mpr (by linarith [ht'.2])).trans hK
    · change |(y' - u - t' * v) / h| ≤ K
      rw [abs_div, abs_of_pos hh]
      exact (div_le_iff₀ hh).mpr hy'
  have hdiff : |z 0 - z' 0| + |z 1 - z' 1| ≤
      ((1 + |v|) * |t - t'| + |y - y'|) / h := by
    have htime : z 0 - z' 0 = (t - t') / h := by dsimp [z, z']; ring
    have hspace : z 1 - z' 1 = ((y - y') - v * (t - t')) / h := by
      dsimp [z, z']; ring
    rw [htime, hspace, abs_div, abs_div, abs_of_pos hh, ← add_div]
    apply (div_le_div_iff_of_pos_right hh).mpr
    have hsub := abs_sub (y - y') (v * (t - t'))
    rw [abs_mul] at hsub
    nlinarith
  have hcoeff := packetPolynomial_coeff_bound F hF hh (by linarith : 0 ≤ K) hbound
  have hL := Cells.quad_lipschitz Q ((packetPolynomial_degree _ _ _ _ _).trans hF)
    hcoeff z z' hz hz'
  have heval : eval z Q = eval ![t, y] F := eval_packetPolynomial_normalized _ _ _ _ _ _ _ hh.ne'
  have heval' : eval z' Q = eval ![t', y'] F := eval_packetPolynomial_normalized _ _ _ _ _ _ _ hh.ne'
  rw [heval, heval'] at hL
  calc
    _ ≤ 10 * (48 * K) * (1 + K) * (|z 0 - z' 0| + |z 1 - z' 1|) := hL
    _ ≤ 10 * (48 * K) * (1 + K) *
        (((1 + |v|) * |t - t'| + |y - y'|) / h) := by
      exact mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = _ := by ring

/-- A sufficiently fine normalized base cell has small predictor oscillation. -/
theorem packet_polynomial_cell_variation (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) {a h u v K t t' y y' ξ : ℝ}
    (hh : 0 < h) (hK : 1 ≤ K) (hξ : 0 ≤ ξ) (hv : |v| ≤ K)
    (hbound : ∀ t ∈ Icc a (a + h), ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + h * w] F| ≤ K)
    (ht : t ∈ Icc a (a + h)) (ht' : t' ∈ Icc a (a + h))
    (hy : |y - u - t * v| ≤ K * h) (hy' : |y' - u - t' * v| ≤ K * h)
    (hdt : |t - t'| ≤ h * ξ) (hdy : |y - y'| ≤ h * ξ) :
    |eval ![t, y] F - eval ![t', y'] F| ≤ 2880 * K ^ 3 * ξ := by
  have hKn : 0 ≤ K := by linarith
  have hconst : 480 * K * (1 + K) * (K + 2) ≤ 2880 * K ^ 3 := by
    calc
      _ ≤ 480 * K * (2 * K) * (3 * K) := by gcongr <;> linarith
      _ = _ := by ring
  calc
    _ ≤ 480 * K * (1 + K) / h * ((1 + |v|) * |t - t'| + |y - y'|) :=
      packet_polynomial_lipschitz F hF hh hK hbound ht ht' hy hy'
    _ ≤ 480 * K * (1 + K) / h * ((1 + K) * (h * ξ) + h * ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul (by linarith : 1 + |v| ≤ 1 + K) hdt
        (abs_nonneg _) (by positivity)) hdy
    _ = 480 * K * (1 + K) * (K + 2) * ξ := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst hξ

end Submission.Obl.k4_scalar_grid_cartesian_field
