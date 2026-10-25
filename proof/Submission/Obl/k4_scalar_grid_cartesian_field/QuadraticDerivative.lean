import Submission.Obl.k4_scalar_normalized_exact_refinement.Coordinates
import Submission.Lib.K4QuadSheetMatching.Lines
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketGeometry

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- An original quadratic fit controls its derivative on the whole normalized block. -/
theorem quadratic_derivative_unit (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {E : ℝ} (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) :
    ∀ t ∈ Icc (0 : ℝ) 1, |p.derivative.eval t| ≤ 26 * E := by
  let A := p.eval 0
  let B := 4 * p.eval (1 / 2) - p.eval 1 - 3 * p.eval 0
  let C := 2 * (p.eval 1 - 2 * p.eval (1 / 2) + p.eval 0)
  have heval : (fun t : ℝ => p.eval t) = (fun t : ℝ => A + B * t + C * t ^ 2) := by
    funext t
    rw [Submission.Obl.k4_scalar_normalized_exact_refinement.quadratic_interpolation p hp t]
    dsimp [A, B, C]
    ring
  have hM : ∀ t ∈ Icc (0 : ℝ) 1, |A + B * t + C * t ^ 2| ≤ E := by
    intro t ht
    rw [← congrFun heval t]
    exact hbound t ht
  intro t ht
  have hd : p.derivative.eval t = B + 2 * C * t := by
    rw [← (p.hasDerivAt t).deriv, heval,
      Submission.Lib.K4QuadSheetMatching.deriv_quad1]
  rw [hd]
  have h := Submission.Lib.K4QuadSheetMatching.abs_iteratedDeriv_quad1_le hM 1 (by norm_num) t ht
  simpa only [Submission.Lib.K4QuadSheetMatching.iteratedDeriv_quad1_one] using h

/-- A quadratic fit on the physical block has the exact inverse-length derivative cost. -/
theorem quadratic_derivative_block (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {a h E : ℝ} (hh : 0 < h)
    (hbound : ∀ t ∈ Icc a (a + h), |p.eval t| ≤ E) :
    ∀ t ∈ Icc a (a + h), |p.derivative.eval t| ≤ 26 * E / h := by
  let A : Polynomial ℝ := Polynomial.C a + Polynomial.C h * Polynomial.X
  let q := p.comp A
  have hA : A.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · rw [Polynomial.natDegree_C]; omega
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hq : q.natDegree ≤ 2 :=
    Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hp hA).trans (by norm_num))
  have heval : ∀ τ, q.eval τ = p.eval (a + h * τ) := by
    intro τ
    simp only [q, A, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
  have hqbound : ∀ τ ∈ Icc (0 : ℝ) 1, |q.eval τ| ≤ E := by
    intro τ hτ
    rw [heval]
    exact hbound _ ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hder : ∀ τ, q.derivative.eval τ = p.derivative.eval (a + h * τ) * h := by
    intro τ
    simp [q, A, Polynomial.derivative_comp]
    ring
  intro t ht
  have hτ : (t - a) / h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [ht.1]) hh.le
    · exact (div_le_one hh).mpr (by linarith [ht.2])
  have hEst := quadratic_derivative_unit q hq hqbound _ hτ
  rw [hder, show a + h * ((t - a) / h) = t by field_simp; ring,
    abs_mul, abs_of_pos hh] at hEst
  exact (le_div_iff₀ hh).mpr hEst

/-- Whole-block packet fits bound the physical directional derivative of their predictor. -/
theorem packet_directional_derivative_bound (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (l : Trajectory) {a h E B : ℝ} (hh : 0 < h)
    (hfit : ∀ t ∈ Icc a (a + h),
      |scalarX l t - eval ![t, scalarY l t] F| ≤ E)
    (hder : ∀ t ∈ Icc a (a + h), |l.2 3 + 2 * t * l.2 4| ≤ B) :
    ∀ t ∈ Icc a (a + h),
      |eval ![t, scalarY l t] (pderiv 0 F) +
        l.2 1 * eval ![t, scalarY l t] (pderiv 1 F)| ≤ B + 26 * E / h := by
  let p := Submission.Obl.k4_scalar_normalized_exact_refinement.residual F l
  have hp : p.natDegree ≤ 2 :=
    Submission.Obl.k4_scalar_normalized_exact_refinement.natDegree_residual_le F hF l
  have hpbound : ∀ t ∈ Icc a (a + h), |p.eval t| ≤ E := by
    intro t ht
    simpa only [p, Submission.Obl.k4_scalar_normalized_exact_refinement.eval_residual,
      Submission.Obl.k4_scalar_normalized_exact_refinement.x,
      Submission.Obl.k4_scalar_normalized_exact_refinement.y,
      Submission.Obl.k4_scalar_linear_critical_extremizers.Split.x,
      Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y, scalarX, scalarY] using hfit t ht
  have heval : ∀ t, p.derivative.eval t = l.2 3 + 2 * t * l.2 4 -
      (eval ![t, scalarY l t] (pderiv 0 F) +
        l.2 1 * eval ![t, scalarY l t] (pderiv 1 F)) := by
    intro t
    simp [p, Submission.Obl.k4_scalar_normalized_exact_refinement.residual,
      eval_derivative_scalarLineHom, scalarY]
    ring
  intro t ht
  have herror := quadratic_derivative_block p hp hh hpbound t ht
  rw [heval] at herror
  have htri := abs_sub (l.2 3 + 2 * t * l.2 4)
    (l.2 3 + 2 * t * l.2 4 - (eval ![t, scalarY l t] (pderiv 0 F) +
      l.2 1 * eval ![t, scalarY l t] (pderiv 1 F)))
  simp only [sub_sub_cancel] at htri
  linarith [hder t ht]

/-- The original coefficient bound and the horizon scale make the directional predictor bound subpower. -/
theorem packet_directional_scale_bound (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (l : Trajectory) {N K κ a h : ℝ}
    (hN : 2 ≤ N) (hK : 1 ≤ K) (hκ : κ ≤ 1) (hh : 0 < h)
    (hscale : N ^ (-κ) / K ≤ h) (ha : 0 ≤ a) (hah : a + h ≤ 1)
    (hl : ∀ e, |l.2 e| ≤ K)
    (hfit : ∀ t ∈ Set.Icc a (a + h),
      |scalarX l t - eval ![t, scalarY l t] F| ≤ K * N ^ (-1 : ℝ)) :
    ∀ t ∈ Set.Icc a (a + h),
      |eval ![t, scalarY l t] (pderiv 0 F) +
        l.2 1 * eval ![t, scalarY l t] (pderiv 1 F)| ≤ 30 * K ^ 2 := by
  have hKpos : 0 < K := by linarith
  have hδ : N ^ (-1 : ℝ) ≤ N ^ (-κ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by linarith)
  have hδh : N ^ (-1 : ℝ) ≤ K * h := by
    have hsc := (div_le_iff₀ hKpos).mp hscale
    nlinarith
  have herror : 26 * (K * N ^ (-1 : ℝ)) / h ≤ 26 * K ^ 2 := by
    apply (div_le_iff₀ hh).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδh (by positivity : 0 ≤ 26 * K)]
  have hder : ∀ t ∈ Icc a (a + h), |l.2 3 + 2 * t * l.2 4| ≤ 3 * K := by
    intro t ht
    have ht0 : 0 ≤ t := ha.trans ht.1
    have ht1 : t ≤ 1 := ht.2.trans hah
    have hterm : |2 * t * l.2 4| ≤ 2 * K := by
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg ht0]
      calc
        _ ≤ 2 * 1 * K := by gcongr; exact hl 4
        _ = _ := by ring
    linarith [abs_add_le (l.2 3) (2 * t * l.2 4), hl 3]
  intro t ht
  have hdir := packet_directional_derivative_bound F hF l hh hfit hder t ht
  nlinarith

end Submission.Obl.k4_scalar_grid_cartesian_field
