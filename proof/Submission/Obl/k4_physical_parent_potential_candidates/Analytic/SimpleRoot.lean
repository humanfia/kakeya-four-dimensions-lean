-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/SimpleRoot.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/SimpleRoot.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/SimpleRoot.lean
-- Earlier source attributions below are retained.
import Mathlib
import Submission.Obl.k4_real_conic_restoration.ScalarRoot
import Submission.Lib.K4QuadraticSublevel
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

/-- The stable root formula divides by the large derivative term, so it also
handles a vanishing or arbitrarily small quadratic coefficient. -/
theorem stable_quadratic_root_formula {K : Type*} [Field K] (a b c r : K)
    (hr : r ^ 2 = b ^ 2 - 4 * a * c) (hden : b + r ≠ 0) :
    c + b * (-2 * c / (b + r)) + a * (-2 * c / (b + r)) ^ 2 = 0 ∧
      b + 2 * a * (-2 * c / (b + r)) = r := by
  constructor
  · field_simp
    linear_combination c * hr
  · field_simp
    linear_combination -hr

/-- A relative perturbation of at most one half preserves derivative sign. -/
lemma same_sign_and_floor {b e : ℝ} (hb : b ≠ 0) (he : |e| ≤ |b| / 2) :
    |b| / 2 ≤ |b + e| ∧ 0 < b * (b + e) := by
  have hbabs : 0 < |b| := abs_pos.mpr hb
  have herr := abs_le.mp he
  constructor
  · have htriangle : |b| ≤ |b + e| + |e| := by
      calc
        |b| = |(b + e) + -e| := by congr 1; ring
        _ ≤ |b + e| + |-e| := abs_add_le _ _
        _ = |b + e| + |e| := by rw [abs_neg]
    linarith
  · obtain hbpos | hbneg := lt_or_gt_of_ne (Ne.symm hb)
    · have hsign : 0 < b + e := by rw [abs_of_pos hbpos] at herr; linarith
      exact mul_pos hbpos hsign
    · have hsign : b + e < 0 := by rw [abs_of_neg hbneg] at herr; linarith
      exact mul_pos_of_neg_of_neg hbneg hsign

/-- Select the nearby real quadratic root with the same derivative sign as the
observation. The derivative floor holds on the whole intervening segment. -/
theorem quadratic_near_simple_root (a b c : ℝ) (hb : b ≠ 0)
    (hsmall : 8 * |a| * |c| ≤ b ^ 2) :
    ∃ t : ℝ, c + b * t + a * t ^ 2 = 0 ∧ |t| ≤ 2 * |c| / |b| ∧
      ∀ u ∈ Set.uIcc (0 : ℝ) t,
        |b| / 2 ≤ |b + 2 * a * u| ∧ 0 < b * (b + 2 * a * u) := by
  have h4 : 4 * |a| * |c| ≤ b ^ 2 := by
    nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg c)]
  obtain ⟨t, ht, hdist⟩ := k4_real_conic_restoration.quadratic_near_zero a b c hb h4
  have hbabs : 0 < |b| := abs_pos.mpr hb
  have hdist' : |t| * |b| ≤ 2 * |c| := (le_div_iff₀ hbabs).mp hdist
  refine ⟨t, ht, hdist, ?_⟩
  intro u hu
  have huabs : |u| ≤ |t| := by
    rcases Set.mem_uIcc.mp hu with hu | hu
    · simpa only [abs_zero, max_eq_right (abs_nonneg t)] using abs_le_max_abs_abs hu.1 hu.2
    · simpa only [abs_zero, max_eq_left (abs_nonneg t)] using abs_le_max_abs_abs hu.1 hu.2
  apply same_sign_and_floor hb
  have hmul := mul_le_mul_of_nonneg_left hdist' (by positivity : 0 ≤ 2 * |a|)
  have htpert : 2 * |a| * |t| ≤ |b| / 2 := by
    apply (mul_le_mul_iff_left₀ hbabs).mp
    nlinarith [sq_abs b]
  calc
    |2 * a * u| = 2 * |a| * |u| := by rw [abs_mul, abs_mul]; norm_num
    _ ≤ 2 * |a| * |t| := mul_le_mul_of_nonneg_left huabs (by positivity)
    _ ≤ |b| / 2 := htpert

/-- The stable-root statement expressed in polynomial values and derivatives. -/
theorem polynomial_quadratic_near_simple_root (p : Polynomial ℝ)
    (hdeg : p.natDegree ≤ 2) (x : ℝ) (hderiv : p.derivative.eval x ≠ 0)
    (hsmall : 4 * |p.derivative.derivative.eval x| * |p.eval x| ≤
      (p.derivative.eval x) ^ 2) :
    ∃ y : ℝ, p.eval y = 0 ∧ |y - x| ≤ 2 * |p.eval x| / |p.derivative.eval x| ∧
      ∀ z ∈ Set.uIcc x y,
        |p.derivative.eval x| / 2 ≤ |p.derivative.eval z| ∧
        0 < p.derivative.eval x * p.derivative.eval z := by
  obtain ⟨a, b, c, hp⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients p hdeg
  have hval (z : ℝ) : p.eval z = a * z ^ 2 + b * z + c := by simp [hp]
  have hd (z : ℝ) : p.derivative.eval z = 2 * a * z + b := by simp [hp]; ring
  have hdd (z : ℝ) : p.derivative.derivative.eval z = 2 * a := by simp [hp]; ring
  have hb : 2 * a * x + b ≠ 0 := by simpa only [hd] using hderiv
  have hsmall' : 8 * |a| * |p.eval x| ≤ (2 * a * x + b) ^ 2 := by
    rw [hdd, hd, abs_mul] at hsmall
    norm_num at hsmall
    nlinarith
  obtain ⟨t, ht, hdist, hsegment⟩ := quadratic_near_simple_root a (2 * a * x + b) (p.eval x) hb hsmall'
  refine ⟨x + t, ?_, ?_, ?_⟩
  · rw [hval x] at ht
    rw [hval]
    nlinarith
  · simpa only [add_sub_cancel_left, hd] using hdist
  · intro z hz
    have hz' : z - x ∈ Set.uIcc (0 : ℝ) t := by
      rcases Set.mem_uIcc.mp hz with hz | hz
      · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
      · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
    have h := hsegment (z - x) hz'
    have hid : 2 * a * x + b + 2 * a * (z - x) = 2 * a * z + b := by ring
    simpa only [hid, hd] using h

/-- A small quadratic residual in the hidden coordinate has a nearby real
simple root. No bound on the magnitude of the hidden coordinate is used. -/
theorem multivariate_quadratic_near_simple_hidden_root
    (P : MvPolynomial (Fin 4) ℝ) (hdeg : P.totalDegree ≤ 2) (x : Fin 4 → ℝ)
    (hderiv : MvPolynomial.eval x (MvPolynomial.pderiv 3 P) ≠ 0)
    (hsmall : 4 * |MvPolynomial.eval x (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| *
      |MvPolynomial.eval x P| ≤ (MvPolynomial.eval x (MvPolynomial.pderiv 3 P)) ^ 2) :
    ∃ w : ℝ, MvPolynomial.eval (Function.update x 3 w) P = 0 ∧
      |w - x 3| ≤ 2 * |MvPolynomial.eval x P| / |MvPolynomial.eval x (MvPolynomial.pderiv 3 P)| ∧
      ∀ z ∈ Set.uIcc (x 3) w,
        |MvPolynomial.eval x (MvPolynomial.pderiv 3 P)| / 2 ≤
          |MvPolynomial.eval (Function.update x 3 z) (MvPolynomial.pderiv 3 P)| ∧
        0 < MvPolynomial.eval x (MvPolynomial.pderiv 3 P) *
          MvPolynomial.eval (Function.update x 3 z) (MvPolynomial.pderiv 3 P) := by
  let q := k4_quadratic_slope_volume.coordinatePolynomialHom x (3 : Fin 4) P
  have hqdeg : q.natDegree ≤ 2 :=
    (k4_quadratic_slope_volume.natDegree_eval₂_affine_le P _ (by
      intro i
      split_ifs <;> simp)).trans hdeg
  have hval (z : ℝ) : q.eval z = MvPolynomial.eval (Function.update x 3 z) P :=
    k4_quadratic_slope_volume.eval_coordinatePolynomialHom P x 3 z
  have hd (z : ℝ) : q.derivative.eval z =
      MvPolynomial.eval (Function.update x 3 z) (MvPolynomial.pderiv 3 P) := by
    rw [k4_quadratic_slope_volume.derivative_coordinatePolynomialHom,
      k4_quadratic_slope_volume.eval_coordinatePolynomialHom]
  have hdd (z : ℝ) : q.derivative.derivative.eval z =
      MvPolynomial.eval (Function.update x 3 z) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P)) := by
    rw [k4_quadratic_slope_volume.derivative_coordinatePolynomialHom,
      k4_quadratic_slope_volume.derivative_coordinatePolynomialHom,
      k4_quadratic_slope_volume.eval_coordinatePolynomialHom]
  have hderivq : q.derivative.eval (x 3) ≠ 0 := by
    simpa only [hd, Function.update_eq_self] using hderiv
  have hsmallq : 4 * |q.derivative.derivative.eval (x 3)| * |q.eval (x 3)| ≤
      (q.derivative.eval (x 3)) ^ 2 := by
    simpa only [hval, hd, hdd, Function.update_eq_self] using hsmall
  simpa only [hval, hd, Function.update_eq_self] using
    polynomial_quadratic_near_simple_root q hqdeg (x 3) hderivq hsmallq

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
