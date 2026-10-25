-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/FamilyLoss.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.DerivativeLoss
import Submission.Obl.k4_quadratic_finite_greedy_cover.PacketBudget

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set

/-- The fourth-power derivative threshold loses only an inverse cubic fraction
of each full eligible trajectory packet. -/
theorem packet_bad_derivative_le
    (ν : Measure Trajectory) (A : Set Trajectory) (hAm : MeasurableSet A)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (l q B K : ℝ) (hq : 0 < q) (hB : 0 < B) (hK : 2 ≤ K)
    (hlarge : ∀ a ∈ A, ∃ t ∈ Icc l (l + q),
      B / K ≤ |MvPolynomial.eval (x a t) (MvPolynomial.pderiv (3 : Fin 4) R)|) :
    ν.prod volume {p : Incidence | p.1 ∈ A ∧ p.2 ∈ Icc l (l + q) ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)| < B / K ^ 4} ≤
      ENNReal.ofReal (8 / K ^ 3) * ν.prod volume (A ×ˢ Icc l (l + q)) := by
  have hKpos : 0 < K := by linarith
  have hKsq : 1 ≤ K ^ 2 := one_le_pow₀ (by linarith : 1 ≤ K)
  have hKcube : 2 ≤ K ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hKsq hKpos.le]
  have hKfour : 2 * K ≤ K ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hKcube hKpos.le]
  have hsmall : B / K ^ 4 ≤ (B / K) / 2 := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hKfour hB.le]
  have hbound := product_bad_derivative_le ν A hAm R hR l q (B / K) (B / K ^ 4)
    hq (div_pos hB hKpos) (by positivity) hsmall hlarge
  have hcoef : 8 * (B / K ^ 4) * q / (B / K) = (8 / K ^ 3) * q := by
    field_simp
  rw [hcoef] at hbound
  calc
    _ ≤ ENNReal.ofReal ((8 / K ^ 3) * q) * ν A := hbound
    _ = ENNReal.ofReal (8 / K ^ 3) * ν.prod volume (A ×ˢ Icc l (l + q)) := by
      rw [Measure.prod_prod, Real.volume_Icc, add_sub_cancel_left,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 8 / K ^ 3)]
      ac_rfl

/-- Disjoint full assignments at one dyadic time depth keep the total loss
independent of the number of candidate polynomials. -/
theorem family_bad_derivative_le {ι : Type*} [Fintype ι]
    (W : ℕ) (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ)
    (γ : ι → Fin W) (j : ι → ℕ) (T : ℕ) (A : ι → Set Trajectory)
    (R : ι → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) (K : ℝ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hωsum : (∑ w, ω w) = 1) (hAm : ∀ a, MeasurableSet (A a))
    (hR : ∀ a, (R a).totalDegree ≤ 2) (hB : ∀ w, 0 < B w) (hK : 2 ≤ K)
    (hj : ∀ a, j a < 2 ^ T)
    (hdisj : ∀ a a', a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a'))
    (hlarge : ∀ a l, l ∈ A a → ∃ t ∈ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
      (((j a : ℝ) + 1) / (2 : ℝ) ^ T),
      B (γ a) / K ≤ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R a))|) :
    (∑ a, ENNReal.ofReal (ω (γ a)) * (ν (γ a)).prod volume
      {p : Incidence | p.1 ∈ A a ∧
        p.2 ∈ Icc ((j a : ℝ) / (2 : ℝ) ^ T) (((j a : ℝ) + 1) / (2 : ℝ) ^ T) ∧
        |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R a))| < B (γ a) / K ^ 4}) ≤
      ENNReal.ofReal (8 / K ^ 3) := by
  let F : ι → Set Incidence := fun a =>
    A a ×ˢ Icc ((j a : ℝ) / (2 : ℝ) ^ T) (((j a : ℝ) + 1) / (2 : ℝ) ^ T)
  have hbad (a : ι) : (ν (γ a)).prod volume
      {p : Incidence | p.1 ∈ A a ∧
        p.2 ∈ Icc ((j a : ℝ) / (2 : ℝ) ^ T) (((j a : ℝ) + 1) / (2 : ℝ) ^ T) ∧
        |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R a))| < B (γ a) / K ^ 4} ≤
      ENNReal.ofReal (8 / K ^ 3) * (ν (γ a)).prod volume (F a) := by
    have hi : ((j a : ℝ) + 1) / (2 : ℝ) ^ T = (j a : ℝ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T := by ring
    simpa only [F, hi] using packet_bad_derivative_le (ν (γ a)) (A a) (hAm a)
      (R a) (hR a) ((j a : ℝ) / (2 : ℝ) ^ T) (1 / (2 : ℝ) ^ T) (B (γ a)) K
      (by positivity) (hB _) hK (by simpa only [hi] using hlarge a)
  calc
    _ ≤ ∑ a, ENNReal.ofReal (ω (γ a)) *
        (ENNReal.ofReal (8 / K ^ 3) * (ν (γ a)).prod volume (F a)) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul' le_rfl (hbad a))
    _ = ENNReal.ofReal (8 / K ^ 3) *
        (∑ a, ENNReal.ofReal (ω (γ a)) * (ν (γ a)).prod volume (F a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ac_rfl
    _ ≤ ENNReal.ofReal (8 / K ^ 3) * 1 :=
      mul_le_mul' le_rfl (full_packet_mass_le_one W ν ω γ j T A hν hω hωsum hAm hj hdisj)
    _ = _ := mul_one _

end Submission.Obl.k4_quadratic_finite_greedy_cover
