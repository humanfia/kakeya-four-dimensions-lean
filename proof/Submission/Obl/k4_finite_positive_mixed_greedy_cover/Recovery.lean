import Submission.Obl.k4_quadratic_finite_greedy_cover.FixedLevel

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
open Submission.Obl.k4_quadratic_finite_greedy_cover
open scoped ENNReal

/-- A square cutoff leaves a loss of at most `8/K` of a full trajectory packet. -/
theorem packet_square_loss (ν : Measure Trajectory) (A : Set Trajectory)
    (hAm : MeasurableSet A) (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (l q B K : ℝ) (hq : 0 < q) (hB : 0 < B) (hK : 2 ≤ K)
    (hlarge : ∀ a ∈ A, ∃ t ∈ Icc l (l + q),
      B / K ≤ |MvPolynomial.eval (x a t) (MvPolynomial.pderiv (3 : Fin 4) R)|) :
    ν.prod volume {p : Incidence | p.1 ∈ A ∧ p.2 ∈ Icc l (l + q) ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)| < B / K ^ 2} ≤
      ENNReal.ofReal (8 / K) * ν.prod volume (A ×ˢ Icc l (l + q)) := by
  have hKpos : 0 < K := by linarith
  have hsmall : B / K ^ 2 ≤ (B / K) / 2 := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh : K * 2 ≤ K ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hh hB.le
  have hb := product_bad_derivative_le ν A hAm R hR l q (B / K) (B / K ^ 2)
    hq (by positivity) (by positivity) hsmall hlarge
  have hc : 8 * (B / K ^ 2) * q / (B / K) = (8 / K) * q := by field_simp
  rw [hc] at hb
  calc
    _ ≤ ENNReal.ofReal ((8 / K) * q) * ν A := hb
    _ = _ := by
      rw [Measure.prod_prod, Real.volume_Icc, add_sub_cancel_left,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 8 / K)]
      ac_rfl

/-- Recovery from priority cylinders with a square derivative cutoff. -/
theorem square_counted_recovery {ι : Type*} [Fintype ι]
    (W : ℕ) (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ)
    (γ : ι → Fin W) (j : ι → ℕ) (T : ℕ) (A : ι → Set Trajectory)
    (R : ι → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) (K : ℝ)
    (H : Fin W → Set Incidence)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hωsum : (∑ w, ω w) = 1) (hAm : ∀ a, MeasurableSet (A a))
    (hR : ∀ a, (R a).totalDegree ≤ 2) (hB : ∀ w, 0 < B w) (hK : 2 ≤ K)
    (hj : ∀ a, j a < 2 ^ T) (hHfin : ∀ w, (ν w).prod volume (H w) ≠ ∞)
    (hdisj : ∀ a a', a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a'))
    (hlarge : ∀ a l, l ∈ A a → ∃ t ∈ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
      (((j a : ℝ) + 1) / (2 : ℝ) ^ T),
      B (γ a) / K ≤ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R a))|) :
    (∑ a, ω (γ a) * ((ν (γ a)).prod volume).real
      (H (γ a) ∩ (A a ×ˢ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
        (((j a : ℝ) + 1) / (2 : ℝ) ^ T)))) ≤
    (∑ a, ω (γ a) * ((ν (γ a)).prod volume).real
      (countedPacket (H (γ a)) (A a) (R a) (B (γ a) / K ^ 2) T (j a))) + 8 / K := by
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  have hKpos : 0 < K := by linarith
  let Bad : ι → Set Incidence := fun a => badPacket (A a) (R a) (B (γ a) / K ^ 2) T (j a)
  let Full : ι → Set Incidence := fun a =>
    A a ×ˢ Icc ((j a : ℝ) / (2 : ℝ) ^ T) (((j a : ℝ) + 1) / (2 : ℝ) ^ T)
  have hbad (a : ι) : (ν (γ a)).prod volume (Bad a) ≤
      ENNReal.ofReal (8 / K) * (ν (γ a)).prod volume (Full a) := by
    have hi : ((j a : ℝ) + 1) / (2 : ℝ) ^ T =
        (j a : ℝ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T := by ring
    simpa only [Bad, badPacket, Full, hi] using packet_square_loss (ν (γ a)) (A a)
      (hAm a) (R a) (hR a) ((j a : ℝ) / (2 : ℝ) ^ T) (1 / (2 : ℝ) ^ T)
      (B (γ a)) K (by positivity) (hB _) hK (by simpa only [hi] using hlarge a)
  have hbadENN : (∑ a, ENNReal.ofReal (ω (γ a)) * (ν (γ a)).prod volume (Bad a)) ≤
      ENNReal.ofReal (8 / K) := by
    calc
      _ ≤ ∑ a, ENNReal.ofReal (ω (γ a)) *
          (ENNReal.ofReal (8 / K) * (ν (γ a)).prod volume (Full a)) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul' le_rfl (hbad a))
      _ = ENNReal.ofReal (8 / K) * ∑ a, ENNReal.ofReal (ω (γ a)) *
          (ν (γ a)).prod volume (Full a) := by simp_rw [mul_left_comm _ (ENNReal.ofReal (8 / K))]; rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (8 / K) * 1 := mul_le_mul' le_rfl
        (full_packet_mass_le_one W ν ω γ j T A hν hω hωsum hAm hj hdisj)
      _ = _ := mul_one _
  have hbadreal : (∑ a, ω (γ a) * ((ν (γ a)).prod volume).real (Bad a)) ≤ 8 / K := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 8 / K)).mp
    rw [ofReal_weighted_mass (fun a => (ν (γ a)).prod volume) (fun a => ω (γ a)) Bad
      (fun a => hω _) (fun a => badPacket_finite _ _ _ _ _ _)]
    exact hbadENN
  have hp (a : ι) := full_mass_le_counted_add_bad (ν (γ a)) (H (γ a)) (H (γ a))
    Subset.rfl (hHfin _) (A a) (R a) (B (γ a) / K ^ 2) T (j a)
  calc
    _ ≤ ∑ a, ω (γ a) *
        (((ν (γ a)).prod volume).real (countedPacket (H (γ a)) (A a) (R a)
          (B (γ a) / K ^ 2) T (j a)) + ((ν (γ a)).prod volume).real (Bad a)) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hp a) (hω _))
    _ = _ + ∑ a, ω (γ a) * ((ν (γ a)).prod volume).real (Bad a) := by
      simp_rw [mul_add]; rw [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl hbadreal

end Submission.Obl.k4_finite_positive_mixed_greedy_cover
