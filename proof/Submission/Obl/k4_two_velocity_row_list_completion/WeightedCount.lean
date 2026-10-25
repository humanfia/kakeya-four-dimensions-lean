import Mathlib

open scoped BigOperators Classical

namespace Submission.Obl.k4_two_velocity_row_list_completion

/-- Double counting separated pairs in the palette bounds the number of states.
Every state sees palette mass at least `c`, while a short interval has mass at most `c/2`.
The estimate concerns every state, without discarding states of small incidence mass. -/
theorem weighted_pair_count {A V : Type*} (states : Finset A) (velocities : Finset V)
    (weight center : V → ℝ) (compatible : A → V → Prop) (c B δ : ℝ)
    (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hw : ∀ j ∈ velocities, 0 ≤ weight j)
    (hw1 : (∑ j ∈ velocities, weight j) ≤ 1)
    (hdegree : ∀ r ∈ states,
      c ≤ ∑ j ∈ velocities, if compatible r j then weight j else 0)
    (hnear : ∀ j ∈ velocities,
      (∑ k ∈ velocities, if |center k - center j| < δ then weight k else 0) ≤ c / 2)
    (hfiber : ∀ j ∈ velocities, ∀ k ∈ velocities, δ ≤ |center k - center j| →
      ((states.filter (fun r => compatible r j ∧ compatible r k)).card : ℝ) ≤ B) :
    (states.card : ℝ) * c ^ 2 ≤ 2 * B := by
  classical
  let degree (r : A) : ℝ :=
    ∑ j ∈ velocities, if compatible r j then weight j else 0
  let far (r : A) (j : V) : ℝ :=
    ∑ k ∈ velocities,
      if compatible r k ∧ δ ≤ |center k - center j| then weight k else 0
  let pairs (r : A) : ℝ :=
    ∑ j ∈ velocities, if compatible r j then weight j * far r j else 0
  have hsplit (r : A) (j : V) (hj : j ∈ velocities) :
      degree r ≤ far r j + c / 2 := by
    calc
      degree r ≤ far r j +
          ∑ k ∈ velocities, if |center k - center j| < δ then weight k else 0 := by
        dsimp only [degree, far]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro k hk
        by_cases hr : compatible r k <;>
          by_cases hd : δ ≤ |center k - center j| <;>
          simp [hr, hd, not_lt.mpr, lt_of_not_ge] <;> linarith [hw k hk]
      _ ≤ far r j + c / 2 := add_le_add le_rfl (hnear j hj)
  have hrow (r : A) (hr : r ∈ states) : c ^ 2 / 2 ≤ pairs r := by
    have hd : c ≤ degree r := hdegree r hr
    have hd0 : 0 ≤ degree r := hc.trans hd
    have hsq : degree r ^ 2 ≤ pairs r + degree r * (c / 2) := by
      calc
        degree r ^ 2 =
            ∑ j ∈ velocities, if compatible r j then weight j * degree r else 0 := by
          calc
            degree r ^ 2 = (∑ j ∈ velocities,
                if compatible r j then weight j else 0) * degree r := by
              simp only [pow_two]; rfl
            _ = _ := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> simp
        _ ≤ ∑ j ∈ velocities,
            if compatible r j then weight j * (far r j + c / 2) else 0 := by
          apply Finset.sum_le_sum
          intro j hj
          split_ifs with h
          · exact mul_le_mul_of_nonneg_left (hsplit r j hj) (hw j hj)
          · rfl
        _ = pairs r + degree r * (c / 2) := by
          dsimp only [pairs, degree]
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          split_ifs <;> ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hd0,
      mul_nonneg (sub_nonneg.mpr hd) hc]
  have hpair_expand (r : A) : pairs r =
      ∑ j ∈ velocities, ∑ k ∈ velocities,
        if compatible r j ∧ compatible r k ∧ δ ≤ |center k - center j|
        then weight j * weight k else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjr : compatible r j
    · simp only [hjr, true_and, ite_true, far, Finset.mul_sum, mul_ite, mul_zero]
    · simp [hjr]
  have hupper : (∑ r ∈ states, pairs r) ≤ B := by
    calc
      (∑ r ∈ states, pairs r) =
          ∑ j ∈ velocities, ∑ k ∈ velocities, ∑ r ∈ states,
            if compatible r j ∧ compatible r k ∧ δ ≤ |center k - center j|
            then weight j * weight k else 0 := by
        simp_rw [hpair_expand]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
      _ ≤ ∑ j ∈ velocities, ∑ k ∈ velocities, B * (weight j * weight k) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        have hp : 0 ≤ weight j * weight k := mul_nonneg (hw j hj) (hw k hk)
        by_cases hsep : δ ≤ |center k - center j|
        · simp only [hsep, and_true]
          rw [← Finset.sum_filter]
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hfiber j hj k hk hsep) hp
        · simpa only [hsep, and_false, ite_false, Finset.sum_const_zero] using
            mul_nonneg hB hp
      _ = B * (∑ j ∈ velocities, weight j) ^ 2 := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring
      _ ≤ B := by
        have hsum0 : 0 ≤ ∑ j ∈ velocities, weight j := Finset.sum_nonneg hw
        have hsq : (∑ j ∈ velocities, weight j) ^ 2 ≤ 1 := by nlinarith
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hB
  have hlower : (states.card : ℝ) * (c ^ 2 / 2) ≤ ∑ r ∈ states, pairs r := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hrow
  nlinarith

end Submission.Obl.k4_two_velocity_row_list_completion
