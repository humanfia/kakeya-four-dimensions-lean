import Submission.Obl.k4_oss_weighted_level_transfer.Input
import Submission.Obl.k4_oss_weighted_level_transfer.PairArithmetic

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

lemma pair_power_budgets {δ a θ γ Q : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (ha : 0 < a) (hθ : 10 * a ≤ θ) (hγ : 20 * a ≤ γ)
    (hQ : δ ^ (1 - γ) ≤ Q) :
    (δ ^ (10 * a)) ^ 2 * (δ ^ (-a)) ^ 2 ≤ δ ^ (6 * a) ∧
    δ ^ (10 * a) * (δ ^ (-a)) ^ 4 ≤ δ ^ (6 * a) ∧
    (δ ^ (-a)) ^ 4 ≤ δ ^ (6 * a) * Q * δ ^ (-1 + γ / 2) ∧
    δ ^ θ * (δ ^ (-a)) ^ 4 ≤ δ ^ (6 * a) := by
  have hp (x : ℝ) (n : ℕ) : (δ ^ x) ^ n = δ ^ (x * n) :=
    (Real.rpow_mul_natCast hδ.le x n).symm
  constructor
  · rw [hp, hp, ← Real.rpow_add hδ]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le
    norm_num only [Nat.cast_ofNat]
    linarith
  constructor
  · rw [hp, ← Real.rpow_add hδ]
    exact le_of_eq (congrArg (fun x : ℝ => δ ^ x) (by ring))
  constructor
  · calc
      _ = δ ^ (-a * 4) := hp _ _
      _ ≤ δ ^ (6 * a + (1 - γ) + (-1 + γ / 2)) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)
      _ = δ ^ (6 * a) * δ ^ (1 - γ) * δ ^ (-1 + γ / 2) := by
        rw [Real.rpow_add hδ, Real.rpow_add hδ]
      _ ≤ _ := by gcongr
  · rw [hp, ← Real.rpow_add hδ]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le
    norm_num only [Nat.cast_ofNat]
    linarith

/-- Every pair of coarse weight levels gains a fixed power relative to the original collision. -/
lemma weighted_pair_bound {s γ θ δ a Q : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (ha : 0 < a) (hθ : 10 * a ≤ θ) (hγ : 20 * a ≤ γ) (hγp : 0 < γ)
    (hG : FiniteGain s γ θ δ) (hQ : δ ^ (1 - γ) ≤ Q)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Icc (1 / 4 : ℝ) 1)ᶜ = 0)
    (hνcap : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      ν (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (s / 2)))
    (A B : Finset ℝ) (w v : ℝ) (hw : 0 ≤ w) (hv : 0 ≤ v)
    (hsepA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hsepB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hmA : w * (A.card : ℝ) ≤ δ ^ (-a))
    (hmB : v * (B.card : ℝ) ≤ δ ^ (-a))
    (hqA : w ^ 2 * (A.card : ℝ) ≤ (δ ^ (-a)) ^ 2 * Q)
    (hqB : v ^ 2 * (B.card : ℝ) ≤ (δ ^ (-a)) ^ 2 * Q)
    (hcapA : δ ^ (10 * a) < w * (A.card : ℝ) →
      ∀ x u : ℝ, δ ≤ u → ((A.filter (fun y => dist y x ≤ u)).card : ℝ) ≤
        δ ^ (-θ) * u ^ (s / 2) * A.card)
    (hcapB : δ ^ (10 * a) < v * (B.card : ℝ) →
      ∀ x u : ℝ, δ ≤ u → ((B.filter (fun y => dist y x ≤ u)).card : ℝ) ≤
        δ ^ (-θ) * u ^ (s / 2) * B.card) :
    w ^ 2 * v ^ 2 * averageEnergy δ ν A B ≤ 130 * δ ^ (6 * a) * Q := by
  have hQ0 : 0 ≤ Q := (Real.rpow_pos_of_pos hδ _).le.trans hQ
  have hA0 : 0 ≤ (A.card : ℝ) := by positivity
  have hB0 : 0 ≤ (B.card : ℝ) := by positivity
  have heL := averageEnergy_le_left hδ ν hν A B hsepB
  have heR : averageEnergy δ ν A B ≤ 130 * (B.card : ℝ) ^ 2 * (A.card : ℝ) := by
    convert averageEnergy_le_right hδ ν A B hsepA using 1 <;> ring
  obtain ⟨hsmall, hratio, hlarge, hgain⟩ := pair_power_budgets hδ hδ1 ha hθ hγ hQ
  by_cases hm : w * (A.card : ℝ) ≤ δ ^ (10 * a)
  · exact (weighted_cubic_mass hw hA0 hB0 (by norm_num) heL hm hqB).trans
      (by gcongr)
  have hmAp := lt_of_not_ge hm
  by_cases hm : v * (B.card : ℝ) ≤ δ ^ (10 * a)
  · have h := (weighted_cubic_mass hv hB0 hA0 (by norm_num) heR hm hqA).trans
      (show 130 * ((δ ^ (10 * a)) ^ 2 * (δ ^ (-a)) ^ 2) * Q ≤
        130 * δ ^ (6 * a) * Q by gcongr)
    convert h using 1 <;> ring
  have hmBp := lt_of_not_ge hm
  by_cases hB : δ ^ (-1 + γ / 2) < (B.card : ℝ)
  · exact weighted_cubic_large hw hv hA0 hB0 (by norm_num)
      (Real.rpow_pos_of_pos hδ _) hB.le heL hmA hmB hlarge
  by_cases hA : δ ^ (-1 + γ / 2) < (A.card : ℝ)
  · have h := weighted_cubic_large hv hw hB0 hA0 (by norm_num)
      (Real.rpow_pos_of_pos hδ _) hA.le heR hmB hmA hlarge
    convert h using 1 <;> ring
  by_cases hAB : δ ^ (10 * a) * (A.card : ℝ) ≤ (B.card : ℝ)
  · by_cases hBA : δ ^ (10 * a) * (B.card : ℝ) ≤ (A.card : ℝ)
    · have hAp : 0 < (A.card : ℝ) := by
        by_contra hn
        have hz : (A.card : ℝ) = 0 := le_antisymm (le_of_not_gt hn) hA0
        rw [hz, mul_zero] at hmAp
        linarith [Real.rpow_pos_of_pos hδ (10 * a)]
      have hBp : 0 < (B.card : ℝ) := by
        by_contra hn
        have hz : (B.card : ℝ) = 0 := le_antisymm (le_of_not_gt hn) hB0
        rw [hz, mul_zero] at hmBp
        linarith [Real.rpow_pos_of_pos hδ (10 * a)]
      have hAne : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hAp)
      have hBne : B.Nonempty := Finset.card_pos.mp (by exact_mod_cast hBp)
      obtain ⟨d, hd0, hd1, hAl, hAu, hBl, hBu⟩ := common_dimension hδ hδ1 hγp hθ
        (by linarith) (by exact_mod_cast hAne.card_pos) (by exact_mod_cast hBne.card_pos)
        (le_of_not_gt hA) (le_of_not_gt hB) hAB hBA
      have he : averageEnergy δ ν A B ≤ δ ^ θ * (A.card : ℝ) ^ 2 * (B.card : ℝ) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity)
          (hG d hd0 hd1 A B hAne hBne hsepA hsepB
            (hcapA hmAp) (hcapB hmBp) hAl hAu hBl hBu ν inferInstance hν hνcap)
      calc
        _ ≤ (δ ^ θ * (δ ^ (-a)) ^ 4) * Q :=
          weighted_cubic_gain hw hA0 hB0 (by positivity) hQ0 he hmA hqB
        _ ≤ δ ^ (6 * a) * Q := by gcongr
        _ ≤ 130 * δ ^ (6 * a) * Q := by nlinarith [Real.rpow_pos_of_pos hδ (6 * a)]
    · have h := weighted_cubic_ratio hw hv hA0 hB0 (by norm_num) (by positivity)
        hQ0 heL (le_of_not_ge hBA) hmB hqA
      exact h.trans (by gcongr)
  · have h := weighted_cubic_ratio hv hw hB0 hA0 (by norm_num) (by positivity)
      hQ0 heR (le_of_not_ge hAB) hmA hqB
    have h' := h.trans (show 130 * (δ ^ (10 * a) * (δ ^ (-a)) ^ 4) * Q ≤
      130 * δ ^ (6 * a) * Q by gcongr)
    convert h' using 1 <;> ring

end Submission.Obl.k4_oss_weighted_level_transfer
