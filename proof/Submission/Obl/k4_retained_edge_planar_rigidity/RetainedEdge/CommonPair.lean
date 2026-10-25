-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/CommonPair.lean;
-- only the namespace and module paths were renamed to o071's.
import Mathlib

/-!
# A common pair of endpoint sets (paper Lemma 7.3, first half)

Rectangles `R_i ⊆ U`, all of size at least `ℓ`, indexed by a probability law `ν`: two independent
indices have expected overlap at least `ℓ²/|U|` (Cauchy–Schwarz on the coverage function), so some
`i₀` has average overlap at least that much with the others, and the indices whose overlap with
`R_{i₀}` is at least half of it carry `ν`-mass at least `ℓ²/(2|U|²)`.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

noncomputable section

/-- **Common pair by averaging.** -/
theorem common_pair_avg {ι P : Type*} [Fintype ι] [DecidableEq P] (ν : ι → ℝ)
    (hν : ∀ i, 0 ≤ ν i) (hν1 : ∑ i, ν i = 1) (U : Finset P) (R : ι → Finset P)
    (hR : ∀ i, R i ⊆ U) {ℓ : ℝ} (hℓ : 0 < ℓ) (hRl : ∀ i, ℓ ≤ (R i).card) :
    ∃ i₀ : ι, ℓ ^ 2 / (2 * (U.card : ℝ) ^ 2) ≤
      ∑ j, (if ℓ ^ 2 / (2 * U.card) ≤ ((R i₀ ∩ R j).card : ℝ) then ν j else 0) := by
  classical
  have hUpos : (0 : ℝ) < U.card := by
    obtain ⟨i⟩ : Nonempty ι := by
      by_contra hne; rw [not_nonempty_iff] at hne; simp at hν1
    have := hRl i
    have h2 : ((R i).card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card (hR i)
    linarith
  -- the coverage function
  set X : P → ℝ := fun p => ∑ i, ν i * (if p ∈ R i then 1 else 0) with hX
  have hsum1 : ∑ p ∈ U, X p = ∑ i, ν i * (R i).card := by
    simp only [hX]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.inter_eq_right.mpr (hR i)]
  have hsum2 : ∑ p ∈ U, X p ^ 2 = ∑ i, ν i * ∑ j, ν j * ((R i ∩ R j).card : ℝ) := by
    simp only [hX, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ p, ν i * (if p ∈ R i then (1 : ℝ) else 0) * (ν j * (if p ∈ R j then 1 else 0)) =
        ν i * ν j * (if p ∈ R i ∩ R j then 1 else 0) := by
      intro p
      by_cases h1 : p ∈ R i <;> by_cases h2 : p ∈ R j <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun p _ => this p, ← Finset.mul_sum, Finset.sum_ite_mem,
      Finset.sum_const, nsmul_eq_mul, mul_one, mul_assoc]
    congr 2
    rw [Finset.inter_eq_right.mpr (Finset.inter_subset_left.trans (hR i))]
  have hlow1 : ℓ ≤ ∑ p ∈ U, X p := by
    rw [hsum1]
    calc ℓ = ∑ i, ν i * ℓ := by rw [← Finset.sum_mul, hν1, one_mul]
      _ ≤ ∑ i, ν i * (R i).card := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hRl i) (hν i)
  have hCS := sq_sum_le_card_mul_sum_sq (s := U) (f := X)
  have hlow2 : ℓ ^ 2 / U.card ≤ ∑ i, ν i * ∑ j, ν j * ((R i ∩ R j).card : ℝ) := by
    rw [← hsum2, div_le_iff₀ hUpos]
    have h0 : 0 ≤ ℓ := hℓ.le
    calc ℓ ^ 2 ≤ (∑ p ∈ U, X p) ^ 2 := pow_le_pow_left₀ h0 hlow1 2
      _ ≤ U.card * ∑ p ∈ U, X p ^ 2 := hCS
      _ = (∑ p ∈ U, X p ^ 2) * U.card := mul_comm _ _
  -- some index has large average overlap
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ℓ ^ 2 / U.card ≤ ∑ j, ν j * ((R i₀ ∩ R j).card : ℝ) := by
    by_contra hne
    push Not at hne
    obtain ⟨i₁, hi₁⟩ : ∃ i, 0 < ν i := by
      by_contra hpos
      push Not at hpos
      have : ∑ i, ν i ≤ 0 := Finset.sum_nonpos fun i _ => hpos i
      linarith
    have hlt : ∑ i, ν i * ∑ j, ν j * ((R i ∩ R j).card : ℝ) < ∑ i, ν i * (ℓ ^ 2 / U.card) :=
      Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hne i).le (hν i))
        ⟨i₁, Finset.mem_univ _, mul_lt_mul_of_pos_left (hne i₁) hi₁⟩
    rw [← Finset.sum_mul, hν1, one_mul] at hlt
    linarith
  refine ⟨i₀, ?_⟩
  set Q := ℓ ^ 2 / (U.card : ℝ) with hQ
  have hpt : ∀ j, ν j * ((R i₀ ∩ R j).card : ℝ) ≤
      (U.card : ℝ) * (if ℓ ^ 2 / (2 * U.card) ≤ ((R i₀ ∩ R j).card : ℝ) then ν j else 0) +
        ν j * (Q / 2) := by
    intro j
    have hQ2 : ℓ ^ 2 / (2 * (U.card : ℝ)) = Q / 2 := by rw [hQ]; field_simp
    split_ifs with hbig
    · have hle : ((R i₀ ∩ R j).card : ℝ) ≤ U.card := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_left.trans (hR i₀))
      have : 0 ≤ ν j * (Q / 2) := mul_nonneg (hν j) (by positivity)
      nlinarith [hν j]
    · push Not at hbig
      rw [hQ2] at hbig
      rw [mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_left hbig.le (hν j)
  have hsum : Q ≤ (U.card : ℝ) * ∑ j, (if ℓ ^ 2 / (2 * U.card) ≤ ((R i₀ ∩ R j).card : ℝ)
      then ν j else 0) + Q / 2 := by
    calc Q ≤ ∑ j, ν j * ((R i₀ ∩ R j).card : ℝ) := hi₀
      _ ≤ ∑ j, ((U.card : ℝ) * (if ℓ ^ 2 / (2 * U.card) ≤ ((R i₀ ∩ R j).card : ℝ) then ν j else 0)
          + ν j * (Q / 2)) := Finset.sum_le_sum fun j _ => hpt j
      _ = (U.card : ℝ) * ∑ j, (if ℓ ^ 2 / (2 * U.card) ≤ ((R i₀ ∩ R j).card : ℝ) then ν j else 0)
          + Q / 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hν1, one_mul]
  rw [div_le_iff₀ (by positivity)]
  have : Q / 2 ≤ (U.card : ℝ) * ∑ j, (if ℓ ^ 2 / (2 * U.card) ≤ ((R i₀ ∩ R j).card : ℝ)
      then ν j else 0) := by linarith
  calc ℓ ^ 2 = Q / 2 * (2 * U.card) := by rw [hQ]; field_simp
    _ ≤ (U.card : ℝ) * (∑ j, (if ℓ ^ 2 / (2 * U.card) ≤ ((R i₀ ∩ R j).card : ℝ)
          then ν j else 0)) * (2 * U.card) := by gcongr
    _ = (∑ j, (if ℓ ^ 2 / (2 * U.card) ≤ ((R i₀ ∩ R j).card : ℝ) then ν j else 0)) *
          (2 * (U.card : ℝ) ^ 2) := by ring

end

end Submission.Obl.k4_retained_edge_planar_rigidity
