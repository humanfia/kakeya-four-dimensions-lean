-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.LinePins.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/LinePins.lean (b19b589).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Classes

/-!
# The pins of a line are `(1 - s)`-dimensional, label by label

`FailData.classes` (`High/Classes.lean`) bounds the number of same-class pairs of labels
whose points are within `d` by `A r ^ (-2 - 4 η) d ^ (1 - s)`, and bounds the total number
of same-class pairs from below by `r ^ (4 η + ε₀ - 2)`. A label `q` is *bad at the
dyadic scale `k`* when more than `T k` times the size of its class lie within `r 2 ^ k` of
its point. By Markov's inequality, summed over the scales, the bad labels carry a small
part of the class-size-weighted mass `∑ q, #(class of q) = #(same-class pairs)`.

* `nearClass D cls q c`: the labels of the class of `q` whose point is within `c` of `q.1`;
* `classSize D cls q`: the number of labels of the class of `q`;
* `bad_labels_weight_le`: the class-size weight of the labels that are bad at some scale
  `k ≤ K₀` is at most `∑ k ≤ K₀, E k / T k`, where `E k` bounds the same-class pairs within
  `r 2 ^ k`;
* `FailData.bad_labels_weight_le`: with `T k = B (r 2 ^ k) ^ (1 - s)`, that weight is at most
  `(K₀ + 1) A r ^ (-2 - 4 η) / B`, which is a small fraction of the total weight
  `≥ r ^ (4 η + ε₀ - 2)` once `B ≥ (K₀ + 1) A r ^ (-8 η - ε₀ - τ)`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

noncomputable section

/-- The labels of the class of `q` whose point is within `c` of the point of `q`. -/
def nearClass (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (q : E2 × E2) (c : ℝ) :
    Finset (E2 × E2) :=
  D.filter (fun q' => cls q' = cls q ∧ dist q.1 q'.1 < c)

/-- The labels of the class of `q`. -/
def classSize (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (q : E2 × E2) : ℕ :=
  (D.filter (fun q' => cls q' = cls q)).card

/-- Summing the near-class counts over the labels counts the near same-class pairs. -/
theorem sum_nearClass (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (c : ℝ) :
    ∑ q ∈ D, ((nearClass D cls q c).card : ℝ) =
      (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < c)).card : ℝ) := by
  classical
  have hmaps : Set.MapsTo (fun qq : (E2 × E2) × (E2 × E2) => qq.1)
      (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < c)) :
        Set ((E2 × E2) × (E2 × E2))) (D : Set (E2 × E2)) := by
    intro qq hqq
    rw [Finset.mem_coe] at hqq
    simp only [sameClass, Finset.mem_filter, Finset.mem_product] at hqq
    exact hqq.1.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.card_bij (fun q' _ => (q, q'))
  · intro q' hq'
    simp only [nearClass, Finset.mem_filter] at hq'
    obtain ⟨hq'D, hcl, hd⟩ := hq'
    simp only [sameClass, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨⟨hq, hq'D⟩, hcl.symm⟩, hd⟩, trivial⟩
  · intro a _ b _ heq
    exact (Prod.ext_iff.mp heq).2
  · intro qq hqq
    simp only [sameClass, Finset.mem_filter, Finset.mem_product] at hqq
    obtain ⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩ := hqq
    refine ⟨qq.2, ?_, ?_⟩
    · simp only [nearClass, Finset.mem_filter]
      rw [← h5]
      exact ⟨h2, h3.symm, h4⟩
    · rw [← h5]

/-- Markov's inequality over the dyadic scales: the labels that are bad at some scale
`k ≤ K₀` carry class-size weight at most `∑ k ≤ K₀, E k / T k`. -/
theorem bad_labels_weight_le (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    {r : ℝ} (K₀ : ℕ) (E T : ℕ → ℝ) (hT : ∀ k, 0 < T k)
    (henergy : ∀ k ≤ K₀,
      (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < r * 2 ^ k)).card : ℝ) ≤
        E k) :
    ∑ q ∈ D.filter (fun q => ∃ k ≤ K₀,
        T k * (classSize D cls q : ℝ) < ((nearClass D cls q (r * 2 ^ k)).card : ℝ)),
      (classSize D cls q : ℝ) ≤ ∑ k ∈ Finset.range (K₀ + 1), E k / T k := by
  classical
  set Bad := D.filter (fun q => ∃ k ≤ K₀,
    T k * (classSize D cls q : ℝ) < ((nearClass D cls q (r * 2 ^ k)).card : ℝ)) with hBad
  have hpt : ∀ q ∈ Bad, (classSize D cls q : ℝ) ≤
      ∑ k ∈ Finset.range (K₀ + 1), ((nearClass D cls q (r * 2 ^ k)).card : ℝ) / T k := by
    intro q hq
    obtain ⟨-, k, hk, hlt⟩ := Finset.mem_filter.mp hq
    have hk' : k ∈ Finset.range (K₀ + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    have h1 : (classSize D cls q : ℝ) ≤ ((nearClass D cls q (r * 2 ^ k)).card : ℝ) / T k := by
      rw [le_div_iff₀ (hT k)]
      linarith
    refine h1.trans ?_
    exact Finset.single_le_sum (f := fun k => ((nearClass D cls q (r * 2 ^ k)).card : ℝ) / T k)
      (fun k _ => div_nonneg (Nat.cast_nonneg _) (hT k).le) hk'
  calc ∑ q ∈ Bad, (classSize D cls q : ℝ)
      ≤ ∑ q ∈ Bad, ∑ k ∈ Finset.range (K₀ + 1),
          ((nearClass D cls q (r * 2 ^ k)).card : ℝ) / T k := Finset.sum_le_sum hpt
    _ ≤ ∑ q ∈ D, ∑ k ∈ Finset.range (K₀ + 1),
          ((nearClass D cls q (r * 2 ^ k)).card : ℝ) / T k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro q _ _
        exact Finset.sum_nonneg (fun k _ => div_nonneg (Nat.cast_nonneg _) (hT k).le)
    _ = ∑ k ∈ Finset.range (K₀ + 1), (∑ q ∈ D,
          ((nearClass D cls q (r * 2 ^ k)).card : ℝ)) / T k := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_div]
    _ ≤ ∑ k ∈ Finset.range (K₀ + 1), E k / T k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [sum_nearClass]
        exact div_le_div_of_nonneg_right
          (henergy k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) (hT k).le

/-- The total class-size weight is the number of same-class pairs. -/
theorem sum_classSize (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) :
    ∑ q ∈ D, (classSize D cls q : ℝ) = ((sameClass D cls).card : ℝ) := by
  classical
  have hmaps : Set.MapsTo (fun qq : (E2 × E2) × (E2 × E2) => qq.1)
      ((sameClass D cls) : Set ((E2 × E2) × (E2 × E2))) (D : Set (E2 × E2)) := by
    intro qq hqq
    rw [Finset.mem_coe] at hqq
    simp only [sameClass, Finset.mem_filter, Finset.mem_product] at hqq
    exact hqq.1.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  unfold classSize
  congr 1
  apply Finset.card_bij (fun q' _ => (q, q'))
  · intro q' hq'
    simp only [Finset.mem_filter] at hq'
    simp only [sameClass, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨hq, hq'.1⟩, hq'.2.symm⟩, trivial⟩
  · intro a _ b _ heq
    exact (Prod.ext_iff.mp heq).2
  · intro qq hqq
    simp only [sameClass, Finset.mem_filter, Finset.mem_product] at hqq
    obtain ⟨⟨⟨-, h2⟩, h3⟩, h5⟩ := hqq
    refine ⟨qq.2, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      rw [← h5]
      exact ⟨h2, h3.symm⟩
    · rw [← h5]

/-- For a failed bush estimate: with thresholds `T k = B (r 2 ^ k) ^ (1 - s)`, the labels
that are bad at some dyadic scale `k ≤ K₀` carry class-size weight at most
`(K₀ + 1) A r ^ (-2 - 4 η) / B`, with `A = 10 ^ 4 / (1 - (1/2) ^ (1 - s))`. -/
theorem FailData.bad_labels_weight_le {r s ε₀ η B : ℝ} {P : Finset E2}
    {D : Finset (E2 × E2)} (h : FailData r s ε₀ η P D) (hB : 0 < B)
    (cls : E2 × E2 → E2 × E2) (K₀ : ℕ)
    (henergy : ∀ d : ℝ, r ≤ d →
      (((sameClass D cls).filter (fun qq => dist qq.1.1 qq.2.1 < d)).card : ℝ) ≤
        10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * r ^ (-2 - 4 * η) * d ^ (1 - s)) :
    ∑ q ∈ D.filter (fun q => ∃ k ≤ K₀,
        B * (r * 2 ^ k) ^ (1 - s) * (classSize D cls q : ℝ) <
          ((nearClass D cls q (r * 2 ^ k)).card : ℝ)),
      (classSize D cls q : ℝ) ≤
        (K₀ + 1) * (10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * r ^ (-2 - 4 * η)) / B := by
  have hr := h.r_pos
  set A := 10 ^ 4 / (1 - (1 / 2 : ℝ) ^ (1 - s)) * r ^ (-2 - 4 * η) with hA
  have hT : ∀ k : ℕ, 0 < B * (r * 2 ^ k) ^ (1 - s) := fun k => by positivity
  have h1 := WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.bad_labels_weight_le D cls K₀ (fun k => A * (r * 2 ^ k) ^ (1 - s))
    (fun k => B * (r * 2 ^ k) ^ (1 - s)) hT (fun k _ => by
      have hk : r ≤ r * 2 ^ k := by
        have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      exact henergy (r * 2 ^ k) hk)
  have hterm : ∀ k : ℕ, A * (r * 2 ^ k) ^ (1 - s) / (B * (r * 2 ^ k) ^ (1 - s)) = A / B := by
    intro k
    have hpos : 0 < (r * 2 ^ k) ^ (1 - s) := by positivity
    field_simp
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have : ((K₀ + 1 : ℕ) : ℝ) * (A / B) = (K₀ + 1) * A / B := by push_cast; ring
  rw [this] at h1
  exact h1

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
