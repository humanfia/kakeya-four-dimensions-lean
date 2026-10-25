-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.Grains.Merge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Merging light pieces (bin packing by prefix sums)

Given finitely many weights `w s ∈ [0, τ]`, label each index by the integer part of `S / τ`,
where `S` is the sum of the weights before it in a fixed enumeration. Each block of equal labels
is contained in an interval `[a, b]` of the enumeration, so its weight is at most
`S(b) - S(a) + w(b) < τ + τ`; every label is at most `(∑ w) / τ`, so there are at most
`(∑ w) / τ + 1` blocks. This replaces a cell count (Warren's theorem): the merged pieces of one
subcube number at most `mass / τ + 1`.
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
namespace Merge

/-- Prefix sums of a weight sequence. -/
noncomputable def pre (w : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, w i

lemma pre_mono {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) : Monotone (pre w) := by
  intro a b hab
  unfold pre
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun i _ _ => hw i)

lemma pre_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (k : ℕ) : 0 ≤ pre w k :=
  Finset.sum_nonneg fun i _ => hw i

/-- The weight of the indices of `K ⊆ [a, b]` is at most `pre (b + 1) - pre a`. -/
lemma sum_le_pre_sub {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (K : Finset ℕ) {a b : ℕ}
    (hK : ∀ k ∈ K, a ≤ k ∧ k ≤ b) (hab : a ≤ b) :
    ∑ k ∈ K, w k ≤ pre w (b + 1) - pre w a := by
  have hsub : K ⊆ Finset.Ico a (b + 1) := by
    intro k hk
    rw [Finset.mem_Ico]
    exact ⟨(hK k hk).1, Nat.lt_succ_of_le (hK k hk).2⟩
  calc ∑ k ∈ K, w k ≤ ∑ k ∈ Finset.Ico a (b + 1), w k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hw i)
    _ = pre w (b + 1) - pre w a := by
        unfold pre
        rw [Finset.sum_Ico_eq_sub _ (by omega)]

/-- Blocks of the prefix-sum labelling have weight at most `2 τ`. -/
lemma block_sum_le {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {τ : ℝ} (hτ : 0 < τ)
    (hwτ : ∀ i, w i ≤ τ) (K : Finset ℕ) (m : ℕ)
    (hK : ∀ k ∈ K, ⌊pre w k / τ⌋₊ = m) :
    ∑ k ∈ K, w k ≤ 2 * τ := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · rw [hK0, Finset.sum_empty]; linarith
  set a := K.min' hKne
  set b := K.max' hKne
  have ha : a ∈ K := K.min'_mem hKne
  have hb : b ∈ K := K.max'_mem hKne
  have hab : a ≤ b := K.min'_le_max' hKne
  have hbound : ∀ k ∈ K, a ≤ k ∧ k ≤ b := fun k hk => ⟨K.min'_le k hk, K.le_max' k hk⟩
  have h1 := sum_le_pre_sub hw K hbound hab
  -- `m τ ≤ pre a` and `pre b < (m + 1) τ`
  have hpa : (m : ℝ) * τ ≤ pre w a := by
    have := Nat.floor_le (div_nonneg (pre_nonneg hw a) hτ.le)
    rw [hK a ha, le_div_iff₀ hτ] at this
    exact this
  have hpb : pre w b < ((m : ℝ) + 1) * τ := by
    have := Nat.lt_floor_add_one (pre w b / τ)
    rw [hK b hb, div_lt_iff₀ hτ] at this
    exact this
  have hsucc : pre w (b + 1) = pre w b + w b := by
    unfold pre
    rw [Finset.sum_range_succ]
  have := hwτ b
  rw [hsucc] at h1
  nlinarith

/-- Prefix-sum labels are at most `(total weight) / τ`. -/
lemma floor_pre_le {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {τ : ℝ} (hτ : 0 < τ) {k n : ℕ}
    (hk : k ≤ n) : (⌊pre w k / τ⌋₊ : ℝ) ≤ pre w n / τ := by
  refine le_trans (Nat.floor_le (div_nonneg (pre_nonneg hw k) hτ.le)) ?_
  exact div_le_div_of_nonneg_right (pre_mono hw hk) hτ.le

/-- Merging: a labelling `g` of a finite index type with weights in `[0, τ]` whose blocks weigh
at most `2 τ` and whose labels are at most `(∑ w) / τ`. -/
theorem exists_merge {σ : Type*} [Fintype σ] (w : σ → ℝ) (hw0 : ∀ s, 0 ≤ w s) {τ : ℝ}
    (hτ : 0 < τ) (hwτ : ∀ s, w s ≤ τ) :
    ∃ g : σ → ℕ, (∀ m : ℕ, ∑ s ∈ Finset.univ.filter (fun s => g s = m), w s ≤ 2 * τ) ∧
      ∀ s, (g s : ℝ) ≤ (∑ s, w s) / τ := by
  classical
  set n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let w' : ℕ → ℝ := fun k => if h : k < n then w (e.symm ⟨k, h⟩) else 0
  have hw' : ∀ k, 0 ≤ w' k := by
    intro k; simp only [w']; split_ifs <;> simp [hw0]
  have hw'τ : ∀ k, w' k ≤ τ := by
    intro k; simp only [w']; split_ifs
    · exact hwτ _
    · exact hτ.le
  have hw'e : ∀ s, w' (e s : ℕ) = w s := by
    intro s
    simp only [w', Fin.is_lt, dite_true, Fin.eta, Equiv.symm_apply_apply]
  have htot : pre w' n = ∑ s, w s := by
    unfold pre
    rw [Finset.sum_range (fun k => w' k)]
    rw [← Equiv.sum_comp e.symm (fun s => w s)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w', Fin.is_lt, dite_true, Fin.eta]
  refine ⟨fun s => ⌊pre w' (e s : ℕ) / τ⌋₊, fun m => ?_, fun s => ?_⟩
  · -- transport the block to `ℕ`
    set B := Finset.univ.filter (fun s => ⌊pre w' (e s : ℕ) / τ⌋₊ = m)
    have himg : ∑ s ∈ B, w s = ∑ k ∈ B.image (fun s => (e s : ℕ)), w' k := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl fun s _ => (hw'e s).symm
      · intro s _ t _ hst
        exact e.injective (Fin.ext hst)
    rw [himg]
    refine block_sum_le hw' hτ hw'τ _ m ?_
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨s, hs, rfl⟩ := hk
    exact (Finset.mem_filter.1 hs).2
  · rw [← htot]
    exact floor_pre_le hw' hτ (e s).isLt.le

end Merge
end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
