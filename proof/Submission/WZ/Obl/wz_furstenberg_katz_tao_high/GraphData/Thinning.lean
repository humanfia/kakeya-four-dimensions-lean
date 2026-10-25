-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.Thinning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/Thinning.lean (82de8bd).
import Mathlib

/-!
# Greedy thinning with weights, and sup-metric packing in the plane

* `greedy_thin`: for a reflexive symmetric relation `R` on a finset `F` whose neighbourhoods
  have at most `D` elements, there is an `R`-independent `S ⊆ F` with
  `∑_{F} w ≤ D · ∑_{S} w` for any nonnegative weights `w` (take the heaviest element, delete its
  neighbourhood, recurse).
* `card_sup_ball_le`: points of `ℝ × ℝ` that are pairwise at sup-distance at least `σ > 0` meet a
  sup-ball of radius `ρ` in at most `(2 ρ / σ + 2) ^ 2` points.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open scoped BigOperators

/-- **Greedy thinning.** -/
theorem greedy_thin {α : Type*} [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ i, R i i) (hsymm : ∀ i j, R i j → R j i) (D : ℕ) (w : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    ∀ F : Finset α, (∀ i ∈ F, (F.filter (R i)).card ≤ D) →
      ∃ S : Finset α, S ⊆ F ∧ (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ R i j) ∧
        ∑ i ∈ F, w i ≤ (D : ℝ) * ∑ i ∈ S, w i := by
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
    intro hdeg
    rcases F.eq_empty_or_nonempty with hF | hF
    · exact ⟨∅, by simp [hF], by simp, by simp [hF]⟩
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image F w hF
    set N := F.filter (R i) with hN
    set F' := F \ N with hF'
    have hiN : i ∈ N := Finset.mem_filter.mpr ⟨hi, hrefl i⟩
    have hsub : F' ⊂ F := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
      intro h
      have : i ∈ F' := h ▸ hi
      exact (Finset.mem_sdiff.mp this).2 hiN
    have hdeg' : ∀ j ∈ F', (F'.filter (R j)).card ≤ D := by
      intro j hj
      exact (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)).trans
        (hdeg j (Finset.mem_sdiff.mp hj).1)
    obtain ⟨S', hS'F', hS'ind, hS'w⟩ := ih F' hsub hdeg'
    have hiS' : i ∉ S' := fun h => (Finset.mem_sdiff.mp (hS'F' h)).2 hiN
    refine ⟨insert i S', ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact (Finset.mem_sdiff.mp (hS'F' hj)).1
    · intro a ha b hb hab
      have hnotR : ∀ j ∈ S', ¬ R i j := by
        intro j hj hR
        exact (Finset.mem_sdiff.mp (hS'F' hj)).2
          (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (hS'F' hj)).1, hR⟩)
      by_cases hai : a = i
      · by_cases hbi : b = i
        · exact absurd (hai.trans hbi.symm) hab
        · have hbS : b ∈ S' := (Finset.mem_insert.mp hb).resolve_left hbi
          rw [hai]; exact hnotR b hbS
      · have haS : a ∈ S' := (Finset.mem_insert.mp ha).resolve_left hai
        by_cases hbi : b = i
        · rw [hbi]; intro hR; exact hnotR a haS (hsymm _ _ hR)
        · have hbS : b ∈ S' := (Finset.mem_insert.mp hb).resolve_left hbi
          exact hS'ind a haS b hbS hab
    · have hsplit : ∑ j ∈ F, w j = ∑ j ∈ N, w j + ∑ j ∈ F', w j := by
        have := Finset.sum_sdiff (f := w) (Finset.filter_subset (R i) F)
        rw [hF', hN]
        linarith
      have hNw : ∑ j ∈ N, w j ≤ (D : ℝ) * w i := by
        calc ∑ j ∈ N, w j ≤ ∑ _j ∈ N, w i := Finset.sum_le_sum (fun j hj =>
              hmax j (Finset.mem_filter.mp hj).1)
          _ = (N.card : ℝ) * w i := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (D : ℝ) * w i := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg i hi) (hw i)
      rw [Finset.sum_insert hiS', hsplit, mul_add]
      linarith

/-- **Packing in the sup metric.** -/
theorem card_sup_ball_le {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (L : Finset (ℝ × ℝ))
    (hsep : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → σ ≤ dist l l') (z : ℝ × ℝ) :
    ((L.filter (fun l => dist l z ≤ ρ)).card : ℝ) ≤ (2 * ρ / σ + 2) ^ 2 := by
  classical
  set K : ℕ := ⌈2 * ρ / σ⌉₊ + 1 with hK
  -- grid code relative to the corner of the ball
  set g : ℝ × ℝ → ℕ × ℕ := fun l =>
    (⌊(l.1 - (z.1 - ρ)) / σ⌋₊, ⌊(l.2 - (z.2 - ρ)) / σ⌋₊) with hg
  have hmaps : ∀ l ∈ L.filter (fun l => dist l z ≤ ρ),
      g l ∈ Finset.range K ×ˢ Finset.range K := by
    intro l hl
    have hd := (Finset.mem_filter.mp hl).2
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hd
    obtain ⟨h1, h2⟩ := hd
    have hb : ∀ t : ℝ, |t| ≤ ρ → ⌊(t + ρ) / σ⌋₊ < K := by
      intro t ht
      have hle : (t + ρ) / σ ≤ 2 * ρ / σ := by
        apply div_le_div_of_nonneg_right _ hσ.le
        linarith [(abs_le.mp ht).2]
      have := Nat.floor_le_floor hle
      have h2 : ⌊2 * ρ / σ⌋₊ ≤ ⌈2 * ρ / σ⌉₊ := Nat.floor_le_ceil _
      omega
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩
    · have := hb (l.1 - z.1) h1
      simpa [hg, sub_sub_eq_add_sub, add_comm, add_sub_assoc] using this
    · have := hb (l.2 - z.2) h2
      simpa [hg, sub_sub_eq_add_sub, add_comm, add_sub_assoc] using this
  have hinj : Set.InjOn g ↑(L.filter (fun l => dist l z ≤ ρ)) := by
    intro l hl l' hl' heq
    by_contra hne
    have hlL := (Finset.mem_filter.mp hl).1
    have hl'L := (Finset.mem_filter.mp hl').1
    have hs := hsep l hlL l' hl'L hne
    simp only [hg, Prod.mk.injEq] at heq
    have hnn1 : 0 ≤ (l.1 - (z.1 - ρ)) / σ := by
      have hd := (Finset.mem_filter.mp hl).2
      rw [Prod.dist_eq, max_le_iff, Real.dist_eq] at hd
      apply div_nonneg _ hσ.le; linarith [(abs_le.mp hd.1).1]
    have hnn1' : 0 ≤ (l'.1 - (z.1 - ρ)) / σ := by
      have hd := (Finset.mem_filter.mp hl').2
      rw [Prod.dist_eq, max_le_iff, Real.dist_eq] at hd
      apply div_nonneg _ hσ.le; linarith [(abs_le.mp hd.1).1]
    have hnn2 : 0 ≤ (l.2 - (z.2 - ρ)) / σ := by
      have hd := (Finset.mem_filter.mp hl).2
      rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hd
      apply div_nonneg _ hσ.le; linarith [(abs_le.mp hd.2).1]
    have hnn2' : 0 ≤ (l'.2 - (z.2 - ρ)) / σ := by
      have hd := (Finset.mem_filter.mp hl').2
      rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hd
      apply div_nonneg _ hσ.le; linarith [(abs_le.mp hd.2).1]
    have close : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ⌊a⌋₊ = ⌊b⌋₊ → |a - b| < 1 := by
      intro a b ha hb hab
      have h1 := Nat.floor_le ha
      have h2 := Nat.lt_floor_add_one a
      have h3 := Nat.floor_le hb
      have h4 := Nat.lt_floor_add_one b
      rw [hab] at h1 h2
      rw [abs_lt]; constructor <;> linarith
    have c1 := close _ _ hnn1 hnn1' heq.1
    have c2 := close _ _ hnn2 hnn2' heq.2
    rw [← sub_div, abs_div, abs_of_pos hσ, div_lt_one hσ] at c1 c2
    have e1 : l.1 - (z.1 - ρ) - (l'.1 - (z.1 - ρ)) = l.1 - l'.1 := by ring
    have e2 : l.2 - (z.2 - ρ) - (l'.2 - (z.2 - ρ)) = l.2 - l'.2 := by ring
    rw [e1] at c1; rw [e2] at c2
    have : dist l l' < σ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt c1 c2
    linarith
  have hcard := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  have hKr : (K : ℝ) ≤ 2 * ρ / σ + 2 := by
    rw [hK]; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * ρ / σ by positivity)
    linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  calc ((L.filter (fun l => dist l z ≤ ρ)).card : ℝ) ≤ (K * K : ℕ) := by exact_mod_cast hcard
    _ = (K : ℝ) ^ 2 := by push_cast; ring
    _ ≤ (2 * ρ / σ + 2) ^ 2 := pow_le_pow_left₀ hK0 hKr 2

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
