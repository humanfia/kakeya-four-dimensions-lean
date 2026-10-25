-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.PopularOverlap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# A popular index for a family of large rectangles

If `A t × B t ⊆ A × B` has density at least `c` for every `t ∈ S`, then some `t₀ ∈ S`
overlaps at least `c ^ 2 * #S / 2` of the rectangles in density `c ^ 2 / 2` in each factor.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped BigOperators

theorem popular_overlap {ι X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (S : Finset ι) (A : Finset X) (B : Finset Y) (Af : ι → Finset X) (Bf : ι → Finset Y)
    (hS : S.Nonempty) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAf : ∀ t ∈ S, Af t ⊆ A) (hBf : ∀ t ∈ S, Bf t ⊆ B) {c : ℝ} (hc : 0 < c)
    (hcard : ∀ t ∈ S, c * (A.card : ℝ) * (B.card : ℝ) ≤ ((Af t).card : ℝ) * ((Bf t).card : ℝ)) :
    ∃ t₀ ∈ S, ∃ S' ⊆ S, c ^ 2 * (S.card : ℝ) / 2 ≤ (S'.card : ℝ) ∧
      ∀ t ∈ S', c ^ 2 * (A.card : ℝ) / 2 ≤ ((Af t₀ ∩ Af t).card : ℝ) ∧
        c ^ 2 * (B.card : ℝ) / 2 ≤ ((Bf t₀ ∩ Bf t).card : ℝ) := by
  classical
  have hnA : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hnB : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hnS : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  -- the multiplicity of a pair
  let n : X × Y → ℝ := fun p => ∑ t ∈ S, (if p.1 ∈ Af t ∧ p.2 ∈ Bf t then (1 : ℝ) else 0)
  have hcardAB (t : ι) (ht : t ∈ S) : ((Af t).card : ℝ) * ((Bf t).card : ℝ) =
      ∑ p ∈ A ×ˢ B, (if p.1 ∈ Af t ∧ p.2 ∈ Bf t then (1 : ℝ) else 0) := by
    rw [Finset.sum_product]
    have hA' : ((Af t).card : ℝ) = ∑ x ∈ A, (if x ∈ Af t then (1 : ℝ) else 0) := by
      rw [Finset.sum_boole]
      congr 2
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hAf t ht h, h⟩, fun h => h.2⟩
    have hB' : ((Bf t).card : ℝ) = ∑ y ∈ B, (if y ∈ Bf t then (1 : ℝ) else 0) := by
      rw [Finset.sum_boole]
      congr 2
      ext y
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hBf t ht h, h⟩, fun h => h.2⟩
    rw [hA', hB', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases hx : x ∈ Af t <;> by_cases hy : y ∈ Bf t <;> simp [hx, hy]
  have hinter (t t' : ι) (ht : t ∈ S) :
      ((Af t ∩ Af t').card : ℝ) * ((Bf t ∩ Bf t').card : ℝ) =
        ∑ p ∈ A ×ˢ B, (if p.1 ∈ Af t ∧ p.2 ∈ Bf t then (1 : ℝ) else 0) *
          (if p.1 ∈ Af t' ∧ p.2 ∈ Bf t' then (1 : ℝ) else 0) := by
    rw [Finset.sum_product]
    have hA' : ((Af t ∩ Af t').card : ℝ) =
        ∑ x ∈ A, (if x ∈ Af t ∧ x ∈ Af t' then (1 : ℝ) else 0) := by
      rw [Finset.sum_boole]
      congr 2
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter]
      exact ⟨fun h => ⟨hAf t ht h.1, h⟩, fun h => h.2⟩
    have hB' : ((Bf t ∩ Bf t').card : ℝ) =
        ∑ y ∈ B, (if y ∈ Bf t ∧ y ∈ Bf t' then (1 : ℝ) else 0) := by
      rw [Finset.sum_boole]
      congr 2
      ext y
      simp only [Finset.mem_filter, Finset.mem_inter]
      exact ⟨fun h => ⟨hBf t ht h.1, h⟩, fun h => h.2⟩
    rw [hA', hB', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases hx : x ∈ Af t <;> by_cases hx' : x ∈ Af t' <;> by_cases hy : y ∈ Bf t <;>
      by_cases hy' : y ∈ Bf t' <;> simp [hx, hx', hy, hy']
  -- first moment
  have hsum1 : c * (S.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) ≤ ∑ p ∈ A ×ˢ B, n p := by
    calc c * (S.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ))
        = ∑ t ∈ S, c * (A.card : ℝ) * (B.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ t ∈ S, ((Af t).card : ℝ) * ((Bf t).card : ℝ) := Finset.sum_le_sum hcard
      _ = ∑ t ∈ S, ∑ p ∈ A ×ˢ B, (if p.1 ∈ Af t ∧ p.2 ∈ Bf t then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun t ht => hcardAB t ht)
      _ = ∑ p ∈ A ×ˢ B, n p := Finset.sum_comm
  -- second moment
  have hsum2 : ∑ p ∈ A ×ˢ B, n p ^ 2 =
      ∑ t ∈ S, ∑ t' ∈ S, ((Af t ∩ Af t').card : ℝ) * ((Bf t ∩ Bf t').card : ℝ) := by
    have h1 : ∀ p ∈ A ×ˢ B, n p ^ 2 = ∑ t ∈ S, ∑ t' ∈ S,
        (if p.1 ∈ Af t ∧ p.2 ∈ Bf t then (1 : ℝ) else 0) *
          (if p.1 ∈ Af t' ∧ p.2 ∈ Bf t' then (1 : ℝ) else 0) := by
      intro p _
      simp only [n, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun t' _ => (hinter t t' ht).symm)
  have hcs : (∑ p ∈ A ×ˢ B, n p) ^ 2 ≤ ((A ×ˢ B).card : ℝ) * ∑ p ∈ A ×ˢ B, n p ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_product, Nat.cast_mul] at hcs
  have hsec : c ^ 2 * (S.card : ℝ) ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) ≤
      ∑ t ∈ S, ∑ t' ∈ S, ((Af t ∩ Af t').card : ℝ) * ((Bf t ∩ Bf t').card : ℝ) := by
    rw [← hsum2]
    have hAB : 0 < (A.card : ℝ) * (B.card : ℝ) := by positivity
    have h0 : 0 ≤ c * (S.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) := by positivity
    have h2 := pow_le_pow_left₀ h0 hsum1 2
    have h3 : (c * (S.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ))) ^ 2 ≤
        ((A.card : ℝ) * (B.card : ℝ)) * ∑ p ∈ A ×ˢ B, n p ^ 2 := h2.trans hcs
    have e : (c * (S.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ))) ^ 2 =
        ((A.card : ℝ) * (B.card : ℝ)) *
          (c ^ 2 * (S.card : ℝ) ^ 2 * ((A.card : ℝ) * (B.card : ℝ))) := by ring
    rw [e] at h3
    exact le_of_mul_le_mul_left h3 hAB
  -- a popular index
  have hexists : ∃ t₀ ∈ S, c ^ 2 * (S.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) ≤
      ∑ t ∈ S, ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ) := by
    apply Finset.exists_le_of_sum_le hS
    rw [Finset.sum_const, nsmul_eq_mul]
    calc (S.card : ℝ) * (c ^ 2 * (S.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ)))
        = c ^ 2 * (S.card : ℝ) ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) := by ring
      _ ≤ _ := hsec
  obtain ⟨t₀, ht₀, hpop⟩ := hexists
  refine ⟨t₀, ht₀, S.filter (fun t => c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 ≤
      ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ)), Finset.filter_subset _ _, ?_, ?_⟩
  · -- size of the popular set
    set S' := S.filter (fun t => c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 ≤
      ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ)) with hS'
    have hsplit := Finset.sum_filter_add_sum_filter_not S
      (fun t => c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 ≤
        ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ))
      (fun t => ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ))
    have hin : ∑ t ∈ S', ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ) ≤
        (S'.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) := by
      calc ∑ t ∈ S', ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ)
          ≤ ∑ t ∈ S', (A.card : ℝ) * (B.card : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            have h1 : ((Af t₀ ∩ Af t).card : ℝ) ≤ A.card := by
              exact_mod_cast Finset.card_le_card (Finset.inter_subset_left.trans (hAf t₀ ht₀))
            have h2 : ((Bf t₀ ∩ Bf t).card : ℝ) ≤ B.card := by
              exact_mod_cast Finset.card_le_card (Finset.inter_subset_left.trans (hBf t₀ ht₀))
            exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = (S'.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hout : ∑ t ∈ S.filter (fun t => ¬ c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 ≤
          ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ)),
          ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ) ≤
        (S.card : ℝ) * (c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2) := by
      calc _ ≤ ∑ t ∈ S.filter (fun t => ¬ c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 ≤
            ((Af t₀ ∩ Af t).card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ)),
            c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 :=
            Finset.sum_le_sum (fun t ht => (not_le.mp (Finset.mem_filter.mp ht).2).le)
        _ = ((S.filter _).card : ℝ) * (c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (S.card : ℝ) * (c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_filter_le _ _
    have hAB : 0 < (A.card : ℝ) * (B.card : ℝ) := by positivity
    have key : c ^ 2 * (S.card : ℝ) / 2 * ((A.card : ℝ) * (B.card : ℝ)) ≤
        (S'.card : ℝ) * ((A.card : ℝ) * (B.card : ℝ)) := by
      rw [← hS'] at hsplit
      nlinarith
    exact le_of_mul_le_mul_right key hAB
  · intro t ht
    have h := (Finset.mem_filter.mp ht).2
    have ht' := (Finset.mem_filter.mp ht).1
    have h1 : ((Af t₀ ∩ Af t).card : ℝ) ≤ A.card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left.trans (hAf t₀ ht₀))
    have h2 : ((Bf t₀ ∩ Bf t).card : ℝ) ≤ B.card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left.trans (hBf t₀ ht₀))
    have h1' : 0 ≤ ((Af t₀ ∩ Af t).card : ℝ) := Nat.cast_nonneg _
    have h2' : 0 ≤ ((Bf t₀ ∩ Bf t).card : ℝ) := Nat.cast_nonneg _
    constructor
    · have : c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 ≤
          ((Af t₀ ∩ Af t).card : ℝ) * (B.card : ℝ) :=
        h.trans (mul_le_mul_of_nonneg_left h2 h1')
      have e : c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 =
          c ^ 2 * (A.card : ℝ) / 2 * (B.card : ℝ) := by ring
      rw [e] at this
      exact le_of_mul_le_mul_right this hnB
    · have : c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 ≤
          (A.card : ℝ) * ((Bf t₀ ∩ Bf t).card : ℝ) :=
        h.trans (mul_le_mul_of_nonneg_right h1 h2')
      have e : c ^ 2 * ((A.card : ℝ) * (B.card : ℝ)) / 2 =
          (A.card : ℝ) * (c ^ 2 * (B.card : ℝ) / 2) := by ring
      rw [e] at this
      exact le_of_mul_le_mul_left this hnA

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
