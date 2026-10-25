/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/Descendants.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.PreparedModel

/-!
# Descendants of a parent label

For a parent label with prior set `A_Q` and dyadic time block `I_Q` at level
`T_Q`, its descendants at a deeper level `T` are the labels whose prior sets lie
in `A_Q` and whose blocks lie in `I_Q`. This file proves, for arbitrary label
families:

* `card_subblocks_mul_le`: the dyadic sub-blocks of `I_Q` at level `T` number
  at most `2^T / 2^T_Q`;
* `sum_desc_le`: descendants with disjoint priors per block carry total
  reference weight `∑ q_T ν(A_i) ≤ q_{T_Q} ν(A_Q)`;
* `ae_desc_cover`: a covered law is covered, inside the parent box, by
  descendants alone, up to the null set of dyadic endpoints;
* `exists_heavy_desc`: a pigeonhole selecting a descendant that carries its
  proportional share of a dense restriction of the parent.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace PreparedModel

theorem interval_nonempty (T : ℕ) (j : Fin (2 ^ T)) :
    ((j : ℝ) / (2 : ℝ) ^ T) ≤ (((j : ℝ) + 1) / (2 : ℝ) ^ T) := by
  have h : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  exact div_le_div_of_nonneg_right (by linarith) h.le

theorem interval_subset_iff {T T' : ℕ} {j : Fin (2 ^ T)} {j' : Fin (2 ^ T')} :
    interval T j ⊆ interval T' j' ↔
      (j' : ℝ) / (2 : ℝ) ^ T' ≤ (j : ℝ) / (2 : ℝ) ^ T ∧
        ((j : ℝ) + 1) / (2 : ℝ) ^ T ≤ ((j' : ℝ) + 1) / (2 : ℝ) ^ T' := by
  unfold interval
  exact Icc_subset_Icc_iff (interval_nonempty T j)

open Classical in
/-- The dyadic sub-blocks of a block. -/
def subblocks (T T' : ℕ) (j' : Fin (2 ^ T')) : Finset (Fin (2 ^ T)) :=
  Finset.univ.filter fun j => interval T j ⊆ interval T' j'

theorem card_subblocks_le (T T' : ℕ) (j' : Fin (2 ^ T')) :
    ((subblocks T T' j').card : ℝ) ≤ (2 : ℝ) ^ T / (2 : ℝ) ^ T' := by
  classical
  set m : ℝ := (2 : ℝ) ^ T / (2 : ℝ) ^ T' with hm
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hT' : (0 : ℝ) < (2 : ℝ) ^ T' := by positivity
  have hm0 : 0 ≤ m := by positivity
  set L : ℝ := (j' : ℝ) * m
  set U : ℝ := ((j' : ℝ) + 1) * m
  have hL0 : 0 ≤ L := by positivity
  -- every sub-block index lies in the integer window `[⌈L⌉, ⌊U⌋)`
  have hmap : ∀ j ∈ subblocks T T' j', ((j : ℕ)) ∈ Finset.Ico ⌈L⌉₊ ⌊U⌋₊ := by
    intro j hj
    simp only [subblocks, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨h1, h2⟩ := interval_subset_iff.mp hj
    have e1 : L ≤ (j : ℝ) := by
      have := (div_le_div_iff₀ hT' hT).mp h1
      simp only [L, hm]
      rw [mul_div_assoc', div_le_iff₀ hT']
      linarith
    have e2 : (j : ℝ) + 1 ≤ U := by
      have := (div_le_div_iff₀ hT hT').mp h2
      simp only [U, hm]
      rw [mul_div_assoc', le_div_iff₀ hT']
      linarith
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.ceil_le.mpr e1
    · have : ((j : ℕ) : ℝ) + 1 ≤ U := e2
      have h3 : ((j : ℕ) + 1 : ℕ) ≤ ⌊U⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega
  have hinj : Set.InjOn (fun j : Fin (2 ^ T) => (j : ℕ)) (subblocks T T' j') := by
    intro a _ b _ hab
    exact Fin.ext hab
  have hcard : (subblocks T T' j').card ≤ (Finset.Ico ⌈L⌉₊ ⌊U⌋₊).card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  rw [Nat.card_Ico] at hcard
  have hU0 : 0 ≤ U := by positivity
  have h5 : (⌊U⌋₊ : ℝ) ≤ U := Nat.floor_le hU0
  have h6 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hUL : U - L = m := by simp only [U, L]; ring
  rcases le_total ⌈L⌉₊ ⌊U⌋₊ with h | h
  · calc ((subblocks T T' j').card : ℝ) ≤ ((⌊U⌋₊ - ⌈L⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (⌊U⌋₊ : ℝ) - (⌈L⌉₊ : ℝ) := by rw [Nat.cast_sub h]
      _ ≤ U - L := by linarith
      _ = m := hUL
  · rw [Nat.sub_eq_zero_of_le h] at hcard
    have : (subblocks T T' j').card = 0 := by omega
    rw [this, Nat.cast_zero]
    exact hm0

theorem card_subblocks_mul_le (T T' : ℕ) (j' : Fin (2 ^ T')) :
    ((subblocks T T' j').card : ℝ) * (2 : ℝ) ^ (-(T : ℤ)) ≤ (2 : ℝ) ^ (-(T' : ℤ)) := by
  have h := card_subblocks_le T T' j'
  have hT : (0 : ℝ) < (2 : ℝ) ^ (-(T : ℤ)) := by positivity
  calc ((subblocks T T' j').card : ℝ) * (2 : ℝ) ^ (-(T : ℤ))
      ≤ (2 : ℝ) ^ T / (2 : ℝ) ^ T' * (2 : ℝ) ^ (-(T : ℤ)) :=
        mul_le_mul_of_nonneg_right h hT.le
    _ = (2 : ℝ) ^ (-(T' : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        field_simp

end PreparedModel

section Families

variable {α : Type*} [MeasurableSpace α]

open PreparedModel

open Classical in
/-- Descendants of a parent `(A_Q, I_Q)` in a label family at level `T`. -/
def descSet {n T : ℕ} (A : Fin n → Set α) (j : Fin n → Fin (2 ^ T))
    (AQ : Set α) (TQ : ℕ) (jQ : Fin (2 ^ TQ)) : Finset (Fin n) :=
  Finset.univ.filter fun i => A i ⊆ AQ ∧ interval T (j i) ⊆ interval TQ jQ

omit [MeasurableSpace α] in
theorem mem_descSet {n T : ℕ} {A : Fin n → Set α} {j : Fin n → Fin (2 ^ T)}
    {AQ : Set α} {TQ : ℕ} {jQ : Fin (2 ^ TQ)} {i : Fin n} :
    i ∈ descSet A j AQ TQ jQ ↔ A i ⊆ AQ ∧ interval T (j i) ⊆ interval TQ jQ := by
  simp [descSet]

/-- Reference weights of descendants are bounded by the parent's. -/
theorem sum_desc_le (ν : Measure α) {n T : ℕ} (A : Fin n → Set α)
    (j : Fin n → Fin (2 ^ T)) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (AQ : Set α) (TQ : ℕ) (jQ : Fin (2 ^ TQ)) :
    ∑ i ∈ descSet A j AQ TQ jQ, ENNReal.ofReal ((2 : ℝ) ^ (-(T : ℤ))) * ν (A i) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(TQ : ℤ))) * ν AQ := by
  classical
  set D := descSet A j AQ TQ jQ
  set q : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-(T : ℤ)))
  -- group the descendants by their block
  have hgroup : ∑ i ∈ D, q * ν (A i) =
      ∑ J ∈ subblocks T TQ jQ, ∑ i ∈ D.filter (fun i => j i = J), q * ν (A i) := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro i hi
    have := (mem_descSet.mp hi).2
    simp [subblocks, this]
  rw [hgroup]
  -- each block carries at most `ν(A_Q)`
  have hblock : ∀ J ∈ subblocks T TQ jQ,
      ∑ i ∈ D.filter (fun i => j i = J), q * ν (A i) ≤ q * ν AQ := by
    intro J _
    rw [← Finset.mul_sum]
    gcongr
    rw [← measure_biUnion_finset]
    · apply measure_mono
      intro x hx
      simp only [mem_iUnion] at hx
      obtain ⟨i, hi, hx⟩ := hx
      exact (mem_descSet.mp (Finset.mem_filter.mp hi).1).1 hx
    · intro i hi i' hi' hne
      have hj : j i = j i' := by
        rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hi').2]
      exact hdisj i i' hne hj
    · intro i _
      exact hA i
  calc ∑ J ∈ subblocks T TQ jQ, ∑ i ∈ D.filter (fun i => j i = J), q * ν (A i)
      ≤ ∑ _J ∈ subblocks T TQ jQ, q * ν AQ := Finset.sum_le_sum hblock
    _ = ((subblocks T TQ jQ).card : ℝ≥0∞) * q * ν AQ := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(TQ : ℤ))) * ν AQ := by
        gcongr
        have h := card_subblocks_mul_le T TQ jQ
        have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(T : ℤ)) := by positivity
        calc ((subblocks T TQ jQ).card : ℝ≥0∞) * q
            = ENNReal.ofReal (((subblocks T TQ jQ).card : ℝ) * (2 : ℝ) ^ (-(T : ℤ))) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(TQ : ℤ))) := ENNReal.ofReal_le_ofReal h

/-- Dyadic endpoints at level `T`. -/
def dyadicPoints (T : ℕ) : Set ℝ := Set.range fun m : ℕ => (m : ℝ) / (2 : ℝ) ^ T

theorem dyadicPoints_countable (T : ℕ) : (dyadicPoints T).Countable :=
  Set.countable_range _

theorem volume_dyadicPoints (T : ℕ) : volume (dyadicPoints T) = 0 :=
  (dyadicPoints_countable T).measure_zero _

/-- Two distinct blocks of the same level meet only at a dyadic endpoint. -/
theorem mem_dyadicPoints_of_mem_inter {T : ℕ} {j j' : Fin (2 ^ T)} (hne : j ≠ j') {t : ℝ}
    (ht : t ∈ interval T j) (ht' : t ∈ interval T j') : t ∈ dyadicPoints T := by
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  simp only [interval, mem_Icc] at ht ht'
  rcases lt_or_gt_of_ne (fun h : (j : ℕ) = (j' : ℕ) => hne (Fin.ext h)) with h | h
  · -- `j + 1 ≤ j'`, so `t = j' / 2^T`
    have h1 : ((j : ℕ) : ℝ) + 1 ≤ ((j' : ℕ) : ℝ) := by exact_mod_cast h
    have e1 : t ≤ (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T := ht.2
    have e2 : ((j' : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ t := ht'.1
    have e3 : (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T ≤ ((j' : ℕ) : ℝ) / (2 : ℝ) ^ T :=
      div_le_div_of_nonneg_right h1 hT.le
    exact ⟨(j' : ℕ), by simp only; linarith⟩
  · have h1 : ((j' : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
    have e1 : t ≤ (((j' : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T := ht'.2
    have e2 : ((j : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ t := ht.1
    have e3 : (((j' : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T ≤ ((j : ℕ) : ℝ) / (2 : ℝ) ^ T :=
      div_le_div_of_nonneg_right h1 hT.le
    exact ⟨(j : ℕ), by simp only; linarith⟩

/-- A law dominated by a prior times Lebesgue measure does not see the dyadic
endpoints. -/
theorem measure_dyadicPoints_eq_zero {ν : Measure α} [SFinite ν] {μ : Measure (α × ℝ)}
    {K : ℝ≥0∞} (hμ : μ ≤ K • ν.prod volume) (T : ℕ) :
    μ (univ ×ˢ dyadicPoints T) = 0 := by
  apply le_antisymm ?_ zero_le
  calc μ (univ ×ˢ dyadicPoints T) ≤ (K • ν.prod volume) (univ ×ˢ dyadicPoints T) := hμ _
    _ = 0 := by
        rw [Measure.smul_apply, Measure.prod_prod, volume_dyadicPoints, mul_zero, smul_zero]

/-- Inside a parent box, a covered law is covered by the descendants alone. -/
theorem ae_desc_cover {ν : Measure α} [SFinite ν] {μ : Measure (α × ℝ)} {K : ℝ≥0∞}
    (hμ : μ ≤ K • ν.prod volume)
    {n T : ℕ} (A B : Fin n → Set α) (j : Fin n → Fin (2 ^ T))
    (hBA : ∀ i, B i ⊆ A i)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ interval T (j i))
    {n' T' : ℕ} (A' : Fin n' → Set α) (j' : Fin n' → Fin (2 ^ T'))
    (hdisj' : ∀ h h', h ≠ h' → j' h = j' h' → Disjoint (A' h) (A' h'))
    (hnest : ∀ i, ∃ h, A i ⊆ A' h ∧ interval T (j i) ⊆ interval T' (j' h))
    (Q : Fin n') :
    ∀ᵐ p ∂μ, p.1 ∈ A' Q → p.2 ∈ interval T' (j' Q) →
      ∃ i ∈ descSet A j (A' Q) T' (j' Q), p.1 ∈ B i ∧ p.2 ∈ interval T (j i) := by
  have hnull : ∀ᵐ p ∂μ, p.2 ∉ dyadicPoints T' := by
    rw [ae_iff]
    simp only [not_not]
    have : {a : α × ℝ | a.2 ∈ dyadicPoints T'} = univ ×ˢ dyadicPoints T' := by
      ext p; simp
    rw [this]
    exact measure_dyadicPoints_eq_zero hμ T'
  filter_upwards [hcover, hnull] with p hp hp2 hpA hpI
  obtain ⟨i, hiB, hiI⟩ := hp
  obtain ⟨h, hAh, hIh⟩ := hnest i
  refine ⟨i, ?_, hiB, hiI⟩
  have hpAi : p.1 ∈ A i := hBA i hiB
  by_cases hhQ : h = Q
  · subst hhQ
    exact mem_descSet.mpr ⟨hAh, hIh⟩
  · exfalso
    by_cases hj : j' h = j' Q
    · exact (Set.disjoint_left.mp (hdisj' h Q hhQ hj)) (hAh hpAi) hpA
    · exact hp2 (mem_dyadicPoints_of_mem_inter hj (hIh hiI) hpI)

/-- Countable subadditivity over the covering descendants. -/
theorem measure_le_sum_desc {ν : Measure α} [SFinite ν] {μ ρ : Measure (α × ℝ)}
    {K : ℝ≥0∞} (hμ : μ ≤ K • ν.prod volume) (hρ : ρ ≤ μ)
    {n T : ℕ} (A B : Fin n → Set α) (j : Fin n → Fin (2 ^ T))
    (hBA : ∀ i, B i ⊆ A i)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ interval T (j i))
    {n' T' : ℕ} (A' : Fin n' → Set α) (j' : Fin n' → Fin (2 ^ T'))
    (hdisj' : ∀ h h', h ≠ h' → j' h = j' h' → Disjoint (A' h) (A' h'))
    (hnest : ∀ i, ∃ h, A i ⊆ A' h ∧ interval T (j i) ⊆ interval T' (j' h))
    (Q : Fin n') (G : Set (α × ℝ)) (hG : G ⊆ A' Q ×ˢ interval T' (j' Q)) :
    ρ G ≤ ∑ i ∈ descSet A j (A' Q) T' (j' Q), ρ (G ∩ (B i ×ˢ interval T (j i))) := by
  have hc := ae_desc_cover hμ A B j hBA hcover A' j' hdisj' hnest Q
  have hc' : ∀ᵐ p ∂ρ, p.1 ∈ A' Q → p.2 ∈ interval T' (j' Q) →
      ∃ i ∈ descSet A j (A' Q) T' (j' Q), p.1 ∈ B i ∧ p.2 ∈ interval T (j i) :=
    ae_mono hρ hc
  calc ρ G ≤ ρ (⋃ i ∈ descSet A j (A' Q) T' (j' Q), G ∩ (B i ×ˢ interval T (j i))) := by
        apply measure_mono_ae
        filter_upwards [hc'] with p hp hpG
        obtain ⟨hpA, hpI⟩ := hG hpG
        obtain ⟨i, hi, hB, hI⟩ := hp hpA hpI
        simp only [mem_iUnion]
        exact ⟨i, hi, hpG, hB, hI⟩
    _ ≤ ∑ i ∈ descSet A j (A' Q) T' (j' Q), ρ (G ∩ (B i ×ˢ interval T (j i))) :=
        measure_biUnion_finset_le _ _

/-- A dense restriction of a parent has a descendant carrying its share. -/
theorem exists_heavy_desc {ν : Measure α} [SFinite ν] {μ ρ : Measure (α × ℝ)}
    {K : ℝ≥0∞} (hμ : μ ≤ K • ν.prod volume) (hρ : ρ ≤ μ)
    {n T : ℕ} (A B : Fin n → Set α) (j : Fin n → Fin (2 ^ T))
    (hA : ∀ i, MeasurableSet (A i)) (hBA : ∀ i, B i ⊆ A i)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ interval T (j i))
    {n' T' : ℕ} (A' : Fin n' → Set α) (j' : Fin n' → Fin (2 ^ T'))
    (hdisj' : ∀ h h', h ≠ h' → j' h = j' h' → Disjoint (A' h) (A' h'))
    (hnest : ∀ i, ∃ h, A i ⊆ A' h ∧ interval T (j i) ⊆ interval T' (j' h))
    (Q : Fin n') (G : Set (α × ℝ)) (hG : G ⊆ A' Q ×ˢ interval T' (j' Q))
    (c : ℝ≥0∞)
    (hmass : c * (ENNReal.ofReal ((2 : ℝ) ^ (-(T' : ℤ))) * ν (A' Q)) < ρ G) :
    ∃ i ∈ descSet A j (A' Q) T' (j' Q),
      c * (ENNReal.ofReal ((2 : ℝ) ^ (-(T : ℤ))) * ν (A i)) <
        ρ (G ∩ (B i ×ˢ interval T (j i))) := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have h1 := measure_le_sum_desc hμ hρ A B j hBA hcover A' j' hdisj' hnest Q G hG
  have h2 : ∑ i ∈ descSet A j (A' Q) T' (j' Q), ρ (G ∩ (B i ×ˢ interval T (j i))) ≤
      ∑ i ∈ descSet A j (A' Q) T' (j' Q),
        c * (ENNReal.ofReal ((2 : ℝ) ^ (-(T : ℤ))) * ν (A i)) :=
    Finset.sum_le_sum hcon
  have h3 := sum_desc_le ν A j hA hdisj (A' Q) T' (j' Q)
  rw [← Finset.mul_sum] at h2
  have h4 : c * ∑ i ∈ descSet A j (A' Q) T' (j' Q),
      ENNReal.ofReal ((2 : ℝ) ^ (-(T : ℤ))) * ν (A i) ≤
      c * (ENNReal.ofReal ((2 : ℝ) ^ (-(T' : ℤ))) * ν (A' Q)) := by
    gcongr
  exact absurd (h1.trans (h2.trans h4)) (not_le.mpr hmass)

end Families

end

end Submission.Obl.k4_row_parent_contact_candidates
