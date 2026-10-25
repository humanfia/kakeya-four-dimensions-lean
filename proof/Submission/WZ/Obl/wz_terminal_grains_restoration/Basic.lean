-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_terminal_grains_restoration.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Generic tools for o149: pigeonholing over classes, multiplicities, reindexing
-/

namespace WangZahlLot.Obl.wz_terminal_grains_restoration

open MeasureTheory Finset

noncomputable section

/-! ### Pigeonholing over finitely many classes -/

/-- If every index carries a class `≤ Λ`, one class carries a `1/(Λ+1)` share of the weight. -/
theorem pigeon {ι : Type*} (s : Finset ι) (cls : ι → ℕ) (Λ : ℕ) (hcls : ∀ i ∈ s, cls i ≤ Λ)
    (wt : ι → ENNReal) :
    ∃ ℓ ≤ Λ, ∑ i ∈ s, wt i ≤ ((Λ + 1 : ℕ) : ENNReal) * ∑ i ∈ s.filter (fun i => cls i = ℓ), wt i := by
  classical
  have hmaps : ∀ i ∈ s, cls i ∈ range (Λ + 1) := fun i hi =>
    mem_range.2 (Nat.lt_succ_of_le (hcls i hi))
  obtain ⟨ℓ, hℓ, hmax⟩ := (range (Λ + 1)).exists_max_image
    (fun ℓ => ∑ i ∈ s.filter (fun i => cls i = ℓ), wt i) ⟨0, by simp⟩
  refine ⟨ℓ, Nat.lt_succ_iff.1 (mem_range.1 hℓ), ?_⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ j ∈ range (Λ + 1), ∑ i ∈ s with cls i = j, wt i
      ≤ (range (Λ + 1)).card • ∑ i ∈ s.filter (fun i => cls i = ℓ), wt i :=
        sum_le_card_nsmul _ _ _ hmax
    _ = ((Λ + 1 : ℕ) : ENNReal) * ∑ i ∈ s.filter (fun i => cls i = ℓ), wt i := by
        rw [card_range, nsmul_eq_mul]

/-! ### Multiplicities of finite families of sets -/

open Classical in
/-- The number of sets of the family `W` over `t` that contain `p`. -/
def mult {ι α : Type*} (t : Finset ι) (W : ι → Set α) (p : α) : ℕ :=
  (t.filter (fun i => p ∈ W i)).card

theorem measurable_mult {ι α : Type*} [MeasurableSpace α] (t : Finset ι) (W : ι → Set α)
    (hW : ∀ i ∈ t, MeasurableSet (W i)) : Measurable (mult t W) := by
  classical
  have : mult t W = fun p => ∑ i ∈ t, if p ∈ W i then 1 else 0 := by
    funext p; unfold mult; rw [card_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun i hi => ?_)
  exact Measurable.ite (hW i hi) measurable_const measurable_const

theorem mult_pos_of_mem {ι α : Type*} {t : Finset ι} {W : ι → Set α} {p : α} {i : ι}
    (hi : i ∈ t) (hp : p ∈ W i) : 0 < mult t W p := by
  classical
  unfold mult
  exact card_pos.2 ⟨i, mem_filter.2 ⟨hi, hp⟩⟩

theorem mult_le_card {ι α : Type*} (t : Finset ι) (W : ι → Set α) (p : α) :
    mult t W p ≤ t.card := by
  classical
  unfold mult
  exact card_filter_le _ _

theorem sum_measure_eq_lintegral_mult {ι α : Type*} [MeasurableSpace α] (μ : Measure α)
    (t : Finset ι) (W : ι → Set α) (hW : ∀ i ∈ t, MeasurableSet (W i)) :
    ∑ i ∈ t, μ (W i) = ∫⁻ p, (mult t W p : ENNReal) ∂μ := by
  classical
  have h1 : ∀ i ∈ t, μ (W i) = ∫⁻ p, (W i).indicator 1 p ∂μ := fun i hi =>
    (lintegral_indicator_one (hW i hi)).symm
  rw [sum_congr rfl h1, ← lintegral_finsetSum]
  · congr 1
    funext p
    simp only [Set.indicator_apply, Pi.one_apply, mult]
    rw [sum_boole]
  · intro i hi
    exact measurable_one.indicator (hW i hi)

theorem sum_measure_le_of_mult_le {ι α : Type*} [MeasurableSpace α] (μ : Measure α)
    (t : Finset ι) (W : ι → Set α) (hW : ∀ i ∈ t, MeasurableSet (W i)) (M : ℝ)
    (hM : ∀ p ∈ ⋃ i ∈ t, W i, (mult t W p : ℝ) ≤ M) :
    ∑ i ∈ t, μ (W i) ≤ ENNReal.ofReal M * μ (⋃ i ∈ t, W i) := by
  classical
  rw [sum_measure_eq_lintegral_mult μ t W hW,
    ← lintegral_indicator_const (Finset.measurableSet_biUnion t hW)]
  refine lintegral_mono (fun p => ?_)
  by_cases hp : p ∈ ⋃ i ∈ t, W i
  · rw [Set.indicator_of_mem hp]
    have := hM p hp
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal this
  · rw [Set.indicator_of_notMem hp]
    have : mult t W p = 0 := by
      unfold mult
      rw [card_eq_zero, filter_eq_empty_iff]
      intro i hi hpi
      exact hp (Set.mem_biUnion hi hpi)
    simp [this]

theorem le_sum_measure_of_le_mult {ι α : Type*} [MeasurableSpace α] (μ : Measure α)
    (t : Finset ι) (W : ι → Set α) (hW : ∀ i ∈ t, MeasurableSet (W i)) (m : ℝ)
    (hm : ∀ p ∈ ⋃ i ∈ t, W i, m ≤ (mult t W p : ℝ)) :
    ENNReal.ofReal m * μ (⋃ i ∈ t, W i) ≤ ∑ i ∈ t, μ (W i) := by
  classical
  rw [sum_measure_eq_lintegral_mult μ t W hW,
    ← lintegral_indicator_const (Finset.measurableSet_biUnion t hW)]
  refine lintegral_mono (fun p => ?_)
  by_cases hp : p ∈ ⋃ i ∈ t, W i
  · rw [Set.indicator_of_mem hp]
    have := hm p hp
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal this
  · rw [Set.indicator_of_notMem hp]
    exact bot_le

/-- Splitting a measurable set along a measurable class function with values `≤ Λ`. -/
theorem measure_eq_sum_classes {α : Type*} [MeasurableSpace α] (μ : Measure α) {A : Set α}
    (hA : MeasurableSet A) (cls : α → ℕ) (hcls : Measurable cls) (Λ : ℕ)
    (hΛ : ∀ p ∈ A, cls p ≤ Λ) :
    μ A = ∑ ℓ ∈ range (Λ + 1), μ (A ∩ cls ⁻¹' {ℓ}) := by
  classical
  have hU : A = ⋃ ℓ ∈ range (Λ + 1), A ∩ cls ⁻¹' {ℓ} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      mem_range, exists_prop]
    constructor
    · intro hp
      exact ⟨cls p, Nat.lt_succ_of_le (hΛ p hp), hp, rfl⟩
    · rintro ⟨_, _, hp, _⟩
      exact hp
  conv_lhs => rw [hU]
  refine measure_biUnion_finset ?_ ?_
  · intro ℓ _ ℓ' _ hne
    refine Set.disjoint_left.2 ?_
    intro p hp hp'
    exact hne (hp.2.symm.trans hp'.2)
  · intro ℓ _
    exact hA.inter (hcls (measurableSet_singleton ℓ))

/-! ### Reindexing a finite set by `Fin` -/

/-- The `k`-th element of a finset. -/
def emb {α : Type*} (R : Finset α) (k : Fin R.card) : α := (R.equivFin.symm k : α)

theorem emb_mem {α : Type*} (R : Finset α) (k : Fin R.card) : emb R k ∈ R :=
  (R.equivFin.symm k).2

theorem emb_injective {α : Type*} (R : Finset α) : Function.Injective (emb R) := by
  intro k k' h
  have : R.equivFin.symm k = R.equivFin.symm k' := Subtype.ext h
  exact R.equivFin.symm.injective this

/-- The index of an element of a finset (a default value outside). -/
def back {α : Type*} (R : Finset α) (k0 : Fin R.card) (k : α) : Fin R.card := by
  classical
  exact if hk : k ∈ R then R.equivFin ⟨k, hk⟩ else k0

theorem emb_back {α : Type*} (R : Finset α) (k0 : Fin R.card) {k : α} (hk : k ∈ R) :
    emb R (back R k0 k) = k := by
  classical
  simp [emb, back, hk]

theorem back_emb {α : Type*} (R : Finset α) (k0 : Fin R.card) (k : Fin R.card) :
    back R k0 (emb R k) = k := by
  classical
  have hk : emb R k ∈ R := emb_mem R k
  simp only [back, hk, dite_true]
  have : (⟨emb R k, hk⟩ : R) = R.equivFin.symm k := rfl
  rw [this, Equiv.apply_symm_apply]

theorem back_eq_iff {α : Type*} (R : Finset α) (k0 : Fin R.card) {k : α} (hk : k ∈ R)
    (k' : Fin R.card) : back R k0 k = k' ↔ k = emb R k' := by
  constructor
  · rintro rfl
    exact (emb_back R k0 hk).symm
  · rintro rfl
    exact back_emb R k0 k'

theorem sum_emb {α M : Type*} [AddCommMonoid M] (R : Finset α) (F : α → M) :
    ∑ k : Fin R.card, F (emb R k) = ∑ k ∈ R, F k := by
  rw [← Finset.sum_coe_sort R F]
  exact Equiv.sum_comp R.equivFin.symm (fun x : R => F x)

theorem ncard_preimage_le {α β : Type*} [Finite β] {e : α → β} (he : Function.Injective e)
    (P : β → Prop) : ({a | P (e a)} : Set α).ncard ≤ ({b | P b} : Set β).ncard := by
  have : ({a | P (e a)} : Set α).ncard = (e '' {a | P (e a)}).ncard :=
    (Set.ncard_image_of_injective _ he).symm
  rw [this]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨a, ha, rfl⟩
  exact ha

end

end WangZahlLot.Obl.wz_terminal_grains_restoration
