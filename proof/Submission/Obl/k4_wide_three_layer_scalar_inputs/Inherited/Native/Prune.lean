/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Native/Prune.lean.
Namespace renamed for o274; unused model imports removed. Earlier provenance retained below. -/
import Mathlib
import Submission.Lib.K4MovingMeshBoxes.Geometry

set_option autoImplicit false

/-!
# Light entries and reference budgets

An *entry* is a measurable set of incidences with a reference weight `T`; it is *heavy* when its
mass is positive and at least `T / K₁`.  The light entries of a finite family carry at most
`Σ T / K₁` over the entries of positive mass (`light_union_le`).

Reference budgets of slot-key entries: the keys met by one true block carry total reference
`≲ K³ q ν(A)` (`block_key_budget`), and a projected piece meets keys of total reference
`≲ N^ε χ D a^d π` over all slots (`piece_key_budget`).
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- An entry is heavy for the reference `T` and cutoff `K₁`. -/
def Heavy (ρ : Measure (α × ℝ)) (S : Set (α × ℝ)) (T K₁ : ℝ) : Prop :=
  ENNReal.ofReal (T / K₁) ≤ ρ S ∧ 0 < ρ S

open scoped Classical in
/-- The union of the light entries of a finite family. -/
def lightUnion {ι : Type*} (ρ : Measure (α × ℝ)) (E : Finset ι) (S : ι → Set (α × ℝ))
    (T : ι → ℝ) (K₁ : ℝ) : Set (α × ℝ) :=
  ⋃ e ∈ E.filter (fun e => ¬ Heavy ρ (S e) (T e) K₁), S e

theorem measurableSet_lightUnion {ι : Type*} (ρ : Measure (α × ℝ)) (E : Finset ι)
    (S : ι → Set (α × ℝ)) (T : ι → ℝ) (K₁ : ℝ) (hS : ∀ e, MeasurableSet (S e)) :
    MeasurableSet (lightUnion ρ E S T K₁) := by
  classical
  unfold lightUnion
  exact Finset.measurableSet_biUnion _ (fun e _ => hS e)

theorem light_union_le {ι : Type*} (ρ : Measure (α × ℝ)) (E : Finset ι)
    (S : ι → Set (α × ℝ)) (T : ι → ℝ) (K₁ : ℝ) :
    ρ (lightUnion ρ E S T K₁) ≤
      ∑ e ∈ E.filter (fun e => 0 < ρ (S e)), ENNReal.ofReal (T e / K₁) := by
  classical
  unfold lightUnion
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ e ∈ E.filter (fun e => ¬ Heavy ρ (S e) (T e) K₁), ρ (S e)
      ≤ ∑ e ∈ E.filter (fun e => ¬ Heavy ρ (S e) (T e) K₁),
          (if 0 < ρ (S e) then ENNReal.ofReal (T e / K₁) else 0) := by
        apply Finset.sum_le_sum
        intro e he
        have hl := (Finset.mem_filter.mp he).2
        unfold Heavy at hl
        by_cases hpos : 0 < ρ (S e)
        · rw [if_pos hpos]
          rcases le_or_gt (ENNReal.ofReal (T e / K₁)) (ρ (S e)) with h | h
          · exact absurd ⟨h, hpos⟩ hl
          · exact h.le
        · rw [if_neg hpos]
          exact le_of_not_gt hpos
    _ ≤ ∑ e ∈ E, (if 0 < ρ (S e) then ENNReal.ofReal (T e / K₁) else 0) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = _ := by rw [Finset.sum_filter]

/-- Velocity bins carry total palette weight at most one. -/
theorem sum_bins_le_one {π : Measure ℝ} [IsProbabilityMeasure π] {χ : ℝ} (hχ : 0 < χ)
    (V : Finset ℤ) :
    ∑ v ∈ V, π (Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ)) ≤ 1 := by
  rw [← measure_biUnion_finset]
  · exact prob_le_one
  · intro v _ v' _ hvv'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hvv'
    have h1 : ⌊x / χ⌋ = v := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hχ]; exact hx.1
      · rw [div_lt_iff₀ hχ]; exact hx.2
    have h2 : ⌊x / χ⌋ = v' := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hχ]; exact hx'.1
      · rw [div_lt_iff₀ hχ]; exact hx'.2
    rw [← h1, ← h2]
  · intro v _
    exact measurableSet_Ico

/-- Keys of the form `![κ₀, κ₁, κ₂]` with `κ₀ ∈ V`, `κ₁ ∈ F₁ κ₀`, `κ₂ ∈ F₂ κ₀ κ₁`. -/
def keyBox (V : Finset ℤ) (F₁ : ℤ → Finset ℤ) (F₂ : ℤ → ℤ → Finset ℤ) : Finset (Fin 3 → ℤ) :=
  (V.sigma fun v => (F₁ v).sigma fun z => F₂ v z).image fun x => ![x.1, x.2.1, x.2.2]

theorem mem_keyBox {V : Finset ℤ} {F₁ : ℤ → Finset ℤ} {F₂ : ℤ → ℤ → Finset ℤ}
    {κ : Fin 3 → ℤ} (h0 : κ 0 ∈ V) (h1 : κ 1 ∈ F₁ (κ 0)) (h2 : κ 2 ∈ F₂ (κ 0) (κ 1)) :
    κ ∈ keyBox V F₁ F₂ := by
  unfold keyBox
  refine Finset.mem_image.mpr ⟨⟨κ 0, κ 1, κ 2⟩, ?_, ?_⟩
  · simp only [Finset.mem_sigma]
    exact ⟨h0, h1, h2⟩
  · funext e
    fin_cases e <;> rfl

/-- The weighted sum over a key box. -/
theorem keyBox_sum_le (V : Finset ℤ) (F₁ : ℤ → Finset ℤ) (F₂ : ℤ → ℤ → Finset ℤ)
    (w : ℤ → ℝ) (hw : ∀ v, 0 ≤ w v) {c₁ c₂ : ℝ}
    (hc₁ : ∀ v, ((F₁ v).card : ℝ) ≤ c₁) (hc₂ : ∀ v z, ((F₂ v z).card : ℝ) ≤ c₂) (hc₂0 : 0 ≤ c₂) :
    ∑ κ ∈ keyBox V F₁ F₂, w (κ 0) ≤ (∑ v ∈ V, w v) * c₁ * c₂ := by
  classical
  unfold keyBox
  refine (Finset.sum_image_le_of_nonneg (fun _ _ => hw _)).trans ?_
  rw [Finset.sum_sigma]
  simp only [Matrix.cons_val_zero]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro v _
  rw [Finset.sum_sigma]
  calc ∑ z ∈ F₁ v, ∑ _y ∈ F₂ v z, w v = ∑ z ∈ F₁ v, ((F₂ v z).card : ℝ) * w v := by
        apply Finset.sum_congr rfl; intro z _; rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _z ∈ F₁ v, c₂ * w v := by
        apply Finset.sum_le_sum; intro z _
        exact mul_le_mul_of_nonneg_right (hc₂ v z) (hw v)
    _ = ((F₁ v).card : ℝ) * (c₂ * w v) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ c₁ * (c₂ * w v) := mul_le_mul_of_nonneg_right (hc₁ v) (mul_nonneg hc₂0 (hw v))
    _ = w v * c₁ * c₂ := by ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
