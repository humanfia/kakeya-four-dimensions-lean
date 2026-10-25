/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ParameterRefinement.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Lib.K4ReferencePruning
import Submission.Lib.K4CommonLocalChoice
import Submission.Obl.k4_scalar_grid_density_extension.GridRelation
import Submission.Obl.k4_two_velocity_row_list_completion.MeasureTable
import Submission.Obl.k4_crop_angular_finite_tail.Transfer

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice Submission.Lib.K4ReferencePruning
open Submission.Obl.k4_scalar_grid_density_extension

noncomputable section

/-- Delete the null atoms of a countable family of records once, before
turning measure-supported lists and coefficient floors into pointwise data. -/
def positiveRecordCore {X I Q : Type*} [MeasurableSpace X]
    (μ : Measure X) (record : I → X → Q) : Set X :=
  {x | ∀ i, μ (record i ⁻¹' {record i x}) ≠ 0}

theorem ae_mem_positiveRecordCore {X I Q : Type*} [MeasurableSpace X]
    [Countable I] [Countable Q] (μ : Measure X) (record : I → X → Q) :
    ∀ᵐ x ∂μ, x ∈ positiveRecordCore μ record := by
  apply ae_all_iff.mpr
  intro i
  exact Submission.Obl.k4_two_velocity_row_list_completion.ae_record_mass_ne_zero μ (record i)

theorem measurableSet_positiveRecordCore {X I Q : Type*} [MeasurableSpace X]
    [Countable I] [Countable Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure X) (record : I → X → Q) (hrecord : ∀ i, Measurable (record i)) :
    MeasurableSet (positiveRecordCore μ record) := by
  have hmeas (i : I) : Measurable (fun x => μ (record i ⁻¹' {record i x})) :=
    (measurable_of_countable (fun q => μ (record i ⁻¹' {q}))).comp (hrecord i)
  have heq : positiveRecordCore μ record = ⋂ i, {x | μ (record i ⁻¹' {record i x}) ≠ 0} := by
    ext x
    simp only [positiveRecordCore, mem_iInter, mem_ofPred_eq]
  rw [heq]
  exact MeasurableSet.iInter (fun i => (measurableSet_eq_fun (hmeas i) measurable_const).compl)

/-- The coarse coefficient boxes compatible with one fine box. The actual
power grids need not be nested. -/
def coarseGridList {n : ℕ} (w w' : ℝ) (b : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j => {⌊(b j : ℝ) * w' / w⌋, ⌊(b j : ℝ) * w' / w⌋ + 1}

theorem card_coarseGridList {n : ℕ} (w w' : ℝ) (b : Fin n → ℤ) :
    (coarseGridList w w' b).card = 2 ^ n := by
  simp [coarseGridList, Fintype.card_piFinset]

theorem cell_mem_coarseGridList {n : ℕ} {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w)
    (c : Fin n → ℝ) : cell w c ∈ coarseGridList w w' (cell w' c) := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact floorCompatible_coarse_mem hw' hww' _ _ ⟨c j, rfl, rfl⟩

/-- Repeating an old reference weight only on a bounded finite list gives
a summable budget, independently of the size of the ambient label type. -/
theorem listed_reference_sum_le {A B : Type*} [DecidableEq A]
    (L : B → Finset A) (w : B → ENNReal) (D : ENNReal)
    (hD : ∀ b, ((L b).card : ENNReal) ≤ D) :
    (∑' ab : A × B, if ab.1 ∈ L ab.2 then w ab.2 else 0) ≤ D * ∑' b, w b := by
  calc
    _ = ∑' b, (L b).card * w b := by
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
      apply tsum_congr
      intro b
      rw [tsum_eq_sum (s := L b) (fun a ha => by simp [ha])]
      simp
    _ ≤ ∑' b, D * w b := ENNReal.tsum_le_tsum (fun b =>
      mul_le_mul_of_nonneg_right (hD b) zero_le)
    _ = _ := ENNReal.tsum_mul_left

/-- Intersections of two parameter partitions inherit a useful original
prior floor after a bounded loss. Only the number of coarse pieces meeting
one fine piece enters the bound, not the number of parameter pieces. -/
theorem parameter_intersection_light_mass_le {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace B] [MeasurableSingletonClass B]
    [Countable A] [Countable B] [DecidableEq A]
    (θ : Measure X) (coarse : X → A) (fine : X → B) (hfine : Measurable fine)
    (L : B → Finset A) (hL : ∀ x, coarse x ∈ L (fine x))
    (D : ℕ) (hD : ∀ b, (L b).card ≤ D) (δ : ENNReal) :
    θ {x | θ {y | coarse y = coarse x ∧ fine y = fine x} <
      δ * θ (fine ⁻¹' {fine x})} ≤ δ * D * θ univ := by
  classical
  let state : X → A × B := fun x => (coarse x, fine x)
  let weight : A × B → ENNReal := fun ab =>
    if ab.1 ∈ L ab.2 then θ (fine ⁻¹' {ab.2}) else 0
  have hsum : ∑' b, θ (fine ⁻¹' {b}) = θ univ := by
    simpa only [univ_inter] using
      (Submission.Obl.k4_crop_angular_finite_tail.measure_eq_tsum_label θ hfine MeasurableSet.univ).symm
  have hweights : ∑' ab, weight ab ≤ (D : ENNReal) * θ univ := by
    have h := listed_reference_sum_le L (fun b => θ (fine ⁻¹' {b})) (D : ENNReal)
      (fun b => by exact_mod_cast hD b)
    simpa only [weight, hsum] using h
  have hset : {x | θ {y | coarse y = coarse x ∧ fine y = fine x} <
      δ * θ (fine ⁻¹' {fine x})} = (referenceKeep θ state weight δ)ᶜ := by
    ext x
    simp only [referenceKeep, mem_compl_iff, mem_ofPred_eq, not_le, state, weight,
      ite_eq_left (hL x), Set.preimage, mem_singleton_iff, Prod.mk.injEq]
  rw [hset]
  exact (reference_light_mass_le θ state weight δ).trans
    ((mul_le_mul_right hweights δ).trans_eq (by ring))

/-- For five displayed coefficients the preceding cost is exactly at most
`32 δ` times the original prior mass. -/
theorem coefficient_intersection_light_mass_le {X : Type*} [MeasurableSpace X]
    (θ : Measure X) (c : X → Fin 5 → ℝ) (hc : Measurable c)
    {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w) (δ : ENNReal) :
    θ {x | θ {y | cell w (c y) = cell w (c x) ∧ cell w' (c y) = cell w' (c x)} <
      δ * θ {y | cell w' (c y) = cell w' (c x)}} ≤ δ * 32 * θ univ := by
  simpa only [show 2 ^ 5 = (32 : ℕ) by norm_num, Nat.cast_ofNat,
    Set.preimage, mem_singleton_iff] using
    parameter_intersection_light_mass_le θ (fun x => cell w (c x))
      (fun x => cell w' (c x)) (measurable_cell w' hc) (coarseGridList w w')
      (fun x => cell_mem_coarseGridList hw' hww' (c x)) (2 ^ 5)
      (fun b => (card_coarseGridList w w' b).le) δ

end

end Submission.Obl.k4_scalar_graph_residual_discovery
