/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file RecordPruning.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.StrongPruning

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

/-- Summable old-reference thresholds restore current floors for finitely
many record systems at once. Only values met by the original finite
record images are used by pruning; the budget remains the countable
reference sum and the conclusion holds for every record value. -/
theorem simultaneous_record_current_floors {X σ Q : Type*}
    [MeasurableSpace X] [Fintype σ] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure X) (record : σ → X → Q) (hrecord : ∀ s, Measurable (record s))
    (E : Set X) (hE : MeasurableSet E)
    (L : σ → Finset Q) (hL : ∀ s, ∀ x ∈ E, record s x ∈ L s)
    (τ : σ → Q → ℝ≥0∞) :
    ∃ R : Set X, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ ∑ s, ∑' q, τ s q ∧
      ∀ s q, R ∩ record s ⁻¹' {q} = ∅ ∨ τ s q < μ (R ∩ record s ⁻¹' {q}) := by
  classical
  let I := Σ s, L s
  let C (i : I) : Set X := record i.1 ⁻¹' {i.2.1}
  let b (i : I) : ℝ≥0∞ := τ i.1 i.2.1
  have hC (i : I) : MeasurableSet (C i) := hrecord i.1 (measurableSet_singleton _)
  obtain ⟨R, hR, hRE, hmass, hfloor⟩ :=
    exists_measurable_current_floor_pruning μ C b hC hE
  have hbudget : (∑ i : I, b i) ≤ ∑ s, ∑' q, τ s q := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro s _
    dsimp only [b]
    rw [Finset.sum_coe_sort]
    exact ENNReal.sum_le_tsum (L s)
  refine ⟨R, hR, hRE, hmass.trans hbudget, ?_⟩
  intro s q
  by_cases hq : q ∈ L s
  · exact hfloor ⟨s, ⟨q, hq⟩⟩
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have heq : record s x = q := hx.2
    exact hq (heq ▸ hL s x (hRE hx.1))

/-- A convenient old-reference form: each record system has total
reference weight at most `B s`, and its floor costs `eta s * B s`.
The returned strict floors concern the SAME final event. -/
theorem simultaneous_old_reference_floors {X σ Q : Type*}
    [MeasurableSpace X] [Fintype σ] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure X) (record : σ → X → Q) (hrecord : ∀ s, Measurable (record s))
    (E : Set X) (hE : MeasurableSet E) (hfinite : ∀ s, (record s '' E).Finite)
    (old : σ → Q → ℝ≥0∞) (η B : σ → ℝ≥0∞)
    (hbudget : ∀ s, (∑' q, old s q) ≤ B s) :
    ∃ R : Set X, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ ∑ s, η s * B s ∧
      ∀ s q, R ∩ record s ⁻¹' {q} = ∅ ∨
        η s * old s q < μ (R ∩ record s ⁻¹' {q}) := by
  classical
  let L (s : σ) := (hfinite s).toFinset
  have hL (s : σ) (x : X) (hx : x ∈ E) : record s x ∈ L s :=
    (hfinite s).mem_toFinset.mpr ⟨x, hx, rfl⟩
  obtain ⟨R, hR, hRE, hmass, hfloor⟩ := simultaneous_record_current_floors μ record hrecord
    E hE L hL (fun s q => η s * old s q)
  refine ⟨R, hR, hRE, hmass.trans ?_, hfloor⟩
  apply Finset.sum_le_sum
  intro s _
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hbudget s) zero_le

end

end Submission.Obl.k4_scalar_graph_residual_discovery
