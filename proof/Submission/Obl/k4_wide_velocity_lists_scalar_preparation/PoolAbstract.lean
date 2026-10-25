import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.PaletteCount
import Submission.Obl.k4_critical_conditional_row_preparation.Pruning

/-!
# Pooling velocity-wise lists by history pruning

A finite disjoint family of earlier (deeper) labels covers the law; each label
meets only listed output states and carries a summable reference weight that
dominates its velocity bins by the palette. Light (label, output state) pairs
are deleted against these weights (accepted o236 `prune_and_forget`), which
gives conditional palette domination for the output states alone; the
velocity-wise lists are then integrated against the palette.
-/

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance {ι : Type*} : MeasurableSpace (Option ι) := ⊤
local instance {ι : Type*} : DiscreteMeasurableSpace (Option ι) := ⟨fun _ => trivial⟩

open Submission.Obl.k4_critical_conditional_row_preparation in
/-- Abstract pooling: one unconditional terminal list of at most `δ⁻¹ * M`
output states carries a submeasure losing at most `δ` times the total
reference weight of the listed (label, state) pairs. -/
theorem pooled_terminal {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    [MeasurableSingletonClass O] [Countable O]
    (law : Measure Ω) [IsFiniteMeasure law]
    (out : Ω → O) (hout : Measurable out) (vel : Ω → ℤ) (hvel : Measurable vel)
    (π : Measure ℤ) (hπ : π univ ≤ 1)
    {n : ℕ} (R : Fin n → Set Ω) (hR : ∀ i, MeasurableSet (R i))
    (hdisj : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hcover : ∀ᵐ p ∂law, ∃ i, p ∈ R i)
    (options : Fin n → Finset O) (hopt : ∀ i, ∀ᵐ p ∂law, p ∈ R i → out p ∈ options i)
    (W : Fin n → ℝ≥0∞) (hW : ∀ i a, law (R i ∩ vel ⁻¹' {a}) ≤ W i * π {a})
    (L : ℤ → Finset O) (M : ℝ≥0∞) (hM : M ≠ ⊤) (hL : ∀ a, ((L a).card : ℝ≥0∞) ≤ M)
    (hmem : ∀ᵐ p ∂law, out p ∈ L (vel p))
    (δ : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδt : δ ≠ ⊤) :
    ∃ τ : Measure Ω, τ ≤ law ∧
      law univ ≤ τ univ + δ * ∑ i, ((options i).card : ℝ≥0∞) * W i ∧
      ∃ terminal : Finset O, (terminal.card : ℝ≥0∞) ≤ δ⁻¹ * M ∧
        ∀ᵐ p ∂τ, out p ∈ terminal := by
  classical
  let state : Ω → Option (Fin n) × O := fun p => (coverLabel R p, out p)
  have hstate : Measurable state := (measurable_coverLabel R hR hdisj).prodMk hout
  have hcap : ∀ q v, law {p | state p = q ∧ vel p = v} ≤
      1 * historyReference options W q * π {v} := by
    rintro ⟨i, o⟩ v
    cases i with
    | none =>
      have hsub : {p | state p = (none, o) ∧ vel p = v} ⊆ {p | ¬ ∃ i, p ∈ R i} := by
        rintro p ⟨hp, -⟩
        exact (coverLabel_eq_none R p).mp (congrArg Prod.fst hp)
      calc _ ≤ law {p | ¬ ∃ i, p ∈ R i} := measure_mono hsub
        _ = 0 := ae_iff.mp hcover
        _ ≤ _ := zero_le
    | some i =>
      by_cases ho : o ∈ options i
      · have hsub : {p | state p = (some i, o) ∧ vel p = v} ⊆ R i ∩ vel ⁻¹' {v} := by
          rintro p ⟨hp, hv⟩
          exact ⟨(coverLabel_eq_some R hdisj p i).mp (congrArg Prod.fst hp), hv⟩
        simp only [historyReference, Option.elim_some, ho, ite_true, one_mul]
        exact (measure_mono hsub).trans (hW i v)
      · have hsub : {p | state p = (some i, o) ∧ vel p = v} ⊆
            {p | ¬ (p ∈ R i → out p ∈ options i)} := by
          rintro p ⟨hp, -⟩ himp
          have hRi := (coverLabel_eq_some R hdisj p i).mp (congrArg Prod.fst hp)
          have hmemo := himp hRi
          rw [show out p = o from congrArg Prod.snd hp] at hmemo
          exact ho hmemo
        calc _ ≤ _ := measure_mono hsub
          _ = 0 := ae_iff.mp (hopt i)
          _ ≤ _ := zero_le
  obtain ⟨τ, hτ, hmass, hdom⟩ := prune_and_forget law state hstate vel hvel π
    (historyReference options W) 1 δ hδ0 hδt Prod.snd measurable_snd hcap
  rw [tsum_historyReference] at hmass
  have : IsFiniteMeasure τ := isFiniteMeasure_of_le law hτ
  have hπsum : ∑' a, π {a} ≤ 1 := by
    rw [← measure_iUnion (fun a b hab => Set.disjoint_singleton.mpr hab)
      (fun a => measurableSet_singleton a)]
    calc π (⋃ a, {a}) ≤ π univ := measure_mono (subset_univ _)
      _ ≤ 1 := hπ
  have hdom' : ∀ o a, τ {p | out p = o ∧ vel p = a} ≤ δ⁻¹ * π {a} * τ {p | out p = o} := by
    intro o a
    have h := hdom o a
    rw [one_div] at h
    exact h
  obtain ⟨terminal, hcard, hae⟩ := exists_terminal_of_palette τ out vel (fun a => π {a})
    hπsum L M hL (ae_mono hτ hmem) δ⁻¹
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hδ0) hM) hdom'
  exact ⟨τ, hτ, hmass, terminal, hcard, hae⟩

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
