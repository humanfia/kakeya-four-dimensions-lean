import Submission.Obl.k4_horizontal_coefficient_count.Families
import Submission.Obl.k4_horizontal_coefficient_count.Selection

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Approximate finite covers at finitely many depths can be made into
simultaneous current-law floors. Only the uncovered mass and the sum of
the original palette-weighted thresholds are charged. -/
theorem predictor_families_common_floors {α : Type*} [MeasurableSpace α]
    {m : ℕ} (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ)
    (χ : ℝ) (D a : Fin m → ℝ) (C M : ℝ)
    (π : Measure ℝ) (d Z : ℝ)
    (f : (r : Fin m) → PredictorFamily b χ (D r) (a r) C M)
    (htime : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) :
    ∃ ρ : Measure (α × ℝ), ρ ≤ μ ∧
      μ univ ≤ ρ univ +
        (∑ r, μ {p | ∃ i, p.1 ∈ (f r).A i}ᶜ) +
        ∑ r, ∑ i, (f r).weight π d Z i ∧
      ∃ g : (r : Fin m) → PredictorFamily b χ (D r) (a r) C M,
        ∀ r, (g r).Covers ρ ∧ (g r).Floors π d Z ρ := by
  classical
  let U (r : Fin m) : Set (α × ℝ) := {p | ∃ i, p.1 ∈ (f r).A i}
  have hU (r : Fin m) : MeasurableSet (U r) := by
    have heq : U r = ⋃ i, Prod.fst ⁻¹' (f r).A i := by ext p; simp [U]
    rw [heq]
    exact MeasurableSet.iUnion (fun i => (f r).measurable i |>.preimage measurable_fst)
  let E : Set (α × ℝ) := ⋂ r, U r
  have hE : MeasurableSet E := MeasurableSet.iInter hU
  let μ₀ : Measure (α × ℝ) := μ.restrict E
  have hμ₀ : μ₀ ≤ μ := Measure.restrict_le_self
  have hcover (r : Fin m) : μ₀ {p | ∃ i, p ∈ (f r).cell i}ᶜ = 0 := by
    have heq : {p | ∃ i, p ∈ (f r).cell i} = U r ∩ (univ ×ˢ Icc (0 : ℝ) 1) := by
      ext p
      simp only [PredictorFamily.cell, mem_ofPred_eq, mem_prod, mem_univ, true_and,
        mem_inter_iff, U]
      aesop
    rw [heq, compl_inter]
    apply measure_union_null
    · rw [Measure.restrict_apply (hU r).compl]
      have hempty : (U r)ᶜ ∩ E = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro p ⟨hp, hpE⟩
        exact hp (mem_iInter.mp hpE r)
      rw [hempty, measure_empty]
    · exact le_antisymm ((hμ₀ _).trans_eq htime) bot_le
  obtain ⟨ρ, hρ, hmass, n', idx, hinj, hfloor, hcov⟩ :=
    finite_floor_subfamilies μ₀ (fun r => (f r).n) (fun r => (f r).cell)
      (fun r i => ((f r).measurable i).prod measurableSet_Icc)
      (fun r => (f r).weight π d Z) hcover
  refine ⟨ρ, hρ.trans hμ₀, ?_, fun r => (f r).reindex (idx r) (hinj r), ?_⟩
  · have hbudget : μ univ ≤ μ₀ univ + ∑ r, μ (U r)ᶜ := by
      calc
        _ = μ E + μ Eᶜ := (measure_add_measure_compl hE).symm
        _ ≤ μ₀ univ + ∑ r, μ (U r)ᶜ := by
          rw [Measure.restrict_apply_univ]
          apply add_le_add le_rfl
          dsimp only [E]
          rw [compl_iInter]
          exact (measure_iUnion_le _).trans_eq (tsum_fintype _)
    calc
      μ univ ≤ μ₀ univ + ∑ r, μ (U r)ᶜ := hbudget
      _ ≤ (ρ univ + ∑ r, ∑ i, (f r).weight π d Z i) + ∑ r, μ (U r)ᶜ :=
        add_le_add hmass le_rfl
      _ = _ := by dsimp [U]; ac_rfl
  · intro r
    constructor
    · apply measure_mono_null _ (hcov r)
      intro p hp hpc
      obtain ⟨i, hi⟩ := hpc
      exact hp ⟨i, hi.1⟩
    · exact hfloor r

end Submission.Obl.k4_horizontal_coefficient_count
