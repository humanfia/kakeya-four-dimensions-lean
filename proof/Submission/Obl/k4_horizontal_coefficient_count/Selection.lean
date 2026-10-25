import Submission.Obl.k4_horizontal_coefficient_count.Common

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- Simultaneous deletion charges each light label at most once, including
labels from overlapping families. -/
theorem finite_floor_selection {Ω ι : Type*} [MeasurableSpace Ω]
    (F : Finset ι) (A : ι → Set Ω) (w : ι → ℝ≥0∞)
    (hA : ∀ i ∈ F, MeasurableSet (A i)) (μ : Measure Ω) :
    ∃ E : Set Ω, MeasurableSet E ∧
      μ univ ≤ μ E + ∑ i ∈ F, w i ∧
      ∀ i ∈ F, μ (A i ∩ E) = 0 ∨ w i ≤ μ (A i ∩ E) := by
  classical
  revert hA μ
  refine F.strongInductionOn ?_
  intro F ih hA μ
  by_cases h : ∀ i ∈ F, μ (A i) = 0 ∨ w i ≤ μ (A i)
  · refine ⟨univ, MeasurableSet.univ, le_self_add, ?_⟩
    simpa only [inter_univ] using h
  · push Not at h
    obtain ⟨i, hi, hzero, hlight⟩ := h
    have hAi := hA i hi
    obtain ⟨E, hE, hmass, hfloor⟩ := ih (F.erase i) (Finset.erase_ssubset hi)
      (fun j hj => hA j (Finset.mem_of_mem_erase hj)) (μ.restrict (A i)ᶜ)
    refine ⟨E ∩ (A i)ᶜ, hE.inter hAi.compl, ?_, ?_⟩
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply hE] at hmass
      calc
        μ univ = μ (A i)ᶜ + μ (A i) :=
          (measure_add_measure_compl hAi.compl).symm.trans (by simp)
        _ ≤ (μ (E ∩ (A i)ᶜ) + ∑ j ∈ F.erase i, w j) + w i :=
            add_le_add hmass hlight.le
        _ = μ (E ∩ (A i)ᶜ) + ∑ j ∈ F, w j := by
          rw [add_assoc, add_comm (∑ j ∈ F.erase i, w j),
            Finset.add_sum_erase _ _ hi]
    · intro j hj
      by_cases hji : j = i
      · subst j
        left
        have heq : A i ∩ (E ∩ (A i)ᶜ) = ∅ := by ext x; simp_all
        rw [heq, measure_empty]
      · have hj' : j ∈ F.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
        have hf := hfloor j hj'
        rw [Measure.restrict_apply ((hA j hj).inter hE)] at hf
        simpa only [inter_assoc] using hf

/-- The same common-floor construction expressed as one unnormalized
submeasure. -/
theorem finite_floor_submeasure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (w : ι → ℝ≥0∞) :
    ∃ ρ : Measure Ω, ρ ≤ μ ∧ μ univ ≤ ρ univ + ∑ i, w i ∧
      ∀ i, ρ (A i) = 0 ∨ w i ≤ ρ (A i) := by
  obtain ⟨E, hE, hmass, hfloor⟩ :=
    finite_floor_selection Finset.univ A w (fun i _ => hA i) μ
  refine ⟨μ.restrict E, Measure.restrict_le_self, ?_, ?_⟩
  · simpa only [Measure.restrict_apply_univ] using hmass
  · intro i
    simpa only [Measure.restrict_apply (hA i)] using hfloor i (Finset.mem_univ i)

/-- Delete the zero cells after making all floors simultaneous. The new
indices are injective maps into the original families, so all stored
witnesses and disjointness survive. -/
theorem finite_floor_subfamilies {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m : ℕ} (n : Fin m → ℕ)
    (A : (r : Fin m) → Fin (n r) → Set Ω)
    (hA : ∀ r i, MeasurableSet (A r i))
    (w : (r : Fin m) → Fin (n r) → ENNReal)
    (hcover : ∀ r, μ {p | ∃ i, p ∈ A r i}ᶜ = 0) :
    ∃ ρ : Measure Ω, ρ ≤ μ ∧ μ univ ≤ ρ univ + ∑ r, ∑ i, w r i ∧
      ∃ (n' : Fin m → ℕ) (idx : (r : Fin m) → Fin (n' r) → Fin (n r)),
        (∀ r, Function.Injective (idx r)) ∧
        (∀ r i, w r (idx r i) ≤ ρ (A r (idx r i))) ∧
        ∀ r, ρ {p | ∃ i, p ∈ A r (idx r i)}ᶜ = 0 := by
  classical
  obtain ⟨ρ, hρ, hmass, hfloor⟩ := finite_floor_submeasure μ
    (fun i : (r : Fin m) × Fin (n r) => A i.1 i.2)
    (fun i => hA i.1 i.2) (fun i => w i.1 i.2)
  let Good (r : Fin m) := {i : Fin (n r) // w r i ≤ ρ (A r i)}
  let n' : Fin m → ℕ := fun r => Fintype.card (Good r)
  let equiv (r : Fin m) : Good r ≃ Fin (n' r) := Fintype.equivFin (Good r)
  let idx (r : Fin m) (i : Fin (n' r)) : Fin (n r) := ((equiv r).symm i).val
  refine ⟨ρ, hρ, ?_, n', idx, ?_, ?_, ?_⟩
  · simpa only [Fintype.sum_sigma] using hmass
  · intro r i j hij
    exact (equiv r).symm.injective (Subtype.ext hij)
  · intro r i
    exact ((equiv r).symm i).property
  · intro r
    have hc : ∀ᵐ p ∂ρ, ∃ i, p ∈ A r i :=
      (ae_iff.mpr (hcover r)).filter_mono (ae_mono hρ)
    have hg : ∀ᵐ p ∂ρ, ∀ i, p ∈ A r i → w r i ≤ ρ (A r i) := by
      rw [ae_all_iff]
      intro i
      by_cases hi : w r i ≤ ρ (A r i)
      · exact Filter.Eventually.of_forall (fun _ _ => hi)
      · have hz : ρ (A r i) = 0 := (hfloor ⟨r, i⟩).resolve_right hi
        filter_upwards [compl_mem_ae_iff.mpr hz] with p hp hpi
        exact (hp hpi).elim
    apply ae_iff.mp
    filter_upwards [hc, hg] with p hp hgp
    obtain ⟨i, hi⟩ := hp
    let g : Good r := ⟨i, hgp i hi⟩
    refine ⟨equiv r g, ?_⟩
    simpa only [idx, Equiv.symm_apply_apply] using hi

end Submission.Obl.k4_horizontal_coefficient_count
