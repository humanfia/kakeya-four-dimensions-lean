/-
Adapted from: here:o062
Original proof: o062/x0212, 01e16678, Submission/Obl/k4_scalar_mesh_projection/OriginalLongRows.lean.
Finite representative menus replace arbitrary measurable-choice assumptions;
original long-row and whole-block conclusions keep the original finite prior mass.
-/

import Submission.Lib.K4Homogenization.RetainedDuration

namespace Submission.Lib.K4ScalarCoreAssembly



open Set MeasureTheory
open Submission.Lib.K4Homogenization
open scoped ENNReal

/-- Long-row pruning for an arbitrary finite original prior. The mass
of that prior occurs on both sides and is never normalized away. -/
theorem exists_original_long_rows {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure (α × ℝ))
    (C m : ℝ) (hC : 0 < C) (hm : 0 < m)
    (hdom : μ ≤ ENNReal.ofReal C • (ν.prod volume))
    (S : Set (α × ℝ)) (hS : MeasurableSet S)
    (hmass : ENNReal.ofReal m*ν univ ≤ μ S) :
    ∃ T : Set (α × ℝ), MeasurableSet T ∧ T ⊆ S ∧
      ENNReal.ofReal (m/2)*ν univ ≤ μ T ∧
      ∀ p ∈ T, ENNReal.ofReal (m/(2*C)) ≤ volume (Prod.mk p.1 ⁻¹' S) := by
  classical
  let r := m/(2*C)
  let G : α × ℝ → ℝ≥0∞ := S.indicator 1
  have hG : Measurable G := measurable_const.indicator hS
  let L := durationRetained volume G univ (ENNReal.ofReal r)
  have hLm : MeasurableSet L := measurableSet_durationRetained volume hG univ _
  have hDur (a : α) : incidenceDuration volume G univ a=volume (Prod.mk a ⁻¹' S) := by
    rw [incidenceDuration,setLIntegral_univ]
    have heq : (fun t => G (a,t))=(Prod.mk a ⁻¹' S).indicator 1 := by
      ext t
      by_cases ht : (a,t) ∈ S <;> simp [G,ht]
    rw [heq]
    have hrowm : MeasurableSet (Prod.mk a ⁻¹' S) :=
      hS.preimage (measurable_const.prodMk measurable_id)
    exact lintegral_indicator_one hrowm
  have hshortprod : (ν.prod volume) (S ∩ (Lᶜ ×ˢ univ)) ≤ ENNReal.ofReal r*ν univ := by
    have h := duration_omission_mass_le ν volume hG MeasurableSet.univ (ENNReal.ofReal r)
    change (ν.prod volume).withDensity G (Lᶜ ×ˢ univ) ≤ _ at h
    change (ν.prod volume).withDensity (S.indicator 1) (Lᶜ ×ˢ univ) ≤ _ at h
    rw [withDensity_indicator hS 1,withDensity_one,
      Measure.restrict_apply (hLm.compl.prod MeasurableSet.univ)] at h
    simpa only [inter_comm] using h
  have hshort : μ (S ∩ (Lᶜ ×ˢ univ)) ≤ ENNReal.ofReal (m/2)*ν univ := by
    calc
      _ ≤ ENNReal.ofReal C*(ν.prod volume) (S ∩ (Lᶜ ×ˢ univ)) := hdom _
      _ ≤ ENNReal.ofReal C*(ENNReal.ofReal r*ν univ) := mul_le_mul' le_rfl hshortprod
      _ = _ := by
        rw [← mul_assoc,← ENNReal.ofReal_mul hC.le]
        congr 2
        dsimp only [r]
        field_simp
  let T := S ∩ (L ×ˢ univ)
  have hcover : S ⊆ T ∪ (S ∩ (Lᶜ ×ˢ univ)) := by
    intro p hp
    by_cases ha : p.1 ∈ L
    · exact Or.inl ⟨hp,ha,mem_univ _⟩
    · exact Or.inr ⟨hp,ha,mem_univ _⟩
  have hbound : ENNReal.ofReal m*ν univ ≤ μ T+ENNReal.ofReal (m/2)*ν univ :=
    hmass.trans ((measure_mono hcover).trans
      ((measure_union_le _ _).trans (add_le_add le_rfl hshort)))
  have hsplit : ENNReal.ofReal m*ν univ=
      ENNReal.ofReal (m/2)*ν univ+ENNReal.ofReal (m/2)*ν univ := by
    rw [← add_mul,← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 2
    ring
  rw [hsplit] at hbound
  refine ⟨T,hS.inter (hLm.prod MeasurableSet.univ),inter_subset_left,
    ENNReal.le_of_add_le_add_right (by finiteness) hbound,?_⟩
  intro p hp
  have hL : p.1 ∈ L := hp.2.1
  change ENNReal.ofReal r ≤ incidenceDuration volume G univ p.1 at hL
  simpa only [hDur] using hL

end Submission.Lib.K4ScalarCoreAssembly
