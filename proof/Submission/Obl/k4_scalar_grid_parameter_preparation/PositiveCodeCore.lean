/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PositiveCodeCore.lean -/
import Mathlib

/-! Remove null physical states before using pointwise trace-cover certificates. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators

theorem exists_positive_code_core {Ω C : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) (code : Ω → C)
    (hcode : ∀ c, MeasurableSet {p | code p = c}) (hfinite : (code '' E).Finite) :
    ∃ G : Set Ω, MeasurableSet G ∧ G ⊆ E ∧ μ (E \ G) = 0 ∧
      μ.restrict G = μ.restrict E ∧ ∀ p ∈ G, (μ.restrict E) {p' | code p' = code p} ≠ 0 := by
  classical
  let Q := hfinite.toFinset.filter fun c => (μ.restrict E) {p | code p = c} = 0
  let B := ⋃ c ∈ Q, {p | code p = c}
  have hB : MeasurableSet B := MeasurableSet.biUnion Q.countable_toSet (fun c _ => hcode c)
  have hBzero : (μ.restrict E) B = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ ∑ c ∈ Q, (μ.restrict E) {p | code p = c} := measure_biUnion_finset_le _ _
      _ = 0 := Finset.sum_eq_zero fun c hc => (Finset.mem_filter.mp hc).2
  let G := E \ B
  have hG : MeasurableSet G := hE.diff hB
  have hsub : G ⊆ E := Set.sdiff_subset
  have hnull : μ (E \ G) = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ μ (B ∩ E) := measure_mono (by intro p hp; exact ⟨by simpa [G,hp.1] using hp.2,hp.1⟩)
      _ = 0 := by rw [← Measure.restrict_apply hB]; exact hBzero
  have heq : G =ᵐ[μ] E := by
    have hn : ∀ᵐ p ∂μ, p ∉ E \ G := (ae_iff).mpr (by
      have hh : {p : Ω | ¬p ∉ E \ G} = E \ G := by ext p; simp
      rw [hh]
      exact hnull)
    filter_upwards [hn] with p hp
    apply propext
    exact ⟨fun h => hsub h,fun h => by by_contra hg; exact hp ⟨h,hg⟩⟩
  refine ⟨G,hG,hsub,hnull,Measure.restrict_congr_set heq,?_⟩
  intro p hp hzero
  have hc : code p ∈ Q := Finset.mem_filter.mpr
    ⟨hfinite.mem_toFinset.mpr ⟨p,hsub hp,rfl⟩,hzero⟩
  exact hp.2 (Set.mem_iUnion₂.mpr ⟨code p,hc,rfl⟩)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
