/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, DenseCodeCover.lean.
   Original source attributions below are retained. -/

import Submission.Lib.K4FinitePlankAtlases.DensityFloors

/-! Adapted from our LOT tree o107 (`k4_finite_narrowness_path_improvement`), session x0353,
`DenseCodeCover.lean` (commit 96bcaa7b); namespace and import paths renamed. -/

/-! A heavy code on every dense residual gives a finite heavy cover. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal Classical

/-- Apply discovery only to the union of light full code cells. A heavy cell
there would contradict its original mass. -/
theorem light_codes_small_of_dense_discovery {Ω Code : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Code] [Countable Code] [MeasurableSingletonClass Code]
    (μ : Measure Ω) (code : Ω → Code) (hcode : Measurable code)
    (θ δ : ℝ≥0∞) (hθ : 0 < θ)
    (hdiscover : ∀ E : Set Ω, MeasurableSet E → δ ≤ μ E →
      ∃ c : Code, θ ≤ μ (E ∩ code ⁻¹' {c})) :
    μ {x | μ (code ⁻¹' {code x}) < θ} < δ := by
  let Bad : Set Ω := {x | μ (code ⁻¹' {code x}) < θ}
  have hBad : MeasurableSet Bad :=
    measurableSet_lt ((measurable_of_countable (fun c => μ (code ⁻¹' {c}))).comp hcode) measurable_const
  by_contra hnot
  have hmass : δ ≤ μ Bad := not_lt.mp hnot
  obtain ⟨c, hc⟩ := hdiscover Bad hBad hmass
  have hne : (Bad ∩ code ⁻¹' {c}).Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    rw [he, measure_empty] at hc
    exact hθ.not_ge hc
  obtain ⟨x, hx, hxc⟩ := hne
  have hlt : μ (code ⁻¹' {c}) < θ := by
    have heq : code x = c := hxc
    change μ (code ⁻¹' {code x}) < θ at hx
    simpa only [heq] using hx
  exact hlt.not_ge (hc.trans (measure_mono Set.inter_subset_right))

/-- Full code cells retain their original floors and cost at most the total
original mass divided by the floor. The cover keeps all but delta mass. -/
theorem finite_heavy_code_cover_of_dense_discovery {Ω Code : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Code] [Countable Code] [MeasurableSingletonClass Code]
    [DecidableEq Code] (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Code) (hcode : Measurable code) (F : Finset Code)
    (hcover : ∀ᵐ x ∂μ, code x ∈ F) (θ : ℝ) (δ : ℝ≥0∞) (hθ : 0 < θ)
    (hdiscover : ∀ E : Set Ω, MeasurableSet E → δ ≤ μ E →
      ∃ c : Code, ENNReal.ofReal θ ≤ μ (E ∩ code ⁻¹' {c})) :
    ∃ G : Finset Code, G ⊆ F ∧
      (∀ c ∈ G, ENNReal.ofReal θ ≤ μ (code ⁻¹' {c})) ∧
      (G.card : ℝ) ≤ μ.real univ / θ ∧ μ {x | code x ∉ G} < δ := by
  let G := F.filter (fun c => ENNReal.ofReal θ ≤ μ (code ⁻¹' {c}))
  have hG : ∀ c ∈ G, ENNReal.ofReal θ ≤ μ (code ⁻¹' {c}) :=
    fun c hc => (Finset.mem_filter.mp hc).2
  refine ⟨G, Finset.filter_subset _ _, hG, ?_, ?_⟩
  · have hdisj : (↑G : Set Code).PairwiseDisjoint (fun c => code ⁻¹' {c}) := by
      intro c hc d hd hcd
      exact Set.disjoint_left.mpr fun x hc hd => hcd (hc.symm.trans hd)
    have hfloor : ∀ c ∈ G, θ ≤ μ.real (code ⁻¹' {c}) := by
      intro c hc
      have hr := ENNReal.toReal_mono (measure_ne_top μ _) (hG c hc)
      simpa only [measureReal_def, ENNReal.toReal_ofReal hθ.le] using hr
    exact Submission.Lib.K4FinitePlankAtlases.old_cell_count μ G (fun c => code ⁻¹' {c})
      hdisj (fun c _ => hcode (measurableSet_singleton c)) hθ hfloor
  · have hsame : {x | code x ∉ G} =ᵐ[μ] {x | μ (code ⁻¹' {code x}) < ENNReal.ofReal θ} := by
      filter_upwards [hcover] with x hx
      simp only [G, Finset.mem_filter, hx, true_and, not_le]
    rw [measure_congr hsame]
    exact light_codes_small_of_dense_discovery μ code hcode (ENNReal.ofReal θ) δ
      (ENNReal.ofReal_pos.mpr hθ) hdiscover

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
