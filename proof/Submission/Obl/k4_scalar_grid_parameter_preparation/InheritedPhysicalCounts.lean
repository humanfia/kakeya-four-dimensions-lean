/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/InheritedPhysicalCounts.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.CoarseGridNeighbors
import Submission.Lib.K4FinitePlankAtlases.DensityFloors

/-! Hereditary physical counts using mass witnesses before later restrictions. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem inherited_physical_cell_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → Fin 3 → ℝ) (hf : Measurable f)
    (A E : Set Ω) (hA : MeasurableSet A) (hEA : E ⊆ A)
    (ξ ζ τ U : ℝ) (hξ : 0 < ξ) (hξζ : ξ ≤ ζ) (hτ : 0 < τ) (hU : 0 ≤ U)
    (hfinite : (physicalScalarGridTag ξ '' (f '' A)).Finite)
    (hfloor : ∀ p ∈ A, ENNReal.ofReal τ ≤ μ (A ∩ {p' | physicalScalarGridTag ξ (f p') = physicalScalarGridTag ξ (f p)}))
    (hcap : ∀ q, μ {p | physicalScalarGridTag ζ (f p) = q} ≤ ENNReal.ofReal U)
    (q₀ : Fin 3 → ℤ) :
    {q : Fin 3 → ℤ | (μ.restrict E) {p | physicalScalarGridTag ξ (f p) = q ∧
      physicalScalarGridTag ζ (f p) = q₀} ≠ 0}.Finite ∧
    ({q : Fin 3 → ℤ | (μ.restrict E) {p | physicalScalarGridTag ξ (f p) = q ∧
      physicalScalarGridTag ζ (f p) = q₀} ≠ 0}.ncard : ℝ) ≤ 27 * U / τ := by
  have htag (w : ℝ) : Measurable (fun p => physicalScalarGridTag w (f p)) := by
    apply Measurable.of_eval
    intro i
    dsimp only [physicalScalarGridTag]
    fun_prop
  have hcell (w : ℝ) (q : Fin 3 → ℤ) : MeasurableSet {p | physicalScalarGridTag w (f p) = q} :=
    measurableSet_eq_fun (htag w) measurable_const
  let Q := {q : Fin 3 → ℤ | (μ.restrict E) {p | physicalScalarGridTag ξ (f p) = q ∧
    physicalScalarGridTag ζ (f p) = q₀} ≠ 0}
  have hwitness (q : Fin 3 → ℤ) (hq : q ∈ Q) :
      ∃ p ∈ E, physicalScalarGridTag ξ (f p) = q ∧ physicalScalarGridTag ζ (f p) = q₀ := by
    have hmeas : MeasurableSet {p | physicalScalarGridTag ξ (f p) = q ∧
        physicalScalarGridTag ζ (f p) = q₀} := (hcell ξ q).inter (hcell ζ q₀)
    change (μ.restrict E) {p | physicalScalarGridTag ξ (f p) = q ∧
      physicalScalarGridTag ζ (f p) = q₀} ≠ 0 at hq
    rw [Measure.restrict_apply hmeas] at hq
    obtain ⟨p,hp⟩ := nonempty_of_measure_ne_zero hq
    exact ⟨p,hp.2,hp.1⟩
  have hQ : Q.Finite := hfinite.subset (by
    intro q hq
    obtain ⟨p,hp,hp',_⟩ := hwitness q hq
    exact ⟨f p, ⟨p,hEA hp,rfl⟩,hp'⟩)
  let C := {p | physicalScalarGridTag ζ (f p) ∈
    Submission.Lib.K4ListedExceptions.integerCodeBox 1 q₀}
  have hC : MeasurableSet C := (htag ζ) (by exact MeasurableSet.of_discrete)
  let cells : (Fin 3 → ℤ) → Set Ω := fun q => A ∩ {p | physicalScalarGridTag ξ (f p) = q}
  have hcC (q : Fin 3 → ℤ) (hq : q ∈ Q) : cells q ⊆ C := by
    obtain ⟨p₀,hp₀,hp₀',hp₀''⟩ := hwitness q hq
    intro p hp
    have heq : physicalScalarGridTag ξ (f p) = physicalScalarGridTag ξ (f p₀) := hp.2.trans hp₀'.symm
    have hn := coarse_grid_neighbor_of_fine_equal ξ ζ hξ hξζ (f p) (f p₀) heq
    change physicalScalarGridTag ζ (f p) ∈
      Submission.Lib.K4ListedExceptions.integerCodeBox 1 (physicalScalarGridTag ζ (f p₀)) at hn
    simpa only [C, Set.mem_ofPred_eq, hp₀''] using hn
  have hdisj : (↑hQ.toFinset : Set (Fin 3 → ℤ)).PairwiseDisjoint cells := by
    intro q hq q' hq' hne
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact hne (hp.2.symm.trans hp'.2)
  have hmass (q : Fin 3 → ℤ) (hq : q ∈ hQ.toFinset) : τ ≤ (μ.restrict C).real (cells q) := by
    have hq' := hQ.mem_toFinset.mp hq
    obtain ⟨p,hp,hp',_⟩ := hwitness q hq'
    have hl := hfloor p (hEA hp)
    rw [hp'] at hl
    have he : (μ.restrict C) (cells q) = μ (cells q) := by
      rw [Measure.restrict_apply (hA.inter (hcell ξ q)), Set.inter_eq_left.mpr (hcC q hq')]
    simpa only [measureReal_def, he, ENNReal.toReal_ofReal hτ.le] using
      ENNReal.toReal_mono (measure_ne_top (μ.restrict C) (cells q)) (hl.trans_eq he.symm)
  have hc := Submission.Lib.K4FinitePlankAtlases.old_cell_count (μ.restrict C) hQ.toFinset cells
    hdisj (fun q _ => hA.inter (hcell ξ q)) hτ hmass
  have htotal : (μ.restrict C).real Set.univ ≤ 27 * U := by
    have hm := physical_grid_neighbor_mass_le μ f ζ U q₀ hcap
    have hr := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hm
    simpa only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, C,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 27) hU)] using hr
  refine ⟨hQ, ?_⟩
  change (Q.ncard : ℝ) ≤ _
  rw [Set.ncard_eq_toFinset_card _ hQ]
  exact hc.trans (div_le_div_of_nonneg_right htotal hτ.le)

theorem inherited_physical_power_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → Fin 3 → ℝ) (hf : Measurable f)
    (A E : Set Ω) (hA : MeasurableSet A) (hEA : E ⊆ A)
    (N K P d r r₀ : ℝ) (hN : 1 ≤ N) (hK : 0 ≤ K) (hP : 0 < P) (hr : r₀ ≤ r)
    (hfinite : (physicalScalarGridTag (N ^ (-r)) '' (f '' A)).Finite)
    (hfloor : ∀ p ∈ A, ENNReal.ofReal (N ^ (-((2 + d) * r)) / P) ≤
      μ (A ∩ {p' | physicalScalarGridTag (N ^ (-r)) (f p') = physicalScalarGridTag (N ^ (-r)) (f p)}))
    (hcap : ∀ q, μ {p | physicalScalarGridTag (N ^ (-r₀)) (f p) = q} ≤
      ENNReal.ofReal (K * N ^ (-((2 + d) * r₀)))) (q₀ : Fin 3 → ℤ) :
    {q : Fin 3 → ℤ | (μ.restrict E) {p | physicalScalarGridTag (N ^ (-r)) (f p) = q ∧
      physicalScalarGridTag (N ^ (-r₀)) (f p) = q₀} ≠ 0}.Finite ∧
    ({q : Fin 3 → ℤ | (μ.restrict E) {p | physicalScalarGridTag (N ^ (-r)) (f p) = q ∧
      physicalScalarGridTag (N ^ (-r₀)) (f p) = q₀} ≠ 0}.ncard : ℝ) ≤
        (27 * K * P) * N ^ ((2 + d) * (r - r₀)) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hτ : 0 < N ^ (-((2 + d) * r)) / P := div_pos (Real.rpow_pos_of_pos hNpos _) hP
  have hc := inherited_physical_cell_count μ f hf A E hA hEA
    (N ^ (-r)) (N ^ (-r₀)) (N ^ (-((2 + d) * r)) / P) (K * N ^ (-((2 + d) * r₀)))
    (Real.rpow_pos_of_pos hNpos _)
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hτ
    (mul_nonneg hK (Real.rpow_nonneg hNpos.le _)) hfinite hfloor hcap q₀
  have hratio : N ^ (-((2 + d) * r₀)) / N ^ (-((2 + d) * r)) = N ^ ((2 + d) * (r - r₀)) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  refine ⟨hc.1, hc.2.trans_eq ?_⟩
  calc
    _ = (27 * K * P) * (N ^ (-((2 + d) * r₀)) / N ^ (-((2 + d) * r))) := by
      field_simp
    _ = _ := by rw [hratio]

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
