/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/AffineConditionalSupport.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineFiberGeometry
import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineStripMass
import Submission.Obl.k4_scalar_grid_parameter_preparation.PaletteScaledCellCount
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarScalePackets
import Submission.Obl.k4_scalar_grid_parameter_preparation.PhysicalSupportCover

/-! Physical support inside one affine bin, with exact original palette cancellation. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped Classical ENNReal

theorem affine_conditional_physical_support {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ)) [IsFiniteMeasure μ] (θ : Measure X) [SFinite θ]
    (π : Measure ℝ) [IsProbabilityMeasure π] (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (A Z : Set (X × ℝ)) (hA : MeasurableSet A) (ξ K D L τ : ℝ)
    (hξ : 0 < ξ) (hK : 0 ≤ K) (hD : 0 ≤ D) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hpoint : ∀ p ∈ A, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a p.1 e| ≤ K)
    (hdom : μ.restrict A ≤ ENNReal.ofReal D • θ.prod volume)
    (hfinite : (physicalScalarGridTag ξ '' (scalarPacketPosition a '' A)).Finite)
    (hfloor : ∀ p ∈ A, ENNReal.ofReal τ * π (scalarVelocityBin ξ ⌊a p.1 1 / ξ⌋) ≤
      μ (A ∩ {p' | physicalScalarGridTag ξ (scalarPacketPosition a p') =
        physicalScalarGridTag ξ (scalarPacketPosition a p) ∧
        a p'.1 1 ∈ scalarVelocityBin ξ ⌊a p.1 1 / ξ⌋}))
    (q₀ c : ℤ) (hZ : ∀ p ∈ Z, p ∈ A ∧ a p.1 0 ∈ scalarVelocityBin ξ q₀ ∧ a p.1 1 ∈ scalarVelocityBin ξ c)
    (hprior : ∀ q : ℤ, θ {l | a l 0 ∈ scalarVelocityBin ξ q ∧ a l 1 ∈ scalarVelocityBin ξ c} ≤
      ENNReal.ofReal L * π (scalarVelocityBin ξ c)) :
    {q : Fin 3 → ℤ | (μ.restrict Z) {p | physicalScalarGridTag ξ (scalarPacketPosition a p) = q} ≠ 0}.Finite ∧
    ({q : Fin 3 → ℤ | (μ.restrict Z) {p | physicalScalarGridTag ξ (scalarPacketPosition a p) = q} ≠ 0}.ncard : ℝ) ≤
      (D * (4 * (K + 3) + 2) * L) / τ := by
  let phys := fun p : X × ℝ => physicalScalarGridTag ξ (scalarPacketPosition a p)
  have hphys : Measurable phys := by
    apply Measurable.of_eval
    intro e
    dsimp only [phys,physicalScalarGridTag]
    have hm := measurable_scalarPacketPosition ha
    fun_prop
  have hcell (q : Fin 3 → ℤ) : MeasurableSet {p | phys p = q} :=
    measurableSet_eq_fun hphys measurable_const
  have hY : Measurable (fun p : X × ℝ => a p.1 0) := (measurable_pi_apply 0).comp (ha.comp measurable_fst)
  have hV : Measurable (fun p : X × ℝ => a p.1 1) := (measurable_pi_apply 1).comp (ha.comp measurable_fst)
  let C := {p : X × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    |a p.1 0 - ξ * (q₀ : ℝ)| ≤ (K + 3) * ξ ∧ a p.1 1 ∈ scalarVelocityBin ξ c}
  have hC : MeasurableSet C := (measurableSet_Icc.preimage measurable_snd).inter
    ((measurableSet_le (hY.sub_const _).abs measurable_const).inter
      ((measurableSet_scalarVelocityBin ξ c).preimage hV))
  let U := D * (4 * (K + 3) + 2) * L
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcapC : μ (A ∩ C) ≤ ENNReal.ofReal U * π (scalarVelocityBin ξ c) := by
    have hh := affine_intercept_strip_incidence_cap θ (μ.restrict A) (fun l => a l 0) (fun l => a l 1)
      π ξ (K + 3) (ξ * (q₀ : ℝ)) D hξ (by linarith) hD hdom c (ENNReal.ofReal L) hprior
    change (μ.restrict A) C ≤ _ at hh
    rw [Measure.restrict_apply hC,Set.inter_comm] at hh
    rw [← ENNReal.ofReal_mul (mul_nonneg hD (by linarith))] at hh
    exact hh
  let Q := {q : Fin 3 → ℤ | (μ.restrict Z) {p | phys p = q} ≠ 0}
  have hwitness (q : Fin 3 → ℤ) (hq : q ∈ Q) : ∃ p ∈ Z, phys p = q := by
    change (μ.restrict Z) {p | phys p = q} ≠ 0 at hq
    rw [Measure.restrict_apply (hcell q)] at hq
    obtain ⟨p,hp⟩ := nonempty_of_measure_ne_zero hq
    exact ⟨p,hp.2,hp.1⟩
  have hQ : Q.Finite := hfinite.subset (by
    intro q hq
    obtain ⟨p,hp,hp'⟩ := hwitness q hq
    exact ⟨scalarPacketPosition a p,⟨p,(hZ p hp).1,rfl⟩,hp'⟩)
  let cells := fun q : Fin 3 → ℤ => A ∩ {p | phys p = q ∧ a p.1 1 ∈ scalarVelocityBin ξ c}
  have hcells (q) : MeasurableSet (cells q) := hA.inter
    ((hcell q).inter ((measurableSet_scalarVelocityBin ξ c).preimage hV))
  have hcover (q) (hq : q ∈ Q) : cells q ⊆ A ∩ C := by
    obtain ⟨p₀,hp₀,hp₀'⟩ := hwitness q hq
    intro p hp
    have he : phys p₀ = phys p := hp₀'.trans hp.2.1.symm
    have hT : (⌊p₀.2 / ξ⌋ : ℤ) = ⌊p.2 / ξ⌋ := by
      simpa only [phys,physicalScalarGridTag,scalarPacketPosition,Matrix.cons_val_zero] using congrFun he 0
    have hY' : (⌊scalarY (a p₀.1) p₀.2 / ξ⌋ : ℤ) = ⌊scalarY (a p.1) p.2 / ξ⌋ := by
      simpa only [phys,physicalScalarGridTag,scalarPacketPosition,Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun he 1
    have hv : (⌊a p₀.1 1 / ξ⌋ : ℤ) = ⌊a p.1 1 / ξ⌋ := (hZ p₀ hp₀).2.2.trans hp.2.2.symm
    have hn := scalar_intercept_near_affine_bin ξ K hξ (a p₀.1) (a p.1) p₀.2 p.2
      (hpoint p₀ (hZ p₀ hp₀).1).1 ((hpoint p hp.1).2 1) hT hY' hv q₀ (hZ p₀ hp₀).2.1
    exact ⟨hp.1,(hpoint p hp.1).1,hn,hp.2.2⟩
  have hdisj : (↑hQ.toFinset : Set (Fin 3 → ℤ)).PairwiseDisjoint cells := by
    intro q hq q' hq' hne
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact hne (hp.2.1.symm.trans hp'.2.1)
  have hlo (q) (hq : q ∈ hQ.toFinset) : ENNReal.ofReal τ * π (scalarVelocityBin ξ c) ≤ μ (cells q) := by
    obtain ⟨p,hp,hp'⟩ := hwitness q (hQ.mem_toFinset.mp hq)
    have hl := hfloor p (hZ p hp).1
    have hv : (⌊a p.1 1 / ξ⌋ : ℤ) = c := (hZ p hp).2.2
    have hp'' : physicalScalarGridTag ξ (scalarPacketPosition a p) = q := hp'
    simpa only [cells,phys,hv,hp''] using hl
  refine ⟨hQ,?_⟩
  change (Q.ncard : ℝ) ≤ U / τ
  by_cases hp : π (scalarVelocityBin ξ c) = 0
  · have hQempty : Q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hz : (μ.restrict Z) {p | phys p = q} ≤ μ (cells q) := by
        rw [Measure.restrict_apply (hcell q)]
        apply measure_mono
        intro p hp
        exact ⟨(hZ p hp.2).1,hp.1,(hZ p hp.2).2.2⟩
      have hh := hz.trans ((measure_mono (hcover q hq)).trans hcapC)
      rw [hp,mul_zero] at hh
      exact hq (le_antisymm hh bot_le)
    rw [hQempty,Set.ncard_empty,Nat.cast_zero]
    exact div_nonneg hU hτ.le
  · rw [Set.ncard_eq_toFinset_card _ hQ]
    exact palette_scaled_old_cell_count μ hQ.toFinset cells hdisj (fun q _ => hcells q)
      (A ∩ C) (fun q hq => hcover q (hQ.mem_toFinset.mp hq)) τ U hτ hU
      (π (scalarVelocityBin ξ c)) hp (measure_ne_top π _) hlo hcapC

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
