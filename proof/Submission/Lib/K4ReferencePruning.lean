import Mathlib
import Submission.Lib.K4ScalarActualSwitching.PaletteConditioning
import Submission.Lib.K4HorizontalCoercivity.VelocityWitnesses

/-!
# Original-reference pruning and palette transfer

Adapted from: here:o200 (session x0696).

Light-state deletion against summable earlier reference weights, followed by
conditional domination using the original velocity palette and actual
separated velocity witnesses outside prescribed null exceptions.
-/

namespace Submission.Lib.K4ReferencePruning

open MeasureTheory Set

noncomputable section

/-- States retained by comparison with their earlier reference weight. -/
def referenceKeep {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (w : Q → ENNReal) (delta : ENNReal) : Set Ω :=
  {p | delta * w (state p) ≤ μ (state ⁻¹' {state p})}

theorem measurableSet_referenceKeep {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (w : Q → ENNReal) (delta : ENNReal) :
    MeasurableSet (referenceKeep μ state w delta) := by
  classical
  have heq : referenceKeep μ state w delta =
      ⋃ q : Q, if delta * w q ≤ μ (state ⁻¹' {q}) then state ⁻¹' {q} else ∅ := by
    ext p
    simp only [referenceKeep, mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hp
      exact ⟨state p, by simpa only [ite_eq_left hp, mem_preimage, mem_singleton_iff]⟩
    · rintro ⟨q, hq⟩
      split_ifs at hq with h
      · have hp : state p = q := hq
        simpa only [hp] using h
      · exact hq.elim
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  split_ifs
  · exact hstate (measurableSet_singleton q)
  · exact MeasurableSet.empty

/-- The total deletion cost is the cutoff times the sum of the old weights,
regardless of the number of current states. -/
theorem reference_light_mass_le {Ω Q : Type*} [MeasurableSpace Ω] [Countable Q]
    (μ : Measure Ω) (state : Ω → Q) (w : Q → ENNReal) (delta : ENNReal) :
    μ (referenceKeep μ state w delta)ᶜ ≤ delta * ∑' q, w q := by
  classical
  let E : Q → Set Ω := fun q =>
    if μ (state ⁻¹' {q}) < delta * w q then state ⁻¹' {q} else ∅
  have hsub : (referenceKeep μ state w delta)ᶜ ⊆ ⋃ q, E q := by
    intro p hp
    have hh : μ (state ⁻¹' {state p}) < delta * w (state p) := lt_of_not_ge hp
    apply mem_iUnion.mpr
    exact ⟨state p, by simp only [E, ite_eq_left hh, mem_preimage, mem_singleton_iff]⟩
  calc
    _ ≤ μ (⋃ q, E q) := measure_mono hsub
    _ ≤ ∑' q, μ (E q) := measure_iUnion_le E
    _ ≤ ∑' q, delta * w q := by
      apply ENNReal.tsum_le_tsum
      intro q
      dsimp only [E]
      split_ifs with h
      · exact h.le
      · simp
    _ = delta * ∑' q, w q := by rw [ENNReal.tsum_mul_left]

/-- A state is retained as a whole, so its restricted mass is either its
original mass or zero. -/
theorem reference_kept_state_mass {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (w : Q → ENNReal) (delta : ENNReal) (q : Q) :
    (μ.restrict (referenceKeep μ state w delta)) (state ⁻¹' {q}) =
      if delta * w q ≤ μ (state ⁻¹' {q}) then μ (state ⁻¹' {q}) else 0 := by
  classical
  rw [Measure.restrict_apply (hstate (measurableSet_singleton q))]
  by_cases hq : delta * w q ≤ μ (state ⁻¹' {q})
  · rw [ite_eq_left hq]
    congr 1
    apply inter_eq_left.mpr
    intro p hp
    change delta * w (state p) ≤ μ (state ⁻¹' {state p})
    have hpq : state p = q := hp
    simpa only [hpq] using hq
  · rw [ite_eq_right hq]
    have heq : state ⁻¹' {q} ∩ referenceKeep μ state w delta = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro p ⟨hp, hk⟩
      have hpq : state p = q := hp
      apply hq
      simpa only [referenceKeep, mem_ofPred_eq, hpq] using hk
    rw [heq, measure_empty]

/-- Earlier palette numerators become relative state ceilings after deleting
light states. The palette itself is unchanged. -/
theorem reference_pruned_palette_cap {Ω Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace V]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → V) (π : Measure V) (w : Q → ENNReal) (C delta : ENNReal)
    (hd0 : delta ≠ 0) (hdtop : delta ≠ ⊤)
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C * w q * π A) :
    ∀ q (A : Set V), MeasurableSet A →
      (μ.restrict (referenceKeep μ state w delta)) {p | state p = q ∧ control p ∈ A} ≤
        (C / delta) * (μ.restrict (referenceKeep μ state w delta)) (state ⁻¹' {q}) * π A := by
  intro q A hA
  let ρ := μ.restrict (referenceKeep μ state w delta)
  have hρ : ρ ≤ μ := Measure.restrict_le_self
  have hmass := reference_kept_state_mass μ state hstate w delta q
  by_cases hq : delta * w q ≤ μ (state ⁻¹' {q})
  · have heq : ρ (state ⁻¹' {q}) = μ (state ⁻¹' {q}) := by
      simpa only [ite_eq_left hq] using hmass
    have href : w q ≤ delta⁻¹ * ρ (state ⁻¹' {q}) := by
      rw [heq]
      calc
        w q = delta⁻¹ * (delta * w q) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hd0 hdtop, one_mul]
        _ ≤ delta⁻¹ * μ (state ⁻¹' {q}) := mul_le_mul_right hq _
    calc
      _ ≤ μ {p | state p = q ∧ control p ∈ A} := hρ _
      _ ≤ C * w q * π A := hcap q A hA
      _ ≤ C * (delta⁻¹ * ρ (state ⁻¹' {q})) * π A := by gcongr
      _ = _ := by dsimp only [ρ]; rw [div_eq_mul_inv]; ring
  · have heq : ρ (state ⁻¹' {q}) = 0 := by simpa only [ite_eq_right hq] using hmass
    calc
      _ ≤ ρ (state ⁻¹' {q}) := measure_mono (fun p hp => hp.1)
      _ = 0 := heq
      _ ≤ _ := zero_le

/-- The mass loss can be compared with any later success threshold before
turning the retained incidence law into a conditional law. -/
theorem reference_pruning_mass_budget {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (w : Q → ENNReal) (delta : ENNReal) :
    μ univ ≤ (μ.restrict (referenceKeep μ state w delta)) univ + delta * ∑' q, w q := by
  have hm := measurableSet_referenceKeep μ state hstate w delta
  calc
    _ = μ (referenceKeep μ state w delta) + μ (referenceKeep μ state w delta)ᶜ :=
      (measure_add_measure_compl hm).symm
    _ ≤ (μ.restrict (referenceKeep μ state w delta)) univ + delta * ∑' q, w q := by
      rw [Measure.restrict_apply_univ]
      exact add_le_add le_rfl (reference_light_mass_le μ state w delta)

/-- The palette numerator after reference pruning gives the actual conditional
velocity law, through the accepted discrete-state disintegration theorem. -/
theorem reference_pruned_conditional_palette {Ω Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → V) (hcontrol : Measurable control) (π : Measure V)
    (w : Q → ENNReal) (C delta : ENNReal) (hd0 : delta ≠ 0) (hdtop : delta ≠ ⊤)
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C * w q * π A) :
    ∀ᵐ q ∂(μ.restrict (referenceKeep μ state w delta)).map state,
      ProbabilityTheory.condDistrib control state (μ.restrict (referenceKeep μ state w delta)) q ≤
        (C / delta) • π := by
  apply Submission.Lib.K4ScalarActualSwitching.condDistrib_palette_le
    (μ.restrict (referenceKeep μ state w delta)) state hstate control hcontrol π (C / delta)
  exact reference_pruned_palette_cap μ state hstate control π w C delta hd0 hdtop hcap

/-- The retained state has actual separated velocity witnesses outside any
chosen null exception. This uses the original palette, with the same reference
weight cutoff used to pay for all deletions. -/
theorem reference_pruned_velocity_witnesses {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (velocity : Ω → ℝ) (π : Measure ℝ) (w : Q → ENNReal) (C delta : ENNReal)
    (hd0 : delta ≠ 0) (hdtop : delta ≠ ⊤)
    (hcap : ∀ q (A : Set ℝ), MeasurableSet A →
      μ {p | state p = q ∧ velocity p ∈ A} ≤ C * w q * π A)
    (q : Q) (G : Set Ω) (hG : ∀ᵐ p ∂μ.restrict (referenceKeep μ state w delta), p ∈ G)
    (r : ℝ) (pmax : ENNReal)
    (hthin : ∀ x : ℝ, π {v | |v - x| ≤ r} ≤ pmax)
    (hmass : ((C / delta) * (μ.restrict (referenceKeep μ state w delta)) (state ⁻¹' {q}) * pmax) +
      ((C / delta) * (μ.restrict (referenceKeep μ state w delta)) (state ⁻¹' {q}) * pmax) <
        (μ.restrict (referenceKeep μ state w delta)) (state ⁻¹' {q})) :
    ∃ p₀ p₁ p₂ : Ω, (state p₀ = q ∧ p₀ ∈ G) ∧ (state p₁ = q ∧ p₁ ∈ G) ∧
      (state p₂ = q ∧ p₂ ∈ G) ∧ r < |velocity p₀ - velocity p₁| ∧
        r < |velocity p₀ - velocity p₂| ∧ r < |velocity p₁ - velocity p₂| := by
  let ρ := μ.restrict (referenceKeep μ state w delta)
  let b := (C / delta) * ρ (state ⁻¹' {q}) * pmax
  have hrel := reference_pruned_palette_cap μ state hstate velocity π w C delta hd0 hdtop hcap
  have hthin' (x : ℝ) : ρ ((state ⁻¹' {q} ∩ G) ∩ {p | |velocity p - x| ≤ r}) ≤ b := by
    calc
      _ ≤ ρ {p | state p = q ∧ velocity p ∈ {v | |v - x| ≤ r}} :=
        measure_mono (fun p hp => ⟨hp.1.1, hp.2⟩)
      _ ≤ (C / delta) * ρ (state ⁻¹' {q}) * π {v | |v - x| ≤ r} :=
        hrel q _ (measurableSet_le (measurable_id.sub measurable_const).abs measurable_const)
      _ ≤ b := by dsimp [b]; gcongr; exact hthin x
  have hmass' : b + b < ρ (state ⁻¹' {q} ∩ G) := by
    rw [measure_inter_conull (ae_iff.mp hG)]
    exact hmass
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, h01, h02, h12⟩ :=
    Submission.Lib.K4HorizontalCoercivity.exists_three_velocity_witnesses
      ρ (state ⁻¹' {q} ∩ G) velocity r b hthin' hmass'
  exact ⟨p₀, p₁, p₂, hp₀, hp₁, hp₂, h01, h02, h12⟩

end
end Submission.Lib.K4ReferencePruning
