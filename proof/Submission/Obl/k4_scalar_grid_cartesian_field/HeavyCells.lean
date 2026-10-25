import Submission.Lib.K4ReferencePruning

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory
open Submission.Lib.K4ReferencePruning

/-- A single original event cap becomes relative to the retained whole cell.
Unlike a cap on every Borel velocity set, this applies directly to the frozen velocity-bin caps. -/
theorem reference_pruned_event_cap {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (weight : Q → ENNReal) {θ : ENNReal} (hθ : θ ≠ 0) (hθtop : θ ≠ ⊤)
    (q : Q) (E : Set Ω) (C p : ENNReal)
    (hcap : μ (code ⁻¹' {q} ∩ E) ≤ C * weight q * p) :
    (μ.restrict (referenceKeep μ code weight θ)) (code ⁻¹' {q} ∩ E) ≤
      (C / θ) * (μ.restrict (referenceKeep μ code weight θ)) (code ⁻¹' {q}) * p := by
  classical
  let η := μ.restrict (referenceKeep μ code weight θ)
  have hη : η ≤ μ := Measure.restrict_le_self
  have hmass := reference_kept_state_mass μ code hcode weight θ q
  by_cases hq : θ * weight q ≤ μ (code ⁻¹' {q})
  · have heq : η (code ⁻¹' {q}) = μ (code ⁻¹' {q}) := by simpa only [ite_eq_left hq] using hmass
    have hw : weight q ≤ θ⁻¹ * η (code ⁻¹' {q}) := by
      rw [heq]
      calc
        weight q = θ⁻¹ * (θ * weight q) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hθ hθtop, one_mul]
        _ ≤ _ := mul_le_mul' le_rfl hq
    calc
      _ ≤ μ (code ⁻¹' {q} ∩ E) := hη _
      _ ≤ C * weight q * p := hcap
      _ ≤ C * (θ⁻¹ * η (code ⁻¹' {q})) * p := mul_le_mul' (mul_le_mul' le_rfl hw) le_rfl
      _ = _ := by dsimp only [η]; rw [div_eq_mul_inv]; ac_rfl
  · have heq : η (code ⁻¹' {q}) = 0 := by simpa only [ite_eq_right hq] using hmass
    calc
      _ ≤ η (code ⁻¹' {q}) := measure_mono inter_subset_left
      _ = 0 := heq
      _ ≤ _ := bot_le

/-- A pruning budget of at most half a known mass floor leaves the other half. -/
theorem pruning_mass_floor {a total kept cost : ENNReal} (hatop : a ≠ ⊤)
    (hfloor : a + a ≤ total) (hbudget : total ≤ kept + cost) (hcost : cost ≤ a) :
    a ≤ kept :=
  ENNReal.le_of_add_le_add_right hatop
    (hfloor.trans (hbudget.trans (add_le_add le_rfl hcost)))

noncomputable def finiteCellKeep {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Q) (F : Finset Q) (θ : ENNReal) : Set Ω := by
  classical
  exact referenceKeep μ code (fun q => if q ∈ F then 1 else 0) θ

/-- Finite-cell pruning has one explicit original mass cost and preserves every original bin cap. -/
theorem finite_cell_pruning {Ω Q I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (F : Finset Q) (hF : ∀ᵐ p ∂μ, code p ∈ F)
    {θ : ENNReal} (hθ : θ ≠ 0) (hθtop : θ ≠ ⊤)
    (event : I → Set Ω) (prior : I → ENNReal) (C : ENNReal)
    (hcap : ∀ q i, μ (code ⁻¹' {q} ∩ event i) ≤ C * prior i) :
    MeasurableSet (finiteCellKeep μ code F θ) ∧
    μ univ ≤ (μ.restrict (finiteCellKeep μ code F θ)) univ + θ * F.card ∧
    (∀ q i, (μ.restrict (finiteCellKeep μ code F θ)) (code ⁻¹' {q} ∩ event i) ≤
      (C / θ) * (μ.restrict (finiteCellKeep μ code F θ)) (code ⁻¹' {q}) * prior i) := by
  classical
  let weight : Q → ENNReal := fun q => if q ∈ F then 1 else 0
  have hsum : ∑' q, weight q = F.card := by
    rw [tsum_eq_sum (s := F) (fun q hq => by simp [weight, hq])]
    simp [weight]
  refine ⟨measurableSet_referenceKeep μ code hcode weight θ, ?_, ?_⟩
  · simpa only [hsum, finiteCellKeep, weight] using reference_pruning_mass_budget μ code hcode weight θ
  · intro q i
    apply reference_pruned_event_cap μ code hcode weight hθ hθtop q (event i) C (prior i)
    by_cases hq : q ∈ F
    · simpa [weight, hq] using hcap q i
    · have hz : μ (code ⁻¹' {q}) = 0 := by
        apply measure_mono_null ?_ (ae_iff.mp hF)
        intro p hp
        have hpq : code p = q := hp
        change code p ∉ F
        simpa only [hpq] using hq
      have hzero : μ (code ⁻¹' {q} ∩ event i) = 0 := measure_mono_null inter_subset_left hz
      rw [hzero]
      exact bot_le

/-- The heavy-cell cut preserves a prescribed mass floor and all original event priors. -/
theorem finite_cell_pruning_with_mass_floor {Ω Q I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (F : Finset Q) (hF : ∀ᵐ p ∂μ, code p ∈ F)
    {θ a : ENNReal} (hθ : θ ≠ 0) (hθtop : θ ≠ ⊤) (hatop : a ≠ ⊤)
    (hfloor : a + a ≤ μ univ) (hcost : θ * F.card ≤ a)
    (event : I → Set Ω) (prior : I → ENNReal) (C : ENNReal)
    (hcap : ∀ q i, μ (code ⁻¹' {q} ∩ event i) ≤ C * prior i) :
    ∃ Keep : Set Ω, MeasurableSet Keep ∧ a ≤ (μ.restrict Keep) univ ∧
      ∀ q i, (μ.restrict Keep) (code ⁻¹' {q} ∩ event i) ≤
        (C / θ) * (μ.restrict Keep) (code ⁻¹' {q}) * prior i := by
  obtain ⟨hkeep, hbudget, hpalette⟩ := finite_cell_pruning μ code hcode F hF
    hθ hθtop event prior C hcap
  exact ⟨finiteCellKeep μ code F θ, hkeep,
    pruning_mass_floor hatop hfloor hbudget hcost, hpalette⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
