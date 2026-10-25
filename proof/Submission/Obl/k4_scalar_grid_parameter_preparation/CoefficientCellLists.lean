import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientPriorCaps
import Submission.Obl.k4_scalar_grid_parameter_preparation.PaletteScaledCellCount
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarScalePackets
import Submission.Obl.k4_scalar_grid_parameter_preparation.PhysicalSupportCover

/-! Current entry floors and original palette caps bound the coefficient list in a physical cell. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical ENNReal

theorem coefficient_grid_image_finite {X : Type*}
    (a : X → Fin 5 → ℝ) (E : Set (X × ℝ)) (ξ B : ℝ) (hξ : 0 < ξ)
    (hbounded : ∀ z ∈ E, ∀ e, |a z.1 e| ≤ B) :
    ((fun l => scalarMixedCoefficientTag ξ ξ (a l)) '' (Prod.fst '' E)).Finite := by
  classical
  let D := Finset.Icc (⌊-B / ξ⌋ : ℤ) ⌊B / ξ⌋
  let F : Finset (Fin 5 → ℤ) := Fintype.piFinset (fun _ => D)
  apply F.finite_toSet.subset
  rintro b ⟨l,⟨z,hz,rfl⟩,rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro e
  have hb := abs_le.mp (hbounded z hz e)
  dsimp only [scalarMixedCoefficientTag]
  simp only [ite_self]
  exact Finset.mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right hb.1 hξ.le),
    Int.floor_mono (div_le_div_of_nonneg_right hb.2 hξ.le)⟩

theorem coefficient_cell_list_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ)) [IsFiniteMeasure μ] (θ : Measure X)
    (π : Measure ℝ) [IsFiniteMeasure π] (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (E : Set (X × ℝ)) (hE : MeasurableSet E) (ξ B α β C : ℝ)
    (hξ : 0 < ξ) (hα : 0 < α) (hβ : 0 < β) (hC : 0 ≤ C)
    (hbounded : ∀ z ∈ E, ∀ e, |a z.1 e| ≤ B)
    (hprior : ∀ z ∈ E,
      ENNReal.ofReal β * π (scalarVelocityBin ξ ⌊a z.1 1 / ξ⌋) ≤
        θ {l | scalarMixedCoefficientTag ξ ξ (a l) = scalarMixedCoefficientTag ξ ξ (a z.1)})
    (hentry : ∀ (q : Fin 3 → ℤ) (b : Fin 5 → ℤ),
      E ∩ {z | physicalScalarGridTag ξ (scalarPacketPosition a z) = q ∧
        scalarMixedCoefficientTag ξ ξ (a z.1) = b} = ∅ ∨
      ENNReal.ofReal α * θ {l | scalarMixedCoefficientTag ξ ξ (a l) = b} ≤
        μ (E ∩ {z | physicalScalarGridTag ξ (scalarPacketPosition a z) = q ∧
          scalarMixedCoefficientTag ξ ξ (a z.1) = b}))
    (hcap : ∀ (q : Fin 3 → ℤ) (c : ℤ),
      μ (E ∩ {z | physicalScalarGridTag ξ (scalarPacketPosition a z) = q ∧
        (⌊a z.1 1 / ξ⌋ : ℤ) = c}) ≤ ENNReal.ofReal C * π (scalarVelocityBin ξ c)) :
    ∀ (q : Fin 3 → ℤ) (c : ℤ),
      {b : Fin 5 → ℤ | μ (E ∩ {z | physicalScalarGridTag ξ (scalarPacketPosition a z) = q ∧
        (⌊a z.1 1 / ξ⌋ : ℤ) = c ∧ scalarMixedCoefficientTag ξ ξ (a z.1) = b}) ≠ 0}.Finite ∧
      ({b : Fin 5 → ℤ | μ (E ∩ {z | physicalScalarGridTag ξ (scalarPacketPosition a z) = q ∧
        (⌊a z.1 1 / ξ⌋ : ℤ) = c ∧ scalarMixedCoefficientTag ξ ξ (a z.1) = b}) ≠ 0}.ncard : ℝ) ≤
          C / (α * β) := by
  classical
  let code := fun l : X => scalarMixedCoefficientTag ξ ξ (a l)
  let phys := fun z : X × ℝ => physicalScalarGridTag ξ (scalarPacketPosition a z)
  let vel := fun z : X × ℝ => (⌊a z.1 1 / ξ⌋ : ℤ)
  have hmcode : Measurable code := (measurable_scalarMixedCoefficientTag ξ ξ).comp ha
  have hmphys : Measurable phys := by
    apply Measurable.of_eval
    intro e
    dsimp only [phys,physicalScalarGridTag]
    have hh := measurable_scalarPacketPosition ha
    fun_prop
  have hmvel : Measurable vel := by dsimp only [vel]; fun_prop
  have hcoeff : (code '' (Prod.fst '' E)).Finite :=
    coefficient_grid_image_finite a E ξ B hξ hbounded
  intro q c
  let region := E ∩ {z | phys z = q ∧ vel z = c}
  let cells := fun b : Fin 5 → ℤ => E ∩ {z | phys z = q ∧ vel z = c ∧ code z.1 = b}
  let Q := {b : Fin 5 → ℤ | μ (cells b) ≠ 0}
  have hcell (b : Fin 5 → ℤ) : MeasurableSet (cells b) := hE.inter
    ((measurableSet_eq_fun hmphys measurable_const).inter
      ((measurableSet_eq_fun hmvel measurable_const).inter
        (measurableSet_eq_fun (hmcode.comp measurable_fst) measurable_const)))
  have hwitness (b : Fin 5 → ℤ) (hb : b ∈ Q) : ∃ z ∈ E,
      phys z = q ∧ vel z = c ∧ code z.1 = b := by
    obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hb
    exact ⟨z,hz.1,hz.2⟩
  have hQ : Q.Finite := hcoeff.subset (by
    intro b hb
    obtain ⟨z,hz,hphys,hvel,hcode⟩ := hwitness b hb
    exact ⟨z.1,⟨z,hz,rfl⟩,hcode⟩)
  have hcover (b) (hb : b ∈ Q) : cells b ⊆ region := fun z hz => ⟨hz.1,hz.2.1,hz.2.2.1⟩
  have hcap' : μ region ≤ ENNReal.ofReal C * π (scalarVelocityBin ξ c) := hcap q c
  refine ⟨hQ,?_⟩
  change (Q.ncard : ℝ) ≤ C / (α * β)
  by_cases hp : π (scalarVelocityBin ξ c) = 0
  · have hQzero : Q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      have hh := (measure_mono (hcover b hb)).trans hcap'
      rw [hp,mul_zero] at hh
      exact hb (le_antisymm hh bot_le)
    rw [hQzero,Set.ncard_empty,Nat.cast_zero]
    exact div_nonneg hC (mul_pos hα hβ).le
  have hfloor (b) (hb : b ∈ hQ.toFinset) :
      ENNReal.ofReal (α * β) * π (scalarVelocityBin ξ c) ≤ μ (cells b) := by
    have hbQ := hQ.mem_toFinset.mp hb
    obtain ⟨z,hz,hzphys,hzvel,hzcode⟩ := hwitness b hbQ
    have hpr := hprior z hz
    change ENNReal.ofReal β * π (scalarVelocityBin ξ (vel z)) ≤ θ {l | code l = code z.1} at hpr
    rw [hzvel,hzcode] at hpr
    have hb₁ : b 1 = c := by
      have hh := congrFun hzcode 1
      change (⌊a z.1 1 / ξ⌋ : ℤ) = b 1 at hh
      exact hh.symm.trans hzvel
    have heq : E ∩ {z | phys z = q ∧ code z.1 = b} = cells b := by
      apply Set.Subset.antisymm
      · intro z' hz'
        have hv : vel z' = c := by
          have hh := congrFun hz'.2.2 1
          change (⌊a z'.1 1 / ξ⌋ : ℤ) = b 1 at hh
          exact hh.trans hb₁
        exact ⟨hz'.1,hz'.2.1,hv,hz'.2.2⟩
      · intro z' hz'
        exact ⟨hz'.1,hz'.2.1,hz'.2.2.2⟩
    rcases hentry q b with hempty | hent
    · have hz' : z ∈ cells b := ⟨hz,hzphys,hzvel,hzcode⟩
      rw [← heq,hempty] at hz'
      exact False.elim hz'
    · change ENNReal.ofReal α * θ {l | code l = b} ≤ μ (E ∩ {z | phys z = q ∧ code z.1 = b}) at hent
      rw [heq] at hent
      calc
        _ = ENNReal.ofReal α * (ENNReal.ofReal β * π (scalarVelocityBin ξ c)) := by
          rw [ENNReal.ofReal_mul hα.le,mul_assoc]
        _ ≤ ENNReal.ofReal α * θ {l | code l = b} := mul_le_mul' le_rfl hpr
        _ ≤ _ := hent
  have hdisj : (↑hQ.toFinset : Set (Fin 5 → ℤ)).PairwiseDisjoint cells := by
    intro b hb b' hb' hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hne (hz.2.2.2.symm.trans hz'.2.2.2)
  rw [Set.ncard_eq_toFinset_card _ hQ]
  exact palette_scaled_old_cell_count μ hQ.toFinset cells hdisj (fun b _ => hcell b)
    region (fun b hb => hcover b (hQ.mem_toFinset.mp hb)) (α * β) C (mul_pos hα hβ) hC
    (π (scalarVelocityBin ξ c)) hp (measure_ne_top π _) hfloor hcap'

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
