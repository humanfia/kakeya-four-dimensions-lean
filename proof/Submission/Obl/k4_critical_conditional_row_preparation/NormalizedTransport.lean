import Submission.Obl.k4_critical_conditional_row_preparation.Interfaces
import Submission.Obl.k4_critical_conditional_row_preparation.ClippedJointCap

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

/-- Floors of a measurable finite vector remain measurable. -/
theorem measurable_floor_vector {X ι : Type*} [MeasurableSpace X]
    (f : X → ι → ℝ) (hf : Measurable f) (a : ℝ) :
    Measurable (fun x i => ⌊f x i / a⌋) := by
  apply Measurable.of_eval
  intro i
  exact Int.measurable_floor.comp (((measurable_pi_apply i).comp hf).div_const a)

theorem measurable_rowPositionCode {α : Type*} [MeasurableSpace α]
    (ξ : ℝ) (b v : α → ℝ) (hb : Measurable b) (hv : Measurable v) :
    Measurable (rowPositionCode ξ b v) := by
  apply measurable_floor_vector
  apply Measurable.of_eval
  intro i
  fin_cases i <;> dsimp <;> fun_prop

/-- Arbitrary finite lists indexed by countable codes have measurable membership. -/
theorem measurableSet_list_membership {X Q V W : Type*} [MeasurableSpace X]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
    (q : X → Q) (v : X → V) (w : X → W)
    (hq : Measurable q) (hv : Measurable v) (hw : Measurable w)
    (lists : Q → V → Finset W) : MeasurableSet {x | w x ∈ lists (q x) (v x)} := by
  have hset : MeasurableSet {z : Q × V × W | z.2.2 ∈ lists z.1 z.2.1} :=
    (Set.to_countable _).measurableSet
  exact hset.preimage (hq.prodMk (hv.prodMk hw))

namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

def normalizedCurrent (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (σ : Measure (α × ℝ)) : Measure (α × ℝ) :=
  ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i))⁻¹ •
    σ.map (unitTimeMap (cfg.leftTime k s i) (cfg.timeLength k s))

def normalizedRow (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (row : α × ℝ → Fin 2 → ℝ) : α × ℝ → Fin 2 → ℝ :=
  row ∘ physicalTimeMap (cfg.leftTime k s i) (cfg.timeLength k s)

theorem measurable_normalizedRow (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (row : α × ℝ → Fin 2 → ℝ) (hr : Measurable row) :
    Measurable (cfg.normalizedRow k s i row) :=
  hr.comp (measurable_physicalTimeMap _ _)

theorem normalizedRow_unitTimeMap (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (row : α × ℝ → Fin 2 → ℝ) (p : α × ℝ) :
    cfg.normalizedRow k s i row (unitTimeMap (cfg.leftTime k s i) (cfg.timeLength k s) p) = row p := by
  apply congrArg row
  exact physicalTimeMap_unitTimeMap _ _ (by unfold timeLength; positivity) p

theorem AssignmentLevel.position_preimage_ae (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (σ : Measure (α × ℝ))
    (hσ : σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    ∀ᵐ p ∂σ, rowPositionCode (cfg.N k ^ (-(200 * s)))
        (cfg.clippedIntercept k s i) (cfg.clippedVelocity k s i)
        (unitTimeMap (cfg.leftTime k s i) (cfg.timeLength k s) p) =
      cfg.physicalPosition k s i p := by
  filter_upwards [a.clipped_coordinates_ae h i σ hσ] with p hp
  have heq : (cfg.b k p.1 0 + cfg.leftTime k s i * cfg.b k p.1 3 - cfg.horizontalOrigin k s i) /
      cfg.timeLength k s + ((p.2 - cfg.leftTime k s i) / cfg.timeLength k s) * cfg.b k p.1 3 =
      (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - cfg.horizontalOrigin k s i) / cfg.timeLength k s := by ring
  funext e
  fin_cases e <;> simp only [rowPositionCode, physicalPosition, unitTimeMap,
    Matrix.cons_val_zero, Matrix.cons_val_one, hp.1, hp.2, heq]

namespace PhysicalPreparation
variable {k : ℕ} {s η : ℝ} {source : Measure (α × ℝ)}
    (p : cfg.PhysicalPreparation k s η source)

/-- The row compatibility assertion is transported through continuous time. -/
theorem normalized_row_constraint (h : cfg.Valid) (a : cfg.AssignmentLevel k s) :
    ∀ᵐ y ∂cfg.normalizedCurrent k s p.index p.current,
      (∀ e, |cfg.normalizedRow k s p.index p.row y e| ≤ cfg.N k ^ η) ∧
      |cfg.normalizedRow k s p.index p.row y 0 + cfg.clippedVelocity k s p.index y.1 *
        cfg.normalizedRow k s p.index p.row y 1 - cfg.b k y.1 5| ≤ cfg.N k ^ η * cfg.N k ^ (-s) := by
  have hr := cfg.measurable_normalizedRow k s p.index p.row p.measurable_row
  have hv := (a.clipped_measurable h p.index).2
  have hb := (h.basic k).1
  have hset : MeasurableSet {y : α × ℝ |
      (∀ e, |cfg.normalizedRow k s p.index p.row y e| ≤ cfg.N k ^ η) ∧
      |cfg.normalizedRow k s p.index p.row y 0 + cfg.clippedVelocity k s p.index y.1 *
        cfg.normalizedRow k s p.index p.row y 1 - cfg.b k y.1 5| ≤ cfg.N k ^ η * cfg.N k ^ (-s)} := by
    have h₁ : MeasurableSet (⋂ e : Fin 2,
        {y : α × ℝ | |cfg.normalizedRow k s p.index p.row y e| ≤ cfg.N k ^ η}) :=
      MeasurableSet.iInter (fun e => measurableSet_le
        (((measurable_pi_apply e).comp hr).abs) measurable_const)
    have h₂ : MeasurableSet {y : α × ℝ |
        |cfg.normalizedRow k s p.index p.row y 0 + cfg.clippedVelocity k s p.index y.1 *
          cfg.normalizedRow k s p.index p.row y 1 - cfg.b k y.1 5| ≤ cfg.N k ^ η * cfg.N k ^ (-s)} :=
      measurableSet_le ((((measurable_pi_apply 0).comp hr).add
        ((hv.comp measurable_fst).mul ((measurable_pi_apply 1).comp hr))).sub
        (((measurable_pi_apply 5).comp hb).comp measurable_fst)).abs measurable_const
    convert h₁.inter h₂ using 1
    ext y
    simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
  apply Measure.ae_smul_measure
  apply (ae_map_iff (measurable_unitTimeMap _ _).aemeasurable hset).mpr
  filter_upwards [p.row_constraint, a.clipped_coordinates_ae h p.index p.current p.current_le_parent]
    with y hy hc
  simp only [cfg.normalizedRow_unitTimeMap]
  simpa only [unitTimeMap, hc.2] using hy

/-- Derivative lists survive the exact same-prior time normalization. -/
theorem normalized_lists (h : cfg.Valid) (a : cfg.AssignmentLevel k s)
    (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ)
    (hlists : ∀ᵐ y ∂source, y.1 ∈ cfg.B k s p.index →
      y.2 ∈ I (cfg.T k s) (cfg.j k s p.index) →
      ⌊cfg.b k y.1 5 / cfg.N k ^ (-s)⌋ ∈ lists (cfg.physicalPosition k s p.index y)
        ⌊cfg.b k y.1 3 / cfg.N k ^ (-(200 * s))⌋) :
    ∀ᵐ y ∂cfg.normalizedCurrent k s p.index p.current,
      ⌊cfg.b k y.1 5 / cfg.N k ^ (-s)⌋ ∈ lists
        (rowPositionCode (cfg.N k ^ (-(200 * s))) (cfg.clippedIntercept k s p.index)
          (cfg.clippedVelocity k s p.index) y)
        ⌊cfg.clippedVelocity k s p.index y.1 / cfg.N k ^ (-(200 * s))⌋ := by
  have hc := a.clipped_measurable h p.index
  have hb := (h.basic k).1
  have hset := measurableSet_list_membership
    (rowPositionCode (cfg.N k ^ (-(200 * s))) (cfg.clippedIntercept k s p.index)
      (cfg.clippedVelocity k s p.index))
    (fun y : α × ℝ => ⌊cfg.clippedVelocity k s p.index y.1 / cfg.N k ^ (-(200 * s))⌋)
    (fun y : α × ℝ => ⌊cfg.b k y.1 5 / cfg.N k ^ (-s)⌋)
    (measurable_rowPositionCode _ _ _ hc.1 hc.2)
    (Int.measurable_floor.comp ((hc.2.comp measurable_fst).div_const _))
    (Int.measurable_floor.comp ((((measurable_pi_apply 5).comp hb).comp measurable_fst).div_const _)) lists
  apply Measure.ae_smul_measure
  apply (ae_map_iff (measurable_unitTimeMap _ _).aemeasurable hset).mpr
  have hsupp : ∀ᵐ y ∂p.current,
      y ∈ cfg.B k s p.index ×ˢ I (cfg.T k s) (cfg.j k s p.index) :=
    (ae_restrict_mem ((a.fitted_measurable p.index).prod measurableSet_Icc)).filter_mono
      (MeasureTheory.ae_mono p.current_le_parent)
  have hl := hlists.filter_mono (MeasureTheory.ae_mono p.current_le_source)
  filter_upwards [hl, hsupp, a.position_preimage_ae h p.index p.current p.current_le_parent,
    a.clipped_coordinates_ae h p.index p.current p.current_le_parent] with y hy hs hz hc
  rw [hz]
  simpa only [unitTimeMap, hc.2] using hy hs.1 hs.2

/-- Conditioning ceilings are invariant under this affine time map and the
common original reference normalization. -/
theorem normalized_conditional_cap (h : cfg.Valid) (a : cfg.AssignmentLevel k s) :
    ∀ (q r : Fin 2 → ℤ) (v : ℤ),
      (cfg.normalizedCurrent k s p.index p.current) {y |
        rowPositionCode (cfg.N k ^ (-(200 * s))) (cfg.clippedIntercept k s p.index)
          (cfg.clippedVelocity k s p.index) y = q ∧
        (fun e => ⌊cfg.normalizedRow k s p.index p.row y e / cfg.N k ^ (-s)⌋) = r ∧
        ⌊cfg.clippedVelocity k s p.index y.1 / cfg.N k ^ (-(200 * s))⌋ = v} ≤
      ENNReal.ofReal (cfg.N k ^ η) *
        cfg.π k (Ico ((v : ℝ) * cfg.N k ^ (-(200 * s)))
          (((v : ℝ) + 1) * cfg.N k ^ (-(200 * s)))) *
        (cfg.normalizedCurrent k s p.index p.current) {y |
          rowPositionCode (cfg.N k ^ (-(200 * s))) (cfg.clippedIntercept k s p.index)
            (cfg.clippedVelocity k s p.index) y = q ∧
          (fun e => ⌊cfg.normalizedRow k s p.index p.row y e / cfg.N k ^ (-s)⌋) = r} := by
  intro q r v
  let ξ := cfg.N k ^ (-(200 * s))
  let E := cfg.N k ^ (-s)
  let code := rowPositionCode ξ (cfg.clippedIntercept k s p.index) (cfg.clippedVelocity k s p.index)
  let row := cfg.normalizedRow k s p.index p.row
  let C : Set (α × ℝ) := {y | code y = q ∧ (fun e => ⌊row y e / E⌋) = r}
  let V : Set (α × ℝ) := {y | ⌊cfg.clippedVelocity k s p.index y.1 / ξ⌋ = v}
  have hc := a.clipped_measurable h p.index
  have hr := cfg.measurable_normalizedRow k s p.index p.row p.measurable_row
  have hC : MeasurableSet C :=
    ((measurable_rowPositionCode ξ _ _ hc.1 hc.2) (measurableSet_singleton q)).inter
      ((measurable_floor_vector row hr E) (measurableSet_singleton r))
  have hV : MeasurableSet V := (Int.measurable_floor.comp
    ((hc.2.comp measurable_fst).div_const ξ)) (measurableSet_singleton v)
  let ψ : α × ℝ → α × ℝ := unitTimeMap (cfg.leftTime k s p.index) (cfg.timeLength k s)
  let W := cfg.timeLength k s * (cfg.ν k).real (cfg.A k s p.index)
  have hpreC : p.current (ψ ⁻¹' C) = p.current {y |
      cfg.physicalPosition k s p.index y = q ∧ (fun e => ⌊p.row y e / E⌋) = r} := by
    apply measure_congr
    filter_upwards [a.position_preimage_ae h p.index p.current p.current_le_parent] with y hy
    simp only [mem_preimage, C, mem_ofPred_eq, code, ψ, row]
    rw [hy, cfg.normalizedRow_unitTimeMap]
  have hpreCV : p.current (ψ ⁻¹' (C ∩ V)) = p.current {y |
      cfg.physicalPosition k s p.index y = q ∧ (fun e => ⌊p.row y e / E⌋) = r ∧
      ⌊cfg.b k y.1 3 / ξ⌋ = v} := by
    apply measure_congr
    filter_upwards [a.position_preimage_ae h p.index p.current p.current_le_parent,
      a.clipped_coordinates_ae h p.index p.current p.current_le_parent] with y hy heq
    simp only [mem_preimage, C, V, mem_inter_iff, mem_ofPred_eq, code, ψ, row]
    rw [hy, cfg.normalizedRow_unitTimeMap]
    simp only [unitTimeMap, heq.2, and_assoc]
  have hevent : {y : α × ℝ | code y = q ∧
      (fun e => ⌊row y e / E⌋) = r ∧ ⌊cfg.clippedVelocity k s p.index y.1 / ξ⌋ = v} = C ∩ V := by
    ext y
    simp only [C, V, mem_inter_iff, mem_ofPred_eq, and_assoc]
  change (cfg.normalizedCurrent k s p.index p.current) {y : α × ℝ | code y = q ∧
      (fun e => ⌊row y e / E⌋) = r ∧ ⌊cfg.clippedVelocity k s p.index y.1 / ξ⌋ = v} ≤
    _ * (cfg.normalizedCurrent k s p.index p.current) C
  rw [hevent]
  simp only [normalizedCurrent, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_unitTimeMap _ _) (hC.inter hV),
    Measure.map_apply (measurable_unitTimeMap _ _) hC]
  change ENNReal.ofReal W⁻¹ * p.current (ψ ⁻¹' (C ∩ V)) ≤
    _ * (ENNReal.ofReal W⁻¹ * p.current (ψ ⁻¹' C))
  rw [hpreCV, hpreC]
  calc
    _ ≤ ENNReal.ofReal W⁻¹ *
        (ENNReal.ofReal (cfg.N k ^ η) * cfg.π k (Ico ((v : ℝ) * ξ) (((v : ℝ) + 1) * ξ)) *
          p.current {y | cfg.physicalPosition k s p.index y = q ∧ (fun e => ⌊p.row y e / E⌋) = r}) :=
      mul_le_mul_of_nonneg_left (p.conditional_cap q r v) (zero_le : 0 ≤ ENNReal.ofReal W⁻¹)
    _ = _ := by ring

end PhysicalPreparation
end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
