-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.StripCensusGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/StripCensusGeometry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripFilling
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NormalStripCensus

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Positive original cell mass has an actual witness on the fixed
reference event, even when null portions outside that event remain. -/
theorem witness_on_reference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {E A : Set Ω} (hfull : ∀ᵐ z ∂μ, z ∈ E) (hA : μ A ≠ 0) :
    ∃ z ∈ E, z ∈ A := by
  have heq : μ (A ∩ E)=μ A := measure_congr (hfull.mono fun z hz => by
    simp only [mem_inter_iff,hz,and_true])
  obtain ⟨z,hzA,hzE⟩ := nonempty_of_measure_ne_zero (heq.symm ▸ hA)
  exact ⟨z,hzE,hzA⟩

namespace PhysicalModel

def originalPoint (p : PhysicalModel) (z : Ev) : Fin 4 → ℝ :=
  originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2

def roundedPoint (p : PhysicalModel) (b : ℝ) (z : Ev) : Fin 4 → ℝ :=
  fun j => b*(p.physicalState b z j : ℝ)

theorem stripLabel_rounded (p : PhysicalModel) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (z : Ev) :
    p.stripLabel b ρ width row z =
      let C : Fin 4 → ℤ := fun j => ⌊p.roundedPoint b z j/ρ⌋
      (C,NormalStripCensus.strip (row C) width (p.roundedPoint b z)) := rfl

theorem stripLabel_coordinates (p : PhysicalModel) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) {z : Ev} {C : Fin 4 → ℤ} {n : ℤ}
    (hlabel : p.stripLabel b ρ width row z=(C,n)) :
    (∀ j, ⌊p.roundedPoint b z j/ρ⌋=C j) ∧
      NormalStripCensus.strip (row C) width (p.roundedPoint b z)=n := by
  rw [p.stripLabel_rounded] at hlabel
  dsimp only at hlabel
  have hC : (fun j => ⌊p.roundedPoint b z j/ρ⌋)=C := congrArg Prod.fst hlabel
  refine ⟨fun j => congrFun hC j,?_⟩
  have hh := congrArg Prod.snd hlabel
  simpa only [hC] using hh

theorem stripLabel_base_box (p : PhysicalModel) (b width : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (row : (Fin 4 → ℤ) → Fin 3 → ℝ)
    {z : Ev} {C : Fin 4 → ℤ} {n : ℤ}
    (hlabel : p.stripLabel b ρ width row z=(C,n)) (j : Fin 3) :
    |p.roundedPoint b z j.castSucc-ρ*(C j.castSucc : ℝ)| ≤ ρ :=
  ParentSource.physical_grid_corner_error hρ ((p.stripLabel_coordinates b ρ width row hlabel).1 _)

theorem stripLabel_normal_slab (p : PhysicalModel) (b ρ : ℝ)
    {width r center : ℝ} (hw : 0 < width)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ)
    {z : Ev} {C : Fin 4 → ℤ} {n : ℤ}
    (hlabel : p.stripLabel b ρ width row z=(C,n))
    (hrange : |width*(n : ℝ)-center|+width ≤ r) :
    |NormalStripCensus.normal (row C) (p.roundedPoint b z)-center| ≤ r := by
  have hbin := (p.stripLabel_coordinates b ρ width row hlabel).2
  have herr := ParentSource.physical_grid_corner_error hw hbin
  exact (abs_sub_le _ (width*(n : ℝ)) _).trans (by linarith only [herr,hrange])

/-- Aligned base offsets make the filled base-cell label a function of
the joint physical code. Neither a fresh witness nor a new state split
is needed for this projection. -/
theorem assigned_code_of_physical_code (p : PhysicalModel) (b : ℝ)
    {ρ width : ℝ} (hρ : 0 < ρ) (hw : 0 < width)
    (corner : Fin 3 → ℝ) (offset : Fin 3 → ℤ)
    (hcorner : ∀ j, corner j=width*(offset j : ℝ)) (z : Ev) :
    NativeAssigned.code ρ b (width/ρ) corner (p.physicalState b z) =
      (fun j => (ShearedSupport.code width (p.roundedPoint b z)).1 j-offset j) := by
  funext j
  change ⌊((p.roundedPoint b z j.castSucc-corner j)/ρ)/(width/ρ)⌋ = _
  have heq : ((p.roundedPoint b z j.castSucc-corner j)/ρ)/(width/ρ) =
      p.roundedPoint b z j.castSucc/width-(offset j : ℝ) := by
    rw [hcorner j]
    field_simp
    <;> ring
  rw [heq,Int.floor_sub_intCast]
  rfl

theorem rounded_code_at_base (p : PhysicalModel) {b : ℝ} (hb : 0 < b) (z : Ev) :
    ShearedSupport.code b (p.roundedPoint b z)=ShearedSupport.code b (p.originalPoint z) := by
  apply Prod.ext
  · funext j
    simp [ShearedSupport.code,roundedPoint,physicalState,originalPoint,hb.ne']
  · simp [ShearedSupport.code,roundedPoint,physicalState,originalPoint,hb.ne']

/-- All tested dyadic codes are exactly the original physical codes.
Rounding first at the fixed state mesh introduces no further ambiguity. -/
theorem rounded_code_dyadic (p : PhysicalModel) {b : ℝ} (hb : 0 < b)
    (steps : ℕ) (z : Ev) :
    ShearedSupport.code (b*(2:ℝ)^steps) (p.roundedPoint b z)=
      ShearedSupport.code (b*(2:ℝ)^steps) (p.originalPoint z) := by
  rw [ShearedSupport.code_dyadic_coarsens (p.roundedPoint b),
    ShearedSupport.code_dyadic_coarsens p.originalPoint,p.rounded_code_at_base hb]

/-- Every positive base cell furnished by the original MK3 filling has
a witness in the same preceding event and the same original strip. -/
theorem strip_filling_witness (p : PhysicalModel)
    (μ : Measure Ev) {E : Set Ev} (hfull : ∀ᵐ z ∂μ, z ∈ E)
    (b ρ width : ℝ) (row : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (g : (Fin 4 → ℤ) × ℤ) (q : Fin 3 → ℤ)
    (hpositive : (μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {g}))
      {z | NativeAssigned.code ρ b (width/ρ) (fun j => ρ*(g.1 j.castSucc : ℝ))
        (p.physicalState b z)=q} ≠ 0) :
    ∃ z ∈ E, p.stripLabel b ρ width row z=g ∧
      NativeAssigned.code ρ b (width/ρ) (fun j => ρ*(g.1 j.castSucc : ℝ))
        (p.physicalState b z)=q := by
  have hfull' : ∀ᵐ z ∂μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {g}),
      z ∈ E ∩ ((p.stripLabel b ρ width row) ⁻¹' {g}) := by
    filter_upwards [ae_mono Measure.restrict_le_self hfull,
      ae_restrict_mem ((p.measurable_stripLabel b ρ width row) (measurableSet_singleton g))]
      with z hz hg
    exact ⟨hz,hg⟩
  obtain ⟨z,⟨hz,hg⟩,hq⟩ := witness_on_reference _ hfull' hpositive
  exact ⟨z,hz,hg,hq⟩

end PhysicalModel

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
