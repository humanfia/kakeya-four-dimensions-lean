-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CanonicalCellIncidenceCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/CanonicalCellIncidenceCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.MovingRectanglePaletteCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomBlockVisits

/-! # Current canonical-cell caps from original moving rectangles

Only four central jets bound the moving center. All absolute intercepts remain
unrestricted. The original palette event and original incidence law are fixed.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal
noncomputable section

/-- Read the exact original box occupied by one canonical zoom cell. -/
theorem canonical_zoom_cell_original_box (c : Fin 7 → ℝ) {ρ s t : ℝ}
    (hρ : 0 < ρ) (hs : 0 < s) (world : Fin 7 → ℤ) (cell : Fin 4 → ℤ)
    (_hworld : parameterCode ρ c=world)
    (hcell : Submission.Lib.K4CommonLocalChoice.cell s
      (zpos (zoomCoefficients ρ (parameterCenter ρ world) c) t)=cell) :
    t∈Icc (s*(cell 0 : ℝ)) (s*(cell 0 : ℝ)+s) ∧
      ∀ i : Fin 3, zpos c t i.succ∈
        Icc (zpos (parameterCenter ρ world) t i.succ+ρ*(s*(cell i.succ : ℝ)))
          (zpos (parameterCenter ρ world) t i.succ+ρ*(s*(cell i.succ : ℝ))+ρ*s) := by
  have hfloor (i : Fin 4) :
      zpos (zoomCoefficients ρ (parameterCenter ρ world) c) t i ∈
        Icc (s*(cell i : ℝ)) (s*(cell i : ℝ)+s) := by
    have heq : (⌊zpos (zoomCoefficients ρ (parameterCenter ρ world) c) t i/s⌋ : ℤ)=cell i :=
      congrFun hcell i
    have hlo := (le_div_iff₀ hs).mp (Int.floor_le
      (zpos (zoomCoefficients ρ (parameterCenter ρ world) c) t i/s))
    have hhi := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one
      (zpos (zoomCoefficients ρ (parameterCenter ρ world) c) t i/s))
    rw [heq] at hlo hhi
    constructor <;> nlinarith
  refine ⟨hfloor 0,?_⟩
  intro i
  have heq : zpos (zoomCoefficients ρ (parameterCenter ρ world) c) t i.succ =
      (zpos c t i.succ-zpos (parameterCenter ρ world) t i.succ)/ρ := by
    fin_cases i
    · exact zx_zoom ρ (parameterCenter ρ world) c t
    · exact congrFun (zy_zoom ρ (parameterCenter ρ world) c t) 0
    · exact congrFun (zy_zoom ρ (parameterCenter ρ world) c t) 1
  have hh := hfloor i.succ
  rw [heq] at hh
  have hlo := (le_div_iff₀ hρ).mp hh.1
  have hhi := (div_le_iff₀ hρ).mp hh.2
  constructor <;> nlinarith

/-- Actual current canonical cells satisfy the required time-times-area
profile ceiling whenever the original short rectangles do. -/
theorem canonical_cell_incidence_palette_cap {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ))
    {ρ s base H C amplitude : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hbase : 0 < base) (hbs : base ≤ s) (hH : 1 ≤ H)
    (_hC : 0 ≤ C) (_hamp : 0 ≤ amplitude)
    (hsmall : 3*(H+ρ)*base ≤ ρ*s)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hjets : ∀ z∈E, |c z.1 1|≤H ∧ |c z.1 2|≤H ∧ |c z.1 4|≤H ∧ |c z.1 6|≤H)
    (π : (Fin 2 → ℤ) → ENNReal)
    (hrect : ∀ τ (Y : Fin 3 → ℝ) v,
      μ {z | z∈E ∧ z.2∈Icc τ (τ+base) ∧
        (∀ i : Fin 3, zpos (c z.1) z.2 i.succ∈Icc (Y i) (Y i+3*(ρ*s))) ∧
        parameterCode (ρ*s) (zv (c z.1))=v} ≤
          ENNReal.ofReal (C*base*(ρ*s)^2*amplitude)*π v) :
    ∀ world cell v,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ s z=cell ∧ parameterCode (ρ*s) (zv (c z.1))=v} ≤
          ENNReal.ofReal ((4*C)*s*(ρ*s)^2*amplitude)*π v := by
  classical
  intro world cell v
  let Box := {z : Λ × ℝ | parameterCode ρ (c z.1)=world ∧
    canonicalZoomCell c ρ s z=cell ∧ parameterCode (ρ*s) (zv (c z.1))=v}
  have hv : Measurable (fun z : Λ × ℝ => parameterCode (ρ*s) (zv (c z.1))) := by
    apply (measurable_parameterCode (ρ*s)).comp
    unfold zv
    fun_prop
  have hBox : MeasurableSet Box :=
    (((measurable_parameterCode ρ).comp (hc.comp measurable_fst))
      (measurableSet_singleton world)).inter
      (((measurable_canonicalZoomCell hc ρ s) (measurableSet_singleton cell)).inter
        (hv (measurableSet_singleton v)))
  rw [Measure.restrict_apply hBox]
  by_cases hne : (Box ∩ E).Nonempty
  · obtain ⟨z₀,hz₀⟩ := hne
    let cen := parameterCenter ρ world
    have hcenter (i : Fin 7) (hi : |c z₀.1 i|≤H) : |cen i|≤H+ρ := by
      have hd := original_parameter_center_distance ρ hρ (c z₀.1) i
      rw [hz₀.1.1] at hd
      have hh := abs_sub_le (cen i) (c z₀.1 i) 0
      rw [sub_zero,sub_zero,abs_sub_comm (cen i) (c z₀.1 i)] at hh
      linarith
    have hj : |cen 1|≤H+ρ ∧ |cen 2|≤H+ρ ∧ |cen 4|≤H+ρ ∧ |cen 6|≤H+ρ :=
      ⟨hcenter 1 (hjets z₀ hz₀.2).1,hcenter 2 (hjets z₀ hz₀.2).2.1,
        hcenter 4 (hjets z₀ hz₀.2).2.2.1,hcenter 6 (hjets z₀ hz₀.2).2.2.2⟩
    have hHρ : 1≤H+ρ := by linarith
    let center := fun t (i : Fin 3) => zpos cen t i.succ
    let offset := fun i : Fin 3 => ρ*(s*(cell i.succ : ℝ))
    have hmotion : ∀ t∈Icc (0 : ℝ) 1, ∀ t'∈Icc (0 : ℝ) 1, ∀ i,
        |center t i-center t' i| ≤ (3*(H+ρ))*|t-t'| := by
      intro t ht t' ht' i
      have hh := original_parameter_world_position_comparison_of_jets cen cen 0 (H+ρ)
        t t' (by norm_num) hHρ ht ht' (fun j => by simp) hj
      have hc' := (norm_le_pi_norm (zpos cen t-zpos cen t') i.succ).trans hh
      simpa only [Pi.sub_apply,Real.norm_eq_abs,add_zero] using hc'
    have hh := Qualification.moving_rectangle_palette_cap (t₀ := s*(cell 0 : ℝ)) μ E Prod.snd
      (fun z i => zpos (c z.1) z.2 i.succ)
      (fun z => parameterCode (ρ*s) (zv (c z.1))) v center offset hbase hs hbs
      (by positivity : 0 ≤ 3*(H+ρ)) hsmall ht hmotion
      (ENNReal.ofReal (C*base*(ρ*s)^2*amplitude)*π v)
      (fun τ Y => hrect τ Y v)
    have hgeom : Box ∩ E ⊆ {z : Λ × ℝ | z∈E ∧
        z.2∈Icc (s*(cell 0 : ℝ)) (s*(cell 0 : ℝ)+s) ∧
        (∀ i, zpos (c z.1) z.2 i.succ∈Icc
          (center z.2 i+offset i) (center z.2 i+offset i+ρ*s)) ∧
        parameterCode (ρ*s) (zv (c z.1))=v} := by
      intro z hz
      have hcell : Submission.Lib.K4CommonLocalChoice.cell s
          (zpos (zoomCoefficients ρ (parameterCenter ρ world) (c z.1)) z.2)=cell := by
        simpa only [canonicalZoomCell,canonicalZoomCoefficients,hz.1.1] using hz.1.2.1
      have hg := canonical_zoom_cell_original_box (c z.1) hρ hs world cell hz.1.1 hcell
      exact ⟨hz.2,hg.1,hg.2,hz.1.2.2⟩
    apply ((measure_mono hgeom).trans hh).trans_eq
    rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*s/base)]
    congr 2
    field_simp [ne_of_gt hbase]
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,measure_empty]
    exact bot_le

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
