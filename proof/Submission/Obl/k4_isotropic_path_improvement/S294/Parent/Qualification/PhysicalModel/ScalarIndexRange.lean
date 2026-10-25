-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ScalarIndexRange, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ScalarIndexRange.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripCensusGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ZoomScalar

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set

noncomputable section

theorem strip_indices_in_slab (N : Finset ℤ) {ρ width R a translation : ℝ}
    (hρ : 0 < ρ) (hw : 0 < width) (hwR : width ≤ ρ*R)
    (hwitness : ∀ n ∈ N, ∃ s : ℝ, s∈Icc a (a+R) ∧
      |ρ*s-(((n : ℝ)+1/2)*width+translation)| ≤ width) :
    ∀ n ∈ N, |width*(n : ℝ)-(ρ*(a+R/2)-translation)|+width ≤ 3*ρ*R := by
  intro n hn
  obtain ⟨s,hs,hfit⟩ := hwitness n hn
  have hlo := mul_le_mul_of_nonneg_left hs.1 hρ.le
  have hhi := mul_le_mul_of_nonneg_left hs.2 hρ.le
  have hmid : |ρ*s-ρ*(a+R/2)| ≤ ρ*R/2 := by
    rw [abs_le]
    constructor <;> nlinarith only [hlo,hhi]
  have hcorner : |width*(n : ℝ)-(ρ*(a+R/2)-translation)| ≤
      width+ρ*R/2+width/2 := by
    have heq : width*(n : ℝ)-(ρ*(a+R/2)-translation) =
        (((n : ℝ)+1/2)*width+translation-ρ*s)+(ρ*s-ρ*(a+R/2))-width/2 := by ring
    rw [heq]
    calc
      _ ≤ |(((n : ℝ)+1/2)*width+translation-ρ*s)+(ρ*s-ρ*(a+R/2))|+|width/2| := abs_sub _ _
      _ ≤ (|((n : ℝ)+1/2)*width+translation-ρ*s|+|ρ*s-ρ*(a+R/2)|)+|width/2| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (width+ρ*R/2)+width/2 := by
        rw [abs_of_pos (div_pos hw (by norm_num))]
        exact add_le_add (add_le_add (by simpa only [abs_sub_comm] using hfit) hmid) le_rfl
      _ = _ := by ring
  linarith only [hcorner,hwR]

/-- A scalar interval in one original coefficient world determines a
single normal slab containing every original strip that it meets.
The same slab then controls all preceding filling witnesses in those
strips, including witnesses at different times. -/
theorem original_scalar_strip_index_range (p : PhysicalModel)
    (E : Set Ev) (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ)
    {ρ b B η width R t a : ℝ}
    (hρ : 0 < ρ) (hb : 0 < b) (hw : 0 < width)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (ht : t∈Icc (0:ℝ) 1) (hwR : width ≤ ρ*R)
    (hsmall : 4*η*ρ+(1+3*B)*b ≤ width/2)
    (hdiam : ∀ l, (l,t)∈E → ∀ i, |p.scalarCoefficients l i-center i| ≤ ρ)
    (hrowB : ∀ C j, |row C j| ≤ B)
    (hrow : ∀ l, (l,t)∈E → ∀ i : Fin 2,
      |row (p.stripLabel b ρ width row (l,t)).1 i.succ-F t i| ≤ η)
    (C : Fin 4 → ℤ) (N : Finset ℤ)
    (hwitness : ∀ n∈N, ∃ l : Ln, (l,t)∈E ∧ p.stripLabel b ρ width row (l,t)=(C,n) ∧
      Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t∈Icc a (a+R)) :
    ∀ n∈N, |width*(n : ℝ)-
      (ρ*(a+R/2)-Jets2.coarseScalarTranslation (row C) center t)|+width ≤ 3*ρ*R := by
  apply strip_indices_in_slab N hρ hw hwR
  intro n hn
  obtain ⟨l,hl,hlabel,hscalar⟩ := hwitness n hn
  let s := Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t
  have hh := p.zoom_scalar_in_original_strip_ball (l,t) center F row
    ρ b B (width/ρ) width η hρ hb hw hB hη ht (by field_simp) hsmall
    (hdiam l hl) (hrowB _) (hrow l hl)
  rw [hlabel] at hh
  change s∈Metric.closedBall (((n : ℝ)+1/2)*width/ρ+
    Jets2.coarseScalarTranslation (row C) center t/ρ) (width/ρ) at hh
  rw [Metric.mem_closedBall,Real.dist_eq] at hh
  refine ⟨s,hscalar,?_⟩
  have heq : ρ*(s-(((n : ℝ)+1/2)*width/ρ+Jets2.coarseScalarTranslation (row C) center t/ρ)) =
      ρ*s-(((n : ℝ)+1/2)*width+Jets2.coarseScalarTranslation (row C) center t) := by
    field_simp
    <;> ring
  calc
    _ = ρ*|s-(((n : ℝ)+1/2)*width/ρ+Jets2.coarseScalarTranslation (row C) center t/ρ)| := by
      rw [←heq,abs_mul,abs_of_pos hρ]
    _ ≤ ρ*(width/ρ) := mul_le_mul_of_nonneg_left hh hρ.le
    _ = width := by field_simp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
