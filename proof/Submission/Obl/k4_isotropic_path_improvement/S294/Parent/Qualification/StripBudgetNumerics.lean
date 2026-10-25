-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.StripBudgetNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/StripBudgetNumerics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalStripPriorBudget

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

noncomputable section

/-- Choose the actual time partition and retain only one inverse coarse
width in its visit budget. No central coefficient bound occurs. -/
theorem exists_strip_partition {H ρ : ℝ} (hH : 1 ≤ H) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ D : ℕ, 1 ≤ D ∧ 3*H ≤ (D:ℝ)*ρ ∧ (D:ℝ)+1 ≤ 5*H/ρ := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  let D := ⌈3*H/ρ⌉₊
  have hD : 1 ≤ D := Nat.ceil_pos.mpr (by positivity)
  have hlo : 3*H ≤ (D:ℝ)*ρ := (div_le_iff₀ hρ).mp (Nat.le_ceil (3*H/ρ))
  have hhi : (D:ℝ) < 3*H/ρ+1 := Nat.ceil_lt_add_one (by positivity)
  have hr : 1 ≤ H/ρ := (one_le_div hρ).mpr (hρ1.trans hH)
  refine ⟨D,hD,hlo,?_⟩
  simp only [mul_div_assoc] at hhi ⊢
  linarith only [hhi,hr]

/-- Actual graph accuracy and fine-state rounding control the number of
normal strips at every tested width. The coarse width cancels after
multiplying the support-prior pruning threshold. -/
theorem strip_visit_bound_le {D : ℕ} {ρ b B error L H width : ℝ}
    (hρ : 0 < ρ) (hw : 0 < width) (hH : 0 ≤ H)
    (hD : (D:ℝ)+1 ≤ 5*H/ρ)
    (hB : 0 ≤ B) (hb : 0 ≤ b) (he : 0 ≤ error) (hL : 0 ≤ L)
    (hround : (1+3*B)*b ≤ width)
    (hgraph : error*ρ ≤ width) (hrow : L*H*ρ^2 ≤ width) :
    stripVisitBound D ρ b B error (4*L*ρ) H width ≤ (300*7^8*H)/ρ := by
  have hinner : 2*(2*((1+3*B)*b)+(error+3*(4*L*ρ)*H)*(2*ρ))/width+4 ≤ 60 := by
    have hn : 2*((1+3*B)*b)+(error+3*(4*L*ρ)*H)*(2*ρ) ≤ 28*width := by
      nlinarith only [hround,hgraph,hrow]
    have hh : 2*(2*((1+3*B)*b)+(error+3*(4*L*ρ)*H)*(2*ρ))/width ≤ 56 :=
      (div_le_iff₀ hw).mpr (by nlinarith only [hn])
    linarith only [hh]
  unfold stripVisitBound
  calc
    _ ≤ (5*H/ρ)*7^4*7^4*60 := by
      gcongr
    _ = (300*7^8*H)/ρ := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
