-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ScalarLocalCover, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ScalarLocalCover.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenScalarLocalCover.lean.
The bounded quadratic physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenScalarLocalCover.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.WorldCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.BoundedIntervalAD


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set Metric

noncomputable section

/-- Construct finite scalar covers from the counted ORIGINAL normal
strips, for the entire actual coefficient world. Actual coarse cells
and strip centres are constructed here, with all zoom errors included. -/
theorem scalar_local_cover_of_original_strips (p : PhysicalModel) (E : Set Ev)
    (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (ρ b B η width r R t a A d : ℝ)
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (hA : 0 ≤ A) (hR : 0 ≤ R) (hw : 0 < width)
    (ht : t ∈ Icc (0 : ℝ) 1) (hwr : width ≤ ρ * r)
    (hsmall : 4 * η * ρ + (1 + 3 * B) * b ≤ width / 2)
    (hdiam : ∀ l, (l,t) ∈ E → ∀ i, |p.scalarCoefficients l i - center i| ≤ ρ)
    (hrowB : ∀ C j, |row C j| ≤ B)
    (hrow : ∀ l, (l,t) ∈ E → ∀ i : Fin 2,
      |row (p.stripLabel b ρ width row (l,t)).1 i.succ - F t i| ≤ η)
    (hcount : ∀ C : Fin 4 → ℤ, ∀ N : Finset ℤ,
      (∀ n ∈ N, ∃ l : Ln, (l,t) ∈ E ∧ p.stripLabel b ρ width row (l,t) = (C,n) ∧
        Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t ∈ Icc a (a+R)) →
      (N.card : ℝ) ≤ A * ((ρ * R) / width) ^ d) :
    ∃ (m : ℕ) (c : Fin m → ℝ),
      {s | ∃ l : Ln, (l,t) ∈ E ∧
        Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t = s} ∩
          Icc a (a+R) ⊆ ⋃ j, closedBall (c j) r ∧
      (m : ℝ) ≤ ((27:ℝ)^4 * A) * ((ρ * R) / width) ^ d := by
  classical
  let scalar : Ln → ℝ := fun l =>
    Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t
  let active : Set Ln := {l | (l,t) ∈ E}
  obtain ⟨Q,hQ,hQknown⟩ := p.exists_parameter_world_coarse_cover active center ρ b t
    hρ hb hbρ ht (fun l hl => hdiam l hl)
  let lines : (Fin 4 → ℤ) → Set Ln := fun C =>
    {l | (l,t) ∈ E ∧ (p.stripLabel b ρ width row (l,t)).1 = C ∧ scalar l ∈ Icc a (a+R)}
  let code : Ln → ℤ := fun l => (p.stripLabel b ρ width row (l,t)).2
  let midpoint : (Fin 4 → ℤ) → ℤ → ℝ := fun C n =>
    ((n : ℝ) + 1 / 2) * width / ρ + Jets2.coarseScalarTranslation (row C) center t / ρ
  have hradius : width / ρ ≤ r := (div_le_iff₀ hρ).mpr (by simpa only [mul_comm] using hwr)
  have hfamily (C : Q) : ∃ (m : ℕ) (c : Fin m → ℝ),
      scalar '' lines C.val ⊆ ⋃ j, closedBall (c j) r ∧
        (m : ℝ) ≤ A * ((ρ * R) / width) ^ d := by
    apply finite_code_ball_cover (lines C.val) scalar code (midpoint C.val) r
      (A * ((ρ * R) / width) ^ d)
    · intro N hN
      apply hcount C.val N
      intro n hn
      obtain ⟨l,hl,hln⟩ := hN hn
      exact ⟨l,hl.1,Prod.ext hl.2.1 hln,hl.2.2⟩
    · intro l hl
      have hh := p.zoom_scalar_in_original_strip_ball (l,t) center F row
        ρ b B (width / ρ) width η hρ hb hw hB hη ht (by field_simp) hsmall
        (hdiam l hl.1) (hrowB _) (hrow l hl.1)
      change scalar l ∈ closedBall _ (width / ρ) at hh
      rw [hl.2.1] at hh
      exact closedBall_subset_closedBall hradius hh
  obtain ⟨m,c,hcover,hcard⟩ := finite_family_ball_cover
    (fun C : Q => scalar '' lines C.val) r (A * ((ρ * R) / width) ^ d) hfamily
  refine ⟨m,c,?_,?_⟩
  · rintro s ⟨⟨l,hl,hls⟩,hs⟩
    have hcoarse : (p.stripLabel b ρ width row (l,t)).1 ∈ Q := by
      rw [p.stripLabel_coarse]
      exact hQknown l hl
    apply hcover
    exact mem_iUnion.mpr ⟨⟨_,hcoarse⟩,l,⟨hl,rfl,by simpa only [scalar,hls] using hs⟩,hls⟩
  · calc
      (m : ℝ) ≤ (Q.card : ℝ) * (A * ((ρ * R) / width) ^ d) := by simpa using hcard
      _ ≤ (27:ℝ)^4 * (A * ((ρ * R) / width) ^ d) :=
        mul_le_mul_of_nonneg_right hQ
          (mul_nonneg hA (Real.rpow_nonneg (div_nonneg (mul_nonneg hρ.le hR) hw.le) _))
      _ = _ := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
