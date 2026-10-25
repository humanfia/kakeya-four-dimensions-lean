-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalPaletteRootBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDescendantReferences
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteCertificate

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open scoped ENNReal BigOperators

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

local instance (b : Fin p.C) : Decidable (F.active b) := Classical.propDecidable _

include hp

/-- Each palette supplier's deletion reference is bounded by that
ancestor's full original assignment and clock, without normalization. -/
theorem Native.PaletteFamily.original_source_mass_le_reference
    (root : Fin p.C) (hroot : F.active root) :
    ((d.ν k (p.γ root)).prod volume) {z | (p.γ root,z)∈F.U root} ≤
      d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹) := by
  calc
    _ ≤ ((d.ν k (p.γ root)).prod volume) (p.fullCylinder root) := measure_mono
      (fun z hz => hp.counted_subset_fullCylinder root
        (F.packet root hroot (p.γ root,z) (F.subset_coarse root hroot hz)).2)
    _ = _ := p.fullCylinder_mass (d.ν k (p.γ root)) root

/-- All active-root reference charges at one level sum to one original
budget. The number of roots and the path saturation never multiply it. -/
theorem Native.PaletteFamily.original_source_mass_sum_le_one
    (hd : d.Valid) :
    (∑ root : Fin p.C, if F.active root then ENNReal.ofReal (d.ω k (p.γ root))*
      ((d.ν k (p.γ root)).prod volume) {z | (p.γ root,z)∈F.U root} else 0) ≤ 1 := by
  classical
  have h := hp.full_reference_mass_le_one (hd.weights k).2.2 (hd.weights k).1 (hd.weights k).2.1 i
  apply le_trans (Finset.sum_le_sum (fun root _ => ?_)) h
  by_cases hroot : F.active root
  · have hl : p.lev root=i := F.level root hroot
    simp only [if_pos hroot,hl,ite_true]
    exact mul_le_mul' le_rfl (by
      simpa only [hl,mul_comm] using F.original_source_mass_le_reference hp root hroot)
  · simp only [if_neg hroot]
    exact zero_le

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
