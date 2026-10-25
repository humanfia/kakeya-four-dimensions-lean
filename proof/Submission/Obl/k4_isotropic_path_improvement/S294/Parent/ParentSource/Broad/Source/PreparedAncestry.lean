-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.PreparedAncestry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/PreparedAncestry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/PreparedAncestry.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.CountedPruning
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PathBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePreparation

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native

noncomputable section

def originalFinePackets {W : ℕ} (p : PathData W) (old : Fin p.C) (mid : ℕ) : Finset (Fin p.C) := by
  classical
  exact Finset.univ.filter (fun b => p.lev b = mid ∧ p.γ b = p.γ old ∧ p.F b ⊆ p.F old)

section Path

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
  (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
    κ₁ m s δ₀ Mp Dp σ)

include hp

theorem Native.PathData.Valid.iterate_par_assignment (n : ℕ) :
    ∀ b : Fin p.C, n ≤ p.lev b → p.A b ⊆ p.A (p.par^[n] b) := by
  induction n with
  | zero => intro b _; simp
  | succ n ih =>
    intro b hn
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hparent⟩ := hch
    obtain ⟨hl, -, hA, -⟩ := hparent (by omega)
    rw [Function.iterate_succ_apply]
    exact hA.trans (ih (p.par b) (by omega))

/-- Prepared uniqueness identifies the actual ancestor, including the
closed-block endpoint issue already removed in the prepared base. -/
theorem Native.PreparedAngularPath.original_ancestor_of_common_incidence
    (old fine : Fin p.C) (hlev : p.lev old ≤ p.lev fine) (hγ : p.γ fine = p.γ old)
    (z : Ev) (hzbase : z ∈ Q.base (p.γ old)) (hzold : z ∈ p.F old) (hzfine : z ∈ p.F fine) :
    p.F fine ⊆ p.F old := by
  have hdiff : p.lev fine - p.lev old ≤ p.lev fine := Nat.sub_le _ _
  obtain ⟨hl, hg, hsub⟩ := Broad.iterate_par_spec hp.toOriginal
    (p.lev fine - p.lev old) fine hdiff
  change p.lev (p.par^[p.lev fine - p.lev old] fine) =
    p.lev fine - (p.lev fine - p.lev old) at hl
  change p.γ (p.par^[p.lev fine - p.lev old] fine) = p.γ fine at hg
  change p.F fine ⊆ p.F (p.par^[p.lev fine - p.lev old] fine) at hsub
  have hl' : p.lev (p.par^[p.lev fine - p.lev old] fine) = p.lev old := by omega
  have hg' : p.γ (p.par^[p.lev fine - p.lev old] fine) = p.γ old := hg.trans hγ
  have heq := Q.base_packet_unique (p.γ old) z hzbase old
    (p.par^[p.lev fine - p.lev old] fine) hl'.symm rfl hg' hzold (hsub hzfine)
  rwa [← heq] at hsub

theorem Native.PreparedAngularPath.mem_original_fine_packets
    (old fine : Fin p.C) (mid : ℕ) (hmid : p.lev old ≤ mid) (hfine : p.lev fine = mid)
    (hγ : p.γ fine = p.γ old) (z : Ev) (hzbase : z ∈ Q.base (p.γ old))
    (hzold : z ∈ p.F old) (hzfine : z ∈ p.F fine) :
    fine ∈ originalFinePackets p old mid := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfine, hγ,
    Q.original_ancestor_of_common_incidence hp old fine (by omega) hγ z hzbase hzold hzfine⟩

theorem Native.PreparedAngularPath.original_assignment_ancestor_of_common_incidence
    (old fine : Fin p.C) (hlev : p.lev old ≤ p.lev fine) (hγ : p.γ fine = p.γ old)
    (z : Ev) (hzbase : z ∈ Q.base (p.γ old)) (hzold : z ∈ p.F old) (hzfine : z ∈ p.F fine) :
    p.A fine ⊆ p.A old := by
  have hdiff : p.lev fine - p.lev old ≤ p.lev fine := Nat.sub_le _ _
  obtain ⟨hl, hg, hsub⟩ := Broad.iterate_par_spec hp.toOriginal
    (p.lev fine - p.lev old) fine hdiff
  change p.lev (p.par^[p.lev fine - p.lev old] fine) =
    p.lev fine - (p.lev fine - p.lev old) at hl
  change p.γ (p.par^[p.lev fine - p.lev old] fine) = p.γ fine at hg
  change p.F fine ⊆ p.F (p.par^[p.lev fine - p.lev old] fine) at hsub
  have hl' : p.lev (p.par^[p.lev fine - p.lev old] fine) = p.lev old := by omega
  have hg' : p.γ (p.par^[p.lev fine - p.lev old] fine) = p.γ old := hg.trans hγ
  have heq := Q.base_packet_unique (p.γ old) z hzbase old
    (p.par^[p.lev fine - p.lev old] fine) hl'.symm rfl hg' hzold (hsub hzfine)
  simpa only [← heq] using hp.iterate_par_assignment (p.lev fine - p.lev old) fine hdiff

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
