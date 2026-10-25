-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.AncestorPackets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/AncestorPackets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SourceBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorPackets

open MeasureTheory Set
open ParentSource ParentSource.Native

noncomputable section

/-- The fixed ancestor of an actual supplied packet, defined without
looking at an incidence or selecting a new assignment. -/
def ancestor {W : ℕ} (p : PathData W) (b : Fin p.C) (level : ℕ) : Fin p.C :=
  p.par^[p.lev b - level] b

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hp

theorem ancestor_spec (b : Fin p.C) (level : ℕ) (hlevel : level ≤ p.lev b) :
    p.lev (ancestor p b level) = level ∧ p.γ (ancestor p b level) = p.γ b ∧
      p.A b ⊆ p.A (ancestor p b level) ∧ p.F b ⊆ p.F (ancestor p b level) := by
  obtain ⟨hl,hγ,hF⟩ := ParentSource.Broad.iterate_par_spec hp.toOriginal
    (p.lev b - level) b (Nat.sub_le _ _)
  change p.lev (ancestor p b level) = p.lev b - (p.lev b - level) at hl
  refine ⟨by omega,hγ,hp.iterate_par_assignment _ b (Nat.sub_le _ _),hF⟩

include Q

/-- The uniqueness mask already prepared on the original path identifies
both the packet and its unchanged full assignment with this fixed
ancestor. Closed dyadic endpoints have already been removed there. -/
theorem eq_ancestor_of_common_incidence (source target : Fin p.C)
    (hlevel : p.lev source ≤ p.lev target) (hworld : p.γ source = p.γ target)
    (x : Ev) (hx : x ∈ Q.base (p.γ target)) (hs : x ∈ p.F source) (ht : x ∈ p.F target) :
    source = ancestor p target (p.lev source) := by
  obtain ⟨hl,hγ,hA,hF⟩ := ancestor_spec hp target (p.lev source) hlevel
  exact Q.base_packet_unique (p.γ target) x hx source (ancestor p target (p.lev source))
    hl.symm hworld hγ hs (hF ht)

/-- A prepared occurrence in a descendant belongs to the fixed original
ancestor at every earlier supplied level. -/
theorem mem_ancestor (target : Fin p.C) (level : ℕ) (hlevel : level ≤ p.lev target)
    {x : Ev} (hx : x ∈ p.F target) : x ∈ p.F (ancestor p target level) :=
  (ancestor_spec hp target level hlevel).2.2.2 hx

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorPackets
