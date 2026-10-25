-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeSelectedResidual, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeSelectedResidual.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeSelectedResidual.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeSelectedResidual.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeSelectedResidual.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeNarrowSelection

/-! The intrinsic narrow-state alternative constructs a measurable ORIGINAL
residual with a substantial floor and actual predicted-strip coverage. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ}
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
  {code : Fin p.C → ℕ} {stop : ℕ}
  {U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ))} {r fraction : ℝ}
  (P : NarrowPredictionFamily Q code stop U r fraction)

def NarrowPredictionFamily.residual (active : Fin p.C → Prop) (i : ℕ) :
    Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  Q.packetFamilyResidual i (Q.narrowHistoryFamily active stop U P.normal P.offset r
    (Q.intrinsicNarrowStates code stop U r fraction))

theorem NarrowPredictionFamily.residual_original_floor (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i : ℕ) (active : Fin p.C → Prop)
    (hcode : ∀ b, active b →
      (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      (Q.coarseLaw (p.lev b) (code b)).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ)
    (hU : ∀ b, active b → MeasurableSet (U b))
    (hUC : ∀ b, active b → U b ⊆ Q.coarseSupport (p.lev b) (code b))
    {mass : ℝ} (hfraction : 0 ≤ fraction)
    (hmass : ENNReal.ofReal mass ≤ Q.law (labelledSupport (Q.packetFamilyResidual i
      (Q.badHistoryFamily active code stop (Q.intrinsicNarrowStates code stop U r fraction))))) :
    (∀ w, MeasurableSet (P.residual active i w)) ∧
      (∀ w, P.residual active i w ⊆ H w) ∧
      ENNReal.ofReal ((p.κ⁻¹ / 8) * (fraction * mass)) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.residual active i w) ∧
      ∀ w x, x ∈ P.residual active i w → ∃ b, p.lev b = i ∧ p.γ b = w ∧ x ∈ p.F b ∧
        ∃ e ∈ Q.intrinsicNarrowStates code stop U r fraction b, active b ∧
          p.normalizedVelocity b x ∈ affineStrip (P.normal b e) (P.offset b e) r :=
  Q.narrow_residual_original_floor hd hp hHE i stop active code hcode U hU hUC
    P.normal P.offset r (Q.intrinsicNarrowStates code stop U r fraction) hfraction
    (fun b _ e he => P.strip_floor_ennreal hfraction b e he) hmass

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
