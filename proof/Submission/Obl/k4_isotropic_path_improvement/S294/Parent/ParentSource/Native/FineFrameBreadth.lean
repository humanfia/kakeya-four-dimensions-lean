-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineFrameBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineFrameBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineFrameBreadth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineFrameBreadth.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineConditionalPalette
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFrameChange

/-! Intrinsic broadness of an original deeper history supplies strip
thinness in the ACTUAL intermediate native unit-base velocity frame.
A genuine final-state full-prior floor is the only relative denominator. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal RealInnerProductSpace

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.final_fine_native_cube_strip_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (b f fine : Fin p.C) (hb : F.active b) (hf : p.lev f = stop) (hfγ : p.γ f = p.γ b)
    {r fraction width : ℝ} (hfraction : 0 ≤ fraction) (hwidth : 0 ≤ width)
    (hscale : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ r)
    (he : F.coding.code f ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b)
    (hretained : F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)))
    (J : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hJ : J ⊆ F.fineOriginalEvent b f univ)
    (δ : ENNReal) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞)
    (hfloor : δ * (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
      d.ν k (p.γ f) (p.A f)) ≤ ((d.ν k (p.γ b)).prod volume) J)
    (n center : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) :
    ((d.ν k (p.γ b)).prod volume) {x | x ∈ J ∧
      |inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity fine x - center)| ≤ width} ≤
      (δ⁻¹ * ENNReal.ofReal (8 * fraction)) * ((d.ν k (p.γ b)).prod volume) J := by
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hF (t : Fin p.C) : MeasurableSet (p.F t) :=
    (hp.2.2.2.2.2.2.2 t).2.2.2.2.2.2.2.2.2.1
  obtain ⟨normal, offset, hnormal, hsub⟩ := hp.native_cube_velocity_strip_pullback hN
    b fine hwidth hscale n center hn
  have hcap := F.fine_conditional_palette_after_full_floor hd hp hHE hH b f hb hf hfγ
    J hJ δ hδ0 hδtop hfloor (affineStrip normal offset r) (measurableSet_affineStrip _ _ _)
  calc
    _ ≤ ((d.ν k (p.γ b)).prod volume)
        (J ∩ (p.normalizedVelocity b ⁻¹' affineStrip normal offset r)) :=
      measure_mono (fun x hx => ⟨hx.1, hsub hx.2⟩)
    _ ≤ δ⁻¹ * ((d.ν k (p.γ b)).prod volume) J *
        F.fineVelocityLaw b (F.coding.code f) (affineStrip normal offset r) := hcap
    _ ≤ δ⁻¹ * ((d.ν k (p.γ b)).prod volume) J * ENNReal.ofReal (8 * fraction) :=
      mul_le_mul' le_rfl (F.fine_strip_mass_le hF r fraction hfraction b hb _ he hretained normal _ hnormal)
    _ = _ := by ac_rfl

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
