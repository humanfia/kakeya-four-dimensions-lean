-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineOutputBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineOutputBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineOutputBreadth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineOutputBreadth.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineFrameBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.OutputReferenceEvents

/-! Fine histories may merge into one physical output state. Sum their
absolute intrinsic strip numerators against the compatible full-reference
sum, then use the SAME final output-state floor. No common fine palette
or hidden history component in the physical state is required. -/

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

theorem PaletteFamily.fine_native_cube_strip_numerator_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (b f fine : Fin p.C) (hb : F.active b) (hf : p.lev f = stop) (hfγ : p.γ f = p.γ b)
    {r fraction width : ℝ} (hfraction : 0 ≤ fraction) (hwidth : 0 ≤ width)
    (hscale : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ r)
    (he : F.coding.code f ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b)
    (hretained : F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)))
    (n center : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) :
    ((d.ν k (p.γ b)).prod volume) {x | x ∈ F.fineOriginalEvent b f univ ∧
      |inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity fine x - center)| ≤ width} ≤
      ENNReal.ofReal (8 * fraction) *
        (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) := by
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hF (t : Fin p.C) : MeasurableSet (p.F t) :=
    (hp.2.2.2.2.2.2.2 t).2.2.2.2.2.2.2.2.2.1
  obtain ⟨normal, offset, hnormal, hsub⟩ := hp.native_cube_velocity_strip_pullback hN
    b fine hwidth hscale n center hn
  calc
    _ ≤ ((d.ν k (p.γ b)).prod volume)
        (F.fineOriginalEvent b f (affineStrip normal offset r)) := by
      apply measure_mono
      intro x hx
      exact ⟨hx.1.1, hx.1.2.1, hsub hx.2⟩
    _ ≤ (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) *
        F.fineVelocityLaw b (F.coding.code f) (affineStrip normal offset r) :=
      F.fine_original_conditional_velocity_cap hd hp hHE hH b f hb hf hfγ _
        (measurableSet_affineStrip _ _ _)
    _ ≤ (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) *
        ENNReal.ofReal (8 * fraction) := mul_le_mul' le_rfl
          (F.fine_strip_mass_le hF r fraction hfraction b hb _ he hretained normal _ hnormal)
    _ = _ := mul_comm _ _

set_option maxHeartbeats 1000000 in
/-- One physical state can merge many original fine palettes. Its summed
output-reference floor is precisely the denominator required by breadth. -/
theorem PaletteFamily.final_output_native_cube_strip_cap {ι I : Type*} [Fintype ι]
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (b fine : Fin p.C) (hb : F.active b) (packet : ι → Fin p.C)
    (hf : ∀ j, p.lev (packet j) = stop) (hfγ : ∀ j, p.γ (packet j) = p.γ b)
    {r fraction width : ℝ} (hfraction : 0 ≤ fraction) (hwidth : 0 ≤ width)
    (hscale : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ r)
    (he : ∀ j, F.coding.code (packet j) ∉
      Q.intrinsicNarrowStates F.code stop F.U r fraction b)
    (hretained : ∀ j, F.coding.code (packet j) ∉
      fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)))
    (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hρ : ρ ≤ (d.ν k (p.γ b)).prod volume)
    (state : ((ℕ × (Fin 6 → ℝ)) × ℝ) → I) (menus : ι → Finset I)
    (hcover : ∀ᵐ x ∂ρ, ∃ j, x ∈ F.fineOriginalEvent b (packet j) univ)
    (hmenu : ∀ᵐ x ∂ρ, ∀ j, x ∈ F.fineOriginalEvent b (packet j) univ → state x ∈ menus j)
    (δ : ENNReal) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞) (label : I)
    (hfloor : δ * Submission.Lib.K4OutputReferenceMenus.outputReferenceWeight menus
        (fun j => ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
          d.ν k (p.γ (packet j)) (p.A (packet j))) label ≤ ρ {x | state x = label})
    (n center : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) :
    ρ {x | state x = label ∧
      |inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity fine x - center)| ≤ width} ≤
      (δ⁻¹ * ENNReal.ofReal (8 * fraction)) * ρ {x | state x = label} := by
  let Test := {x | |inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity fine x - center)| ≤ width}
  have hTest : MeasurableSet Test := by
    have hm : Measurable (fun x => (6 * p.κ)⁻¹ • p.normalizedVelocity fine x - center) :=
      ((p.measurable_normalizedVelocity fine).const_smul ((6 * p.κ)⁻¹)).sub_const center
    exact measurableSet_le ((measurable_const.inner hm).abs) measurable_const
  exact output_reference_relative_event_cap ((d.ν k (p.γ b)).prod volume) ρ hρ
    (fun j => F.fineOriginalEvent b (packet j) univ) state menus
    (fun j => ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
      d.ν k (p.γ (packet j)) (p.A (packet j))) (ENNReal.ofReal (8 * fraction)) δ hδ0 hδtop
    hcover hmenu Test hTest
    (fun j => F.fine_native_cube_strip_numerator_cap hd hp hHE hH b (packet j) fine hb
      (hf j) (hfγ j) hfraction hwidth hscale (he j) (hretained j) n center hn) label hfloor

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
