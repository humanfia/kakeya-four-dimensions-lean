-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineOriginalCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineOriginalCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineOriginalCaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineOriginalCaps.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineOriginalPosterior
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeSampling

/-! Original fine-packet palette numerators are bounded in full original
assignment times block-length units, before any geometric state refinement. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.fine_original_source_mass_le_full (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b f : Fin p.C) (hf : p.lev f = stop) (hfγ : p.γ f = p.γ b) :
    ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f univ) ≤
      ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f) := by
  let := (hd.weights k).2.2 (p.γ b)
  have hsub : F.fineOriginalEvent b f univ ⊆ p.A f ×ˢ p.block f := by
    intro x hx
    have hxW := hx.1
    simp only [PathData.packetWitness,
      ite_eq_left (show p.lev f = stop ∧ p.γ f = p.γ b from ⟨hf, hfγ⟩),
      mem_inter_iff, mem_ofPred_eq] at hxW
    rcases hp.2.2.2.2.2.2.2 f with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hF, _⟩
    exact ⟨(hF x hxW.1.1).2.1, (hF x hxW.1.1).2.2.1⟩
  calc
    _ ≤ ((d.ν k (p.γ b)).prod volume) (p.A f ×ˢ p.block f) := measure_mono hsub
    _ = _ := by rw [Measure.prod_prod, p.volume_block, hf, hfγ, mul_comm]

/-- The bound holds for every set of discrete palette values, so it can
feed original-reference pruning after changing the geometric state. -/
theorem PaletteFamily.fine_original_palette_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (hA : 0 ≤ A) (b f : Fin p.C) (hb : F.active b) (hf : p.lev f = stop)
    (hfγ : p.γ f = p.γ b)
    (hretained : F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)))
    (B : Set (ℤ × ℤ)) (hB : MeasurableSet B) :
    ((d.ν k (p.γ b)).prod volume)
        (F.fineOriginalEvent b f ((fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) ⁻¹' B)) ≤
      ENNReal.ofReal (8 * A) *
        (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) *
        ((Q.velocityPosterior b).map (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v)) B := by
  have hF (c : Fin p.C) : MeasurableSet (p.F c) :=
    (hp.2.2.2.2.2.2.2 c).2.2.2.2.2.2.2.2.2.1
  have hm : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) :=
    measurable_euclidean_velocityPalette id measurable_id a
  have hcap := F.fine_palette_domination hF hA b hb (F.coding.code f) hretained B
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm hB] at hcap
  calc
    _ = F.fineVelocityLaw b (F.coding.code f)
        ((fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) ⁻¹' B) *
        ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f univ) :=
      (F.fine_velocity_original_mass hd hp hHE hH b hb f hf hfγ _ (hB.preimage hm)).symm
    _ ≤ (ENNReal.ofReal (8 * A) *
        ((Q.velocityPosterior b).map (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v)) B) *
        (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) :=
      mul_le_mul' hcap (F.fine_original_source_mass_le_full hd hp b f hf hfγ)
    _ = _ := by ring

/-- The old original velocity palette remains unchanged. The new fine
history contributes its full original reference weight, with no inverse
selected-source mass. -/
theorem PaletteFamily.fine_original_bin_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (hA : 0 ≤ A) (b f : Fin p.C) (hb : F.active b) (hf : p.lev f = stop)
    (hfγ : p.γ f = p.γ b)
    (hretained : F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)))
    (β : Fin 2 → ℤ) :
    ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f (Sampling.bin a β)) ≤
      ENNReal.ofReal (8 * A) *
        (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) *
        Q.velocityPosterior b (Sampling.bin a β) := by
  have hF (c : Fin p.C) : MeasurableSet (p.F c) :=
    (hp.2.2.2.2.2.2.2 c).2.2.2.2.2.2.2.2.2.1
  have hcap := F.fine_bin_domination hF hA b hb (F.coding.code f) hretained β
  change F.fineVelocityLaw b (F.coding.code f) (Sampling.bin a β) ≤
    ENNReal.ofReal (8 * A) * Q.velocityPosterior b (Sampling.bin a β) at hcap
  calc
    _ = F.fineVelocityLaw b (F.coding.code f) (Sampling.bin a β) *
        ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f univ) :=
      (F.fine_velocity_original_mass hd hp hHE hH b hb f hf hfγ _
        (Sampling.measurableSet_bin a β)).symm
    _ ≤ (ENNReal.ofReal (8 * A) * Q.velocityPosterior b (Sampling.bin a β)) *
        (ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ f) (p.A f)) :=
      mul_le_mul' hcap (F.fine_original_source_mass_le_full hd hp b f hf hfγ)
    _ = _ := by ring

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
