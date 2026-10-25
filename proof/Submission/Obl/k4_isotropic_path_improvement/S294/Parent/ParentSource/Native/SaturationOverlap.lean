-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.SaturationOverlap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/SaturationOverlap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/SaturationOverlap.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/SaturationOverlap.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SaturationCapture
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeStripOverlaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.OriginalDeletion

/- The old-native overlap bookkeeping follows Native.NativeNarrowWidth,
adapted there from LOT o116/x0389/e3859a9b; this proof uses the complete
statewise saturated capture and its fixed original mass threshold. -/

/-! One overlap deletion from the COMPLETE saturated capture preserves the
fixed original 1/(8*kappa) mass required by the frozen weak atlas. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
  {F : PaletteFamily Q i stop a A θ} (P : PaletteStripSaturation F r fraction)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteStripSaturation.capture_after_overlaps (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i < m) (hstop : stop < m)
    (M : ℕ) (n : Fin p.C → Fin M → StripSpace) (β : Fin p.C → Fin M → ℝ)
    {width radius ε : ℝ} (hradius : 0 < radius) (hsmall : 4 * width ≤ radius)
    (hn : ∀ b, F.active b → ∀ j, ‖n b j‖ = 1)
    (hcap : ∀ b, F.active b → ∀ x : StripSpace,
      Q.velocityPosterior b (Metric.closedBall x (32 * (1 + 2 * p.κ) * width / radius)) ≤ ENNReal.ofReal ε)
    (hcost : (M : ENNReal) ^ 2 * ENNReal.ofReal ε ≤ ENNReal.ofReal (p.κ⁻¹ / 64))
    (hmass : ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w)) :
    ∃ J : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (J w)) ∧ (∀ w, J w ⊆ H w) ∧
      ENNReal.ofReal (p.κ⁻¹ / 8) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (J w) ∧
      ∀ w x, x ∈ J w → ∃ b, p.lev b = i ∧ p.γ b = w ∧ F.active b ∧ x ∈ p.F b ∧ ∃ f,
        p.lev f = stop ∧ p.γ f = w ∧ x ∈ p.packetWitness m stop w f ∧
        (∃ q ∈ P.predictions b (F.coding.code f), p.normalizedVelocity b x ∈ affineStrip q.val.1 q.val.2 r) ∧
        p.normalizedVelocity b x ∉ stripFarOverlap (n b) (β b) width radius (2 * p.κ) := by
  classical
  let omissions := Q.stripOverlapOmissions F.active n β width radius (2 * p.κ)
  let bad := Q.packetFamilyResidual i omissions
  let J := fun w => P.cleanCapture w \ bad w
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  have hT : 0 ≤ 2 * p.κ := by positivity
  have hM : ∀ b, F.active b → Fintype.card (Fin M) ≤ M := by simp
  obtain ⟨hDm, _, _⟩ := Q.strip_overlap_prepared_mass_le hd hp hHE hH i hi
    F.active n β hT hradius hsmall hn hcap M hM
  have hbad := (Q.strip_overlap_original_mass_le hd hp hHE hH i hi F.active n β
    hT hradius hsmall hn hcap M hM).trans hcost
  have hcleanmass : ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.cleanCapture w) := by
    rw [P.cleanCapture_original_mass hp]
    exact hmass
  have hkeep : ENNReal.ofReal (p.κ⁻¹ / 8) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (J w) := by
    apply mixture_remove_budget (fun w => (d.ν k w).prod volume)
      (fun w => ENNReal.ofReal (d.ω k w)) P.cleanCapture bad
      (loss := ENNReal.ofReal (p.κ⁻¹ / 64)) ENNReal.ofReal_ne_top _ hbad
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have heq : p.κ⁻¹ / 8 + p.κ⁻¹ / 64 = 9 * p.κ⁻¹ / 64 := by ring
    simpa only [heq] using hcleanmass
  refine ⟨J, ?_, ?_, hkeep, ?_⟩
  · intro w
    exact (P.cleanCapture_measurable hp w).diff
      (Q.measurableSet_packetFamilyResidual i omissions hDm w)
  · intro w x hx
    exact P.captureResidual_subset_H w hx.1.1.1
  · intro w x hx
    obtain ⟨b, hbi, hbγ, hb, hxb, f, hf, hfγ, hxf, hpred⟩ :=
      P.cleanCapture_witness hp hH hstop w x hx.1
    refine ⟨b, hbi, hbγ, hb, hxb, f, hf, hfγ, hxf, hpred, ?_⟩
    intro hOverlap
    apply hx.2
    refine ⟨b, hbi, hbγ, ?_⟩
    have hxQ : x ∈ Q.residual (p.γ b) := by
      simpa only [hbγ] using
        Q.packetFamilyResidual_subset i P.captureFamily P.captureFamily_subset w hx.1.1.1
    simpa only [omissions, PreparedAngularPath.stripOverlapOmissions, if_pos hb,
      mem_inter_iff, mem_preimage] using
      (show (x ∈ Q.residual (p.γ b) ∧ x ∈ p.F b) ∧
        p.normalizedVelocity b x ∈ stripFarOverlap (n b) (β b) width radius (2 * p.κ) from
          ⟨⟨hxQ, hxb⟩, hOverlap⟩)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
