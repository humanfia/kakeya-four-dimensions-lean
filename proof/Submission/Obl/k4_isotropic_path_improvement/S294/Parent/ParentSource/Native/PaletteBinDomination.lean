-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PaletteBinDomination, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PaletteBinDomination.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PaletteBinDomination.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PaletteBinDomination.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SelectedFineLaws

/-! Domination on the exact velocity bins used by seven-direction sampling.
No domination of the entire continuous fine law is asserted. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)

theorem PaletteFamily.fine_bin_domination (hF : ∀ b, MeasurableSet (p.F b))
    (hA : 0 ≤ A) (b : Fin p.C) (hb : F.active b) (e : ℕ)
    (hretained : e ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)))
    (β : Fin 2 → ℤ) :
    F.fineVelocityLaw b e {v | (fun j => ⌊v j / a⌋) = β} ≤
      ENNReal.ofReal (8 * A) * Q.velocityPosterior b {v | (fun j => ⌊v j / a⌋) = β} := by
  have hdom := F.fine_palette_domination hF hA b hb e hretained
  have hm : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) :=
    measurable_euclidean_velocityPalette id measurable_id a
  have hset : (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) ⁻¹' {(β 0, β 1)} =
      {v | (fun j => ⌊v j / a⌋) = β} := by
    ext v
    change (⌊v 0 / a⌋, ⌊v 1 / a⌋) = (β 0, β 1) ↔ (fun j => ⌊v j / a⌋) = β
    rw [Prod.mk.injEq]
    constructor
    · rintro ⟨h0, h1⟩
      funext j
      fin_cases j <;> assumption
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
  have h := hdom {(β 0, β 1)}
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm (measurableSet_singleton _),
    Measure.map_apply hm (measurableSet_singleton _), hset] at h
  exact h

theorem PaletteFamily.fine_strip_mass_le (hF : ∀ b, MeasurableSet (p.F b))
    (r fraction : ℝ) (hfraction : 0 ≤ fraction) (b : Fin p.C) (hb : F.active b) (e : ℕ)
    (he : e ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b)
    (hretained : e ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)))
    (n : StripSpace) (β : ℝ) (hn : ‖n‖ = 1) :
    F.fineVelocityLaw b e (affineStrip n β r) ≤ ENNReal.ofReal (8 * fraction) := by
  obtain ⟨hprob, hstrip⟩ := F.broad_fine_velocity_law hF r fraction hfraction b hb e he hretained
  let := hprob
  rw [← ENNReal.ofReal_toReal (measure_ne_top (F.fineVelocityLaw b e) (affineStrip n β r))]
  exact ENNReal.ofReal_le_ofReal (hstrip n β hn).le

variable {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.fine_velocity_tail_zero
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (hb : F.active b) (e : ℕ) :
    F.fineVelocityLaw b e {v | 2 * p.κ < ‖v‖} = 0 := by
  simpa only [not_le] using ae_iff.mp (F.fine_velocity_envelope hp b hb e)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
