-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.SaturationPredictions, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/SaturationPredictions.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/SaturationPredictions.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/SaturationPredictions.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteStripSaturation

/- The default unit-normal calculation follows Native.StripCover,
adapted there from LOT o116/x0389/e3859a9b. -/

/-! Freeze a constant-size array for each original fine-state strip list. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
  {F : PaletteFamily Q i stop a A θ} (P : PaletteStripSaturation F r fraction)

theorem PaletteStripSaturation.exists_prediction_arrays (J : ℕ) (hJ : fraction⁻¹ ≤ (J : ℝ)) :
    ∃ params : Fin p.C → ℕ → Fin J → UnitStripParameter,
      ∀ b, F.active b → ∀ e, ∀ q ∈ P.predictions b e, ∃ j, params b e j = q := by
  classical
  let n₀ : StripSpace := WithLp.toLp 2 ![(1 : ℝ), 0]
  have hn₀ : ‖n₀‖ = 1 := by
    have h : ‖n₀‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [n₀, Fin.sum_univ_two]
    nlinarith [norm_nonneg n₀]
  let fallback : UnitStripParameter := ⟨(n₀, 0), hn₀⟩
  have hex (b : Fin p.C) (e : ℕ) : ∃ params : Fin J → UnitStripParameter,
      F.active b → ∀ q ∈ P.predictions b e, ∃ j, params j = q := by
    by_cases hb : F.active b
    · have hcard : (P.predictions b e).card ≤ J := by
        exact_mod_cast (P.count b hb e).trans hJ
      obtain ⟨params, hparams⟩ := exists_prediction_array (P.predictions b e) fallback J hcard
      exact ⟨params, fun _ => hparams⟩
    · exact ⟨fun _ => fallback, fun h => False.elim (hb h)⟩
  choose params hparams using hex
  exact ⟨params, fun b hb e => hparams b e hb⟩

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
