-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeAngularCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeAngularCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeAngularCap.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeAngularCap.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteCertificate
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteBudgetChoice

/-! The actual fixed original native velocity posterior has an explicit
real power cap, after choosing the actual light-parent threshold. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ}
  (F : PaletteFamily Q i stop a A (lightParentThreshold p.κ))
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.native_velocity_ball_cap (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hm : 0 < m) (hHE : ∀ w, H w ⊆ d.E k w)
    (b : Fin p.C) (hb : F.active b) (t : T) {radius : ℝ}
    (hscale : p.κ * radius ≤ δ (d.N k) (u t)) (center : EuclideanSpace ℝ (Fin 2)) :
    Q.velocityPosterior b (Metric.closedBall center radius) ≤
      ENNReal.ofReal (819200 * (m : ℝ) * p.κ ^ 3 * d.N k ^ (-d.S * u t + 2 * τ)) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  have h := Q.velocity_posterior_ball_cap hd hp hHE b t
    (lightParentThreshold_ne_zero hκ) (lightParentThreshold_ne_top p.κ)
    (F.current_positive b hb) (F.reference_floor b hb) hscale center
  rw [angularPreparationEpsilon,
    native_angular_cap_coefficient hκ hm
      (Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans (hd.1 k)) _)] at h
  exact h

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
