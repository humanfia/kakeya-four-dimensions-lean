-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripPhysical, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripPhysical.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripPhysical.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripPhysical.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripPhysical.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripObservation

/-! Compose the normalized strip frame through its actual parent chart. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

def physicalStripCenter (Q : Matrix (Fin 2) (Fin 2) ℝ) (c n : StripSpace)
    (t₀ q s β : ℝ) : StripSpace :=
  c + Matrix.toEuclideanLin Q (stripCenter n s β - (t₀ / q) • stripVelocity n β)

def physicalStripVelocity (Q : Matrix (Fin 2) (Fin 2) ℝ) (u n : StripSpace)
    (q β : ℝ) : StripSpace :=
  u + Matrix.toEuclideanLin Q (q⁻¹ • stripVelocity n β)

theorem physical_strip_whole_block_fit
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u e n : StripSpace)
    (l : ℕ × (Fin 6 → ℝ)) {t₀ q K D r s β t : ℝ}
    (hQ : Q.det ≠ 0) (hq : 0 < q) (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (hfit : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖packetPosition Q c u l (t₀ + q * θ)‖ ≤ K)
    (hvel : |inner ℝ (packetVelocity q Q u l) n - β| ≤ D * r)
    (hmid : |inner ℝ (packetPosition Q c u l (t₀ + q / 2)) n - s| ≤ r)
    (ht : t ∈ Set.Icc t₀ (t₀ + q)) :
    ‖Matrix.toEuclideanLin (Q * stripLocalFrame K D r e n)⁻¹
      (gy l t - physicalStripCenter Q c n t₀ q s β -
        t • physicalStripVelocity Q u n q β)‖ ≤ 2 := by
  let θ := (t - t₀) / q
  have hθ : θ ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith [ht.1]) hq.le, ?_⟩
    exact (div_le_one hq).mpr (by linarith [ht.2])
  have htime : t₀ + q * θ = t := by dsimp [θ]; field_simp; ring
  have hmidtime : t₀ + q * (1 / 2 : ℝ) = t₀ + q / 2 := by ring
  have hlocal := strip_whole_block_fit hK hD hr he hn hen
    (a := packetPosition Q c u l t₀) (v := packetVelocity q Q u l)
    (fun θ hθ => by rw [← packetPosition_affine]; exact hfit θ hθ) hvel
    (by rw [← packetPosition_affine, hmidtime]; exact hmid) hθ
  have hN : (stripLocalFrame K D r e n).det ≠ 0 := by
    have hdet := stripLocalFrame_abs_det hK hD hr he hn hen
    exact abs_pos.mp (hdet ▸ (by positivity : 0 < K * (1 + D) * r))
  unfold physicalStripCenter physicalStripVelocity
  rw [frame_comp_apply Q (stripLocalFrame K D r e n) hQ hN]
  have hid : packetPosition Q c u l t -
      (stripCenter n s β - (t₀ / q) • stripVelocity n β) -
        t • (q⁻¹ • stripVelocity n β) =
      packetPosition Q c u l t₀ + θ • packetVelocity q Q u l -
        stripCenter n s β - θ • stripVelocity n β := by
    have hpos : packetPosition Q c u l t =
        packetPosition Q c u l t₀ + θ • packetVelocity q Q u l := by
      simpa only [htime] using packetPosition_affine Q c u l t₀ q θ
    rw [hpos]
    dsimp [θ]
    module
  change ‖Matrix.toEuclideanLin (stripLocalFrame K D r e n)⁻¹
    (packetPosition Q c u l t - (stripCenter n s β - (t₀ / q) • stripVelocity n β) -
      t • (q⁻¹ • stripVelocity n β))‖ ≤ 2
  rw [hid]
  exact hlocal

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
