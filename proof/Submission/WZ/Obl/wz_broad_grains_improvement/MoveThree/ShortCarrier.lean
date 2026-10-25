-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ShortCarrier.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ShortCarrier.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, ShortCarrier.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseNormalize

set_option maxHeartbeats 800000

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap uniformMap_apply)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit norm_smul_unit)

/-- A fixed contraction puts any nonzero carrier of length at most twenty into
the short square prisms used by the accepted separated-net theorem. -/
theorem contracted_short_carrier_prism {r k : ℝ} (hk : 0 < k)
    (hk20 : 20 * k ≤ 1 / 1000000) (hkr : k * r ≤ 1 / 1000000)
    (x v : V) (hv : v ≠ 0) (hv20 : ‖v‖ ≤ 20) :
    ∃ u : Fin 3 → V, Orthonormal ℝ u ∧
      uniformMap hk '' T r x v ⊆
        WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          (k * r) (k * r) (uniformMap hk (x + (1 / 2 : ℝ) • v)) u := by
  let f := uniformMap (by norm_num : (0 : ℝ) < 1 / 20)
  let g := uniformMap (by positivity : 0 < 20 * k)
  let z := f (x + (1 / 2 : ℝ) • v) - (1 / 2 : ℝ) • unit v
  have hsub : f '' T r x v ⊆ T ((1 / 20) * r) z (unit v) := by
    apply WangZahlLot.Obl.wz_affine_robust_cluster_estimate.image_tube_extend f x v (unit v)
      (l := (1 / 20) * ‖v‖) (by norm_num) (by positivity) (by linarith)
    · change (1 / 20 : ℝ) • v = ((1 / 20) * ‖v‖) • unit v
      rw [mul_smul, norm_smul_unit hv]
    · intro p q
      simp only [f, uniformMap_apply, dist_smul₀, Real.norm_eq_abs]
      norm_num
  have hgLip : ∀ p q, dist (g p) (g q) ≤ (20 * k) * dist p q := by
    intro p q
    simp only [g, uniformMap_apply, dist_smul₀, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 20 * k)]
    rfl
  have hglen : ‖g.toAffineEquiv.linear (unit v)‖ ≤ 1 / 1000000 := by
    change ‖(20 * k) • unit v‖ ≤ _
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 20 * k),
      norm_unit hv, mul_one] using hk20
  obtain ⟨u, hu, hprism⟩ := WangZahlLot.Obl.wz_nonflat_factored_improvement.affine_tube_prism
    g.toAffineEquiv (by positivity : 0 < 20 * k)
    (by nlinarith : (20 * k) * ((1 / 20) * r) ≤ 1 / 1000000) hgLip z (unit v)
    (norm_unit hv) hglen
  have hcomp (p : V) : g (f p) = uniformMap hk p := by
    simp only [f, g, uniformMap_apply, smul_smul]
    congr 1
    ring
  have hmid : z + (1 / 2 : ℝ) • unit v = f (x + (1 / 2 : ℝ) • v) := by
    dsimp [z]
    abel
  have hradius : (20 * k) * ((1 / 20) * r) = k * r := by ring
  change g '' T ((1 / 20) * r) z (unit v) ⊆
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
      ((20 * k) * ((1 / 20) * r)) ((20 * k) * ((1 / 20) * r))
      (g (z + (1 / 2 : ℝ) • unit v)) u at hprism
  rw [hmid, hcomp, hradius] at hprism
  refine ⟨u, hu, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have H := hprism ⟨f p, hsub ⟨p, hp, rfl⟩, rfl⟩
  exact (hcomp p) ▸ H

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
