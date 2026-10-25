/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ProjectedZoomGap.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.ParentZoom
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedBaseGap
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Projected-cell uncertainty in the true parent's normalized packet axes. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

theorem supportZoom_base_gap {K q g sigma chi tmid z₀ : ℝ} (c : Fin 5 → ℝ)
    (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (hg1 : g ≤ 1)
    (hs : 0 ≤ sigma) (hc : 0 ≤ chi) (hc₃ : |c 3| ≤ K) (hc₄ : |c 4| ≤ K)
    (p p' : NativePoint)
    (ht : |p 0 - p' 0| ≤ 2 * sigma)
    (hz : |p 1 - p' 1| ≤ 4 * chi + 2 * K * sigma)
    (hy : |p 2 - p' 2| ≤ 2 * g * sigma + 2 * K * sigma) :
    ‖nativeBase ((supportZoom K q g tmid z₀ c).nativePoint p) -
      nativeBase ((supportZoom K q g tmid z₀ c).nativePoint p')‖ ≤
        24 * K ^ 2 * (sigma + chi) / (q * g) := by
  let Z := supportZoom K q g tmid z₀ c
  let B := 8 * K ^ 2 * (sigma + chi)
  let D := B / (q * g)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hK21 : 1 ≤ K ^ 2 := hK.trans hK2
  have hqg : 0 < q * g := mul_pos hq hg
  have hdenq : q * g ≤ 32 * K * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) hq.le,
      mul_nonneg (sub_nonneg.mpr hg1) hq.le]
  have hdenw : q * g ≤ 16 * K * q * g := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) hqg.le]
  have htB : 2 * sigma ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg (sub_nonneg.mpr hK21) hs,
      mul_nonneg (sq_nonneg K) hc]
  have hzB : 4 * chi + 2 * K * sigma ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg (sub_nonneg.mpr hK2) hs,
      mul_nonneg (sub_nonneg.mpr hK21) hc,
      mul_nonneg (sq_nonneg K) hs]
  have hyB : |tiltedTransverse (c 3) (c 4) (fun i => p i.castSucc) -
      tiltedTransverse (c 3) (c 4) (fun i => p' i.castSucc)| ≤ B :=
    tiltedTransverse_gap hK hs hc hg1 hc₃ hc₄ ht hz hy
  have hdiv {x d : ℝ} (hd : q * g ≤ d) (hx : |x| ≤ B) : |x / d| ≤ D := by
    have hd0 : 0 < d := hqg.trans_le hd
    rw [abs_div, abs_of_pos hd0]
    exact (div_le_div_of_nonneg_left (abs_nonneg x) hqg hd).trans
      (div_le_div_of_nonneg_right hx hqg.le)
  have hcoord (i : Fin 3) :
      |nativeBase (Z.nativePoint p) i - nativeBase (Z.nativePoint p') i| ≤ D := by
    fin_cases i
    · change |nativeBase (Z.nativePoint p) 0 - nativeBase (Z.nativePoint p') 0| ≤ D
      have heq : nativeBase (Z.nativePoint p) 0 - nativeBase (Z.nativePoint p') 0 =
          (p 0 - p' 0) / (32 * K * q) := by
        dsimp [nativeBase, Zoom.nativePoint, Zoom.pos, Z, supportZoom]
        ring
      rw [heq]
      exact hdiv hdenq (ht.trans htB)
    · change |nativeBase (Z.nativePoint p) 1 - nativeBase (Z.nativePoint p') 1| ≤ D
      have heq : nativeBase (Z.nativePoint p) 1 - nativeBase (Z.nativePoint p') 1 =
          (p 1 - p' 1) / (32 * K * q) := by
        dsimp [nativeBase, Zoom.nativePoint, Zoom.pos, Z, supportZoom]
        ring
      rw [heq]
      exact hdiv hdenq (hz.trans hzB)
    · change |nativeBase (Z.nativePoint p) 2 - nativeBase (Z.nativePoint p') 2| ≤ D
      have heq : nativeBase (Z.nativePoint p) 2 - nativeBase (Z.nativePoint p') 2 =
          (tiltedTransverse (c 3) (c 4) (fun i => p i.castSucc) -
            tiltedTransverse (c 3) (c 4) (fun i => p' i.castSucc)) / (16 * K * q * g) := by
        dsimp [nativeBase, Zoom.nativePoint, Zoom.pos, Z, supportZoom, tiltedTransverse]
        ring
      rw [heq]
      exact hdiv hdenw hyB
  have hn := Submission.Obl.k4_scalar_coefficient_clustering.coeff_norm_le_abs_add
    (nativeBase (Z.nativePoint p) - nativeBase (Z.nativePoint p'))
  change ‖nativeBase (Z.nativePoint p) - nativeBase (Z.nativePoint p')‖ ≤
    |nativeBase (Z.nativePoint p) 0 - nativeBase (Z.nativePoint p') 0| +
      |nativeBase (Z.nativePoint p) 1 - nativeBase (Z.nativePoint p') 1| +
      |nativeBase (Z.nativePoint p) 2 - nativeBase (Z.nativePoint p') 2| at hn
  calc
    _ ≤ 3 * D := by linarith [hcoord 0, hcoord 1, hcoord 2]
    _ = _ := by dsimp [D, B]; ring

end

end Submission.Obl.k4_general_parent_projected_layers
