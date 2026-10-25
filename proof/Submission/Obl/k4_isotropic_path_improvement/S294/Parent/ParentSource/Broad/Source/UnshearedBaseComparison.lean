-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UnshearedBaseComparison, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/UnshearedBaseComparison.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/UnshearedBaseComparison.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedOldBase
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.FrameExpansion

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open MeasureTheory Set Native
noncomputable section

section Path
variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
include hp

/-- The actual native old base is Lipschitz in the unsheared old base.
Only the original path tolerance and actual center velocity are paid. -/
theorem Native.PathData.Valid.native_base_le_unsheared
    (hN : 1 ≤ N) (old : Fin p.C) (z z' : Ev) :
    ‖packetBase p old z-packetBase p old z'‖ ≤
      (1+2*(p.κ*N^(2*δ₀*L))*(1+‖p.u old‖))*
        ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖ := by
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let h : ℝ := ((2:ℝ)^p.T (p.lev old))⁻¹
  have hh : 0 < h := by dsimp [h]; positivity
  let t0 : ℝ := (p.j old:ℝ)*h
  let D := unshearedPacketBase p old z-unshearedPacketBase p old z'
  let V : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![D 1,D 2]
  let P := packetPosition (p.Q old) (p.c old) (p.u old) z.1 z.2-
    packetPosition (p.Q old) (p.c old) (p.u old) z'.1 z'.2
  have hdt : z.2-z'.2=h*D 0 := by
    change z.2-z'.2=h*((z.2-t0)/h-(z'.2-t0)/h)
    field_simp [hh.ne'] <;> ring
  have hdy : y z.1 z.2-y z'.1 z'.2=h • V := by
    ext i
    fin_cases i
    · change (xp z.1 z.2) 1-(xp z'.1 z'.2) 1 =
        h*((((xp z.1 z.2) 1-(p.c old 0+t0*p.u old 0))/h)-
          (((xp z'.1 z'.2) 1-(p.c old 0+t0*p.u old 0))/h))
      field_simp [hh.ne'] <;> ring
    · change (xp z.1 z.2) 2-(xp z'.1 z'.2) 2 =
        h*((((xp z.1 z.2) 2-(p.c old 1+t0*p.u old 1))/h)-
          (((xp z'.1 z'.2) 2-(p.c old 1+t0*p.u old 1))/h))
      field_simp [hh.ne'] <;> ring
  have hV : ‖V‖ ≤ ‖D‖ := by
    rw [EuclideanSpace.norm_eq,EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    simp only [Fin.sum_univ_two,Fin.sum_univ_three]
    change ‖D 1‖^2+‖D 2‖^2 ≤ ‖D 0‖^2+‖D 1‖^2+‖D 2‖^2
    nlinarith [sq_nonneg ‖D 0‖]
  have hD0 : |D 0| ≤ ‖D‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le D 0
  have hP : P=Matrix.toEuclideanLin (p.Q old)⁻¹
      ((y z.1 z.2-y z'.1 z'.2)-(z.2-z'.2) • p.u old) := by
    dsimp only [P,packetPosition]
    rw [←map_sub]
    congr 1
    change (y z.1 z.2-p.c old-z.2 • p.u old)-
      (y z'.1 z'.2-p.c old-z'.2 • p.u old)=_
    module
  let w := (y z.1 z.2-y z'.1 z'.2)-(z.2-z'.2) • p.u old
  have hw : ‖w‖ ≤ h*((1+‖p.u old‖)*‖D‖) := by
    calc
      _ ≤ ‖y z.1 z.2-y z'.1 z'.2‖+‖(z.2-z'.2) • p.u old‖ := norm_sub_le _ _
      _ = h*‖V‖+h*|D 0| *‖p.u old‖ := by
        rw [hdy,hdt,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_pos hh,abs_mul,abs_of_pos hh]
      _ ≤ h*‖D‖+h*‖D‖*‖p.u old‖ := by gcongr
      _ = _ := by ring
  have hQ := hp.normalized_frame_operator_bound hN old w
  change ‖h • Matrix.toEuclideanLin (p.Q old)⁻¹ w‖ ≤ _ at hQ
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh] at hQ
  have hPbound : ‖P‖ ≤ (p.κ*N^(2*δ₀*L))*((1+‖p.u old‖)*‖D‖) := by
    have hscaled : h*‖P‖ ≤ (p.κ*N^(2*δ₀*L))*(h*((1+‖p.u old‖)*‖D‖)) := by
      rw [hP]
      exact hQ.trans (mul_le_mul_of_nonneg_left hw (by positivity))
    nlinarith
  have hn0 : (packetBase p old z-packetBase p old z') 0=D 0 := by
    simp [packetBase_apply_zero',D,unshearedPacketBase,div_eq_mul_inv] <;> ring
  have hn1 : (packetBase p old z-packetBase p old z') 1=P 0 := by
    simp [P,packetBase_apply_one']
  have hn2 : (packetBase p old z-packetBase p old z') 2=P 1 := by
    simp [P,packetBase_apply_two']
  have hP0 : |P 0| ≤ ‖P‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le P 0
  have hP1 : |P 1| ≤ ‖P‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le P 1
  calc
    _ ≤ ∑ i : Fin 3, |(packetBase p old z-packetBase p old z') i| :=
      euclidean_norm_le_sum_abs _
    _ = |D 0|+|P 0|+|P 1| := by rw [Fin.sum_univ_three,hn0,hn1,hn2]
    _ ≤ ‖D‖+2*‖P‖ := by linarith
    _ ≤ _ := by dsimp only [D] at hPbound ⊢; nlinarith

end Path
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
