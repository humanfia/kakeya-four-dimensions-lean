-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.UnshearedSourceBox, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/UnshearedSourceBox.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/UnshearedSourceBox.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedOldBase
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CenterVelocity
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PathFacts

/-! # The actual unsheared source lies in a subpower box -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native

noncomputable section

section Path

variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The original whole-block chart bounds control every actual selected point
in isotropic old units, using its physical center velocity. -/
theorem Native.PathData.Valid.unsheared_source_box (b : Fin p.C) {q : Ev}
    (hq : q ∈ p.F b) :
    ‖unshearedPacketBase p b q‖ ≤ 1 + 2 * p.κ ^ 2 + 2 * ‖p.u b‖ := by
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  let clock : ℝ := (2 : ℝ) ^ p.T (p.lev b)
  let h : ℝ := clock⁻¹
  let t0 : ℝ := (p.j b : ℝ) * h
  have hc : 0 < clock := by dsimp [clock]; positivity
  have hh : 0 < h := inv_pos.mpr hc
  have hs := path_packet_support hp b hq
  have hlow : t0 ≤ q.2 := by
    simpa only [t0, h, clock, div_eq_mul_inv] using hs.2.2.1.1
  have hhigh : q.2 ≤ t0 + h := by
    convert hs.2.2.1.2 using 1 <;> dsimp [t0, h, clock] <;> ring
  have hdt : |q.2 - t0| ≤ h := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
    linarith
  let residual := y q.1 q.2 - p.c b - q.2 • p.u b
  have hresidual : ‖residual‖ ≤ h * p.κ ^ 2 := by
    rcases hp.2.2.2.2.2.2.2 b with ⟨_, _, _, _, _, _, _, _, _, _, _, hfit, _⟩
    have hpos : ‖Matrix.toEuclideanLin (p.Q b)⁻¹ residual‖ ≤ p.κ :=
      ((hfit q.1 hs.2.1).2.2 q.2 hs.2.2.1).1
    have hbound := hp.denormalized_frame_operator_bound b
      (Matrix.toEuclideanLin (p.Q b)⁻¹ residual)
    change ‖clock • Matrix.toEuclideanLin (p.Q b)
      (Matrix.toEuclideanLin (p.Q b)⁻¹ residual)‖ ≤ _ at hbound
    rw [Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel _
      (hp.2.2.2.2.2.2.2 b).2.2.1, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hbound
    have hscaled : clock * ‖residual‖ ≤ p.κ ^ 2 := by
      calc
        _ ≤ p.κ * ‖Matrix.toEuclideanLin (p.Q b)⁻¹ residual‖ := hbound
        _ ≤ p.κ * p.κ := mul_le_mul_of_nonneg_left hpos hκ
        _ = _ := (pow_two _).symm
    calc
      ‖residual‖ = h * (clock * ‖residual‖) := by dsimp [h]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hscaled hh.le
  let Y := h⁻¹ • (y q.1 q.2 - (p.c b + t0 • p.u b))
  have hY : ‖Y‖ ≤ p.κ ^ 2 + ‖p.u b‖ := by
    have heq : y q.1 q.2 - (p.c b + t0 • p.u b) =
        residual + (q.2 - t0) • p.u b := by dsimp [residual]; module
    calc
      ‖Y‖ = h⁻¹ * ‖residual + (q.2 - t0) • p.u b‖ := by
        rw [show Y = h⁻¹ • (residual + (q.2 - t0) • p.u b) by rw [← heq],
          norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
      _ ≤ h⁻¹ * (‖residual‖ + |q.2 - t0| * ‖p.u b‖) := by
        gcongr
        simpa only [norm_smul, Real.norm_eq_abs] using
          norm_add_le residual ((q.2 - t0) • p.u b)
      _ ≤ h⁻¹ * (h * p.κ ^ 2 + h * ‖p.u b‖) := by gcongr
      _ = _ := by field_simp
  have ht : |unshearedPacketBase p b q 0| ≤ 1 := by
    change |(q.2 - t0) / h| ≤ 1
    rw [abs_div, abs_of_pos hh, div_le_one hh]
    exact hdt
  have hcoord1 : unshearedPacketBase p b q 1 = Y 0 := by
    change ((xp q.1 q.2) 1 - (p.c b 0 + t0 * p.u b 0)) / h = _
    simp [Y, y, xp, Native.x, div_eq_mul_inv, mul_comm]
  have hcoord2 : unshearedPacketBase p b q 2 = Y 1 := by
    change ((xp q.1 q.2) 2 - (p.c b 1 + t0 * p.u b 1)) / h = _
    simp [Y, y, xp, Native.x, div_eq_mul_inv, mul_comm]
  have hY0 : |Y 0| ≤ p.κ ^ 2 + ‖p.u b‖ :=
    (PiLp.norm_apply_le Y 0).trans hY
  have hY1 : |Y 1| ≤ p.κ ^ 2 + ‖p.u b‖ :=
    (PiLp.norm_apply_le Y 1).trans hY
  calc
    _ ≤ ∑ i : Fin 3, |unshearedPacketBase p b q i| := euclidean_norm_le_sum_abs _
    _ = |unshearedPacketBase p b q 0| + |Y 0| + |Y 1| := by
      rw [Fin.sum_univ_three, hcoord1, hcoord2]
    _ ≤ _ := by linarith

end Path

/-- The original problem turns the pointwise source box into a fixed `K` power. -/
theorem original_unsheared_source_box {d : ProblemData} (hd : d.Valid)
    {k m : ℕ} {p : PathData (d.W k)} {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ) {K : ℝ} (hK : 16 ≤ K)
    (hκ : p.κ ≤ K) (hOrig : d.K k ≤ K) (b : Fin p.C) {q : Ev} (hq : q ∈ p.F b) :
    ‖unshearedPacketBase p b q‖ ≤ K ^ 3 := by
  have hκ0 : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hcenter := original_packet_center_velocity hd hp b
  have hbox := hp.unsheared_source_box b hq
  have hsq : p.κ ^ 2 ≤ K ^ 2 := by nlinarith
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hp3 : 0 ≤ (K - 9) * K ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
