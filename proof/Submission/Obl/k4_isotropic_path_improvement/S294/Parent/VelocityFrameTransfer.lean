-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.VelocityFrameTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/VelocityFrameTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFrameChange
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripCover

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.VelocityFrameTransfer

open MeasureTheory Set
open ParentSource ParentSource.Native
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

noncomputable section

section Path

variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- A strip in any original normalized packet frame is a strip in any
other packet frame with only the actual isotropic frame cost. Unused
strips can be recentered, giving a bounded offset on the target's FULL
original assignment. No occurrence or posterior is used to define it. -/
theorem exists_bounded_strip_transfer (hN : 1 ≤ N) (source target : Fin p.C)
    {width radius : ℝ} (hwidth : 0 ≤ width) (hradius : 0 ≤ radius)
    (hscale : width * (p.κ ^ 2 * N ^ (2 * δ₀ * L)) ≤ radius)
    (n : StripSpace) (offset : ℝ) (hn : ‖n‖ = 1) :
    ∃ normal : StripSpace, ∃ bias : ℝ, ‖normal‖ = 1 ∧ |bias| ≤ 2 * p.κ + radius ∧
      ∀ x : Ev, x.1 ∈ p.A target →
        p.normalizedVelocity source x ∈ affineStrip n offset width →
        p.normalizedVelocity target x ∈ affineStrip normal bias radius := by
  let A := (p.normalizedFrameOperator source).comp (p.denormalizedFrameOperator target)
  let R := (p.normalizedFrameOperator target).comp (p.denormalizedFrameOperator source)
  have hR (v : StripSpace) : ‖R v‖ ≤ (p.κ ^ 2 * N ^ (2 * δ₀ * L)) * ‖v‖ := by
    calc
      _ ≤ p.κ * N ^ (2 * δ₀ * L) * ‖p.denormalizedFrameOperator source v‖ :=
        hp.normalized_frame_operator_bound hN target _
      _ ≤ p.κ * N ^ (2 * δ₀ * L) * (p.κ * ‖v‖) := by
        apply mul_le_mul_of_nonneg_left (hp.denormalized_frame_operator_bound source v)
        have hκ : 0 ≤ p.κ := by linarith [hp.1]
        positivity
      _ = _ := by ring
  have hAR (v : StripSpace) : A (R v) = v := by
    change p.normalizedFrameOperator source
      (p.denormalizedFrameOperator target (p.normalizedFrameOperator target
        (p.denormalizedFrameOperator source v))) = v
    rw [hp.denormalized_normalized_frame_cancel,hp.normalized_denormalized_frame_cancel]
  let shift := p.normalizedFrameOperator source (p.u target - p.u source)
  have hexact (x : Ev) : A (p.normalizedVelocity target x) + shift =
      p.normalizedVelocity source x := by
    change p.normalizedFrameOperator source
      (p.denormalizedFrameOperator target
        (p.normalizedFrameOperator target (ParentSource.Native.v x.1 - p.u target))) +
        p.normalizedFrameOperator source (p.u target - p.u source) =
      p.normalizedFrameOperator source (ParentSource.Native.v x.1 - p.u source)
    rw [hp.denormalized_normalized_frame_cancel,← map_add]
    congr 1
    abel
  obtain ⟨normal,bias,hnormal,hsub⟩ := affine_velocity_strip_pullback A R
    (show 0 ≤ p.κ ^ 2 * N ^ (2 * δ₀ * L) by positivity) hwidth hR hAR hscale
    n shift (offset • n) hn
  have htransfer (x : Ev) (hx : p.normalizedVelocity source x ∈ affineStrip n offset width) :
      p.normalizedVelocity target x ∈ affineStrip normal bias radius := by
    apply hsub
    change |inner ℝ n (A (p.normalizedVelocity target x) + shift - offset • n)| ≤ width
    rw [hexact,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hn]
    change |inner ℝ (p.normalizedVelocity source x) n - offset| ≤ width at hx
    simpa only [one_pow,mul_one,real_inner_comm] using hx
  by_cases hused : ∃ x : Ev, x.1 ∈ p.A target ∧
      p.normalizedVelocity target x ∈ affineStrip normal bias radius
  · obtain ⟨x,hx,hstrip⟩ := hused
    have hV : ‖p.normalizedVelocity target x‖ ≤ 2 * p.κ := hp.normalized_velocity_bound target x.1 hx
    have hbias := boundedStrip_offset_le hnormal
      (show p.normalizedVelocity target x ∈ boundedStrip normal bias radius (2 * p.κ) from
        ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hV,hstrip⟩)
    exact ⟨normal,bias,hnormal,hbias,fun x _ hx => htransfer x hx⟩
  · refine ⟨normal,0,hnormal,?_,?_⟩
    · rw [abs_zero]
      linarith [hp.1]
    · intro x hx hstrip
      exact False.elim (hused ⟨x,hx,htransfer x hstrip⟩)

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.VelocityFrameTransfer
