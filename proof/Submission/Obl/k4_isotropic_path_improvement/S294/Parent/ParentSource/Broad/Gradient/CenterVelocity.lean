-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.CenterVelocity, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/CenterVelocity.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/CenterVelocity.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFrameChange
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Problem

/-!
# Original packet center velocities have subpower size

A positive original assignment supplies a line obeying the original velocity bound.
The existing normalized and denormalized frame estimates cancel the packet clock.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native

noncomputable section

section Path

variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- Only one actual assigned line is needed to control the packet's physical center velocity. -/
theorem Native.PathData.Valid.center_velocity_of_assigned_line
    (b : Fin p.C) (l : ℕ × (Fin 6 → ℝ)) (hl : l ∈ p.A b) {Kv : ℝ} (hv : ‖v l‖ ≤ Kv) :
    ‖p.u b‖ ≤ Kv + 2 * p.κ ^ 2 := by
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hnorm : ‖p.normalizedFrameOperator b (v l - p.u b)‖ ≤ 2 * p.κ :=
    hp.normalized_velocity_bound b l hl
  have hdenorm := hp.denormalized_frame_operator_bound b
    (p.normalizedFrameOperator b (v l - p.u b))
  rw [hp.denormalized_normalized_frame_cancel] at hdenorm
  have hdiff : ‖v l - p.u b‖ ≤ 2 * p.κ ^ 2 := by
    calc
      _ ≤ p.κ * ‖p.normalizedFrameOperator b (v l - p.u b)‖ := hdenorm
      _ ≤ p.κ * (2 * p.κ) := mul_le_mul_of_nonneg_left hnorm hκ
      _ = _ := by ring
  calc
    ‖p.u b‖ = ‖v l - (v l - p.u b)‖ := by congr 1; abel
    _ ≤ ‖v l‖ + ‖v l - p.u b‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hv hdiff

/-- The witness is chosen from the unchanged original prior, using positive assignment mass. -/
theorem Native.PathData.Valid.center_velocity_of_original_ae (hN : 0 < N)
    (b : Fin p.C) {Kv : ℝ} (hv : ∀ᵐ l ∂ν (p.γ b), ‖v l‖ ≤ Kv) :
    ‖p.u b‖ ≤ Kv + 2 * p.κ ^ 2 := by
  obtain ⟨l, hl, hv⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hp.assignment_mass_pos hN b).ne'
    ((ae_mono Measure.restrict_le_self) hv)
  exact hp.center_velocity_of_assigned_line b l hl hv

end Path

/-- The literal original problem supplies a uniform bound for every actual packet center. -/
theorem original_packet_center_velocity {d : ProblemData} (hd : d.Valid)
    {k m : ℕ} {p : PathData (d.W k)} {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ) (b : Fin p.C) :
    ‖p.u b‖ ≤ d.K k + 2 * p.κ ^ 2 :=
  (hd.path_frame_bounds hp b).1

/-- The explicit unshearing coefficient is a fixed power once all original bounds
are dominated by `K`. No coefficient-format exponent enters. -/
theorem physical_unshearing_power {κ F U K : ℝ} (hK : 9 ≤ K)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ K) (hF0 : 0 ≤ F) (hF : F ≤ K)
    (hU0 : 0 ≤ U) (hU : U ≤ K + 2 * κ ^ 2) :
    1 + 2 * (κ * F) * (1 + U) ≤ K ^ 5 := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hκsq : κ ^ 2 ≤ K ^ 2 := by nlinarith
  have hinner : 1 + U ≤ 4 * K ^ 2 := by nlinarith
  have hpow : (1 : ℝ) ≤ K ^ 4 := one_le_pow₀ hK1
  calc
    _ ≤ 1 + 2 * (K * K) * (4 * K ^ 2) := by gcongr
    _ = 1 + 8 * K ^ 4 := by ring
    _ ≤ 9 * K ^ 4 := by linarith
    _ ≤ K ^ 5 := by
      simpa only [pow_succ, mul_comm] using
        mul_le_mul_of_nonneg_right (by linarith : (9 : ℝ) ≤ K) (pow_nonneg hK0 4)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
