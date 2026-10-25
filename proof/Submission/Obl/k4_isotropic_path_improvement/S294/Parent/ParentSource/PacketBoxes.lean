-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketBoxes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketBoxes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketBoxes.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketBoxes.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames

/-! # Actual fine-packet boxes in a fixed old native frame -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The normalized base of the original incidence. The observation widths
in this definition are immaterial to its first component. -/
def packetBase {W : ℕ} (p : Native.PathData W) (a : Fin p.C) (q : Event) :
    EuclideanSpace ℝ (Fin 3) :=
  (nativeOldBaseFrame p a).obsBase (obs 1 1 q).1

/-- The fine packet's moving center, evaluated at its actual left endpoint
and then expressed in the fixed old frame. -/
def packetBaseCenter {W : ℕ} (p : Native.PathData W) (a b : Fin p.C) :
    EuclideanSpace ℝ (Fin 3) :=
  let t := (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)
  let z := p.c b + t • p.u b
  (nativeOldBaseFrame p a).obsBase (WithLp.toLp 2 ![t, z 0, z 1])

theorem measurable_packetBase {W : ℕ} (p : Native.PathData W) (a : Fin p.C) :
    Measurable (packetBase p a) := by
  exact (nativeOldBaseFrame p a).measurable_obsBase.comp
    (show Measurable (fun q : Event => (obs 1 1 q).1) from by unfold obs x; fun_prop)

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The full fine assignment fit controls a physical spatial error in the
original coordinates. No selected posterior or format exponent is used. -/
theorem packet_physical_error (b : Fin p.C) (q : Event) (hq : q ∈ p.F b) :
    ‖y q.1 q.2 - p.c b - q.2 • p.u b‖ ≤
      p.κ ^ 2 * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by
  rcases hp.2.2.2.2.2.2.2 b with
    ⟨_, _, hdet, _, _, hsize, _, _, _, _, _, hwhole, hsel, _⟩
  have hsel := hsel q hq
  exact Native.physical_error_le_of_frame hdet (by linarith [hp.1])
    (by positivity) (by simpa only [div_eq_mul_inv] using hsize)
    (((hwhole q.1 hsel.2.1).2.2 q.2 hsel.2.2.1).1)

/-- All points of an actual fine packet lie in one explicit base box in
old units. Whole-block source velocity bounds and the actual determinant
floor supply every factor in the radius. -/
theorem packet_base_box (hNk : 1 ≤ Nk) (a b : Fin p.C) {K : ℝ}
    (hK : 0 ≤ K) (ha : ‖p.u a‖ ≤ K + 2 * p.κ ^ 2)
    (hb : ‖p.u b‖ ≤ K + 2 * p.κ ^ 2)
    (q : Event) (hq : q ∈ p.F b) (j : Fin 3) :
    |packetBase p a q j - packetBaseCenter p a b j| ≤
      (1 + p.κ * Nk ^ (2 * δ₀ * L) * (2 * K + 5 * p.κ ^ 2)) *
        ((2 : ℝ) ^ p.T (p.lev a) / (2 : ℝ) ^ p.T (p.lev b)) := by
  let t := (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)
  let h := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  let h₀ := ((2 : ℝ) ^ p.T (p.lev a))⁻¹
  let A := ∑ i, ∑ j, |(p.Q a)⁻¹ i j|
  have hh : 0 < h := by dsimp [h]; positivity
  have hh₀ : 0 < h₀ := by dsimp [h₀]; positivity
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hright : t + h = ((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b) := by
    dsimp [t, h]
    ring
  have hsel := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.2.2.2.1 q hq
  have htime : q.2 ∈ Icc t (t + h) := by
    rw [hright]
    exact hsel.2.2.1
  have hdt : |q.2 - t| ≤ h := by
    rw [abs_of_nonneg (sub_nonneg.mpr htime.1)]
    linarith [htime.2]
  have herror := packet_physical_error hp b q hq
  have hspatial : ‖Matrix.toEuclideanLin (p.Q a)⁻¹
        (y q.1 q.2 - p.c a - q.2 • p.u a) -
      Matrix.toEuclideanLin (p.Q a)⁻¹
        (p.c b + t • p.u b - p.c a - t • p.u a)‖ ≤
        A * (2 * K + 5 * p.κ ^ 2) * h := by
    rw [← map_sub]
    have hid : (y q.1 q.2 - p.c a - q.2 • p.u a) -
        (p.c b + t • p.u b - p.c a - t • p.u a) =
        (y q.1 q.2 - p.c b - q.2 • p.u b) + (q.2 - t) • (p.u b - p.u a) := by
      module
    rw [hid]
    calc
      _ ≤ A * ‖(y q.1 q.2 - p.c b - q.2 • p.u b) +
          (q.2 - t) • (p.u b - p.u a)‖ := Native.matrix_action_norm_le_entry_sum _ _
      _ ≤ A * (‖y q.1 q.2 - p.c b - q.2 • p.u b‖ +
          |q.2 - t| * (‖p.u b‖ + ‖p.u a‖)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        have hsmul : ‖(q.2 - t) • (p.u b - p.u a)‖ ≤
            |q.2 - t| * (‖p.u b‖ + ‖p.u a‖) := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
        exact (norm_add_le _ _).trans (add_le_add le_rfl hsmul)
      _ ≤ A * (p.κ ^ 2 * h + h * ((K + 2 * p.κ ^ 2) + (K + 2 * p.κ ^ 2))) := by
        gcongr
      _ = _ := by ring
  have hinverse : h₀ * A ≤ p.κ * Nk ^ (2 * δ₀ * L) :=
    hp.normalized_inverse_bound hNk a
  have hscale : A * h ≤ p.κ * Nk ^ (2 * δ₀ * L) * (h / h₀) := by
    have hmul := mul_le_mul_of_nonneg_right hinverse (show 0 ≤ h / h₀ by positivity)
    convert hmul using 1 <;> field_simp
  have hratio : h / h₀ = (2 : ℝ) ^ p.T (p.lev a) / (2 : ℝ) ^ p.T (p.lev b) := by
    dsimp [h, h₀]
    field_simp
  have hspatial' : ‖Matrix.toEuclideanLin (p.Q a)⁻¹
        (y q.1 q.2 - p.c a - q.2 • p.u a) -
      Matrix.toEuclideanLin (p.Q a)⁻¹
        (p.c b + t • p.u b - p.c a - t • p.u a)‖ ≤
      (1 + p.κ * Nk ^ (2 * δ₀ * L) * (2 * K + 5 * p.κ ^ 2)) * (h / h₀) := by
    calc
      _ ≤ A * (2 * K + 5 * p.κ ^ 2) * h := hspatial
      _ ≤ (p.κ * Nk ^ (2 * δ₀ * L) * (h / h₀)) *
          (2 * K + 5 * p.κ ^ 2) := by
        convert mul_le_mul_of_nonneg_right hscale
          (show 0 ≤ 2 * K + 5 * p.κ ^ 2 by positivity) using 1 <;> ring
      _ ≤ _ := by nlinarith [show 0 ≤ h / h₀ by positivity]
  have hcoord (i : Fin 2) :
      |(Matrix.toEuclideanLin (p.Q a)⁻¹
          (y q.1 q.2 - p.c a - q.2 • p.u a)) i -
        (Matrix.toEuclideanLin (p.Q a)⁻¹
          (p.c b + t • p.u b - p.c a - t • p.u a)) i| ≤
        (1 + p.κ * Nk ^ (2 * δ₀ * L) * (2 * K + 5 * p.κ ^ 2)) * (h / h₀) := by
    exact (PiLp.norm_apply_le _ i).trans hspatial'
  rw [← hratio]
  fin_cases j
  · change |(q.2 - _) / h₀ - (t - _) / h₀| ≤ _
    rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hh₀]
    exact (div_le_div_of_nonneg_right hdt hh₀.le).trans
      (by nlinarith [show 0 ≤ h / h₀ by positivity,
          show 0 ≤ p.κ * Nk ^ (2 * δ₀ * L) * (2 * K + 5 * p.κ ^ 2) by positivity])
  · convert hcoord 0 using 1 <;>
      simp [packetBase, packetBaseCenter, nativeOldBaseFrame,
        Submission.Lib.K4ChartLifting.Frame.obsBase, obs, x, y, t,
        Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail,
        PiLp.add_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]
  · convert hcoord 1 using 1 <;>
      simp [packetBase, packetBaseCenter, nativeOldBaseFrame,
        Submission.Lib.K4ChartLifting.Frame.obsBase, obs, x, y, t,
        Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail,
        PiLp.add_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]

/-- The actual mesh is resolved by the actual time ratio, up to four
frozen grid errors. This supplies the size condition in the cell cover. -/
theorem path_relative_mesh_le_time_ratio (hNk : 1 ≤ Nk) (hL : 0 ≤ L)
    (hκ₁ : κ₁ ≤ 1) (i j : ℕ) (ha : i < m) (hb : j < m)
    (hs : s (i) ≤ s (j)) :
    Nk ^ (-(p.r (j) - p.r (i))) ≤
      Nk ^ (4 * δ₀ * L) *
        ((2 : ℝ) ^ p.T (i) / (2 : ℝ) ^ p.T (j)) := by
  have hNpos : 0 < Nk := zero_lt_one.trans_le hNk
  obtain ⟨hra, _, hTa, _, _, _⟩ := hp.2.2.2.2.1 (i) ha
  obtain ⟨hrb, _, _, hTb, _, _⟩ := hp.2.2.2.2.1 (j) hb
  have hexp : -(p.r (j) - p.r (i)) ≤
      4 * δ₀ * L + ((κ₁ * s (i) - δ₀) * L -
        (κ₁ * s (j) + δ₀) * L) := by
    have hprod : 0 ≤ (1 - κ₁) * (s (j) - s (i)) * L := by positivity
    rcases abs_le.mp hra with ⟨hra₀, hra₁⟩
    rcases abs_le.mp hrb with ⟨hrb₀, hrb₁⟩
    nlinarith
  calc
    _ ≤ Nk ^ (4 * δ₀ * L + ((κ₁ * s (i) - δ₀) * L -
        (κ₁ * s (j) + δ₀) * L)) := Real.rpow_le_rpow_of_exponent_le hNk hexp
    _ = Nk ^ (4 * δ₀ * L) *
        (Nk ^ ((κ₁ * s (i) - δ₀) * L) /
          Nk ^ ((κ₁ * s (j) + δ₀) * L)) := by
      rw [Real.rpow_add hNpos, Real.rpow_sub hNpos]
    _ ≤ _ := by
      gcongr

end Path

/-- The exact source problem supplies both packet center-speed bounds,
so the preceding base box has no external geometric hypothesis. -/
theorem source_packet_base_box
    {d : Native.ProblemData} (hd : d.Valid) {k : ℕ} {p : Native.PathData (d.W k)}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (a b : Fin p.C) (q : Event) (hq : q ∈ p.F b) (j : Fin 3) :
    |packetBase p a q j - packetBaseCenter p a b j| ≤
      (1 + p.κ * d.N k ^ (2 * δ₀ * d.L) * (2 * d.K k + 5 * p.κ ^ 2)) *
        ((2 : ℝ) ^ p.T (p.lev a) / (2 : ℝ) ^ p.T (p.lev b)) := by
  exact packet_base_box hp (by linarith [hd.1 k]) a b
    (by linarith [(hd.2.2.1).1 k])
    (hd.path_frame_bounds hp a).1 (hd.path_frame_bounds hp b).1 q hq j

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
