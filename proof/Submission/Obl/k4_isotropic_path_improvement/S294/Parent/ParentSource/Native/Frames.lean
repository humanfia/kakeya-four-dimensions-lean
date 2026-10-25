-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.Frames, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/Frames.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/Frames.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204/x0749, commit 6f2478eeecc213e54a9862f7bddfc3321aef9b01;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/Frames.lean. General numerical proofs are imported from accepted lib.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Problem
import Submission.Lib.K4NativePreparationNumerics.Frames

/-! General native preparation helpers imported from gate-accepted library g00875. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped BigOperators

export Submission.Lib.K4NativePreparationNumerics (
  euclidean_norm_le_sum_abs
  matrix_action_norm_le_entry_sum
  inverse_entry_sum_two
  normalized_inverse_frame_bound
  physical_error_le_of_frame
  affine_velocity_bound
  affine_center_velocity_bound)

theorem y_eq_affine (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    y l t = WithLp.toLp 2 ![l.2 0, l.2 1] + t • v l := by
  ext i
  fin_cases i <;> simp [y, x, v, PiLp.add_apply, PiLp.smul_apply]

/-- Every saturated path packet has center and center velocity bounds depending
on actual subpower losses, rather than on its input format exponent. -/
theorem ProblemData.Valid.path_frame_bounds {d : ProblemData} (h : d.Valid)
    {k : ℕ} {p : PathData (d.W k)} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) :
    ‖p.u b‖ ≤ d.K k + 2 * p.κ ^ 2 ∧
      ‖p.c b‖ ≤ 2 * d.K k + 3 * p.κ ^ 2 ∧
      ‖p.c b‖ + ‖p.u b‖ ≤ 3 * d.K k + 5 * p.κ ^ 2 := by
  have hN : 0 < d.N k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (h.1 k)
  obtain ⟨l, hl, hnative⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hp.assignment_mass_pos hN b).ne' (ae_restrict_of_ae (h.native_bounds k (p.γ b)))
  rcases hp.2.2.2.2.2.2.2 b with ⟨_, hj, hdet, _, _, hsize, _, _, _, _, _, hfit, _⟩
  let q : ℝ := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  let t : ℝ := (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)
  have hden : 0 < (2 : ℝ) ^ p.T (p.lev b) := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    have hden1 : 1 ≤ (2 : ℝ) ^ p.T (p.lev b) := one_le_pow₀ (by norm_num)
    simpa [q, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hright : t + q = ((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b) := by
    dsimp [t, q]
    ring
  have hjend : (p.j b : ℝ) + 1 ≤ (2 : ℝ) ^ p.T (p.lev b) := by
    exact_mod_cast Nat.succ_le_of_lt hj
  have htq1 : t + q ≤ 1 := by
    rw [hright]
    exact (div_le_one hden).mpr hjend
  have ht1 : t ≤ 1 := by linarith
  have hinterval : Icc t (t + q) =
      Icc ((p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) := by
    rw [hright]
  have hphysical (z : ℝ) (hz : z ∈ Icc t (t + q)) :
      ‖y l z - p.c b - z • p.u b‖ ≤ p.κ ^ 2 * q := by
    apply physical_error_le_of_frame hdet (by linarith [hp.1]) hq
      (by simpa [q, div_eq_mul_inv] using hsize)
    exact ((hfit l hl).2.2 z (hinterval ▸ hz)).1
  have hstart := hphysical t ⟨le_rfl, by linarith⟩
  have hend := hphysical (t + q) ⟨by linarith, le_rfl⟩
  have hy := hnative t ⟨ht, ht1⟩
  simp only [y_eq_affine] at hstart hend hy
  exact affine_center_velocity_bound _ _ _ _ t q (p.κ ^ 2) (d.K k)
    ht ht1 hq hq1 (by positivity) hstart hend
    (by linarith [norm_nonneg (v l)]) (by
      have hz := norm_nonneg (y l t)
      rw [y_eq_affine] at hz
      linarith)

/-- The block-normalized inverse frame also has a bound independent of Mp:
only the fixed profile tolerance and actual path factor enter. -/
theorem PathData.Valid.normalized_inverse_bound {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 1 ≤ Nk) (b : Fin p.C) :
    ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * (∑ i, ∑ j, |(p.Q b)⁻¹ i j|) ≤
      p.κ * Nk ^ (2 * δ₀ * L) := by
  rcases h.2.2.2.2.2.2.2 b with
    ⟨hlev, _, _, _, _, hsize, _, _, _, _, _, _, _, _, _, hdetlow, _⟩
  obtain ⟨_, _, _, _, hnw, _⟩ := h.2.2.2.2.1 (p.lev b) hlev
  simp only [zero_mul, sub_zero] at hnw
  have hnwle : p.nw (p.lev b) ≤ δ₀ * L := (le_abs_self _).trans hnw
  have hraw : Nk ^ (-(2 * δ₀ * L)) ≤ |(p.Q b).det| * (4 : ℝ) ^ p.T (p.lev b) := by
    exact (Real.rpow_le_rpow_of_exponent_le hNk (by linarith)).trans hdetlow
  have hpow : (4 : ℝ) ^ p.T (p.lev b) = ((2 : ℝ) ^ p.T (p.lev b)) ^ 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hpow] at hraw
  let q : ℝ := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hfloor : Nk ^ (-(2 * δ₀ * L)) * q ^ 2 ≤ |(p.Q b).det| := by
    have hr := (div_le_iff₀ (show 0 < ((2 : ℝ) ^ p.T (p.lev b)) ^ 2 by positivity)).mpr hraw
    simpa only [q, div_eq_mul_inv, inv_pow] using hr
  have hbound := normalized_inverse_frame_bound (κ := p.κ) hq (by linarith [h.1])
    (show 0 < Nk ^ (-(2 * δ₀ * L)) by positivity)
    (by simpa only [div_eq_mul_inv, q] using hsize) hfloor
  simpa only [q, Real.rpow_neg (show 0 ≤ Nk by linarith), div_eq_mul_inv, inv_inv] using hbound

/-- In a packet's own space and time units every assigned planar velocity is
bounded by the actual path factor. No input format exponent enters this bound. -/
theorem PathData.Valid.normalized_velocity_bound {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (l : ℕ × (Fin 6 → ℝ)) (hl : l ∈ p.A b) :
    ‖((2 : ℝ) ^ p.T (p.lev b))⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹ (v l - p.u b)‖ ≤
      2 * p.κ := by
  rcases h.2.2.2.2.2.2.2 b with ⟨_, _, _, _, _, _, _, _, _, _, _, hfit, _⟩
  let q : ℝ := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  let t : ℝ := (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)
  have hq : 0 < q := by dsimp [q]; positivity
  have hright : t + q = ((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b) := by
    dsimp [t, q]
    ring
  have hstart : ‖Matrix.toEuclideanLin (p.Q b)⁻¹ (y l t - p.c b - t • p.u b)‖ ≤ p.κ := by
    apply ((hfit l hl).2.2 t _).1
    constructor
    · exact le_rfl
    · change t ≤ ((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)
      rw [← hright]
      linarith
  have hend : ‖Matrix.toEuclideanLin (p.Q b)⁻¹
      (y l (t + q) - p.c b - (t + q) • p.u b)‖ ≤ p.κ := by
    apply ((hfit l hl).2.2 (t + q) _).1
    constructor
    · change t ≤ t + q
      linarith
    · rw [hright]
  have hid : q • Matrix.toEuclideanLin (p.Q b)⁻¹ (v l - p.u b) =
      Matrix.toEuclideanLin (p.Q b)⁻¹ (y l (t + q) - p.c b - (t + q) • p.u b) -
      Matrix.toEuclideanLin (p.Q b)⁻¹ (y l t - p.c b - t • p.u b) := by
    rw [← map_smul, ← map_sub]
    congr 1
    simp only [y_eq_affine]
    module
  change ‖q • _‖ ≤ _
  rw [hid]
  exact (norm_sub_le _ _).trans (by linarith)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
