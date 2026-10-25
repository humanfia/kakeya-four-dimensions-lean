-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.UnitPrismGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/- Adapted from this workspace: o196/x0579, commit5ac3173, UnitGeometry.lean. -/
import Mathlib
import Submission.WZ.ChallengeDeps
noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric

local notation "Sp" => LeanEval.Analysis.WangZahlKakeya.Space

def unitAxis (k : Fin 3) : Sp := EuclideanSpace.single k 1

def unitCarrier (k : Fin 3) : Set Sp :=
  Metric.thickening 1 (segment ℝ (-(1 / 2 : ℝ) • unitAxis k)
    (-(1 / 2 : ℝ) • unitAxis k + unitAxis k))

theorem norm_unitAxis (k : Fin 3) : ‖unitAxis k‖ = 1 := by
  simp [unitAxis]

theorem axis_point_mem_segment (k : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    t • unitAxis k ∈ segment ℝ (-(1 / 2 : ℝ) • unitAxis k)
      (-(1 / 2 : ℝ) • unitAxis k + unitAxis k) := by
  rw [segment_eq_image']
  refine ⟨t + 1 / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  module

theorem ball_zero_subset_unitCarrier (k : Fin 3) :
    ball (0 : Sp) 1 ⊆ unitCarrier k := by
  intro p hp
  apply Metric.mem_thickening_iff.mpr
  refine ⟨0, ?_, by simpa only [mem_ball, dist_zero_right] using hp⟩
  simpa only [zero_smul] using axis_point_mem_segment k (t := 0) (by norm_num)

/-- Three centered unit tubes cover every small ball centered in the closed
unit ball. The tube chosen for the ball still contains the entire open unit ball. -/
theorem exists_unitCarrier_of_small_ball {q : Sp} (hq : ‖q‖ ≤ 1) :
    ∃ k : Fin 3, closedBall q (1 / 20) ⊆ unitCarrier k := by
  by_cases hsmall : ‖q‖ ≤ 9 / 10
  · refine ⟨0, fun p hp => ball_zero_subset_unitCarrier 0 ?_⟩
    have hpq : ‖p - q‖ ≤ 1 / 20 := by
      simpa only [mem_closedBall, dist_eq_norm] using hp
    have hpn := norm_add_le (p - q) q
    rw [sub_add_cancel] at hpn
    rw [mem_ball, dist_zero_right]
    linarith
  · have hlarge : ∃ k : Fin 3, 1 / 2 ≤ |q k| := by
      by_contra h
      push Not at h
      have hsq (k : Fin 3) : (q k) ^ 2 < 1 / 4 := by
        have := (sq_lt_sq₀ (abs_nonneg (q k)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr (h k)
        nlinarith [sq_abs (q k)]
      have hnorm := EuclideanSpace.real_norm_sq_eq q
      rw [Fin.sum_univ_three] at hnorm
      have hqpos := norm_nonneg q
      nlinarith [hsq 0, hsq 1, hsq 2]
    obtain ⟨k, hk⟩ := hlarge
    let t : ℝ := if 0 ≤ q k then 1 / 2 else -(1 / 2)
    have ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      dsimp [t]
      split_ifs <;> norm_num
    have htabs : |t| = 1 / 2 := by
      dsimp [t]
      split_ifs <;> norm_num
    have hinner : 2 * inner ℝ q (t • unitAxis k) = |q k| := by
      simp only [inner_smul_right, unitAxis, EuclideanSpace.inner_single_right,
        RCLike.conj_to_real, one_mul]
      dsimp [t]
      split_ifs with h
      · rw [abs_of_nonneg h]
        ring
      · rw [abs_of_neg (lt_of_not_ge h)]
        ring
    have hnormpoint : ‖t • unitAxis k‖ = 1 / 2 := by
      rw [norm_smul, norm_unitAxis, Real.norm_eq_abs, htabs, mul_one]
    have hdist : dist q (t • unitAxis k) ≤ 9 / 10 := by
      rw [dist_eq_norm]
      have hh := norm_sub_sq_real q (t • unitAxis k)
      rw [hnormpoint] at hh
      have hqpos := norm_nonneg q
      have hp := norm_nonneg (q - t • unitAxis k)
      nlinarith
    refine ⟨k, ?_⟩
    intro p hp
    apply Metric.mem_thickening_iff.mpr
    refine ⟨t • unitAxis k, axis_point_mem_segment k ht, ?_⟩
    have hpq : dist p q ≤ 1 / 20 := hp
    have htriangle := dist_triangle p q (t • unitAxis k)
    linarith

end WangZahlLot.Obl.wz_broad_grains_improvement
