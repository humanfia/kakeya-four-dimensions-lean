-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.ScalarAlignment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_depth_step.Shifts

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open Set Metric

noncomputable def axialMidpoint (x v : Space) : ℝ := inner ℝ v (x + (1 / 2 : ℝ) • v)
noncomputable def axisFoot (x v : Space) : Space :=
  x + (1 / 2 : ℝ) • v - axialMidpoint x v • v
noncomputable def alignBase (t : ℝ) (x v : Space) : Space :=
  x + (t - axialMidpoint x v) • v

lemma axisFoot_inner {x v : Space} (hv : ‖v‖ = 1) : inner ℝ v (axisFoot x v) = 0 := by
  simp only [axisFoot, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv,
    one_pow, mul_one]
  simp [axialMidpoint]

lemma alignBase_eq (t : ℝ) (x v : Space) :
    alignBase t x v = axisFoot x v + (t - 1 / 2) • v := by
  unfold alignBase axisFoot
  module

lemma alignBase_end_eq (t : ℝ) (x v : Space) :
    alignBase t x v + v = axisFoot x v + (t + 1 / 2) • v := by
  unfold alignBase axisFoot
  module

lemma alignBase_midpoint {x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    axialMidpoint (alignBase t x v) v = t := by
  unfold axialMidpoint
  rw [alignBase_eq]
  simp only [inner_add_right, inner_smul_right, axisFoot_inner hv,
    real_inner_self_eq_norm_sq, hv, one_pow]
  ring

lemma axisFoot_norm_sq {x v : Space} (hv : ‖v‖ = 1) (a : ℝ) :
    ‖axisFoot x v + a • v‖ ^ 2 = ‖axisFoot x v‖ ^ 2 + a ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, real_inner_comm v (axisFoot x v),
    axisFoot_inner hv, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
  ring

lemma alignBase_norm_sq {x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖alignBase t x v‖ ^ 2 = ‖axisFoot x v‖ ^ 2 + (t - 1 / 2) ^ 2 := by
  rw [alignBase_eq, axisFoot_norm_sq hv]

lemma alignBase_end_norm_sq {x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖alignBase t x v + v‖ ^ 2 = ‖axisFoot x v‖ ^ 2 + (t + 1 / 2) ^ 2 := by
  rw [alignBase_end_eq, axisFoot_norm_sq hv]

lemma alignBase_self (x v : Space) : alignBase (axialMidpoint x v) x v = x := by
  simp [alignBase]

/-- Moving the signed axial midpoint toward zero cannot enlarge the larger endpoint norm. -/
theorem alignBase_endpoints {t R : ℝ} {x v : Space} (hv : ‖v‖ = 1)
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (hxv : ‖x + v‖ ≤ R)
    (ht : |t| ≤ |axialMidpoint x v|) :
    ‖alignBase t x v‖ ≤ R ∧ ‖alignBase t x v + v‖ ≤ R := by
  let a := axialMidpoint x v
  have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := sq_le_sq₀ (norm_nonneg _) hR |>.mpr hx
  have hxv2 : ‖x + v‖ ^ 2 ≤ R ^ 2 := sq_le_sq₀ (norm_nonneg _) hR |>.mpr hxv
  have hmax : ‖axisFoot x v‖ ^ 2 + (|a| + 1 / 2) ^ 2 ≤ R ^ 2 := by
    rcases le_total 0 a with ha | ha
    · have h := alignBase_end_norm_sq (x := x) hv a
      rw [show a = axialMidpoint x v from rfl, alignBase_self] at h
      rw [abs_of_nonneg ha]
      linarith
    · have h := alignBase_norm_sq (x := x) hv a
      rw [show a = axialMidpoint x v from rfl, alignBase_self] at h
      rw [abs_of_nonpos ha]
      nlinarith
  have hminus : |t - 1 / 2| ≤ |a| + 1 / 2 := by
    calc
      _ ≤ |t| + |(1 / 2 : ℝ)| := abs_sub _ _
      _ ≤ _ := by norm_num; exact ht
  have hplus : |t + 1 / 2| ≤ |a| + 1 / 2 := by
    calc
      _ ≤ |t| + |(1 / 2 : ℝ)| := abs_add_le _ _
      _ ≤ _ := by norm_num; exact ht
  have hm2 : (t - 1 / 2) ^ 2 ≤ (|a| + 1 / 2) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (t - 1 / 2)) (by positivity)).mpr hminus
  have hp2 : (t + 1 / 2) ^ 2 ≤ (|a| + 1 / 2) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (t + 1 / 2)) (by positivity)).mpr hplus
  constructor
  · have he := alignBase_norm_sq (x := x) hv t
    nlinarith [norm_nonneg (alignBase t x v)]
  · have he := alignBase_end_norm_sq (x := x) hv t
    nlinarith [norm_nonneg (alignBase t x v + v)]

lemma norm_add_radius_le {δ : ℝ} (hδ : 0 < δ) {x v : Space} (hv : ‖v‖ = 1)
    (hball : ball x δ ⊆ ball (0 : Space) 1) : ‖x‖ + δ ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    have hd : δ ≤ 1 := by
      by_contra h
      have hmem : v ∈ ball (0 : Space) δ := by simp [hv]; linarith
      have hh := hball hmem
      simp [hv] at hh
    simpa using hd
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hx1 : ‖x‖ < 1 := by
      have hh := hball (mem_ball_self hδ)
      simpa using hh
    by_contra h
    have hbad : 1 < ‖x‖ + δ := lt_of_not_ge h
    let s := (δ + 1 - ‖x‖) / 2
    have hs : 0 < s := by dsimp [s]; linarith
    have hsδ : s < δ := by dsimp [s]; linarith
    have hs1 : 1 < ‖x‖ + s := by dsimp [s]; linarith
    let p := (1 + s / ‖x‖) • x
    have hdist : dist p x = s := by
      rw [dist_eq_norm]
      have he : p - x = (s / ‖x‖) • x := by dsimp [p]; module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hs hxn), div_mul_cancel₀ _ hxn.ne']
    have hp : p ∈ ball (0 : Space) 1 := hball (by rwa [mem_ball, hdist])
    have hpnorm : ‖p‖ = ‖x‖ + s := by
      dsimp [p]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    have hh : ‖p‖ < 1 := by simpa using hp
    linarith

/-- Scalar alignment toward zero preserves the exact containing unit ball. -/
theorem alignBase_tube_subset_ball {δ t : ℝ} (hδ : 0 < δ) {x v : Space}
    (hv : ‖v‖ = 1) (hball : Tube δ x v ⊆ ball (0 : Space) 1)
    (ht : |t| ≤ |axialMidpoint x v|) : Tube δ (alignBase t x v) v ⊆ ball (0 : Space) 1 := by
  have hx := norm_add_radius_le hδ hv
    ((ball_subset_thickening (left_mem_segment ℝ x (x + v)) δ).trans hball)
  have hxv := norm_add_radius_le hδ hv
    ((ball_subset_thickening (right_mem_segment ℝ x (x + v)) δ).trans hball)
  have hR : 0 ≤ 1 - δ := by linarith [norm_nonneg x]
  obtain ⟨h₀, h₁⟩ := alignBase_endpoints hv hR (by linarith) (by linarith) ht
  have hseg : segment ℝ (alignBase t x v) (alignBase t x v + v) ⊆
      closedBall (0 : Space) (1 - δ) :=
    (convex_closedBall (0 : Space) (1 - δ)).segment_subset (by simpa using h₀) (by simpa using h₁)
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  have hzn : ‖z‖ ≤ 1 - δ := by simpa using hseg hz
  have hn := norm_le_norm_add_norm_sub z p
  rw [← dist_eq_norm, dist_comm z p] at hn
  rw [mem_ball, dist_zero_right]
  linarith

end WangZahlLot.Obl.wz_tower_depth_step
