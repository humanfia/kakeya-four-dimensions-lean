-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.GBeAux.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.GridCount
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Regularize
import Submission.WZ.Obl.wz_intermediate_twist_normalization.NoBad
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Slice

/-!
# Auxiliary facts for graceful B

* The thin cylinder `safeCyl r e` is convex, bounded, open, of volume at most `8 r²`; a family
  inside it with convex count `Kt |W + 2e(W - W)|` has at most `216 r² Kt` tubes.
* Horizontal translates by at most `r / √2` keep tubes of `safeCyl r e` in the unit ball.
* Grid translations have horizontal size at most `√2 h M`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube proj fib)
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib ofTwist_zero ofTwist_one
  ofTwist_two)
open WangZahlLot.Obl.wz_compact_offset_normalization (norm_sq_eq abs_coord_le_norm
  norm_le_of_sq_le)

theorem safeCyl_convex (r e : ℝ) : Convex ℝ (safeCyl r e) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  refine ⟨?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have h1 : (a * p 0 + b * q 0) ^ 2 + (a * p 1 + b * q 1) ^ 2 ≤
        a * (p 0 ^ 2 + p 1 ^ 2) + b * (q 0 ^ 2 + q 1 ^ 2) := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1), mul_nonneg ha hb]
    have h2 : a * (p 0 ^ 2 + p 1 ^ 2) + b * (q 0 ^ 2 + q 1 ^ 2) < r ^ 2 := by
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · rw [← ha0] at hab ⊢; simp at hab; rw [hab]; linarith
      · have e1 := mul_lt_mul_of_pos_left hp1 ha0
        have e2 := mul_le_mul_of_nonneg_left hq1.le hb
        have e3 : a * r ^ 2 + b * r ^ 2 = r ^ 2 := by rw [← add_mul, hab, one_mul]
        linarith
    linarith
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have h1 : |a * p 2 + b * q 2| ≤ a * |p 2| + b * |q 2| := by
      calc |a * p 2 + b * q 2| ≤ |a * p 2| + |b * q 2| := abs_add_le _ _
        _ = a * |p 2| + b * |q 2| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · rw [← ha0] at hab h1 ⊢; simp at hab; rw [hab] at h1 ⊢; simp at h1 ⊢; exact hq2
    · have e1 := mul_lt_mul_of_pos_left hp2 ha0
      have e2 := mul_le_mul_of_nonneg_left hq2.le hb
      have e3 : a * (1 - e) + b * (1 - e) = 1 - e := by rw [← add_mul, hab, one_mul]
      linarith

theorem safeCyl_subset_ball {r e : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) (he : 0 ≤ e) :
    safeCyl r e ⊆ ball 0 2 := by
  intro p ⟨h1, h2⟩
  rw [mem_ball_zero_iff]
  have h3 : p 2 ^ 2 < 1 := by
    have : |p 2| < 1 := by linarith
    nlinarith [abs_nonneg (p 2), sq_abs (p 2)]
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hsq : ‖p‖ ^ 2 < 2 ^ 2 := by rw [norm_sq_eq]; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

theorem safeCyl_bounded {r e : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) (he : 0 ≤ e) :
    Bornology.IsBounded (safeCyl r e) :=
  isBounded_ball.subset (safeCyl_subset_ball hr0 hr he)

theorem measurableSet_safeCyl (r e : ℝ) : MeasurableSet (safeCyl r e) := by
  have h0 : Continuous fun p : Space => p 0 ^ 2 + p 1 ^ 2 := by fun_prop
  have h2 : Continuous fun p : Space => |p 2| := by fun_prop
  exact (measurableSet_lt h0.measurable measurable_const).inter
    (measurableSet_lt h2.measurable measurable_const)

/-- The volume of the thin cylinder. -/
theorem volume_safeCyl_le {r e : ℝ} (hr : 0 ≤ r) (he : 0 ≤ e) :
    volume (safeCyl r e) ≤ ENNReal.ofReal (8 * r ^ 2) := by
  set f0 : ℝ → ℝ := fun _ => 0
  have hfib : ∀ u z, volume (grainFib f0 (safeCyl r e) u z) ≤ ENNReal.ofReal (2 * r) := by
    intro u z
    have hsub : grainFib f0 (safeCyl r e) u z ⊆ Icc (-r) r := by
      intro y hy
      obtain ⟨h1, -⟩ := hy
      simp only [ofTwist_zero, ofTwist_one] at h1
      have : y ^ 2 < r ^ 2 := by nlinarith [sq_nonneg (u - f0 z * y)]
      exact ⟨by nlinarith, by nlinarith⟩
    calc volume (grainFib f0 (safeCyl r e) u z) ≤ volume (Icc (-r) r) := measure_mono hsub
      _ = ENNReal.ofReal (2 * r) := by rw [Real.volume_Icc]; congr 1; ring
  have hloc : ∀ u z, (grainFib f0 (safeCyl r e) u z).Nonempty →
      z ∈ Icc (-1 : ℝ) 1 ∧ |u - (fun _ => (0 : ℝ)) z| ≤ r := by
    intro u z ⟨y, h1, h2⟩
    simp only [ofTwist_zero, ofTwist_one, ofTwist_two, f0, zero_mul, sub_zero] at h1 h2
    refine ⟨⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩, ?_⟩
    have : u ^ 2 < r ^ 2 := by nlinarith [sq_nonneg y]
    rw [sub_zero]
    exact abs_le_of_sq_le_sq' (by nlinarith) hr |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
  have h := volume_le_of_fib continuous_const (measurableSet_safeCyl r e) (by positivity) hfib hloc
  rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-- A family in the thin cylinder with the enlarged convex count has at most `216 r² Kt`
tubes. -/
theorem card_le_of_safeCyl {ρ r e Kt : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (he : 0 ≤ e)
    (he4 : e ≤ 1 / 4) {m : ℕ} (hm : 0 < m) {x v : Fin m → Space}
    (hcyl : ∀ i, tube ρ (x i) (v i) ⊆ safeCyl r e)
    (hcount : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | tube ρ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal Kt * volume (W + (2 * e) • (W - W))) :
    (m : ℝ) ≤ Kt * (216 * r ^ 2) := by
  have h1 := hcount _ (safeCyl_convex r e)
  have hall : {i | tube ρ (x i) (v i) ⊆ safeCyl r e} = Set.univ := by
    ext i; simp [hcyl i]
  rw [hall, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := volume_add_smul_sub_le (safeCyl_convex r e) (safeCyl_bounded hr hr1 he)
    (t := 2 * e) (by positivity)
  have h3 := volume_safeCyl_le hr he
  have h4 : volume (safeCyl r e + (2 * e) • (safeCyl r e - safeCyl r e)) ≤
      ENNReal.ofReal (216 * r ^ 2) := by
    refine h2.trans ?_
    calc ENNReal.ofReal ((1 + 4 * (2 * e)) ^ 3) * volume (safeCyl r e)
        ≤ ENNReal.ofReal 27 * ENNReal.ofReal (8 * r ^ 2) := by
          gcongr
          have : 1 + 4 * (2 * e) ≤ 3 := by linarith
          calc (1 + 4 * (2 * e)) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (by linarith) this 3
            _ = 27 := by norm_num
      _ = ENNReal.ofReal (216 * r ^ 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have h5 := h1.trans (mul_le_mul_right h4 _)
  rw [← ENNReal.ofReal_mul' (by positivity)] at h5
  by_cases hKt : 0 ≤ Kt
  · exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h5
  · exfalso
    push Not at hKt
    have h6 : Kt * (216 * r ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hKt.le (by positivity)
    rw [ENNReal.ofReal_of_nonpos h6] at h5
    have h8 : (m : ℝ) ≤ 0 := ENNReal.ofReal_eq_zero.mp (le_antisymm h5 bot_le)
    have : (0 : ℝ) < m := by exact_mod_cast hm
    linarith

/-- Horizontal translates of tubes in the thin cylinder stay in the unit ball. -/
theorem translate_subset_ball {ρ r e : ℝ} (he16 : 16 * r ^ 2 ≤ e) (he4 : e ≤ 1 / 4)
    {x v s : Space} (hT : tube ρ x v ⊆ safeCyl r e) (hs2 : s 2 = 0)
    (hs : s 0 ^ 2 + s 1 ^ 2 ≤ r ^ 2) : tube ρ (x + s) v ⊆ ball 0 1 := by
  rw [tube_translate]
  intro p hp
  obtain ⟨h1, h2⟩ := hT hp
  simp only [PiLp.sub_apply, hs2, sub_zero] at h1 h2
  rw [mem_ball_zero_iff]
  have he0 : 0 ≤ e := by nlinarith [sq_nonneg r]
  have h3 : p 2 ^ 2 ≤ (1 - e) ^ 2 := by
    have : |p 2| ≤ 1 - e := h2.le
    have h0 : 0 ≤ 1 - e := by linarith
    calc p 2 ^ 2 = |p 2| ^ 2 := (sq_abs _).symm
      _ ≤ (1 - e) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have h4 : p 0 ^ 2 + p 1 ^ 2 ≤ 2 * ((p 0 - s 0) ^ 2 + (p 1 - s 1) ^ 2) + 2 * (s 0 ^ 2 + s 1 ^ 2) := by
    nlinarith [sq_nonneg (p 0 - 2 * s 0), sq_nonneg (p 1 - 2 * s 1)]
  have hsq : ‖p‖ ^ 2 < 1 ^ 2 := by
    rw [norm_sq_eq]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

/-- Grid translations are short. -/
theorem sgrid_sq_le {h : ℝ} (hh : 0 ≤ h) (M : ℕ) (a b : Fin (2 * M + 1)) :
    sgrid h M a b 0 ^ 2 + sgrid h M a b 1 ^ 2 ≤ 2 * (h * M) ^ 2 := by
  simp only [sgrid_zero, sgrid_one]
  have ha : |((a : ℝ) - M)| ≤ M := by
    have h1 : (a : ℕ) < 2 * M + 1 := a.isLt
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ (a : ℕ) := Nat.cast_nonneg _; linarith
    · have : ((a : ℕ) : ℝ) ≤ 2 * M := by exact_mod_cast (by omega : (a : ℕ) ≤ 2 * M)
      linarith
  have hb : |((b : ℝ) - M)| ≤ M := by
    have h1 : (b : ℕ) < 2 * M + 1 := b.isLt
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ (b : ℕ) := Nat.cast_nonneg _; linarith
    · have : ((b : ℕ) : ℝ) ≤ 2 * M := by exact_mod_cast (by omega : (b : ℕ) ≤ 2 * M)
      linarith
  have e1 : (h * ((a : ℝ) - M)) ^ 2 ≤ (h * M) ^ 2 := by
    rw [mul_pow, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg h)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have e2 : (h * ((b : ℝ) - M)) ^ 2 ≤ (h * M) ^ 2 := by
    rw [mul_pow, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg h)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  linarith

end WangZahlLot.Obl.wz_intermediate_twist_normalization
