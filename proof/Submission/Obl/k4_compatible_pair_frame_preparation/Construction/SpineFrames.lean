-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/SpineFrames.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/SpineFrames.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.SpineInterface

/-!
# Frame coordinates of a confined trajectory

If a trajectory stays in a moving frame, `‖Q⁻¹(y(l,t) - c - t u)‖ ≤ κ`, at the two ends
of a dyadic block, then on the whole block its frame coordinates `base` have norm at
most `1/8`, and `base` is `2^T`-Lipschitz in time.  These are the two geometric
clauses of the source sets of the paired stage; they need nothing beyond the
confinement.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open Matrix

/-- The frame offset of a trajectory. -/
noncomputable def frameOffset (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)

theorem y_eq_add_smul (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : y l t = y l 0 + t • v l := by
  ext i
  fin_cases i <;> simp [y, v, x]

/-- The frame offset is affine in time. -/
theorem frameOffset_sub (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t t' : ℝ) :
    frameOffset c u Q l t - frameOffset c u Q l t' =
      (t - t') • Matrix.toEuclideanLin Q⁻¹ (v l - u) := by
  unfold frameOffset
  rw [← map_sub, ← map_smul]
  congr 1
  rw [y_eq_add_smul l t, y_eq_add_smul l t']
  module

theorem base_eq (T : ℕ) (j κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    base T j κ c u Q l t = WithLp.toLp 2 ![((2 : ℝ) ^ T * t - j - 1 / 2) / (100 * κ),
      frameOffset c u Q l t 0 / (100 * κ), frameOffset c u Q l t 1 / (100 * κ)] := rfl

theorem norm_toLp_three (a b c : ℝ) :
    ‖(WithLp.toLp 2 ![a, b, c] : EuclideanSpace ℝ (Fin 3))‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, sq_abs]

theorem norm_sq_two (w : EuclideanSpace ℝ (Fin 2)) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

/-- A confined trajectory has frame coordinates of norm at most `1/8` on the block. -/
theorem base_norm_le {T : ℕ} {j κ : ℝ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {l : ℕ × (Fin 6 → ℝ)} {t : ℝ} (hκ : 1 ≤ κ)
    (ht : t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T))
    (hconf : ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ) :
    ‖base T j κ c u Q l t‖ ≤ 1 / 8 := by
  have hpow : (0 : ℝ) < 2 ^ T := by positivity
  have hκpos : 0 < κ := by linarith
  set g := frameOffset c u Q l t with hg
  have hgκ : ‖g‖ ≤ κ := hconf
  have hg2 : g 0 ^ 2 + g 1 ^ 2 ≤ κ ^ 2 := by
    rw [← norm_sq_two]
    exact pow_le_pow_left₀ (norm_nonneg _) hgκ 2
  obtain ⟨ht1, ht2⟩ := ht
  have h1 : j ≤ 2 ^ T * t := by
    rw [div_le_iff₀ hpow] at ht1
    linarith
  have h2 : 2 ^ T * t ≤ j + 1 := by
    rw [le_div_iff₀ hpow] at ht2
    linarith
  have hfirst : |(2 : ℝ) ^ T * t - j - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [base_eq, norm_toLp_three]
  rw [Real.sqrt_le_left (by norm_num)]
  have e1 : (((2 : ℝ) ^ T * t - j - 1 / 2) / (100 * κ)) ^ 2 ≤ (1 / 200) ^ 2 := by
    rw [div_pow]
    rw [div_le_iff₀ (by positivity)]
    have : ((2 : ℝ) ^ T * t - j - 1 / 2) ^ 2 ≤ (1 / 2) ^ 2 := by
      have := abs_le.mp hfirst
      nlinarith
    have hκ2 : 1 ≤ (100 * κ) ^ 2 / 10000 := by nlinarith
    nlinarith
  have e2 : (g 0 / (100 * κ)) ^ 2 + (g 1 / (100 * κ)) ^ 2 ≤ (1 / 100) ^ 2 := by
    rw [div_pow, div_pow, ← add_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- A trajectory confined at both ends of the block has `2^T`-Lipschitz frame
coordinates. -/
theorem base_lipschitz {T : ℕ} {j κ : ℝ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {l : ℕ × (Fin 6 → ℝ)} (hκ : 1 ≤ κ)
    (h₁ : ‖Matrix.toEuclideanLin Q⁻¹ (y l (j / (2 : ℝ) ^ T) - c - (j / (2 : ℝ) ^ T) • u)‖ ≤ κ)
    (h₂ : ‖Matrix.toEuclideanLin Q⁻¹ (y l ((j + 1) / (2 : ℝ) ^ T) - c -
      ((j + 1) / (2 : ℝ) ^ T) • u)‖ ≤ κ) (t t' : ℝ) :
    ‖base T j κ c u Q l t - base T j κ c u Q l t'‖ ≤ (2 : ℝ) ^ T * |t - t'| := by
  have hpow : (0 : ℝ) < 2 ^ T := by positivity
  have hκpos : 0 < κ := by linarith
  set w := Matrix.toEuclideanLin Q⁻¹ (v l - u) with hw
  -- the velocity in frame coordinates
  have hwle : ‖w‖ ≤ 2 * κ * 2 ^ T := by
    have hd := frameOffset_sub c u Q l ((j + 1) / (2 : ℝ) ^ T) (j / (2 : ℝ) ^ T)
    have hdiff : (j + 1) / (2 : ℝ) ^ T - j / 2 ^ T = 1 / 2 ^ T := by
      field_simp
      ring
    rw [hdiff] at hd
    have hn : ‖(1 / (2 : ℝ) ^ T) • w‖ ≤ 2 * κ := by
      rw [← hd]
      refine (norm_sub_le _ _).trans ?_
      have := h₁
      have := h₂
      unfold frameOffset
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hn
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpow] at hn
    linarith
  have hsub : base T j κ c u Q l t - base T j κ c u Q l t' =
      WithLp.toLp 2 ![(2 : ℝ) ^ T * (t - t') / (100 * κ), (t - t') * w 0 / (100 * κ),
        (t - t') * w 1 / (100 * κ)] := by
    have hfo := frameOffset_sub c u Q l t t'
    have h0 : frameOffset c u Q l t 0 - frameOffset c u Q l t' 0 = (t - t') * w 0 := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hfo
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
      rw [this]
    have h1 : frameOffset c u Q l t 1 - frameOffset c u Q l t' 1 = (t - t') * w 1 := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hfo
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
      rw [this]
    rw [base_eq, base_eq]
    ext i
    fin_cases i
    · simp
      ring
    · simp
      rw [← h0]
      ring
    · simp
      rw [← h1]
      ring
  rw [hsub, norm_toLp_three]
  rw [Real.sqrt_le_left (by positivity)]
  have hw2 : w 0 ^ 2 + w 1 ^ 2 ≤ (2 * κ * 2 ^ T) ^ 2 := by
    rw [← norm_sq_two]
    exact pow_le_pow_left₀ (norm_nonneg _) hwle 2
  have hκ' : (100 * κ) ^ 2 ≠ 0 := by positivity
  have key : ((2 : ℝ) ^ T * (t - t')) ^ 2 + ((t - t') * w 0) ^ 2 + ((t - t') * w 1) ^ 2 ≤
      ((2 : ℝ) ^ T * |t - t'| * (100 * κ)) ^ 2 := by
    have habs : (t - t') ^ 2 = |t - t'| ^ 2 := (sq_abs _).symm
    have e : ((2 : ℝ) ^ T * (t - t')) ^ 2 + ((t - t') * w 0) ^ 2 + ((t - t') * w 1) ^ 2 =
        (t - t') ^ 2 * ((2 ^ T) ^ 2 + (w 0 ^ 2 + w 1 ^ 2)) := by ring
    rw [e, habs]
    have hk : ((2 : ℝ) ^ T) ^ 2 + (2 * κ * 2 ^ T) ^ 2 ≤ (2 ^ T * (100 * κ)) ^ 2 := by
      have : (1 : ℝ) + (2 * κ) ^ 2 ≤ (100 * κ) ^ 2 := by nlinarith
      nlinarith [pow_pos hpow 2]
    calc |t - t'| ^ 2 * ((2 ^ T) ^ 2 + (w 0 ^ 2 + w 1 ^ 2))
        ≤ |t - t'| ^ 2 * ((2 ^ T) ^ 2 + (2 * κ * 2 ^ T) ^ 2) := by gcongr
      _ ≤ |t - t'| ^ 2 * (2 ^ T * (100 * κ)) ^ 2 := by gcongr
      _ = ((2 : ℝ) ^ T * |t - t'| * (100 * κ)) ^ 2 := by ring
  calc ((2 : ℝ) ^ T * (t - t') / (100 * κ)) ^ 2 + ((t - t') * w 0 / (100 * κ)) ^ 2 +
        ((t - t') * w 1 / (100 * κ)) ^ 2
      = (((2 : ℝ) ^ T * (t - t')) ^ 2 + ((t - t') * w 0) ^ 2 + ((t - t') * w 1) ^ 2) /
          (100 * κ) ^ 2 := by
        field_simp
    _ ≤ ((2 : ℝ) ^ T * |t - t'| * (100 * κ)) ^ 2 / (100 * κ) ^ 2 := by gcongr
    _ = ((2 : ℝ) ^ T * |t - t'|) ^ 2 := by
        field_simp

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
