-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Algebra.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Scalar estimates

The slope hypothesis keeps `f` within `2` of `c = f 0` on `[-1, 1]`.  The key inequality
`key_algebra` converts closeness of twisted coordinates `a + f(z) b` into closeness of the
fixed linear coordinate `a / c + b`; it is where `1 ≤ δ c²` enters.  The remaining lemmas are
the arithmetic of the final parameter choice.
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Set

/-- The slope hypothesis of the frozen statement. -/
def SlopeN (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
    1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1 / 100 : ℝ)

lemma SlopeN.continuous {f : ℝ → ℝ} (hf : SlopeN f) : Continuous f :=
  hf.1.continuous

lemma SlopeN.sub_le {f : ℝ → ℝ} (hf : SlopeN f) {z : ℝ} (hz : |z| ≤ 1) :
    |f z - f 0| ≤ 2 := by
  have hd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  have hz' : z ∈ Icc (-1 : ℝ) 1 := abs_le.mp hz
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun w _ => hd w) (fun w hw => by simpa only [Real.norm_eq_abs] using (hf.2 w hw).2.1) h0 hz'
  simp only [Real.norm_eq_abs, sub_zero] at h
  linarith

/-- The key inequality.  If `|a| ≤ 10`, `|F - c| ≤ 2` and the twisted difference `a + F b`
is at most `6δ(|c|+3)`, then the fixed coordinate difference `a / c + b` is at most `27δ`,
provided `100 < |c|` and `1 ≤ δ c²`. -/
lemma key_algebra {c F a b δ : ℝ} (hc : 100 < |c|) (hδc : 1 ≤ δ * c ^ 2) (hδ : 0 < δ)
    (hF : |F - c| ≤ 2) (ha : |a| ≤ 10) (hD : |a + F * b| ≤ 6 * δ * (|c| + 3)) :
    |a / c + b| ≤ 27 * δ := by
  have hc0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; norm_num at hc
  set C := |c| with hC
  set W := 6 * δ * (C + 3) with hW
  have hC2 : c ^ 2 = C ^ 2 := (sq_abs c).symm
  have hFabs : C - 2 ≤ |F| := by
    have := abs_sub_abs_le_abs_sub c F
    rw [abs_sub_comm] at hF
    linarith
  have hF0 : 0 < |F| := by linarith
  -- `|b|` is small
  have hb : |b| * (C - 2) ≤ W + 10 := by
    have h1 : |b| * |F| ≤ W + 10 := by
      rw [← abs_mul, mul_comm]
      have : F * b = (a + F * b) - a := by ring
      rw [this]
      exact (abs_sub _ _).trans (by linarith)
    calc |b| * (C - 2) ≤ |b| * |F| := mul_le_mul_of_nonneg_left hFabs (abs_nonneg b)
      _ ≤ W + 10 := h1
  -- rewrite the target
  have heq : a / c + b = ((a + F * b) + (c - F) * b) / c := by
    field_simp
    ring
  rw [heq, abs_div, div_le_iff₀ (by positivity : 0 < |c|)]
  have hcF : |(c - F) * b| ≤ 2 * |b| := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right hF (abs_nonneg b)
  have hsum : |(a + F * b) + (c - F) * b| ≤ W + 2 * |b| :=
    (abs_add_le _ _).trans (by linarith)
  -- `W + 2|b| ≤ 27 δ C`
  have hδC : 1 ≤ δ * C ^ 2 := by rwa [hC2] at hδc
  have hfinal : (W + 2 * |b|) * (C - 2) ≤ 27 * δ * C * (C - 2) := by
    have h2 : 2 * |b| * (C - 2) ≤ 2 * (W + 10) := by linarith
    have hexp : (W + 2 * |b|) * (C - 2) = W * (C - 2) + 2 * |b| * (C - 2) := by ring
    rw [hexp]
    have hpos : 0 ≤ δ * C * (C - 100) := by
      apply mul_nonneg (mul_nonneg hδ.le (by linarith)) (by linarith)
    nlinarith
  have hC2pos : 0 < C - 2 := by linarith
  have : W + 2 * |b| ≤ 27 * δ * C := by
    by_contra hcon
    have := mul_lt_mul_of_pos_right (not_le.mp hcon) hC2pos
    linarith
  linarith

/-- `k + 1 ≤ (2 / a) (2 ^ k) ^ a` for `0 < a ≤ 1`. -/
lemma nat_succ_le_rpow {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (k : ℕ) :
    (k : ℝ) + 1 ≤ (2 / a) * ((2 : ℝ) ^ k) ^ a := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hpow : ((2 : ℝ) ^ k) ^ a = Real.exp (a * k * Real.log 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [hpow]
  have hexp := Real.add_one_le_exp (a * k * Real.log 2)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : a * k / 2 ≤ a * k * Real.log 2 := by
    have : 0 ≤ a * k := mul_nonneg ha.le hk
    nlinarith
  have h2 : (2 / a) * (a * k / 2 + 1) = k + 2 / a := by
    field_simp
  have h3 : (1 : ℝ) ≤ 2 / a := by rw [le_div_iff₀ ha]; linarith
  calc (k : ℝ) + 1 ≤ k + 2 / a := by linarith
    _ = (2 / a) * (a * k / 2 + 1) := h2.symm
    _ ≤ (2 / a) * Real.exp (a * k * Real.log 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

end WangZahlLot.Obl.wz_small_twist_projection_estimate
