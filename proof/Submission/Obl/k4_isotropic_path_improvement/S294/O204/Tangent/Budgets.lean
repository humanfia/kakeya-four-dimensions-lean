-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Budgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1080,
-- branch x1080, commit 5a0a478a0, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/Budgets.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- Polynomial size budgets of the unscaled virtual instance (x1078, o204).
-- Uses o280's `PFrame.coeffL1_normTest_le`, `Frame.unsubstBound`, `Frame.substBound` and the
-- `coeffL1` kernel of `k4_remainder_pure_profile_normalization` (imported, not copied).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.RelativeOrchestration

/-!
# Size budgets of the virtual instance

For the unscaled virtual frame `rFrame N rA jA TA cA B` (time `jA/2^TA`, dilation `2^-TA`, centre
`cA`, hidden scale `B/δ(N, rA)`), every size budget that `RelPPP` asks for is a fixed power of `N`
once `2^T ≤ N^E`, `rA ≤ E`, `B^{±1} ≤ N^Mb`, `‖cA‖ ≤ N^Mr` and the chart of the packet (exponent
`Mp`) are known: `rel_budgets` proves all of them at `M' = 2E + Mp + 2Mr + 2Mb + 16`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory MvPolynomial
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

lemma δ_le_one (N r : ℝ) (hN : 1 ≤ N) (hr : 0 ≤ r) : Split.δ N r ≤ 1 := by
  rw [δ_eq]
  apply zpow_le_one_of_nonpos₀ (by norm_num)
  have h : 0 ≤ r * Real.log N / Real.log 2 :=
    div_nonneg (mul_nonneg hr (Real.log_nonneg hN)) (Real.log_nonneg (by norm_num))
  have := Int.floor_nonneg.mpr h
  omega

lemma δ_inv_le (N r : ℝ) (hN : 1 ≤ N) : (Split.δ N r)⁻¹ ≤ N ^ r := by
  rw [δ_eq, ← zpow_neg, neg_neg]
  have hN0 : 0 < N := by linarith
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  calc (2:ℝ) ^ (⌊r * Real.log N / Real.log 2⌋ : ℤ)
      = (2:ℝ) ^ ((⌊r * Real.log N / Real.log 2⌋ : ℤ) : ℝ) := (Real.rpow_intCast 2 _).symm
    _ ≤ (2:ℝ) ^ (r * Real.log N / Real.log 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le _)
    _ = N ^ r := by
        rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hN0]
        congr 1
        field_simp

lemma virtualFrame_unsubstBudget_le (t₀ q : ℝ) (cA : P2) (sc : ℝ) (ht₀ : 0 ≤ t₀)
    (ht₁ : t₀ ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (virtualFrame t₀ q cA sc).unsubstBudget ≤ 9 * (1 + ‖cA‖) + |sc⁻¹| := by
  have hc := norm_nonneg cA
  have hb : (virtualFrame t₀ q cA sc).F.unsubstBound ≤ 9 * (1 + ‖cA‖) := by
    simp only [virtualFrame, Frame.unsubstBound]
    have hsum : ∑ e : Fin 2, ∑ e' : Fin 2, |(q • (1 : Matrix (Fin 2) (Fin 2) ℝ)) e e'| =
        2 * q := by
      simp [Fin.sum_univ_two, Matrix.one_apply, abs_of_nonneg hq0]; ring
    rw [hsum, norm_zero, add_zero, abs_of_nonneg ht₀, abs_of_nonneg hq0]
    calc (1 + t₀ + q) * (1 + ‖cA‖) * (1 + 2 * q) ≤ 3 * (1 + ‖cA‖) * 3 := by
          gcongr <;> linarith
      _ = 9 * (1 + ‖cA‖) := by ring
  unfold PFrame.unsubstBudget
  apply max_le
  · linarith [abs_nonneg sc⁻¹]
  · change |sc⁻¹| ≤ _
    linarith

lemma virtualFrame_substBudget_le (t₀ q : ℝ) (cA : P2) (sc : ℝ) (ht₀ : 0 ≤ t₀)
    (ht₁ : t₀ ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (virtualFrame t₀ q cA sc).substBudget ≤ 5 * q⁻¹ * (1 + ‖cA‖) + |sc| := by
  have hc := norm_nonneg cA
  have hqi : 1 ≤ q⁻¹ := (one_le_inv₀ hq0).mpr hq1
  have hb : (virtualFrame t₀ q cA sc).F.substBound ≤ 5 * q⁻¹ * (1 + ‖cA‖) := by
    simp only [virtualFrame, Frame.substBound, smul_one_inv q hq0.ne']
    have hsum : ∑ e : Fin 2, ∑ e' : Fin 2, |(q⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) e e'| =
        2 * q⁻¹ := by
      simp [Fin.sum_univ_two, Matrix.one_apply, abs_of_nonneg (inv_nonneg.mpr hq0.le)]; ring
    rw [hsum, norm_zero, add_zero, abs_of_nonneg ht₀, abs_of_nonneg (inv_nonneg.mpr hq0.le)]
    nlinarith
  unfold PFrame.substBudget
  apply max_le
  · linarith [abs_nonneg sc]
  · have : 0 ≤ 5 * q⁻¹ * (1 + ‖cA‖) := by positivity
    change |sc| ≤ _
    linarith

lemma normTest_coeff_le (Φ : PFrame) (δ : ℝ) (R : Po) (hR : R.totalDegree ≤ 2) (H : ℝ)
    (hH : ∀ e, |R.coeff e| ≤ H) (e : Fin 4 →₀ ℕ) :
    |(Φ.normTest δ R).coeff e| ≤ |δ⁻¹| * (81 * H * Φ.unsubstBudget ^ 2) := by
  have hL : coeffL1 R ≤ 81 * H := by simpa using coeffL1_le_of_coeff_le R hR H hH
  have hpow : Φ.unsubstBudget ^ R.totalDegree ≤ Φ.unsubstBudget ^ 2 :=
    pow_le_pow_right₀ Φ.one_le_unsubstBudget hR
  have hH0 : 0 ≤ 81 * H := by have := hH 0; linarith [abs_nonneg (R.coeff 0)]
  calc |(Φ.normTest δ R).coeff e| ≤ coeffL1 (Φ.normTest δ R) := abs_coeff_le_coeffL1 _ _
    _ ≤ |δ⁻¹| * (coeffL1 R * Φ.unsubstBudget ^ R.totalDegree) := Φ.coeffL1_normTest_le δ R
    _ ≤ |δ⁻¹| * (81 * H * Φ.unsubstBudget ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact mul_le_mul hL hpow (pow_nonneg (zero_le_one.trans Φ.one_le_unsubstBudget) _) hH0

/-- A quantity bounded by a constant `≤ 2^k` times `N^a` is at most `N^M` for `k + a ≤ M`. -/
lemma le_pow_of_le_const_mul (N : ℝ) (hN : 2 ≤ N) (x C : ℝ) (k a M : ℕ) (hC : C ≤ 2 ^ k)
    (hx : x ≤ C * N ^ a) (hM : k + a ≤ M) : x ≤ N ^ M := by
  have hN1 : (1:ℝ) ≤ N := by linarith
  calc x ≤ C * N ^ a := hx
    _ ≤ 2 ^ k * N ^ a := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ N ^ k * N ^ a := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hN k)
        (by positivity)
    _ = N ^ (k + a) := by rw [pow_add]
    _ ≤ N ^ M := pow_le_pow_right₀ hN1 hM

lemma residualBudget_zero_one : residualBudget 0 1 = 2 := by
  simp [residualBudget]; norm_num

/-- Products of quantities at least one. -/
lemma one_le_mul_of_one_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y := by nlinarith

lemma le_mul_of_one_le' {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x) : a ≤ a * x :=
  le_mul_of_one_le_right ha hx

lemma arith_centre (W X Y a b : ℝ) (hW : 1 ≤ W) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (ha : a ≤ W * (X + Y)) (hb : b ≤ X) : a + b ≤ 4 * (W * X * Y) := by
  have h1 : W * X ≤ W * X * Y := le_mul_of_one_le' (by positivity) hY
  have h2 : W * Y ≤ W * X * Y := by
    have := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ W * Y) hX
    linarith [mul_comm (W * Y) X, mul_assoc W X Y, mul_comm X Y, mul_assoc W Y X]
  have h3 : X ≤ W * X * Y := by
    have := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ X) hW
    have := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ X * W) hY
    nlinarith
  have hpos : 0 ≤ W * X * Y := by positivity
  nlinarith

lemma arith_unsubst (Y Z a : ℝ) (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (hc : a ≤ Y) (b : ℝ) (hb : b ≤ Z) :
    9 * (1 + a) + b ≤ 19 * (Y * Z) := by
  have h1 : 1 ≤ Y * Z := one_le_mul_of_one_le hY hZ
  have h2 : Y ≤ Y * Z := le_mul_of_one_le' (by positivity) hZ
  have h3 : Z ≤ Y * Z := by
    have := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ Z) hY
    linarith [mul_comm Z Y]
  linarith

lemma arith_subst (W Y Z a b c : ℝ) (hW : 1 ≤ W) (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (ha : a ≤ W)
    (hb : b ≤ Y) (hc : c ≤ Z * W) (hb0 : 0 ≤ b) :
    5 * a * (1 + b) + c ≤ 11 * (W * Y * Z) := by
  have h1 : 5 * a * (1 + b) ≤ 5 * W * (1 + Y) := by gcongr
  have h2 : W ≤ W * Y * Z := by
    have := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ W) (one_le_mul_of_one_le hY hZ)
    linarith [mul_assoc W Y Z]
  have h3 : W * Y ≤ W * Y * Z := le_mul_of_one_le' (by positivity) hZ
  have h4 : Z * W ≤ W * Y * Z := by
    have := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ Z * W) hY
    linarith [mul_comm (Z * W) Y, mul_comm Z W, mul_assoc W Y Z, mul_comm Y Z, mul_assoc W Z Y]
  nlinarith

lemma budget_clock (N : ℝ) (hN : 1 ≤ N) (T TA E M : ℕ) (hT : (2:ℝ) ^ T ≤ N ^ E)
    (hM : E ≤ M) : (2:ℝ) ^ (T - TA) ≤ N ^ M :=
  calc (2:ℝ) ^ (T - TA) ≤ (2:ℝ) ^ T := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    _ ≤ N ^ E := hT
    _ ≤ N ^ M := pow_le_pow_right₀ hN hM

lemma budget_frame (N : ℝ) (hN : 1 ≤ N) (T TA E Mp M : ℕ) (hTT : TA ≤ T)
    (hT : (2:ℝ) ^ T ≤ N ^ E) (hM : E + Mp ≤ M) : (2:ℝ) ^ TA * N ^ Mp ≤ N ^ M := by
  have h2TA : (2:ℝ) ^ TA ≤ N ^ E := le_trans (pow_le_pow_right₀ (by norm_num) hTT) hT
  calc (2:ℝ) ^ TA * N ^ Mp ≤ N ^ E * N ^ Mp := by gcongr
    _ = N ^ (E + Mp) := by rw [pow_add]
    _ ≤ N ^ M := pow_le_pow_right₀ hN hM

lemma budget_centre (N : ℝ) (hN : 2 ≤ N) (c u cA : P2) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (ht₁ : t₀ ≤ 1)
    (TA E Mp Mr M : ℕ) (hcu : ‖c‖ + ‖u‖ ≤ N ^ Mp) (hcA : ‖cA‖ ≤ N ^ Mr)
    (h2TA : (2:ℝ) ^ TA ≤ N ^ E) (hM : 2 + (E + Mp + Mr) ≤ M) :
    ‖((2:ℝ) ^ TA) • (c + t₀ • u - cA)‖ + ‖u‖ ≤ N ^ M := by
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hu : ‖u‖ ≤ N ^ Mp := by linarith [norm_nonneg c]
  have hnorm : ‖c + t₀ • u - cA‖ ≤ N ^ Mp + N ^ Mr := by
    calc ‖c + t₀ • u - cA‖ ≤ ‖c‖ + t₀ * ‖u‖ + ‖cA‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg ht₀]
      _ ≤ ‖c‖ + 1 * ‖u‖ + ‖cA‖ := by gcongr
      _ ≤ N ^ Mp + N ^ Mr := by linarith
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  apply le_pow_of_le_const_mul N hN _ 4 2 (E + Mp + Mr) _ (by norm_num) _ hM
  have e1 : (2:ℝ) ^ TA * ‖c + t₀ • u - cA‖ ≤ N ^ E * (N ^ Mp + N ^ Mr) :=
    mul_le_mul h2TA hnorm (norm_nonneg _) (by positivity)
  rw [pow_add, pow_add]
  exact arith_centre _ _ _ _ _ (one_le_pow₀ hN1) (one_le_pow₀ hN1) (one_le_pow₀ hN1) e1 hu

lemma budget_normTest (N : ℝ) (hN : 2 ≤ N) (Φ : PFrame) (δ : ℝ) (hδ0 : 0 < δ) (R : Po)
    (hR : R.totalDegree ≤ 2) (E Mp Mr Mb M : ℕ) (hRc : ∀ e, |R.coeff e| ≤ N ^ Mp)
    (hδinv : δ⁻¹ ≤ N ^ E) (hU : Φ.unsubstBudget ≤ 19 * (N ^ Mr * N ^ Mb))
    (hM : 15 + (E + Mp + 2 * Mr + 2 * Mb) ≤ M) (e : Fin 4 →₀ ℕ) :
    |(Φ.normTest δ R).coeff e| ≤ N ^ M := by
  have hcoef := normTest_coeff_le Φ δ R hR (N ^ Mp) hRc e
  apply le_pow_of_le_const_mul N hN _ 29241 15 (E + Mp + 2 * Mr + 2 * Mb) _ (by norm_num) _ hM
  refine hcoef.trans ?_
  rw [abs_of_pos (inv_pos.mpr hδ0)]
  have hU1 := Φ.one_le_unsubstBudget
  have hsq : Φ.unsubstBudget ^ 2 ≤ (19 * (N ^ Mr * N ^ Mb)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hU 2
  calc δ⁻¹ * (81 * N ^ Mp * Φ.unsubstBudget ^ 2)
      ≤ N ^ E * (81 * N ^ Mp * (19 * (N ^ Mr * N ^ Mb)) ^ 2) := by
        apply mul_le_mul hδinv _ (by positivity) (by positivity)
        gcongr
    _ = 29241 * N ^ (E + Mp + 2 * Mr + 2 * Mb) := by
        rw [show E + Mp + 2 * Mr + 2 * Mb = E + Mp + (Mr + Mr) + (Mb + Mb) by ring]
        simp only [pow_add]; ring

lemma budget_subst (N : ℝ) (hN : 2 ≤ N) (Φ : PFrame) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (E Mr Mb M : ℕ) (hS : Φ.substBudget ≤ 11 * (N ^ E * N ^ Mr * N ^ Mb))
    (hM : 16 + (2 * E + 2 * Mr + 2 * Mb) ≤ M) :
    81 * |δ| * residualBudget 0 1 ^ 2 * Φ.substBudget ^ 2 ≤ N ^ M := by
  apply le_pow_of_le_const_mul N hN _ 39204 16 (2 * E + 2 * Mr + 2 * Mb) _ (by norm_num) _ hM
  rw [residualBudget_zero_one, abs_of_pos hδ0]
  have hS1 := Φ.one_le_substBudget
  have hsq : Φ.substBudget ^ 2 ≤ (11 * (N ^ E * N ^ Mr * N ^ Mb)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hS 2
  calc 81 * δ * 2 ^ 2 * Φ.substBudget ^ 2
      ≤ 81 * 1 * 2 ^ 2 * (11 * (N ^ E * N ^ Mr * N ^ Mb)) ^ 2 := by gcongr
    _ = 39204 * N ^ (2 * E + 2 * Mr + 2 * Mb) := by
        rw [show 2 * E + 2 * Mr + 2 * Mb = E + E + (Mr + Mr) + (Mb + Mb) by ring]
        simp only [pow_add]; ring

/-- One coordinate row of a tangent line, as a bound. -/
lemma budget_row (N : ℝ) (hN : 1 ≤ N) (x y z t₀ s : ℝ) (ht₀ : 0 ≤ t₀) (ht₁ : t₀ ≤ 1)
    (hs : 0 < s) (E Mp Mr Mb : ℕ) (hx : |x| ≤ N ^ Mp) (hy : |y| ≤ N ^ Mp) (hz : |z| ≤ N ^ Mr)
    (hsE : s ≤ N ^ E) :
    |(x + t₀ * y - z) / s⁻¹| ≤ 5 * (N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb)) := by
  have hX := one_le_pow₀ (n := Mp) hN
  have hY := one_le_pow₀ (n := Mr) hN
  have hZ := one_le_pow₀ (n := Mb) hN
  have hW := one_le_pow₀ (n := E) hN
  rw [div_inv_eq_mul, abs_mul, abs_of_pos hs]
  have hty : |t₀ * y| ≤ N ^ Mp := by
    rw [abs_mul, abs_of_nonneg ht₀]
    calc t₀ * |y| ≤ 1 * N ^ Mp := by gcongr
      _ = N ^ Mp := one_mul _
  have h1 : |x + t₀ * y - z| ≤ N ^ Mp + N ^ Mp + N ^ Mr := by
    calc |x + t₀ * y - z| ≤ |x| + |t₀ * y| + |z| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ N ^ Mp + N ^ Mp + N ^ Mr := by linarith
  have h2 : |x + t₀ * y - z| * s ≤ (N ^ Mp + N ^ Mp + N ^ Mr) * N ^ E :=
    mul_le_mul h1 hsE hs.le (by positivity)
  have h3 : (N ^ Mp + N ^ Mp + N ^ Mr) * N ^ E ≤ 4 * (N ^ E * N ^ Mp * N ^ Mr) := by
    have a1 := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ N ^ E * N ^ Mp) hY
    have a2 := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ N ^ E * N ^ Mr) hX
    have e1 : (N ^ Mp + N ^ Mp + N ^ Mr) * N ^ E = 2 * (N ^ E * N ^ Mp) + N ^ E * N ^ Mr := by
      ring
    have e2 : N ^ E * N ^ Mr * N ^ Mp = N ^ E * N ^ Mp * N ^ Mr := by ring
    have hpos : 0 ≤ N ^ E * N ^ Mp * N ^ Mr := by positivity
    linarith
  have h4 : N ^ E * N ^ Mp * N ^ Mr ≤ N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb) := by
    rw [← mul_assoc]; exact le_mul_of_one_le' (by positivity) hZ
  nlinarith

lemma budget_hidden (N : ℝ) (hN : 1 ≤ N) (sc x : ℝ) (E Mp Mr Mb : ℕ)
    (hsc : |sc| ≤ N ^ Mb * N ^ E) (hx : |x| ≤ 2 * N ^ Mp) :
    |sc * x| ≤ 5 * (N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb)) := by
  have hY := one_le_pow₀ (n := Mr) hN
  rw [abs_mul]
  have h1 : |sc| * |x| ≤ N ^ Mb * N ^ E * (2 * N ^ Mp) :=
    mul_le_mul hsc hx (abs_nonneg _) (by positivity)
  have h2 : N ^ Mb * N ^ E * (2 * N ^ Mp) ≤ 2 * (N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb)) := by
    have := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ 2 * (N ^ E * N ^ Mp * N ^ Mb)) hY
    have e : 2 * (N ^ E * N ^ Mp * N ^ Mb) * N ^ Mr = 2 * (N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb)) := by
      ring
    have e' : N ^ Mb * N ^ E * (2 * N ^ Mp) = 2 * (N ^ E * N ^ Mp * N ^ Mb) := by ring
    linarith
  have hpos : 0 ≤ N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb) := by positivity
  linarith

lemma budget_tanLine (N : ℝ) (hN : 1 ≤ N) (t₀ q : ℝ) (cA : P2) (sc : ℝ) (ht₀ : 0 ≤ t₀)
    (ht₁ : t₀ ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1) (E Mp Mr Mb : ℕ) (hqE : q⁻¹ ≤ N ^ E)
    (hcA : ∀ i, |cA i| ≤ N ^ Mr) (hsc : |sc| ≤ N ^ Mb * N ^ E) (l : Ln)
    (hl : ∀ i, |l.2 i| ≤ N ^ Mp) (e : Fin 6) :
    |(tanLine (isoPFrame t₀ q cA sc) 0 l).2 e| ≤ 5 * (N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb)) := by
  have hX := one_le_pow₀ (n := Mp) hN
  have hpos : 0 ≤ N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb) := by positivity
  have hXle : N ^ Mp ≤ N ^ E * N ^ Mp * (N ^ Mr * N ^ Mb) := by
    have h1 := le_mul_of_one_le_left (by positivity : (0:ℝ) ≤ N ^ Mp) (one_le_pow₀ (n := E) hN)
    have h2 := le_mul_of_one_le' (by positivity : (0:ℝ) ≤ N ^ E * N ^ Mp)
      (one_le_mul_of_one_le (one_le_pow₀ (n := Mr) hN) (one_le_pow₀ (n := Mb) hN))
    linarith
  have hq : q = (q⁻¹)⁻¹ := (inv_inv q).symm
  rw [tanLine_iso t₀ q cA sc hq0.ne' l]
  fin_cases e
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [hq]
    exact budget_row N hN _ _ _ t₀ q⁻¹ ht₀ ht₁ (inv_pos.mpr hq0) E Mp Mr Mb (hl 0) (hl 3)
      (hcA 0) hqE
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hq]
    exact budget_row N hN _ _ _ t₀ q⁻¹ ht₀ ht₁ (inv_pos.mpr hq0) E Mp Mr Mb (hl 1) (hl 4)
      (hcA 1) hqE
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    apply budget_hidden N hN sc _ E Mp Mr Mb hsc
    have := hl 2
    have := hl 5
    have : |t₀ * l.2 5| ≤ N ^ Mp := by
      rw [abs_mul, abs_of_nonneg ht₀]
      calc t₀ * |l.2 5| ≤ 1 * N ^ Mp := by gcongr
        _ = N ^ Mp := one_mul _
    linarith [abs_add_le (l.2 2) (t₀ * l.2 5)]
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]; linarith [hl 3]
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]; linarith [hl 4]
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    apply budget_hidden N hN sc _ E Mp Mr Mb hsc
    rw [abs_mul, abs_of_pos hq0]
    have := hl 5
    calc q * |l.2 5| ≤ 1 * N ^ Mp := by gcongr
      _ ≤ 2 * N ^ Mp := by linarith

/-- All size budgets of `RelPPP`, at `M' = 2E + Mp + 2Mr + 2Mb + 16`, from the packet's chart,
`2^T ≤ N^E`, `rA ≤ E`, `B^{±1} ≤ N^Mb` and `‖cA‖ ≤ N^Mr`. -/
theorem rel_budgets (N : ℝ) (hN : 2 ≤ N) (Mp Dp Mr Mb E : ℕ) (κ : ℝ) (T jb : ℕ) (rb Bv : ℝ)
    (Ev' : Set Ev) (c u : P2) (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : Po) (A : Set Ln) (F : Set Ev)
    (ex : Prop) (hch : Split.ch N Mp Dp κ T (jb:ℝ) rb Bv Ev' c u Q R A F ex)
    (hB : 0 < Bv) (hBle : Bv ≤ N ^ Mb) (hBinv : Bv⁻¹ ≤ N ^ Mb) (hT : (2:ℝ) ^ T ≤ N ^ E)
    (rA : ℝ) (hrA : 0 ≤ rA) (hrAE : rA ≤ E) (jA TA : ℕ) (hTT : TA ≤ T) (hjA : jA < 2 ^ TA)
    (cA : P2) (hcA : ‖cA‖ ≤ N ^ Mr) :
    (2:ℝ) ^ (T - TA) ≤ N ^ (2*E + Mp + 2*Mr + 2*Mb + 16) ∧
    Mp ≤ 2*E + Mp + 2*Mr + 2*Mb + 16 ∧
    (2:ℝ) ^ TA * N ^ Mp ≤ N ^ (2*E + Mp + 2*Mr + 2*Mb + 16) ∧
    ‖((2:ℝ) ^ TA) • (c + ((jA:ℝ) / (2:ℝ) ^ TA) • u - cA)‖ + ‖u‖ ≤
      N ^ (2*E + Mp + 2*Mr + 2*Mb + 16) ∧
    (∀ e, |((rFrame N rA jA TA cA Bv).normTest (Split.δ N rA) R).coeff e| ≤
      N ^ (2*E + Mp + 2*Mr + 2*Mb + 16)) ∧
    (∀ l ∈ A, ∀ e, |(tanLine (rFrame N rA jA TA cA Bv) 0 l).2 e| ≤
      N ^ (2*E + Mp + 2*Mr + 2*Mb + 16)) ∧
    81 * |Split.δ N rA| * residualBudget 0 1 ^ 2 * (rFrame N rA jA TA cA Bv).substBudget ^ 2 ≤
      N ^ (2*E + Mp + 2*Mr + 2*Mb + 16) := by
  have hN1 : (1:ℝ) ≤ N := by linarith
  obtain ⟨-, hcu, -, -, hRdeg, hRc, -, -, -, hAl, -, -⟩ := hch
  have h2TA : (2:ℝ) ^ TA ≤ N ^ E := le_trans (pow_le_pow_right₀ (by norm_num) hTT) hT
  have h2TA1 : (1:ℝ) ≤ (2:ℝ) ^ TA := one_le_pow₀ (by norm_num)
  have ht₀ : (0:ℝ) ≤ (jA:ℝ) / (2:ℝ) ^ TA := by positivity
  have ht₁ : (jA:ℝ) / (2:ℝ) ^ TA ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hjA.le
  have hq0 : (0:ℝ) < ((2:ℝ) ^ TA)⁻¹ := by positivity
  have hq1 : ((2:ℝ) ^ TA)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2TA1
  have hδ0 := δ_pos N rA
  have hδ1 := δ_le_one N rA hN1 hrA
  have hδinv : (Split.δ N rA)⁻¹ ≤ N ^ E := (δ_inv_le N rA hN1).trans (by
    calc N ^ rA ≤ N ^ (E:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hrAE
      _ = N ^ E := Real.rpow_natCast N E)
  have hsc : |Bv / Split.δ N rA| ≤ N ^ Mb * N ^ E := by
    rw [abs_of_pos (div_pos hB hδ0), div_eq_mul_inv]
    exact mul_le_mul hBle hδinv (inv_nonneg.mpr hδ0.le) (by positivity)
  have hscinv : |(Bv / Split.δ N rA)⁻¹| ≤ N ^ Mb := by
    rw [abs_of_pos (inv_pos.mpr (div_pos hB hδ0)), inv_div]
    calc Split.δ N rA / Bv ≤ 1 / Bv := by gcongr
      _ = Bv⁻¹ := one_div _
      _ ≤ N ^ Mb := hBinv
  have hcA0 : ∀ i, |cA i| ≤ N ^ Mr := fun i => (plane_abs_le_norm cA i).trans hcA
  refine ⟨budget_clock N hN1 T TA E _ hT (by omega), by omega,
    budget_frame N hN1 T TA E Mp _ hTT hT (by omega),
    budget_centre N hN c u cA _ ht₀ ht₁ TA E Mp Mr _ hcu hcA h2TA (by omega), ?_, ?_, ?_⟩
  · intro e
    have hU := virtualFrame_unsubstBudget_le ((jA:ℝ) / (2:ℝ) ^ TA) ((2:ℝ) ^ TA)⁻¹ cA
      (Bv / Split.δ N rA) ht₀ ht₁ hq0.le hq1
    exact budget_normTest N hN _ _ hδ0 R hRdeg E Mp Mr Mb _ hRc hδinv
      (hU.trans (arith_unsubst _ _ _ (one_le_pow₀ hN1) (one_le_pow₀ hN1) hcA _ hscinv))
      (by omega) e
  · intro l hl e
    obtain ⟨-, hl2, -⟩ := hAl l hl
    have h := budget_tanLine N hN1 ((jA:ℝ) / (2:ℝ) ^ TA) ((2:ℝ) ^ TA)⁻¹ cA
      (Bv / Split.δ N rA) ht₀ ht₁ hq0 hq1 E Mp Mr Mb (by rw [inv_inv]; exact h2TA) hcA0 hsc l
      hl2 e
    refine h.trans (le_pow_of_le_const_mul N hN _ 5 3 (E + Mp + Mr + Mb) _ (by norm_num) ?_
      (by omega))
    rw [pow_add, pow_add, pow_add]
    exact le_of_eq (by ring)
  · have hS := virtualFrame_substBudget_le ((jA:ℝ) / (2:ℝ) ^ TA) ((2:ℝ) ^ TA)⁻¹ cA
      (Bv / Split.δ N rA) ht₀ ht₁ hq0 hq1
    rw [inv_inv] at hS
    exact budget_subst N hN _ _ hδ0 hδ1 E Mr Mb _
      (hS.trans (arith_subst _ _ _ _ _ _ (one_le_pow₀ hN1) (one_le_pow₀ hN1) (one_le_pow₀ hN1)
        h2TA hcA hsc (norm_nonneg _))) (by omega)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
