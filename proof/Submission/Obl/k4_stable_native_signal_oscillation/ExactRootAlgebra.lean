import Mathlib

/-!
# Exact-root signal partition: real algebra

The exact root identity (the signal is affine in the hidden derivative with base
coefficients), the two-root comparison identity, and the three Lipschitz estimates used
for linear tests, close branches and separated branches.
-/

namespace Submission.Obl.k4_stable_native_signal_oscillation

/-- At an exact root of `γ + β t + κ t² / 2` with `κ ≠ 0`, the hidden derivative `u = β + κ t`
squares to the base discriminant and the signal is affine in `u` with base coefficients. -/
lemma er_root_identity {κ κ' γ β γ' β' t : ℝ} (hκ : κ ≠ 0)
    (hroot : γ + β * t + κ * t ^ 2 / 2 = 0) :
    (β + κ * t) ^ 2 = β ^ 2 - 2 * κ * γ ∧
    γ' + β' * t + κ' * t ^ 2 / 2 =
      (γ' - β * β' / κ + κ' / (2 * κ ^ 2) * ((β ^ 2 - 2 * κ * γ) + β ^ 2)) +
        (β' / κ - κ' / κ ^ 2 * β) * (β + κ * t) := by
  constructor
  · linear_combination (2 * κ) * hroot
  · field_simp
    linear_combination (2 * κ * κ') * hroot

/-- The two-root comparison identity. -/
lemma er_two_root_identity (Mx My Bx By ux uy : ℝ) :
    ((Mx + Bx * ux) - (My + By * uy)) * ((My + By * uy) - (Mx - Bx * ux)) =
      2 * (My + By * uy) * (Mx - My) -
        ((Mx ^ 2 - Bx ^ 2 * ux ^ 2) - (My ^ 2 - By ^ 2 * uy ^ 2)) := by
  ring

/-- Linear hidden tests: the signal is a quotient of base polynomials. -/
lemma er_linear_case_bound {K Sx Sy βx βy N0x N0y L1 L2 d : ℝ} (hK : 0 < K)
    (hβx : K⁻¹ ≤ |βx|) (hβx' : |βx| ≤ K) (hβy' : |βy| ≤ K)
    (hNx : N0x = βx ^ 2 * Sx) (hNy : N0y = βy ^ 2 * Sy) (hSy : |Sy| ≤ K)
    (hL1 : |N0x - N0y| ≤ L1 * d) (hL2 : |βx - βy| ≤ L2 * d) (hd : 0 ≤ d)
    (hL1n : 0 ≤ L1) (hL2n : 0 ≤ L2) :
    |Sx - Sy| ≤ (K ^ 2 * L1 + 2 * K ^ 4 * L2) * d := by
  have hβx0 : βx ≠ 0 := fun h => by
    rw [h, abs_zero] at hβx
    exact absurd hβx (not_le.mpr (inv_pos.mpr hK))
  have hsq : 0 < βx ^ 2 := by positivity
  have hinv : (βx ^ 2)⁻¹ ≤ K ^ 2 := by
    rw [← inv_pow]
    have h1 : |βx|⁻¹ ≤ K := by
      rw [inv_le_comm₀ (abs_pos.mpr hβx0) hK]
      exact hβx
    calc (βx⁻¹) ^ 2 = |βx|⁻¹ ^ 2 := by rw [← abs_inv, sq_abs]
      _ ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have hexp : Sx - Sy = (N0x - N0y) * (βx ^ 2)⁻¹ + Sy * ((βy - βx) * (βy + βx)) * (βx ^ 2)⁻¹ := by
    rw [hNx, hNy]
    field_simp
    ring
  rw [hexp]
  have h1 : |(N0x - N0y) * (βx ^ 2)⁻¹| ≤ L1 * d * K ^ 2 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hsq)]
    exact mul_le_mul hL1 hinv (inv_pos.mpr hsq).le (by positivity)
  have hsum : |βy + βx| ≤ 2 * K := by
    calc |βy + βx| ≤ |βy| + |βx| := abs_add_le _ _
      _ ≤ 2 * K := by linarith
  have h2 : |Sy * ((βy - βx) * (βy + βx)) * (βx ^ 2)⁻¹| ≤ K * (L2 * d * (2 * K)) * K ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hsq)]
    have hb : |βy - βx| ≤ L2 * d := by rw [abs_sub_comm]; exact hL2
    apply mul_le_mul _ hinv (inv_pos.mpr hsq).le (by positivity)
    apply mul_le_mul hSy _ (by positivity) hK.le
    exact mul_le_mul hb hsum (abs_nonneg _) (by positivity)
  calc _ ≤ |(N0x - N0y) * (βx ^ 2)⁻¹| + |Sy * ((βy - βx) * (βy + βx)) * (βx ^ 2)⁻¹| :=
        abs_add_le _ _
    _ ≤ L1 * d * K ^ 2 + K * (L2 * d * (2 * K)) * K ^ 2 := add_le_add h1 h2
    _ = (K ^ 2 * L1 + 2 * K ^ 4 * L2) * d := by ring

/-- Small branch separation: both hidden derivatives have the same sign, and the branch
coefficients are controlled directly. -/
lemma er_small_branch_bound {K Mx My Bx By ux uy LM LB LD L0 d : ℝ} (hK : 0 < K)
    (hux : K⁻¹ ≤ |ux|) (huy : K⁻¹ ≤ |uy|) (hux' : |ux| ≤ K) (hsign : 0 < ux * uy)
    (hBy : |By| ≤ L0) (hLM : |Mx - My| ≤ LM * d) (hLB : |Bx - By| ≤ LB * d)
    (hLD : |ux ^ 2 - uy ^ 2| ≤ LD * d) (hd : 0 ≤ d) (hL0 : 0 ≤ L0) (hLBn : 0 ≤ LB) :
    |(Mx + Bx * ux) - (My + By * uy)| ≤ (LM + LB * K + L0 * K * LD / 2) * d := by
  have hsum : 2 * K⁻¹ ≤ |ux + uy| := by
    rcases lt_or_gt_of_ne (ne_of_gt hsign) with h | h
    · exact absurd h (lt_asymm hsign)
    · by_cases hx : 0 < ux
      · have hy : 0 < uy := by
          by_contra hy
          push Not at hy
          nlinarith
        rw [abs_of_pos hx] at hux
        rw [abs_of_pos hy] at huy
        rw [abs_of_pos (by linarith)]
        linarith
      · push Not at hx
        have hx' : ux < 0 := lt_of_le_of_ne hx (by rintro rfl; simp at hsign)
        have hy : uy < 0 := by
          by_contra hy
          push Not at hy
          nlinarith
        rw [abs_of_neg hx'] at hux
        rw [abs_of_neg hy] at huy
        rw [abs_of_neg (by linarith)]
        linarith
  have hsumpos : 0 < |ux + uy| := lt_of_lt_of_le (by positivity) hsum
  have hdiff : |ux - uy| ≤ K * LD * d / 2 := by
    have hfac : ux ^ 2 - uy ^ 2 = (ux - uy) * (ux + uy) := by ring
    rw [hfac, abs_mul] at hLD
    have h1 : |ux - uy| * (2 * K⁻¹) ≤ LD * d :=
      (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)).trans hLD
    have h2 : |ux - uy| ≤ LD * d / (2 * K⁻¹) := by
      rw [le_div_iff₀ (by positivity)]
      exact h1
    calc |ux - uy| ≤ LD * d / (2 * K⁻¹) := h2
      _ = K * LD * d / 2 := by field_simp
  have hexp : (Mx + Bx * ux) - (My + By * uy) = (Mx - My) + (Bx - By) * ux + By * (ux - uy) := by
    ring
  rw [hexp]
  calc |(Mx - My) + (Bx - By) * ux + By * (ux - uy)|
      ≤ |Mx - My| + |(Bx - By) * ux| + |By * (ux - uy)| := abs_add_three _ _ _
    _ ≤ LM * d + LB * d * K + L0 * (K * LD * d / 2) := by
      gcongr
      · rw [abs_mul]; exact mul_le_mul hLB hux' (abs_nonneg _) (by positivity)
      · rw [abs_mul]; exact mul_le_mul hBy hdiff (abs_nonneg _) hL0
    _ = (LM + LB * K + L0 * K * LD / 2) * d := by ring

/-- Separated branches: the comparison identity and a lower bound for the other branch. -/
lemma er_separated_branch_bound {K Mx My Bx By ux uy LM LN ℓ d : ℝ} (hK : 0 < K)
    (hSx : |Mx + Bx * ux| ≤ K) (hSy : |My + By * uy| ≤ K)
    (hsep : ℓ ≤ 2 * |Bx| * |ux| - 2 * K) (hℓ : 0 < ℓ)
    (hLM : |Mx - My| ≤ LM * d) (hLN : |(Mx ^ 2 - Bx ^ 2 * ux ^ 2) - (My ^ 2 - By ^ 2 * uy ^ 2)| ≤ LN * d) :
    |(Mx + Bx * ux) - (My + By * uy)| ≤ (2 * K * LM + LN) * d / ℓ := by
  have hid := er_two_root_identity Mx My Bx By ux uy
  set F := (Mx + Bx * ux) - (My + By * uy) with hF
  set W := (My + By * uy) - (Mx - Bx * ux) with hW
  have hWlow : ℓ ≤ |W| := by
    have h1 : Mx - Bx * ux = (Mx + Bx * ux) - 2 * (Bx * ux) := by ring
    have h2 : |2 * (Bx * ux)| = 2 * |Bx| * |ux| := by rw [abs_mul, abs_mul]; norm_num; ring
    have h3 : 2 * |Bx| * |ux| ≤ |W| + |My + By * uy| + |Mx + Bx * ux| := by
      rw [← h2]
      have : 2 * (Bx * ux) = W - (My + By * uy) + (Mx + Bx * ux) := by rw [hW]; ring
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    linarith
  have hrhs : |2 * (My + By * uy) * (Mx - My) -
        ((Mx ^ 2 - Bx ^ 2 * ux ^ 2) - (My ^ 2 - By ^ 2 * uy ^ 2))| ≤ (2 * K * LM + LN) * d := by
    calc _ ≤ |2 * (My + By * uy) * (Mx - My)| +
          |(Mx ^ 2 - Bx ^ 2 * ux ^ 2) - (My ^ 2 - By ^ 2 * uy ^ 2)| := abs_sub _ _
      _ ≤ 2 * K * (LM * d) + LN * d := by
        gcongr
        rw [abs_mul, abs_mul]
        norm_num
        exact mul_le_mul (mul_le_mul_of_nonneg_left hSy (by norm_num)) hLM (abs_nonneg _)
          (by positivity)
      _ = (2 * K * LM + LN) * d := by ring
  have hFW : |F| * |W| ≤ (2 * K * LM + LN) * d := by
    rw [← abs_mul, hid]
    exact hrhs
  rw [le_div_iff₀ hℓ]
  calc |F| * ℓ ≤ |F| * |W| := mul_le_mul_of_nonneg_left hWlow (abs_nonneg _)
    _ ≤ _ := hFW

end Submission.Obl.k4_stable_native_signal_oscillation
