import Mathlib

namespace Submission.Obl.k4_lifted_plank_cap_saturation

open Filter

/-- The coefficient cap bounds the radius of a heavy plank after a small power loss. -/
theorem cap_radius_le {d C N κ σ p v R : ℝ}
    (hd : d < 1) (hC : 1 ≤ C) (hN : 1 ≤ N) (hκ : 0 < κ)
    (hκσ : κ ≤ σ) (hexp : 3 * κ ≤ σ * (1 - d))
    (hlarge : max 2 (2 * C ^ 2) < N ^ κ)
    (hp : 0 < p) (_hv : 0 < v) (hR : p ≤ R) (hRle : R ≤ p + C * v)
    (hcap : p ^ (d - 1) / N ^ κ * v ≤ C * N ^ κ * R ^ d) :
    R ≤ p * N ^ σ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hK : 0 < N ^ κ := Real.rpow_pos_of_pos hN0 _
  have hR0 : 0 < R := hp.trans_le hR
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hσ : 0 < σ := hκ.trans_le hκσ
  have hKσ : N ^ κ ≤ N ^ σ := Real.rpow_le_rpow_of_exponent_le hN hκσ
  have htwo : 2 < N ^ σ := (lt_of_le_of_lt (le_max_left _ _) hlarge).trans_le hKσ
  by_cases hsmall : R ≤ 2 * p
  · exact hsmall.trans (by nlinarith)
  have hpR : p < R / 2 := by linarith
  have hRv : R ≤ 2 * C * v := by nlinarith
  have hcap' : p ^ (d - 1) * v ≤ C * (N ^ κ) ^ 2 * R ^ d := by
    have h := (div_le_iff₀ hK).mp
      (show p ^ (d - 1) * v / N ^ κ ≤ C * N ^ κ * R ^ d by
        simpa only [div_mul_eq_mul_div] using hcap)
    nlinarith
  have hscaled : p ^ (d - 1) * R ≤ 2 * C ^ 2 * (N ^ κ) ^ 2 * R ^ d := by
    have h₁ := mul_le_mul_of_nonneg_left hRv (Real.rpow_nonneg hp.le (d - 1))
    have h₂ := mul_le_mul_of_nonneg_left hcap' (by positivity : 0 ≤ 2 * C)
    nlinarith
  have hid : (R / p) ^ (1 - d) * R ^ d = p ^ (d - 1) * R := by
    rw [Real.div_rpow hR0.le hp.le, Real.rpow_sub hR0, Real.rpow_one,
      Real.rpow_sub hp, Real.rpow_one, Real.rpow_sub_one hp.ne']
    field_simp
  have hratio : (R / p) ^ (1 - d) ≤ 2 * C ^ 2 * (N ^ κ) ^ 2 := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hR0 d)).mp
    simpa only [hid, mul_comm, mul_left_comm, mul_assoc] using hscaled
  by_contra hbad
  have hratio' : N ^ σ < R / p := (lt_div_iff₀ hp).mpr (by nlinarith)
  have hlower := Real.rpow_lt_rpow (Real.rpow_nonneg hN0.le σ) hratio' (sub_pos.mpr hd)
  rw [← Real.rpow_mul hN0.le] at hlower
  have hconst : 2 * C ^ 2 < N ^ κ := lt_of_le_of_lt (le_max_right _ _) hlarge
  have hupper : 2 * C ^ 2 * (N ^ κ) ^ 2 < N ^ (3 * κ) := by
    calc
      2 * C ^ 2 * (N ^ κ) ^ 2 < N ^ κ * (N ^ κ) ^ 2 :=
        mul_lt_mul_of_pos_right hconst (by positivity)
      _ = N ^ (3 * κ) := by
        rw [show 3 * κ = κ + (κ + κ) by ring, Real.rpow_add hN0,
          Real.rpow_add hN0]
        ring
  have hpower : N ^ (3 * κ) ≤ N ^ (σ * (1 - d)) :=
    Real.rpow_le_rpow_of_exponent_le hN hexp
  exact (not_lt_of_ge (hratio.trans hupper.le |>.trans hpower)) hlower

/-- The numerical losses in ball saturation and finite bin counting can be chosen uniformly. -/
theorem saturation_power_slack {d ε C : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hε : 0 < ε) (hC : 1 ≤ C) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ p v R : ℝ,
        0 < p → p / N ^ κ ≤ v → p ≤ R → R ≤ p + C * v →
        p ^ (d - 1) / N ^ κ * v ≤ C * N ^ κ * R ^ d →
        C * (4 * R / p + 2) ^ 3 * (p ^ d * N ^ (-ε)) <
          p ^ (d - 1) / N ^ κ * v := by
  let κ : ℝ := ε * (1 - d) / 100
  let σ : ℝ := ε / 10
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hκσ : κ ≤ σ := by dsimp [κ, σ]; nlinarith
  have hcapexp : 3 * κ ≤ σ * (1 - d) := by
    dsimp [κ, σ]
    nlinarith
  have hbinexp : κ + 3 * σ - ε ≤ -2 * κ := by
    dsimp [κ, σ]
    nlinarith
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hκ).eventually
      (Filter.eventually_gt_atTop (max (max 2 (2 * C ^ 2)) (216 * C))))
  refine ⟨κ, hκ, max 2 A, le_max_left _ _, ?_⟩
  intro N hN p v R hp hv hR hRle hcap
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hK : 0 < N ^ κ := Real.rpow_pos_of_pos hN0 _
  have hv0 : 0 < v := (div_pos hp hK).trans_le hv
  have hlarge := hA N ((le_max_right _ _).trans hN)
  have hlargecap : max 2 (2 * C ^ 2) < N ^ κ :=
    lt_of_le_of_lt (le_max_left _ _) hlarge
  have hlargebin : 216 * C < N ^ κ := lt_of_le_of_lt (le_max_right _ _) hlarge
  have hrad := cap_radius_le hd1 hC hN1 hκ hκσ hcapexp hlargecap hp hv0 hR hRle hcap
  have hratio : R / p ≤ N ^ σ := (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hrad)
  have hR0 : 0 < R := hp.trans_le hR
  have hpow1 : 1 ≤ N ^ σ := Real.one_le_rpow hN1 hσ.le
  have hcount : (4 * R / p + 2) ^ 3 ≤ (6 * N ^ σ) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity : 0 ≤ 4 * R / p + 2)
    calc
      4 * R / p + 2 = 4 * (R / p) + 2 := by ring
      _ ≤ 6 * N ^ σ := by linarith
  have hpow3 : N ^ (3 * σ) = (N ^ σ) ^ 3 := by
    rw [show 3 * σ = σ * (3 : ℕ) by ring, Real.rpow_mul_natCast hN0.le]
  have hpow2 : N ^ (-2 * κ) = ((N ^ κ) ^ 2)⁻¹ := by
    rw [show -2 * κ = -(κ * (2 : ℕ)) by ring, Real.rpow_neg hN0.le,
      Real.rpow_mul_natCast hN0.le]
  have hmain : C * (4 * R / p + 2) ^ 3 * (p ^ d * N ^ (-ε)) <
      p ^ d * N ^ (-2 * κ) := by
    calc
      C * (4 * R / p + 2) ^ 3 * (p ^ d * N ^ (-ε)) ≤
          C * (6 * N ^ σ) ^ 3 * (p ^ d * N ^ (-ε)) := by
            gcongr
      _ = (216 * C) * p ^ d * N ^ (3 * σ - ε) := by
        rw [Real.rpow_sub hN0, Real.rpow_neg hN0.le,
          hpow3]
        ring
      _ < N ^ κ * p ^ d * N ^ (3 * σ - ε) := by
        gcongr
      _ = p ^ d * N ^ (κ + 3 * σ - ε) := by
        rw [show κ + 3 * σ - ε = κ + (3 * σ - ε) by ring, Real.rpow_add hN0]
        ring
      _ ≤ p ^ d * N ^ (-2 * κ) := by
        gcongr
  refine hmain.trans_le ?_
  calc
    p ^ d * N ^ (-2 * κ) = p ^ (d - 1) / N ^ κ * (p / N ^ κ) := by
      rw [Real.rpow_sub_one hp.ne', hpow2]
      field_simp
    _ ≤ p ^ (d - 1) / N ^ κ * v := by gcongr

end Submission.Obl.k4_lifted_plank_cap_saturation
