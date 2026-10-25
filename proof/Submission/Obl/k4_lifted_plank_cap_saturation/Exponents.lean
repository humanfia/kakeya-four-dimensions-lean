import Submission.Obl.k4_lifted_plank_cap_saturation.Numerics

namespace Submission.Obl.k4_lifted_plank_cap_saturation

open scoped ENNReal

/-- The power losses leave more mass than can be spread over the bins of the enclosing ball. -/
theorem lifted_saturation_exponents {d c ε : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) (_hc : 0 < c) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ u v : ℝ,
        N ^ (-c - κ) ≤ u → u ≤ v → ∀ M : ℝ≥0∞,
          ENNReal.ofReal (N ^ (-c * (d - 1) - κ) * u * v) ≤
            ENNReal.ofReal (8 * u) * M →
          M ≤ ENNReal.ofReal (N ^ κ * (max (N ^ (-c)) (5 * v)) ^ d) →
          ENNReal.ofReal ((4 * (5 * v) / N ^ (-c) + 2) ^ 3 *
            N ^ (-c * d - ε)) < M := by
  obtain ⟨κ, hκ, N₀, hN₀, hnum⟩ := saturation_power_slack hd0 hd1 hε
    (show (1 : ℝ) ≤ 25 by norm_num)
  refine ⟨κ, hκ, N₀, hN₀, ?_⟩
  intro N hN u v hu huv M hheavy hcap
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hN0 : 0 < N := by linarith
  let p : ℝ := N ^ (-c)
  let R : ℝ := max p (5 * v)
  have hp : 0 < p := Real.rpow_pos_of_pos hN0 _
  have hK : 0 < N ^ κ := Real.rpow_pos_of_pos hN0 _
  have hulow : p / N ^ κ ≤ u := by
    simpa only [p, Real.rpow_sub hN0] using hu
  have hu0 : 0 < u := (div_pos hp hK).trans_le hulow
  have hv0 : 0 < v := hu0.trans_le huv
  have hR0 : 0 < R := hp.trans_le (le_max_left _ _)
  have hscale : N ^ (-c * (d - 1) - κ) = p ^ (d - 1) / N ^ κ := by
    dsimp [p]
    rw [Real.rpow_sub hN0, Real.rpow_mul hN0.le]
  have htarget : N ^ (-c * d - ε) = p ^ d * N ^ (-ε) := by
    dsimp [p]
    rw [Real.rpow_sub hN0, Real.rpow_mul hN0.le]
    simp only [Real.rpow_neg hN0.le, div_eq_mul_inv]
  have cancel (B : ℝ) (hB : 0 ≤ B)
      (h : ENNReal.ofReal (N ^ (-c * (d - 1) - κ) * u * v) ≤
        ENNReal.ofReal (8 * u) * ENNReal.ofReal B) :
      p ^ (d - 1) / N ^ κ * v ≤ 8 * B := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * u),
      ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 8 * u * B), hscale] at h
    apply (mul_le_mul_iff_left₀ hu0).mp
    nlinarith only [h]
  have hcapreal : p ^ (d - 1) / N ^ κ * v ≤ 25 * N ^ κ * R ^ d := by
    have h := cancel (N ^ κ * R ^ d) (by positivity)
      (hheavy.trans (by gcongr))
    exact h.trans (by nlinarith [Real.rpow_nonneg hN0.le κ, Real.rpow_nonneg hR0.le d])
  have hRle : R ≤ p + 25 * v := by
    apply max_le
    · linarith
    · linarith
  have hstrict := hnum N hN p v R hp (hulow.trans huv) (le_max_left _ _) hRle hcapreal
  by_contra hbad
  have hM : M ≤ ENNReal.ofReal ((4 * (5 * v) / N ^ (-c) + 2) ^ 3 *
      N ^ (-c * d - ε)) := le_of_not_gt hbad
  have hbinreal := cancel ((4 * (5 * v) / p + 2) ^ 3 * N ^ (-c * d - ε))
    (by positivity) (hheavy.trans (by gcongr))
  rw [htarget] at hbinreal
  have hcount : (4 * (5 * v) / p + 2) ^ 3 ≤ (4 * R / p + 2) ^ 3 := by
    gcongr
    exact le_max_right _ _
  have hweak : p ^ (d - 1) / N ^ κ * v ≤
      25 * (4 * R / p + 2) ^ 3 * (p ^ d * N ^ (-ε)) := by
    refine hbinreal.trans ?_
    calc
      8 * ((4 * (5 * v) / p + 2) ^ 3 * (p ^ d * N ^ (-ε))) ≤
          8 * ((4 * R / p + 2) ^ 3 * (p ^ d * N ^ (-ε))) := by gcongr
      _ ≤ 25 * (4 * R / p + 2) ^ 3 * (p ^ d * N ^ (-ε)) := by
        nlinarith [show 0 ≤ (4 * R / p + 2) ^ 3 * (p ^ d * N ^ (-ε)) by positivity]
  exact (not_lt_of_ge hweak) hstrict

end Submission.Obl.k4_lifted_plank_cap_saturation
