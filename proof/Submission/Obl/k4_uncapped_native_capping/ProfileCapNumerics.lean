/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/ProfileCapNumerics.lean. Existing source attributions below are retained.
-/
import Mathlib

namespace Submission.Obl.k4_uncapped_native_capping

noncomputable section

/-- The explicit projected-volume constants require only a fixed power of
the geometric slack, uniformly over every packet. -/
theorem projected_cap_prefactors {K κ : ℝ} (hK : 0 ≤ K) (hκ : 1 ≤ κ) (hKκ : K ≤ κ) :
    64 * K ^ 2 * (4 * κ ^ 2) ≤ 256 * κ ^ 4 ∧
      (8 * κ + 2) ^ 2 * (64 * K ^ 2) * (4 * κ ^ 2) ≤ 25600 * κ ^ 6 := by
  have hκ₀ : 0 ≤ κ := le_trans zero_le_one hκ
  have hpure : 64 * K ^ 2 * (4 * κ ^ 2) ≤ 64 * κ ^ 2 * (4 * κ ^ 2) := by
    gcongr
  have hang : (8 * κ + 2) ^ 2 * (64 * K ^ 2) * (4 * κ ^ 2) ≤
      (10 * κ) ^ 2 * (64 * κ ^ 2) * (4 * κ ^ 2) := by
    gcongr
    linarith
  constructor
  · convert hpure using 1
    ring
  · convert hang using 1
    ring

theorem projected_cap_prefactors_rpow {N K σ χ : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K)
    (hσ : 0 ≤ σ) (hσχ : σ ≤ χ / 48) (hKσ : K ≤ N ^ σ)
    (hconstant : 25600 ≤ N ^ (χ / 8)) :
    64 * K ^ 2 * (4 * (N ^ σ) ^ 2) ≤ N ^ (χ / 4) ∧
      (8 * N ^ σ + 2) ^ 2 * (64 * K ^ 2) * (4 * (N ^ σ) ^ 2) ≤ N ^ (χ / 4) := by
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hκ : 1 ≤ N ^ σ := Real.one_le_rpow hN hσ
  have hbound : 25600 * (N ^ σ) ^ 6 ≤ N ^ (χ / 4) := by
    calc
      _ = 25600 * N ^ (σ * (6 : ℕ)) := by rw [Real.rpow_mul_natCast hN₀.le]
      _ ≤ N ^ (χ / 8) * N ^ (χ / 8) := by
        apply mul_le_mul hconstant
          (Real.rpow_le_rpow_of_exponent_le hN (by norm_num; linarith))
          (Real.rpow_nonneg hN₀.le _) (by positivity)
      _ = _ := by rw [← Real.rpow_add hN₀]; congr 1; ring
  have hangular := (projected_cap_prefactors hK hκ hKσ).2.trans hbound
  refine ⟨le_trans ?_ hangular, hangular⟩
  have hfactor : 1 ≤ (8 * N ^ σ + 2) ^ 2 := by nlinarith
  calc
    _ = 1 * (64 * K ^ 2 * (4 * (N ^ σ) ^ 2)) := (one_mul _).symm
    _ ≤ (8 * N ^ σ + 2) ^ 2 * (64 * K ^ 2 * (4 * (N ^ σ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by ring

/-- Only a relative profile estimate is needed: the same initial density
factor occurs in the original cap and the full assignment prior. -/
theorem density_profile_cancellation
    {N F₀ Fᵣ d r ξ τ χ a C qJ : ℝ} (hN : 1 ≤ N) (hqJ : 0 ≤ qJ)
    (hprofile : d * r - ξ ≤ Fᵣ - F₀) (hC : C ≤ N ^ a)
    (hslack : a + τ + 2 * ξ ≤ χ) :
    C * N ^ (-Fᵣ + τ) * qJ ≤
      (qJ * N ^ (-F₀ - ξ)) * (N ^ χ * (N ^ (-r)) ^ d) := by
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ N ^ a * N ^ (-Fᵣ + τ) * qJ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN₀.le _)) hqJ
    _ = qJ * N ^ (a + (-Fᵣ + τ)) := by rw [Real.rpow_add hN₀ a (-Fᵣ + τ)]; ring
    _ ≤ qJ * N ^ ((-F₀ - ξ) + (χ + (-r) * d)) := by
      apply mul_le_mul_of_nonneg_left _ hqJ
      apply Real.rpow_le_rpow_of_exponent_le hN
      nlinarith
    _ = _ := by
      rw [Real.rpow_add hN₀ (-F₀ - ξ), Real.rpow_add hN₀ χ,
        Real.rpow_mul hN₀.le (-r) d]
      ring

/-- The cap coefficient is bounded by the unchanged full time-prior
budget. No assumption on the absolute value of the initial profile enters. -/
theorem original_prior_cap_coefficient
    {N F₀ Fᵣ d r ξ τ χ a C q J : ℝ} {prior : ENNReal}
    (hN : 1 ≤ N) (hq : 0 ≤ q) (hJ : 0 ≤ J)
    (hprofile : d * r - ξ ≤ Fᵣ - F₀) (hC : C ≤ N ^ a)
    (hslack : a + τ + 2 * ξ ≤ χ)
    (hprior : ENNReal.ofReal (N ^ (-F₀ - ξ) * J) ≤ prior) :
    ENNReal.ofReal (C * N ^ (-Fᵣ + τ) * q * J) ≤
      (ENNReal.ofReal q * prior) * ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d) := by
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hreal := density_profile_cancellation hN (mul_nonneg hq hJ) hprofile hC hslack
  calc
    _ ≤ ENNReal.ofReal (((q * J) * N ^ (-F₀ - ξ)) *
        (N ^ χ * (N ^ (-r)) ^ d)) :=
      ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using hreal)
    _ = (ENNReal.ofReal q * ENNReal.ofReal (N ^ (-F₀ - ξ) * J)) *
        ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d) := by
      rw [show (q * J) * N ^ (-F₀ - ξ) = q * (N ^ (-F₀ - ξ) * J) by ring,
        ENNReal.ofReal_mul (mul_nonneg hq (mul_nonneg (by positivity) hJ)),
        ENNReal.ofReal_mul hq]
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hprior) le_rfl

/-- Retaining half the original angular gain absorbs all nonnegative
requested angular depths into the same coefficient budget. -/
theorem original_prior_angular_cap_coefficient
    {N F₀ Fᵣ d r ξ τ χ a C q J S θ : ℝ} {prior : ENNReal}
    (hN : 1 ≤ N) (hq : 0 ≤ q) (hJ : 0 ≤ J) (hSθ : 0 ≤ S * θ)
    (hprofile : d * r - ξ ≤ Fᵣ - F₀) (hC : C ≤ N ^ a)
    (hslack : a + τ + 2 * ξ ≤ χ)
    (hprior : ENNReal.ofReal (N ^ (-F₀ - ξ) * J) ≤ prior) :
    ENNReal.ofReal (C * N ^ (-Fᵣ + τ) * q * J) * ENNReal.ofReal (N ^ (-S * θ)) ≤
      (ENNReal.ofReal q * prior) *
        ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d * N ^ (-(S / 2) * θ)) := by
  have hbase := original_prior_cap_coefficient hN hq hJ hprofile hC hslack hprior
  have hang : N ^ (-S * θ) ≤ N ^ (-(S / 2) * θ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  calc
    _ ≤ ((ENNReal.ofReal q * prior) * ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d)) *
        ENNReal.ofReal (N ^ (-(S / 2) * θ)) :=
      mul_le_mul' hbase (ENNReal.ofReal_le_ofReal hang)
    _ = _ := by
      rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end
end Submission.Obl.k4_uncapped_native_capping
