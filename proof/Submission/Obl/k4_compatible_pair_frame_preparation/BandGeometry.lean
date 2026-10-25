import Submission.Obl.k4_compatible_pair_frame_preparation.FrameDensity
import Submission.Obl.k4_compatible_pair_frame_preparation.BandPowers

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Set MvPolynomial Construction

namespace NativeSample

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ}
    {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ}
    {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}

variable (p : NativeSample True 4 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)

/-- The Jacobian of every common frame has the same native scale budget. -/
theorem jacobian_budget (hN : 2 ≤ Nk) (ha : 0 < a) (he : 0 < e) (hB : ∀ γ, 0 < Bk γ)
    (hκX : frameSlack p.κ ≤ Nk ^ (a + e)) (hX : (2 : ℝ) ^ 100 ≤ Nk ^ (a + e))
    (i : Fin p.toPrep.J) :
    (100 * frameSlack p.κ) ^ 3 * |(p.toPrep.fQ i).det| ≤
      (Nk ^ (a + e)) ^ 9 * (p.R₁ * p.R₂) := by
  let hp := p.toPrep_hyp hN hB
  have hN1 : 1 ≤ Nk := by linarith
  have hκ0 : 0 ≤ p.κ := zero_le_one.trans p.κ_one
  have hK0 : 0 ≤ frameSlack p.κ := zero_le_one.trans (frameSlack_one p.κ_one)
  have hκleX : p.κ ≤ Nk ^ (a + e) := (frameSlack_input p.κ_one).trans hκX
  have hNa : Nk ^ a ≤ Nk ^ (a + e) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hq : (2 : ℝ) ^ p.s ≤ 2 * Nk ^ (a + e) :=
    p.hgainhi.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num))
  have hR₁ : 0 ≤ p.R₁ := (p.hR₂pos.trans_le p.hR21).le
  have hR₂ : 0 ≤ p.R₂ := p.hR₂pos.le
  have hd : |(p.toPrep.fQ i).det| ≤
      p.toPrep.Afr ^ 2 * ((2 : ℝ) ^ p.s) ^ 2 * (8 * Nk ^ (a + e)) * (p.R₁ * p.R₂) :=
    (p.determinant_le hN hB ha.le i).trans (by gcongr)
  exact frame_jacobian_le hX hκ0 hκleX hK0 hκX (by positivity) hq
    (zero_le_one.trans hp.Afr_one) hp.Afr_le hR₁ hR₂ hd

/-- The Jacobian prefactor is uniformly measured at the chosen common sigma. -/
theorem jacobian_at_sigma (hN : 2 ≤ Nk) (ha : 0 < a) (he : 0 < e) (hB : ∀ γ, 0 < Bk γ)
    (hκX : frameSlack p.κ ≤ Nk ^ (a + e)) (hX : (2 : ℝ) ^ 100 ≤ Nk ^ (a + e))
    (i : Fin p.toPrep.J) :
    Nk ^ (-f L) * ((100 * frameSlack p.κ) ^ 3 * |(p.toPrep.fQ i).det|) ≤
      p.sigma * Nk ^ (9 * (a + e)) := by
  have hN0 : 0 < Nk := by linarith
  have hp : (Nk ^ (a + e)) ^ 9 = Nk ^ (9 * (a + e)) := by
    rw [← Real.rpow_mul_natCast hN0.le]
    congr 1
    ring
  calc
    _ ≤ Nk ^ (-f L) * ((Nk ^ (a + e)) ^ 9 * (p.R₁ * p.R₂)) :=
      mul_le_mul_of_nonneg_left (p.jacobian_budget hN ha he hB hκX hX i)
        (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [hp, sigma]; ring

/-- The complete profile-band coefficient fits the universal output loss. -/
theorem band_coefficient_le (hN : 2 ≤ Nk) (ha : 0 < a) (he : 0 < e) (hB : ∀ γ, 0 < Bk γ)
    (hκX : frameSlack p.κ ≤ Nk ^ (a + e)) (hX : (2 : ℝ) ^ 100 ≤ Nk ^ (a + e))
    {d : ℝ} (hd : d ≤ 1) (i : Fin p.toPrep.J) :
    (32 * p.κ ^ 2 * Nk ^ (-f L + a) *
      ((100 * frameSlack p.κ) ^ 3 * |(p.toPrep.fQ i).det|)) *
      (2 : ℝ) ^ d * Nk ^ (d * e) ≤ p.sigma * Nk ^ (100 * (a + e)) := by
  have hN1 : 1 ≤ Nk := by linarith
  have hlarge : 64 ≤ Nk ^ (a + e) := by norm_num at hX; linarith
  have hK : p.κ ≤ Nk ^ (a + e) := (frameSlack_input p.κ_one).trans hκX
  have hc := Band.band_coefficient_power_budget (by linarith : 1 < Nk)
    (zero_le_one.trans p.κ_one) (p.sigma_pos hN).le hd hlarge hK (by linarith : a ≤ a + e)
    (by nlinarith : d * e ≤ a + e) (p.jacobian_at_sigma hN ha he hB hκX hX i)
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (p.sigma_pos hN).le
  exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

end NativeSample
end Submission.Obl.k4_compatible_pair_frame_preparation
