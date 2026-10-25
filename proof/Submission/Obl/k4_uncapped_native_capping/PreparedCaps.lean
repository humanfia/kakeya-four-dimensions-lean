import Submission.Obl.k4_uncapped_native_capping.OriginalCapTransport
import Submission.Obl.k4_uncapped_native_capping.PacketCapBounds
import Submission.Obl.k4_uncapped_native_capping.ProfileCapNumerics

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

/-- Original density masks give the complete scalar caps for any law with
its unchanged full assignment budget. The constants are uniform in the
packet, its formats, and its time block. -/
theorem prepared_native_law_caps
    {p : UWE.Problem} {S η : ℝ} (hp : p.Valid S η) (hL : p.L = 1)
    (k : ℕ) (γ : Fin (p.W k)) (R V : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L)
    (hV : ∀ u ∈ V, 0 < u ∧ u ≤ η * p.L)
    {s U ε τ ξ χ loss d m : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 < ε) (hτ : 0 ≤ τ)
    (hRgrid : UWE.coarseDepthGrid s ε ⊆ R)
    (hVgrid : ∀ u ∈ UWE.coarseDepthGrid U ε, 0 < u → u ∈ V)
    (hloss : 0 ≤ loss) (hlossχ : loss ≤ χ / 48)
    (hslack : χ / 4 + 3 * τ + (1 + S) * ε + 2 * ξ ≤ χ)
    (hconstant : 25600 ≤ p.N k ^ (χ / 8))
    (hprofile : ∀ r, 0 ≤ r → r ≤ s → d * r - ξ ≤ p.f r - p.f 0)
    (A : Set Traj) (F : Set Inc) (hF : MeasurableSet F) (hFE : F ⊆ p.E k γ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (c u : EuclideanSpace ℝ (Fin 2)) (t₀ q offset : ℝ) (hq : 0 < q)
    (v' : Fin 3 → ℝ) (hv : v' 0 = 0)
    (hK : p.K k ≤ p.N k ^ loss)
    (hframe : ∀ z ∈ F,
      ‖Matrix.toEuclideanLin Q⁻¹ (y z.1 z.2 - c - z.2 • u)‖ ≤ p.N k ^ loss)
    (hfull : q / p.N k ^ loss ≤ ‖Matrix.toEuclideanLin Q.transpose (packetAxis q v')‖)
    (n : EuclideanSpace ℝ (Fin 2)) (he : ‖packetAxis q v'‖ = 1)
    (hn : ‖n‖ = 1) (hen : inner ℝ (packetAxis q v') n = 0) (β : ℝ)
    (hnormal : ∀ z ∈ F, |inner ℝ n (v z.1) - β| ≤ p.N k ^ loss * p.N k ^ (-U))
    (hprior : ENNReal.ofReal (p.N k ^ (-p.f 0 - ξ) * |Q.det|) ≤ p.ν k γ A)
    (μ : Measure Inc)
    (hsupport : ∀ᵐ z ∂μ, z.1 ∈ A)
    (hregular : RegularScalarLaw (p.N k) χ d s m (S / 2) U
      ((p.ν k γ A)⁻¹ • (p.ν k γ).restrict A) μ
      (nativeCoeff (p.P k γ) t₀ q offset v' A))
    (hdom : (ENNReal.ofReal q * p.ν k γ A) •
      Measure.map (fun z : Inc => (z.1, t₀ + q * z.2)) μ ≤
        ((p.ν k γ).prod volume).restrict
          (F ∩ (UWE.densityPreparationBad p S R V τ k γ)ᶜ)) :
    ScalarCaps (p.N k) χ d s m (S / 2) U
      ((p.ν k γ A)⁻¹ • (p.ν k γ).restrict A) μ
      (nativeCoeff (p.P k γ) t₀ q offset v' A) := by
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (PacketCapBounds.valid_two_le_N hp k)
  have hN0 : 0 < p.N k := lt_of_lt_of_le zero_lt_one hN
  have hS : 0 ≤ S := (PacketCapBounds.valid_S_pos hp).le
  have hκ : 1 ≤ p.N k ^ loss := Real.one_le_rpow hN hloss
  have hpref := projected_cap_prefactors_rpow hN
    (Real.rpow_nonneg hN0.le loss) hloss hlossχ le_rfl hconstant
  have hprior0 : p.ν k γ A ≠ 0 := by
    exact ((ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos hN0 _)
      (abs_pos.mpr hQ))).trans_le hprior).ne'
  have hν : IsProbabilityMeasure (p.ν k γ) := by
    rcases hp with ⟨_, _, _, _, _, _, _, _, ⟨M, D, hdata⟩, _⟩
    exact ((hdata k).2.2.2.1 γ).1
  haveI := hν
  have hpure_slack : χ / 4 + (τ + ε) + 2 * ξ ≤ χ := by
    have h := mul_nonneg hS hε.le
    nlinarith
  apply native_law_caps_of_original_domination hN0 (p.ν k γ) A t₀ q offset hq v' hv
    (p.P k γ) (PacketCapBounds.valid_world hp k γ).2 μ _ hprior0
    (measure_ne_top _ _) hdom hsupport hregular
  · intro r j E hr hrs hE
    have hcap := PacketCapBounds.prepared_projected_cap (s := s) (ε := ε) (τ := τ)
      hp k γ R V hR hV hε
      (hL ▸ hs1) hRgrid F hF hFE Q hQ c u (packetAxis q v') t₀ (-q * offset)
      hq (Real.rpow_pos_of_pos hN0 loss) hκ hK hframe hfull r hr hrs j E hE
    have hcoeff := original_prior_cap_coefficient (χ := χ) (τ := τ + ε) (a := χ / 4)
      hN hq.le (abs_nonneg Q.det)
      (hprofile r hr hrs) hpref.1 hpure_slack hprior
    have heq : ENNReal.ofReal (p.N k ^ (-p.f r + τ + ε)) *
        ENNReal.ofReal (64 * (p.N k ^ loss) ^ 2) *
        ENNReal.ofReal (4 * (p.N k ^ loss) ^ 2 * q * |Q.det|) =
        ENNReal.ofReal ((64 * (p.N k ^ loss) ^ 2 * (4 * (p.N k ^ loss) ^ 2)) *
          p.N k ^ (-p.f r + (τ + ε)) * q * |Q.det|) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show -p.f r + τ + ε = -p.f r + (τ + ε) by ring]
      ring
    exact hcap.trans (by simpa only [UWE.packetProjection, physicalProjection,
      UWE.x, UWE.y, x, y, heq] using mul_le_mul' hcoeff (le_refl (volume E)))
  · intro r j kk E hr hrU hE
    have hcap := PacketCapBounds.prepared_projected_angular_cap
      (s := s) (ε := ε) (τ := τ) (Adepth := U) hp k γ R V hR hV hε hτ
      (hL ▸ hs1) hRgrid hVgrid F hF hFE Q hQ c u (packetAxis q v') he
      t₀ (-q * offset) hq (Real.rpow_pos_of_pos hN0 loss) hκ hK hframe hfull n hn hen β hκ
      (Real.rpow_nonneg hN0.le (-U)) le_rfl hnormal s r hs le_rfl hr hrU j kk E hE
    have hcoeff := original_prior_angular_cap_coefficient
      (S := S) (θ := r) (χ := χ) (τ := 3 * τ + (1 + S) * ε) (a := χ / 4)
      hN hq.le (abs_nonneg Q.det) (mul_nonneg hS hr.le)
      (hprofile s hs le_rfl) hpref.2 (by linarith only [hslack]) hprior
    have heq : ENNReal.ofReal (p.N k ^ (-S * r + 2 * τ + S * ε)) *
        ENNReal.ofReal ((8 * p.N k ^ loss + 2) ^ 2) *
        ENNReal.ofReal (p.N k ^ (-p.f s + τ + ε)) *
        ENNReal.ofReal (64 * (p.N k ^ loss) ^ 2) *
        ENNReal.ofReal (4 * (p.N k ^ loss) ^ 2 * q * |Q.det|) =
        ENNReal.ofReal (((8 * p.N k ^ loss + 2) ^ 2 *
          (64 * (p.N k ^ loss) ^ 2) * (4 * (p.N k ^ loss) ^ 2)) *
          p.N k ^ (-p.f s + (3 * τ + (1 + S) * ε)) * q * |Q.det|) *
        ENNReal.ofReal (p.N k ^ (-S * r)) := by
      repeat rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hpow : p.N k ^ (-S * r + 2 * τ + S * ε) *
          p.N k ^ (-p.f s + τ + ε) =
          p.N k ^ (-p.f s + (3 * τ + (1 + S) * ε)) * p.N k ^ (-S * r) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
        congr 1
        ring
      calc
        _ = (p.N k ^ (-S * r + 2 * τ + S * ε) * p.N k ^ (-p.f s + τ + ε)) *
            (((8 * p.N k ^ loss + 2) ^ 2 * (64 * (p.N k ^ loss) ^ 2) *
              (4 * (p.N k ^ loss) ^ 2)) * q * |Q.det|) := by ring
        _ = _ := by rw [hpow]; ring
    rw [heq] at hcap
    exact hcap.trans (by simpa only [UWE.packetProjection, physicalProjection,
      UWE.x, UWE.y, UWE.v, x, y, v] using mul_le_mul' hcoeff (le_refl (volume E)))

end
end Submission.Obl.k4_uncapped_native_capping
