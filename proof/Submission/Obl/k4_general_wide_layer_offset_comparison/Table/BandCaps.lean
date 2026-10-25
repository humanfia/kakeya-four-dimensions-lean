import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.GoodData
import Submission.Obl.k4_general_wide_layer_offset_comparison.ShiftedBandCaps
import Submission.Obl.k4_critical_intercept_concentration.CriticalScales
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# Eventual native band caps on the short codes

For a fixed depth `r`, major mesh `m > (κ + ℓ) r` and finest thickness
exponent `smax`, eventually every original submeasure of `μ` puts at most
`16800 K² χ q (q g) Δ^d π(bin)` on the native band of thickness `Δ ≥ N^(-smax)`
around any degree-two polynomial with coefficients at most `N^(m/1000)`,
shifted by any constant, on the short code of any original base point.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem eventually_short_band_cap (hp : p.Valid) {r m smax : ℝ} (hr : 0 < r)
    (hrU : r ≤ p.U) (hm : (p.κ + p.ℓ) * r < m) (hsmax : 0 ≤ smax) :
    ∀ᶠ k in atTop, ∀ (σ : Measure (α × ℝ)), σ ≤ p.μ k → ∀ ω ∈ p.baseGood k,
      ∀ (G : MvPolynomial (Fin 2) ℝ) (x Δ : ℝ), G.totalDegree ≤ 2 →
      (∀ e, |G.coeff e| ≤ p.N k ^ (m / 1000)) → p.N k ^ (-smax) ≤ Δ →
      σ (p.comparisonBand k m ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
        (![⌊p.b k ω.1 3 / p.N k ^ (-m)⌋, ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋])
        (p.shortDomainCode k r ω) (G + C x) Δ) ≤
      ENNReal.ofReal (16800 * p.K k ^ 2 * p.N k ^ (-m) * (2 : ℝ) ^ (-(p.T k r : ℤ)) *
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) * Δ ^ p.d) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋} := by
  have hκ := hp.rate_pos
  have hℓ := hp.transverse_pos
  have hm0 : 0 < m := by nlinarith
  have hκr : p.κ * r < m := by nlinarith
  -- the mesh exponent of the native caps
  set ρ : ℝ := smax + 2 * m + 2 with hρ_def
  have hρ : 0 < ρ := by rw [hρ_def]; linarith
  have hρm : m < ρ := by rw [hρ_def]; linarith
  set R : ℝ := 2 + ρ + smax + m + m⁻¹ + ρ⁻¹ + r⁻¹ with hR_def
  have hR : 1 < R := by
    have := inv_pos.mpr hm0
    have := inv_pos.mpr hρ
    have := inv_pos.mpr hr
    rw [hR_def]; linarith
  have hinv (x : ℝ) (hx : 0 < x) (hxR : x⁻¹ ≤ R) : R⁻¹ ≤ x := by
    have h := inv_anti₀ (inv_pos.mpr hx) hxR
    simpa only [inv_inv] using h
  have hRm : R⁻¹ ≤ m := hinv m hm0 (by
    have := inv_pos.mpr hρ; have := inv_pos.mpr hr; rw [hR_def]; linarith)
  have hRρ : R⁻¹ ≤ ρ := hinv ρ hρ (by
    have := inv_pos.mpr hm0; have := inv_pos.mpr hr; rw [hR_def]; linarith)
  have hRr : R⁻¹ ≤ r := hinv r hr (by
    have := inv_pos.mpr hm0; have := inv_pos.mpr hρ; rw [hR_def]; linarith)
  have hρR : ρ ≤ R := by
    have := inv_pos.mpr hm0; have := inv_pos.mpr hρ; have := inv_pos.mpr hr
    rw [hR_def]; linarith
  have hmR : m ≤ R := by
    have := inv_pos.mpr hm0; have := inv_pos.mpr hρ; have := inv_pos.mpr hr
    rw [hR_def]; linarith
  have hsR : smax ≤ R := by
    have := inv_pos.mpr hm0; have := inv_pos.mpr hρ; have := inv_pos.mpr hr
    rw [hR_def]; linarith
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.scale k]
  have hK1 := hp.subpower.1
  have e1 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.scale_limit hK1 hp.subpower.2 1 (show -ρ < -p.κ * r by linarith)
    (show (0 : ℝ) ≤ 1 by norm_num)
  have e2 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.scale_limit hK1 hp.subpower.2 2 (show -ρ < -(p.κ * r) + -p.ℓ * r by linarith)
    (show (0 : ℝ) ≤ 2 by norm_num)
  have e3 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.scale_limit hK1 hp.subpower.2 1 (show -ρ < -m by linarith)
    (show (0 : ℝ) ≤ 2 by norm_num)
  have e4 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.scale_limit hK1 hp.subpower.2 4 (show m / 1000 + -ρ < -smax by
      rw [hρ_def]; linarith) (show (0 : ℝ) ≤ 864 by norm_num)
  filter_upwards [hp.prepared R hR, hp.caps R hR, e1, e2, e3, e4] with k hprep hcapk h1 h2 h3 h4
  intro σ hσ ω hω G x Δ hG hcoeff hΔ
  have hat := hprep r hRr hrU
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hNgt : 1 < p.N k := by linarith [hp.scale k]
  have hK : 1 ≤ p.K k := hK1 k
  have hKpos : 0 < p.K k := by linarith
  set q := (2 : ℝ) ^ (-(p.T k r : ℤ)) with hq_def
  set g := p.N k ^ (-p.ℓ * r) with hg_def
  set χ := p.N k ^ (-m) with hχ_def
  have hq : 0 < q := by rw [hq_def]; positivity
  have hg : 0 < g := by rw [hg_def]; positivity
  have hχ : 0 < χ := by rw [hχ_def]; positivity
  have hlength := Submission.Obl.k4_critical_intercept_concentration.time_length_comparison
    hN hKpos hat.1 hat.2.1
  have hqlo : p.N k ^ (-p.κ * r) ≤ p.K k * q := by
    simpa only [hq_def, zpow_neg, zpow_natCast] using hlength.2
  have hg1 : g ≤ 1 := by
    rw [hg_def]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNgt.le (by nlinarith)
  have hχ1 : χ ≤ 1 := by
    rw [hχ_def]
    exact Real.rpow_le_one_of_one_le_of_nonpos hNgt.le (by linarith)
  have hNρ : 0 < p.N k ^ (-ρ) := Real.rpow_pos_of_pos hN _
  simp only [pow_one, one_mul] at h1 h3
  -- the mesh inequalities
  have hdtime : p.N k ^ (-ρ) ≤ q := by
    have : p.K k * p.N k ^ (-ρ) ≤ p.K k * q := h1.le.trans hqlo
    exact le_of_mul_le_mul_left this hKpos
  have hqg_lo : p.N k ^ (-(p.κ * r) + -p.ℓ * r) ≤ p.K k * (q * g) := by
    rw [Real.rpow_add hN, hg_def]
    have : p.N k ^ (-(p.κ * r)) = p.N k ^ (-p.κ * r) := by ring_nf
    rw [this]
    calc p.N k ^ (-p.κ * r) * p.N k ^ (-p.ℓ * r) ≤ (p.K k * q) * p.N k ^ (-p.ℓ * r) :=
          mul_le_mul_of_nonneg_right hqlo (by positivity)
      _ = _ := by ring
  have hV : 0 ≤ p.K k + 1 := by linarith
  have hmb : (p.K k + 1) * p.N k ^ (-ρ) ≤ 2 * (q * g) := by
    have hK2 : p.K k * (p.K k + 1) ≤ 2 * p.K k ^ 2 := by nlinarith
    have hlt : 2 * p.K k ^ 2 * p.N k ^ (-ρ) < p.K k * (2 * (q * g)) := by
      calc 2 * p.K k ^ 2 * p.N k ^ (-ρ) < p.N k ^ (-(p.κ * r) + -p.ℓ * r) := h2
        _ ≤ p.K k * (q * g) := hqg_lo
        _ ≤ p.K k * (2 * (q * g)) := by nlinarith [mul_pos hq hg]
    have : p.K k * ((p.K k + 1) * p.N k ^ (-ρ)) ≤ p.K k * (2 * (q * g)) := by
      calc p.K k * ((p.K k + 1) * p.N k ^ (-ρ)) = (p.K k * (p.K k + 1)) * p.N k ^ (-ρ) := by ring
        _ ≤ (2 * p.K k ^ 2) * p.N k ^ (-ρ) := mul_le_mul_of_nonneg_right hK2 hNρ.le
        _ ≤ _ := hlt.le
    exact le_of_mul_le_mul_left this hKpos
  have hdb : p.N k ^ (-ρ) ≤ 2 * (q * g) :=
    (le_mul_of_one_le_left hNρ.le (by linarith)).trans hmb
  have hmχ : (p.K k + 1) * p.N k ^ (-ρ) ≤ 2 * χ := by
    have : (p.K k + 1) * p.N k ^ (-ρ) ≤ 2 * p.K k * p.N k ^ (-ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) hNρ.le
    exact this.trans (h3.le.trans (by linarith))
  have hdχ : p.N k ^ (-ρ) ≤ 2 * χ :=
    (le_mul_of_one_le_left hNρ.le (by linarith)).trans hmχ
  have hres : 54 * p.N k ^ (m / 1000) * (p.K k + 1) ^ 4 * p.N k ^ (-ρ) ≤ p.N k ^ (-smax) := by
    have hK4 : (p.K k + 1) ^ 4 ≤ 16 * p.K k ^ 4 := by
      have : p.K k + 1 ≤ 2 * p.K k := by linarith
      calc (p.K k + 1) ^ 4 ≤ (2 * p.K k) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
        _ = 16 * p.K k ^ 4 := by ring
    calc 54 * p.N k ^ (m / 1000) * (p.K k + 1) ^ 4 * p.N k ^ (-ρ) ≤
        54 * p.N k ^ (m / 1000) * (16 * p.K k ^ 4) * p.N k ^ (-ρ) := by gcongr
      _ = 864 * p.K k ^ 4 * p.N k ^ (m / 1000 + -ρ) := by
        rw [Real.rpow_add hN]; ring
      _ ≤ p.N k ^ (-smax) := h4.le
  have hv₀ : |(((![⌊p.b k ω.1 3 / χ⌋, ⌊p.b k ω.1 0 / χ⌋] : Fin 2 → ℤ) 0 : ℤ) : ℝ) * χ| ≤
      p.K k + 1 := by
    have h := p.baseGood_major_velocity_bound (m := m) hN hω
    simp only [Matrix.cons_val_zero]
    linarith
  have hv : |domainVelocity g (p.shortDomainCode k r ω)| ≤ p.K k + 1 := by
    have h := (p.baseGood_domain_bounds hq hg (mul_pos hq hg) hω).2.2
    exact h.trans (by linarith)
  have hcap := p.comparisonBand_add_constant_cap hp.basic hNgt hK hp.dimension_nonneg hsmax
    hρ.le (by positivity : (0 : ℝ) ≤ p.N k ^ (m / 1000)) hq hg (mul_pos hq hg) le_rfl hV
    hdtime hdχ hdb hmχ hmb (![⌊p.b k ω.1 3 / χ⌋, ⌊p.b k ω.1 0 / χ⌋])
    (p.shortDomainCode k r ω) hv₀ hv G hG hcoeff x hres
    ((Real.rpow_pos_of_pos hN _).trans_le hΔ) hΔ σ hσ
    (fun s hs hss c j v₁ => (hcapk ρ s m hRρ hρR hs (hss.trans hsR) hRm hmR).2.2 true c j v₁)
  simpa only [Matrix.cons_val_zero] using hcap

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
