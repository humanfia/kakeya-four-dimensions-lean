import Submission.Obl.k4_compatible_pair_frame_preparation.FramePolynomial
import Submission.Obl.k4_compatible_pair_frame_preparation.FrameDensity
import Submission.Obl.k4_compatible_pair_frame_preparation.FrameLists
import Submission.Obl.k4_compatible_pair_frame_preparation.FrameTests
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepInterface

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Set MvPolynomial Construction
open scoped ENNReal

namespace NativeSample

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ}
    {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ}
    {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε₀ : ℝ}

variable (p : NativeSample True 4 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε₀)

/-- Assemble the tested sample once its measurable-band estimate is supplied. -/
noncomputable def testedSample_of_band [∀ γ, IsProbabilityMeasure (νk γ)]
    (hN : 2 ≤ Nk) (ha : 0 < a) (he : 0 < e)
    {Mb : ℕ} (hB : ∀ γ, 0 < Bk γ ∧ Bk γ ≤ Nk ^ Mb ∧ (Bk γ)⁻¹ ≤ Nk ^ Mb)
    (hκN : frameSlack p.κ ≤ Nk) (hκX : frameSlack p.κ ≤ Nk ^ (a + e))
    (hκa : p.κ ≤ Nk ^ a) (hX : (2 : ℝ) ^ 100 ≤ Nk ^ (a + e))
    (hLmem : L ∈ depths)
    (hmap : ∀ γ, Measurable (gk γ L) ∧
      Measure.map (obs (Bk γ) (δ Nk L)) (((νk γ).prod volume).restrict (Ek γ)) =
        (volume.prod Measure.count).withDensity (gk γ L))
    {d ε : ℝ} (hκε : frameSlack p.κ ≤ Nk ^ ε) (hε₀ : ε₀ ≤ ε)
    (hband : ∀ (b : Fin p.toPrep.J) (ρ : ℝ) (U : Set (EuclideanSpace ℝ (Fin 3)))
      (G : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < ρ → MeasurableSet U → Measurable G →
      ENNReal.ofReal ((2 : ℝ) ^ p.T) ^ 2 *
        ((νk (p.toPrep.fγ b)).prod (volume.prod volume))
          (p.toPrep.bandPairs Nk (frameSlack p.κ) b ρ U G) ≤
        ENNReal.ofReal (p.sigma * Nk ^ (100 * (a + e)) *
          (max ρ (δ Nk L) / δ Nk L) ^ d) * volume U) :
    TestedSample False 4 Nk Wk ωk νk Ek Bk L d (100 * (a + e)) h
      (30 * (M + Mb + 10)) (max D 1) ε := by
  let hp := p.toPrep_hyp hN (fun γ => (hB γ).1)
  let M' := 30 * (M + Mb + 10)
  have hN1 : 1 ≤ Nk := by linarith
  have hN0 : 0 < Nk := by linarith
  have hpow : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hN1 (by omega)
  have hκ2 := frameSlack_two p.κ_one
  have hfmtpow : Nk ^ M + 1 ≤ Nk ^ M' := by
    calc
      Nk ^ M + 1 ≤ Nk ^ M + Nk ^ M := by linarith [one_le_pow₀ hN1 (n := M)]
      _ ≤ Nk ^ M * Nk := by nlinarith [pow_nonneg hN0.le M]
      _ = Nk ^ (M + 1) := by rw [pow_succ]
      _ ≤ Nk ^ M' := pow_le_pow_right₀ hN1 (by omega)
  have hBsize (γ) : Bk γ * (2 * Nk ^ M) ≤ Nk ^ M' := by
    calc
      Bk γ * (2 * Nk ^ M) ≤ Nk ^ Mb * (2 * Nk ^ M) := by
        exact mul_le_mul_of_nonneg_right (hB γ).2.1 (by positivity)
      _ = 2 * Nk ^ (Mb + M) := by rw [pow_add]; ring
      _ ≤ Nk ^ (Mb + M + 1) := by
        rw [pow_succ, mul_comm (Nk ^ (Mb + M)) Nk]
        exact mul_le_mul_of_nonneg_right hN (by positivity)
      _ ≤ Nk ^ M' := pow_le_pow_right₀ hN1 (by omega)
  refine {
    κ := frameSlack p.κ
    κ_one := frameSlack_one p.κ_one
    κ_le := hκε
    σ := p.sigma
    σ_pos := p.sigma_pos hN
    T := p.T
    m := p.toPrep.m
    J := p.toPrep.J
    γ := p.toPrep.fγ
    j := p.toPrep.fj
    c := p.toPrep.fc
    u := p.toPrep.fu
    Q := p.toPrep.fQ
    frame := p.toPrep.frame
    P := p.toPrep.P (frameSlack p.κ)
    S := p.toPrep.S
    H := p.toPrep.H
    β := fun _ => p.sigma * Nk ^ (100 * (a + e))
    lst := p.toPrep.lst'
    hT := p.hT.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
    hm := ?_
    hJ := ?_
    hframe := ?_
    hP := ?_
    hS := ?_
    hdisj := fun s s' hne hγ _ => hp.S_disj s s' hne hγ
    hlst := ?_
    hlstfmt := ?_
    hH := fun s s' => ⟨hp.H_meas s s', fun z hz => hp.H_props hκ2
      (p.output_value_factor hN ha he hκX hX) (p.output_derivative_floor hN ha he) s s' z hz⟩
    hβ := ?_
    hcount := p.entry_count_le hN ha he (fun γ => (hB γ).1) hκX hX
    hband := hband
    hcoverage := p.coverage hN (fun γ => (hB γ).1) (frameSlack_input p.κ_one) }
  · have hm : p.toPrep.m ≤ p.C ^ 2 := p.toPrep.entries_card_le
    have hmR : (p.toPrep.m : ℝ) ≤ (p.C : ℝ) ^ 2 := by exact_mod_cast hm
    calc
      (p.toPrep.m : ℝ) ≤ (p.C : ℝ) ^ 2 := hmR
      _ ≤ (Nk ^ M) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) p.hC 2
      _ = Nk ^ (M * 2) := (pow_mul _ _ _).symm
      _ ≤ Nk ^ M' := pow_le_pow_right₀ hN1 (by omega)
  · have hJ : (p.toPrep.J : ℝ) ≤ (p.C : ℝ) := by exact_mod_cast p.toPrep.frames_card_le
    exact hJ.trans (p.hC.trans hpow)
  · intro i
    have hfr := p.polynomial_frame_bounds hN (fun γ => (hB γ).1) hκN i
    exact ⟨hfr.1, hfr.2.1.trans (pow_le_pow_right₀ hN1 (by omega)),
      hfr.2.2.1.trans (pow_le_pow_right₀ hN1 (by omega)), hfr.2.2.2⟩
  · intro s
    have hP := p.polynomial_test_bounds hN (fun γ => (hB γ).1) (fun γ => (hB γ).2.2) hκN s
    exact ⟨hP.1, hP.2, False.elim⟩
  · intro s
    obtain ⟨hSm, hSf, hSp⟩ := hp.S_props hκ2 s
    refine ⟨hSm, fun i => Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hSf i) hfmtpow le_rfl,
      fun z hz => ?_⟩
    obtain ⟨hzE, hz1, hz2, hzt, hzwhole⟩ := hSp z hz
    refine ⟨hzE, hz1.trans hpow, fun q => (hz2 q).trans hpow, hzt, fun t ht => ?_⟩
    obtain ⟨hconf, hhidden, hnorm, hlip⟩ := hzwhole t ht
    exact ⟨hconf, hhidden.trans (hBsize _), hnorm, hlip⟩
  · intro γ o
    have hc : ((p.toPrep.lst' γ o).card : ℝ) ≤ ((p.lst γ o).card : ℝ) *
        ((98 * (2 * p.toPrep.Kb + 1) ^ 4 + 1 : ℕ) : ℝ) := by
      exact_mod_cast p.toPrep.lst'_card_le γ o
    calc
      ((p.toPrep.lst' γ o).card : ℝ) ≤ ((p.lst γ o).card : ℝ) *
          ((98 * (2 * p.toPrep.Kb + 1) ^ 4 + 1 : ℕ) : ℝ) := hc
      _ ≤ p.κ * ((98 * (2 * p.toPrep.Kb + 1) ^ 4 + 1 : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (p.hlst γ o) (by positivity)
      _ ≤ frameSlack p.κ := frameSlack_lists p.κ_one
  · intro γ s
    have hf := p.toPrep.copied_list_format p.hlstfmt γ s
    exact ⟨hf.1, fun i => Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hf.2 i) hpow
      (le_max_left _ _)⟩
  · intro s
    refine ⟨mul_nonneg (p.sigma_pos hN).le (Real.rpow_nonneg hN0.le _), le_rfl, ?_⟩
    intro U hU
    exact ⟨p.base_density_le hN ha he (fun γ => (hB γ).1) hκX hκa hX hLmem hmap s U hU _
      (fun _ hz => Or.inl hz),
      p.base_density_le hN ha he (fun γ => (hB γ).1) hκX hκa hX hLmem hmap s U hU _
      (fun _ hz => Or.inr hz)⟩

end NativeSample
end Submission.Obl.k4_compatible_pair_frame_preparation
