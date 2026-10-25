import Submission.Obl.k4_contact_regular_quadratic_reconstruction.PowerCalibration
import Submission.Obl.k4_scalar_grid_parameter_preparation.IncidenceFacts

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The original full-block fit, with the hidden derivatives in original units. -/
def trajectoryFit (b : Fin 6 → ℝ) (Q : MvPolynomial (Fin 4) ℝ)
    (I : Set ℝ) (H a : ℝ) : Prop :=
  ∀ t ∈ I, |eval (point b t) Q| ≤ H * a ∧
    |eval (point b t) (pderiv (3 : Fin 4) Q)| ≤ H ∧
    |eval (point b t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ H / a

/-- A fine affine preparation on an original law gives the exact polynomial
candidate. Every mass comparison uses the same original witness law. -/
theorem original_candidate_of_affine_source
    {C : ℝ} (hcal : MeshCalibration C) (hC : 1 ≤ C)
    {N B : ℝ} (hN : 2 ≤ N) (hCN : C ≤ N) (hB : 1 ≤ B)
    {α : Type*} [MeasurableSpace α]
    (ρ σ : Measure (α × ℝ)) [IsFiniteMeasure σ] (hσρ : σ ≤ ρ)
    (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (A : Set α) (I : Set ℝ)
    (F P : MvPolynomial (Fin 4) ℝ) (hF : F.totalDegree ≤ 2)
    (L : Fin 4 → ℝ) {a c H J ε : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hH : 0 ≤ H) (hJ : 1 ≤ J)
    (hsmall : J * c ≤ a) (hfitLoss : 2 * H * J ≤ N ^ ε)
    (hcalValue : 3 * H * a ≤ N ^ B)
    (hmass : ENNReal.ofReal (N ^ (-B)) ≤ σ univ)
    (hcap : ∀ q : Fin 3 → ℤ,
      σ {p | (fun i : Fin 3 =>
        ⌊point (b p.1) p.2 i.castSucc / N ^ (-(calibrationPower C B + 1))⌋) = q} ≤
          ENNReal.ofReal (N ^ B * (N ^ (-(calibrationPower C B + 1))) ^ (3 : ℕ)))
    (hsource : ∀ᵐ p ∂σ,
      p.1 ∈ A ∧ p.2 ∈ I ∧
      (∀ i : Fin 3, |point (b p.1) p.2 i.castSucc| ≤ N ^ B) ∧
      trajectoryFit (b p.1) F I H a ∧
      (∀ t ∈ I, |eval (point (b p.1) t) (affineBase L) - point (b p.1) t 3| ≤ J * c) ∧
      N ^ (-ε) ≤ |eval (point (b p.1) p.2) (pderiv (3 : Fin 4) F)|) :
    ∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤
        N ^ (calibrationPower C B + B + 1) *
          ((1 + ∑ f ∈ F.support, |F.coeff f|) +
            ∑ f ∈ P.support, |P.coeff f|) ^ (calibrationPower C B + B + 1)) ∧
      σ univ ≤ ρ {p | p.1 ∈ A ∧ p.2 ∈ I ∧
        trajectoryFit (b p.1) Q I (N ^ ε) c ∧
        N ^ (-ε) ≤ |eval (point (b p.1) p.2) (pderiv (3 : Fin 4) Q)|} := by
  let G := affineSheetRestriction L F
  let Q := baseCalibratedTest F G
  have hG : G.totalDegree ≤ 2 := (affineSheetRestriction_degree L F).trans hF
  have hZ : Measurable (fun p : α × ℝ => point (b p.1) p.2 ∘ Fin.castSucc) := by
    unfold point
    fun_prop
  have htrace : ∀ᵐ p ∂σ,
      (∀ i : Fin 3, |(point (b p.1) p.2 ∘ Fin.castSucc) i| ≤ N ^ B) ∧
      |eval (point (b p.1) p.2 ∘ Fin.castSucc) G| ≤ N ^ B := by
    filter_upwards [hsource] with p hp
    obtain ⟨hpA, hpI, hpbase, hpfit, hpclose, hpfloor⟩ := hp
    obtain ⟨hv, hd, hdd⟩ := hpfit p.2 hpI
    refine ⟨hpbase, ?_⟩
    exact (affineSheetRestriction_value_bound L F hF (point (b p.1) p.2) ha hH
      hv hd hdd ((hpclose p.2 hpI).trans hsmall)).trans hcalValue
  have hcoeff := hcal.coefficients_of_power_caps hC hN hCN hB σ
    (fun p => point (b p.1) p.2 ∘ Fin.castSucc) hZ G hG hmass hcap htrace
  have hpow0 : 0 ≤ N ^ (calibrationPower C B + B) := by positivity
  have hQcoeff (e : Fin 4 →₀ ℕ) : |Q.coeff e| ≤ |F.coeff e| + N ^ (calibrationPower C B + B) := by
    have hr := coeff_rename_base_le G hpow0 hcoeff e
    exact (show |Q.coeff e| ≤ |F.coeff e| + |(rename Fin.castSucc G).coeff e| by
      simpa only [Q, baseCalibratedTest, coeff_sub] using
        abs_sub (F.coeff e) ((rename Fin.castSucc G).coeff e)).trans
          (add_le_add le_rfl hr)
  refine ⟨Q, baseCalibratedTest_degree hF hG, ?_, ?_⟩
  · intro e
    exact (hQcoeff e).trans (homogeneous_coeff_add_power hN
      (by have := calibrationPower_pos hC hB; linarith) F P e)
  · have hgood : ∀ᵐ p ∂σ,
        p.1 ∈ A ∧ p.2 ∈ I ∧ trajectoryFit (b p.1) Q I (N ^ ε) c ∧
        N ^ (-ε) ≤ |eval (point (b p.1) p.2) (pderiv (3 : Fin 4) Q)| := by
      filter_upwards [hsource] with p hp
      obtain ⟨hpA, hpI, hpbase, hpfit, hpclose, hpfloor⟩ := hp
      refine ⟨hpA, hpI, ?_, ?_⟩
      · have hf := affine_correction_fit_with_loss L F hF (b p.1) I
          ha hc hH hJ hsmall hpfit hpclose
        intro t ht
        obtain ⟨hv, hd, hdd⟩ := hf t ht
        refine ⟨hv.trans (mul_le_mul_of_nonneg_right hfitLoss hc.le),
          hd.trans hfitLoss, hdd.trans (div_le_div_of_nonneg_right hfitLoss hc.le)⟩
      · simpa only [Q, pderiv_baseCalibratedTest] using hpfloor
    exact Submission.Obl.k4_scalar_grid_parameter_preparation.original_mass_of_ae_event
      σ ρ hσρ _ hgood

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
