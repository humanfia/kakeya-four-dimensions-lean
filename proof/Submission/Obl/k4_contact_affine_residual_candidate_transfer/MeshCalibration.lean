import Submission.Lib.K4ContactNormalization.HomogeneousCorrection

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory MvPolynomial Set
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting

/-- The coefficient calibration supplied by the frozen statement. -/
def MeshCalibration : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ K β m E δ : ℝ,
    1 ≤ K → 0 < β → 0 < m → 0 ≤ E → 0 < δ →
    C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2 →
    ∀ μ : Measure (Fin 3 → ℝ), IsFiniteMeasure μ →
    ENNReal.ofReal m ≤ μ univ →
    (∀ q : Fin 3 → ℤ,
      μ {z | (fun i : Fin 3 => ⌊z i / δ⌋) = q} ≤
        ENNReal.ofReal (β * δ ^ (3 : ℕ))) →
    ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
    (∀ᵐ z ∂μ, (∀ i, |z i| ≤ K) ∧ |eval z G| ≤ E) →
    ∀ e, |G.coeff e| ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * E

/-- Use a mesh ceiling on the original incidence law, rather than assuming
domination of its base projection on arbitrary measurable sets. -/
theorem mesh_calibration_on_original_law (h : MeshCalibration) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 3 → ℝ),
      Measurable Z → ∀ K β m E δ : ℝ,
      1 ≤ K → 0 < β → 0 < m → 0 ≤ E → 0 < δ →
      C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2 →
      ENNReal.ofReal m ≤ μ univ →
      (∀ q : Fin 3 → ℤ,
        μ {ω | (fun i : Fin 3 => ⌊Z ω i / δ⌋) = q} ≤
          ENNReal.ofReal (β * δ ^ (3 : ℕ))) →
      ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
      (∀ᵐ ω ∂μ, (∀ i, |Z ω i| ≤ K) ∧ |eval (Z ω) G| ≤ E) →
      ∀ e, |G.coeff e| ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * E := by
  obtain ⟨C, hC, hcal⟩ := h
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ Z hZ K β m E δ hK hβ hm hE hδ hsmall hmass hcell G hG hgood
  apply hcal K β m E δ hK hβ hm hE hδ hsmall (μ.map Z) inferInstance
  · simpa only [Measure.map_apply hZ MeasurableSet.univ, preimage_univ] using hmass
  · intro q
    rw [Measure.map_apply hZ]
    · exact hcell q
    · have hfloor : Measurable (fun z : Fin 3 → ℝ =>
          fun i : Fin 3 => (⌊z i / δ⌋ : ℤ)) :=
        Measurable.of_eval (fun i => by
          have hi : Measurable (fun z : Fin 3 → ℝ => z i) := measurable_pi_apply i
          have hid : Measurable (fun z : Fin 3 → ℝ => z i / δ) := hi.div_const δ
          exact hid.floor)
      exact measurableSet_eq_fun hfloor measurable_const
  · exact hG
  · apply (ae_map_iff hZ.aemeasurable ?_).2 hgood
    have hbounded : MeasurableSet {z : Fin 3 → ℝ | ∀ i, |z i| ≤ K} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun i =>
        measurableSet_le (measurable_pi_apply i).abs measurable_const)
    exact hbounded.inter (measurableSet_le G.continuous_eval.measurable.abs measurable_const)

/-- Subtracting a calibrated base polynomial retains a homogeneous coefficient
bound in the original test, independently of the affine predictor. -/
theorem base_correction_coeff_bound (F : MvPolynomial (Fin 4) ℝ)
    (G : MvPolynomial (Fin 3) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ e, |G.coeff e| ≤ B) (e : Fin 4 →₀ ℕ) :
    |(baseCalibratedTest F G).coeff e| ≤ coeffL1 F + B := by
  calc
    _ ≤ |F.coeff e| + |(rename Fin.castSucc G).coeff e| := by
      simpa only [baseCalibratedTest, coeff_sub] using
        abs_sub (F.coeff e) ((rename Fin.castSucc G).coeff e)
    _ ≤ coeffL1 F + B :=
      add_le_add (abs_coeff_le_coeffL1 F e) (coeff_rename_base_le G hB hG e)

/-- The original-law mesh theorem calibrates the original quadratic after
substitution of an arbitrary affine predictor. Its coefficients are not an
input to this estimate. -/
theorem mesh_calibrated_affine_correction (h : MeshCalibration) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsFiniteMeasure μ] (x : Ω → Fin 4 → ℝ),
      Measurable (fun ω => x ω ∘ Fin.castSucc) →
      ∀ K β m H a δ : ℝ,
      1 ≤ K → 0 < β → 0 < m → 0 ≤ H → 0 < a → 0 < δ →
      C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2 →
      ENNReal.ofReal m ≤ μ univ →
      (∀ q : Fin 3 → ℤ,
        μ {ω | (fun i : Fin 3 => ⌊x ω i.castSucc / δ⌋) = q} ≤
          ENNReal.ofReal (β * δ ^ (3 : ℕ))) →
      ∀ (F : MvPolynomial (Fin 4) ℝ) (L : Fin 4 → ℝ), F.totalDegree ≤ 2 →
      (∀ᵐ ω ∂μ, (∀ i : Fin 3, |x ω i.castSucc| ≤ K) ∧
        |eval (x ω) F| ≤ H * a ∧ |eval (x ω) (pderiv 3 F)| ≤ H ∧
        |eval (x ω) (pderiv 3 (pderiv 3 F))| ≤ H / a ∧
        |eval (x ω) (affineBase L) - x ω 3| ≤ a) →
      let Q := baseCalibratedTest F (affineSheetRestriction L F)
      Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤ coeffL1 F +
        C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * (3 * H * a)) ∧
      pderiv 3 Q = pderiv 3 F ∧
      pderiv 3 (pderiv 3 Q) = pderiv 3 (pderiv 3 F) := by
  obtain ⟨C, hC, hcal⟩ := mesh_calibration_on_original_law h
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ x hx K β m H a δ hK hβ hm hH ha hδ hsmall hmass hcell F L hF htrace
  have hG : (affineSheetRestriction L F).totalDegree ≤ 2 :=
    (affineSheetRestriction_degree L F).trans hF
  have hgood : ∀ᵐ ω ∂μ, (∀ i : Fin 3, |(x ω ∘ Fin.castSucc) i| ≤ K) ∧
      |eval (x ω ∘ Fin.castSucc) (affineSheetRestriction L F)| ≤ 3 * H * a := by
    filter_upwards [htrace] with ω hω
    exact ⟨hω.1, affineSheetRestriction_value_bound L F hF (x ω) ha hH
      hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2⟩
  have hcoeff := hcal Ω μ (fun ω => x ω ∘ Fin.castSucc) hx K β m (3 * H * a) δ
    hK hβ hm (by positivity) hδ hsmall hmass hcell (affineSheetRestriction L F) hG hgood
  refine ⟨baseCalibratedTest_degree hF hG, ?_,
    pderiv_baseCalibratedTest _ _, second_pderiv_baseCalibratedTest _ _⟩
  exact base_correction_coeff_bound F (affineSheetRestriction L F) (by positivity) hcoeff

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
