import Submission.Lib.K4ContactNormalization.HomogeneousCorrection
import Submission.Lib.K4AffineMeshCaps.Transport

/-!
The return from a fine affine predictor uses the original true test.  Its hidden
derivatives stay unchanged; the base correction is calibrated on the original
finite-mesh witness law, independently of the predictor's coefficients.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The frozen finite-mesh quadratic calibration interface. -/
def MeshCalibration (C : ℝ) : Prop :=
  ∀ K β m E δ : ℝ, 1 ≤ K → 0 < β → 0 < m → 0 ≤ E → 0 < δ →
    C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2 →
    ∀ μ : Measure (Fin 3 → ℝ), IsFiniteMeasure μ →
      ENNReal.ofReal m ≤ μ univ →
      (∀ q : Fin 3 → ℤ,
        μ {z | (fun i : Fin 3 => ⌊z i / δ⌋) = q} ≤
          ENNReal.ofReal (β * δ ^ (3 : ℕ))) →
      ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
        (∀ᵐ z ∂μ, (∀ i, |z i| ≤ K) ∧ |eval z G| ≤ E) →
        ∀ e, |G.coeff e| ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * E

/-- Calibration also applies to a measurable observation of an original law. -/
theorem MeshCalibration.observation_bound {C : ℝ} (hcal : MeshCalibration C)
    {Ω : Type*} [MeasurableSpace Ω] (σ : Measure Ω) [IsFiniteMeasure σ]
    (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z)
    (G : MvPolynomial (Fin 3) ℝ) (hG : G.totalDegree ≤ 2)
    {K β m E δ : ℝ} (hK : 1 ≤ K) (hβ : 0 < β) (hm : 0 < m)
    (hE : 0 ≤ E) (hδ : 0 < δ)
    (hsmall : C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2)
    (hmass : ENNReal.ofReal m ≤ σ univ)
    (hcap : ∀ q : Fin 3 → ℤ,
      σ {p | (fun i : Fin 3 => ⌊Z p i / δ⌋) = q} ≤
        ENNReal.ofReal (β * δ ^ (3 : ℕ)))
    (htrace : ∀ᵐ p ∂σ, (∀ i, |Z p i| ≤ K) ∧ |eval (Z p) G| ≤ E) :
    ∀ e, |G.coeff e| ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * E := by
  apply hcal K β m E δ hK hβ hm hE hδ hsmall (σ.map Z) inferInstance
  · simpa only [Measure.map_apply hZ MeasurableSet.univ, preimage_univ] using hmass
  · intro q
    have hq : MeasurableSet {z : Fin 3 → ℝ | (fun i : Fin 3 => ⌊z i / δ⌋) = q} := by
      exact (Submission.Lib.K4AffineMeshCaps.measurable_baseMesh δ)
        (measurableSet_singleton q)
    rw [Measure.map_apply hZ hq]
    exact hcap q
  · exact hG
  · apply (ae_map_iff hZ.aemeasurable ?_).mpr htrace
    have hcoord : MeasurableSet {z : Fin 3 → ℝ | ∀ i, |z i| ≤ K} := by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i =>
        (isClosed_le (continuous_apply i).abs continuous_const).measurableSet
    exact hcoord.inter (isClosed_le G.continuous_eval.abs continuous_const).measurableSet

/-- A predictor loss belongs in the fit constant, rather than in its width. -/
theorem affine_correction_fit_with_loss
    (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ) (hF : F.totalDegree ≤ 2)
    (b : Fin 6 → ℝ) (I : Set ℝ) {a c H J : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hH : 0 ≤ H) (hJ : 1 ≤ J)
    (hsmall : J * c ≤ a)
    (hfit : ∀ t ∈ I, |eval (point b t) F| ≤ H * a ∧
      |eval (point b t) (pderiv 3 F)| ≤ H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 F))| ≤ H / a)
    (hclose : ∀ t ∈ I,
      |eval (point b t) (affineBase L) -
        point b t 3| ≤ J * c) :
    ∀ t ∈ I,
      |eval (point b t)
        (baseCalibratedTest F (affineSheetRestriction L F))| ≤ (2 * H * J) * c ∧
      |eval (point b t)
        (pderiv 3 (baseCalibratedTest F (affineSheetRestriction L F)))| ≤ 2 * H * J ∧
      |eval (point b t)
        (pderiv 3 (pderiv 3 (baseCalibratedTest F (affineSheetRestriction L F))))| ≤
          (2 * H * J) / c := by
  have hJ0 : 0 < J := by linarith
  have hH2 : 2 * H ≤ 2 * H * J := le_mul_of_one_le_right (by positivity) hJ
  have hcc : c ≤ J * c := by nlinarith
  have he := affine_correction_full_fit L F hF b I ha (mul_pos hJ0 hc) hsmall hH hfit hclose
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := he t ht
  refine ⟨by simpa only [mul_assoc] using hv, hd.trans hH2, ?_⟩
  exact hdd.trans ((div_le_div_of_nonneg_left (by positivity) hc hcc).trans
    (div_le_div_of_nonneg_right hH2 hc.le))

/-- The homogeneous coefficient bound depends on original witness mass and mesh
caps, and has no dependence on the affine sheet's coefficients. -/
theorem MeshCalibration.affine_correction_coefficients {C : ℝ}
    (hcal : MeshCalibration C) {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) [IsFiniteMeasure σ] (X : Ω → Fin 4 → ℝ)
    (hX : Measurable (fun p => X p ∘ Fin.castSucc))
    (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ) (hF : F.totalDegree ≤ 2)
    {K β m a H δ : ℝ} (hK : 1 ≤ K) (hβ : 0 < β) (hm : 0 < m)
    (ha : 0 < a) (hH : 0 ≤ H) (hδ : 0 < δ)
    (hsmall : C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2)
    (hmass : ENNReal.ofReal m ≤ σ univ)
    (hcap : ∀ q : Fin 3 → ℤ,
      σ {p | (fun i : Fin 3 => ⌊X p i.castSucc / δ⌋) = q} ≤
        ENNReal.ofReal (β * δ ^ (3 : ℕ)))
    (htrace : ∀ᵐ p ∂σ,
      (∀ i : Fin 3, |X p i.castSucc| ≤ K) ∧
      |eval (X p) F| ≤ H * a ∧ |eval (X p) (pderiv 3 F)| ≤ H ∧
      |eval (X p) (pderiv 3 (pderiv 3 F))| ≤ H / a ∧
      |eval (X p) (affineBase L) - X p 3| ≤ a) :
    ∀ e, |(baseCalibratedTest F (affineSheetRestriction L F)).coeff e| ≤
      |F.coeff e| + C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * (3 * H * a) := by
  have hG : (affineSheetRestriction L F).totalDegree ≤ 2 :=
    (affineSheetRestriction_degree L F).trans hF
  have hval : ∀ᵐ p ∂σ,
      (∀ i : Fin 3, |(X p ∘ Fin.castSucc) i| ≤ K) ∧
      |eval (X p ∘ Fin.castSucc) (affineSheetRestriction L F)| ≤ 3 * H * a := by
    filter_upwards [htrace] with p hp
    exact ⟨hp.1, affineSheetRestriction_value_bound L F hF (X p) ha hH
      hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2⟩
  have hcoeff := hcal.observation_bound σ (fun p => X p ∘ Fin.castSucc) hX
    (affineSheetRestriction L F) hG hK hβ hm (by positivity) hδ hsmall hmass hcap hval
  intro e
  have hnonneg : 0 ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * (3 * H * a) := by
    exact (abs_nonneg _).trans (hcoeff 0)
  have hrename := coeff_rename_base_le (affineSheetRestriction L F) hnonneg hcoeff e
  have hsub : |(baseCalibratedTest F (affineSheetRestriction L F)).coeff e| ≤
      |F.coeff e| + |(rename Fin.castSucc (affineSheetRestriction L F)).coeff e| := by
    simpa only [baseCalibratedTest, coeff_sub] using
      abs_sub (F.coeff e) ((rename Fin.castSucc (affineSheetRestriction L F)).coeff e)
  exact hsub.trans (add_le_add le_rfl hrename)

/-- The first hidden derivative on an affine sheet is controlled directly by
its original value and curvature bounds. -/
theorem affineSheetRestriction_derivative_bound
    (L : Fin 4 → ℝ) (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (x : Fin 4 → ℝ) {r H J : ℝ} (hr : 0 ≤ r)
    (hclose : |eval x (affineBase L) - x 3| ≤ r)
    (hd : |eval x (pderiv (3 : Fin 4) P)| ≤ H)
    (hdd : |eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ J) :
    |eval (x ∘ Fin.castSucc) (affineSheetRestriction L (pderiv (3 : Fin 4) P))| ≤
      H + r * J := by
  rw [eval_affineSheetRestriction]
  have ht := Submission.Lib.K4HiddenQuadratic.eval_update_add_pderiv P hP x
    (3 : Fin 4) (eval x (affineBase L) - x 3)
  rw [show x 3 + (eval x (affineBase L) - x 3) = eval x (affineBase L) by ring] at ht
  rw [ht]
  calc
    _ ≤ |eval x (pderiv (3 : Fin 4) P)| +
        |eval x (affineBase L) - x 3| *
          |eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| := by
      simpa only [abs_mul] using abs_add_le (eval x (pderiv (3 : Fin 4) P))
        ((eval x (affineBase L) - x 3) *
          eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)))
    _ ≤ H + r * J := add_le_add hd (mul_le_mul hclose hdd (abs_nonneg _) hr)

/-- Native value and derivative calibration after arbitrary affine subtraction.
Only the original witness law and the bounded residual enter the coefficient
cost, so this also applies when the original affine part is unbounded. -/
theorem MeshCalibration.affine_sheet_jet_coefficients {C : ℝ}
    (hcal : MeshCalibration C) {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure Ω) [IsFiniteMeasure σ] (X : Ω → Fin 4 → ℝ)
    (hX : Measurable (fun p => X p ∘ Fin.castSucc))
    (L : Fin 4 → ℝ) (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {K β m H δ : ℝ} (hK : 1 ≤ K) (hβ : 0 < β) (hm : 0 < m)
    (hH : 0 ≤ H) (hδ : 0 < δ)
    (hsmall : C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2)
    (hmass : ENNReal.ofReal m ≤ σ univ)
    (hcap : ∀ q : Fin 3 → ℤ,
      σ {p | (fun i : Fin 3 => ⌊X p i.castSucc / δ⌋) = q} ≤
        ENNReal.ofReal (β * δ ^ (3 : ℕ)))
    (htrace : ∀ᵐ p ∂σ,
      (∀ i : Fin 3, |X p i.castSucc| ≤ K) ∧
      |eval (X p) P| ≤ H ∧ |eval (X p) (pderiv (3 : Fin 4) P)| ≤ H ∧
      |eval (X p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ H ∧
      |eval (X p) (affineBase L) - X p 3| ≤ 1) :
    (∀ e, |(affineSheetRestriction L P).coeff e| ≤
      C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * (3 * H)) ∧
    (∀ e, |(affineSheetRestriction L (pderiv (3 : Fin 4) P)).coeff e| ≤
      C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * (3 * H)) := by
  have hP' : (pderiv (3 : Fin 4) P).totalDegree ≤ 2 :=
    (Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred P 3).trans (by omega)
  have htrace0 : ∀ᵐ p ∂σ,
      (∀ i : Fin 3, |(X p ∘ Fin.castSucc) i| ≤ K) ∧
      |eval (X p ∘ Fin.castSucc) (affineSheetRestriction L P)| ≤ 3 * H := by
    filter_upwards [htrace] with p hp
    refine ⟨hp.1, ?_⟩
    have hh := affineSheetRestriction_value_bound L P hP (X p)
      (by norm_num : (0 : ℝ) < 1) hH
      (by simpa only [mul_one] using hp.2.1) hp.2.2.1
      (by simpa only [div_one] using hp.2.2.2.1) hp.2.2.2.2
    simpa only [mul_one] using hh
  have htrace1 : ∀ᵐ p ∂σ,
      (∀ i : Fin 3, |(X p ∘ Fin.castSucc) i| ≤ K) ∧
      |eval (X p ∘ Fin.castSucc) (affineSheetRestriction L (pderiv (3 : Fin 4) P))| ≤
        3 * H := by
    filter_upwards [htrace] with p hp
    refine ⟨hp.1, ?_⟩
    have hh := affineSheetRestriction_derivative_bound L P hP (X p)
      (by norm_num : (0 : ℝ) ≤ 1) hp.2.2.2.2 hp.2.2.1 hp.2.2.2.1
    exact hh.trans (by simpa only [one_mul] using (show H + H ≤ 3 * H by linarith))
  exact ⟨hcal.observation_bound σ _ hX _ ((affineSheetRestriction_degree L P).trans hP)
      hK hβ hm (by positivity) hδ hsmall hmass hcap htrace0,
    hcal.observation_bound σ _ hX _ ((affineSheetRestriction_degree L _).trans hP')
      hK hβ hm (by positivity) hδ hsmall hmass hcap htrace1⟩

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
