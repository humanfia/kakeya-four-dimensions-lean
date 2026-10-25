import Submission.Lib.K4ModelReduction.IndexedSmoothing

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 The framework's six real coefficients, retaining the original discrete label. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

/-- First the three intercepts, then the three slopes. -/
noncomputable def coefficientPairEquiv :
    (Fin 6 → ℝ) ≃ᵐ (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 6 => ℝ)
    (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6)).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ)).trans
      (MeasurableEquiv.prodCongr
        (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.toMeasurableEquiv
        (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.toMeasurableEquiv))

theorem coefficientPairEquiv_intercept (c : Fin 6 → ℝ) (i : Fin 3) :
    (coefficientPairEquiv c).1 i = c (i.castAdd 3) := rfl

theorem coefficientPairEquiv_slope (c : Fin 6 → ℝ) (i : Fin 3) :
    (coefficientPairEquiv c).2 i = c (i.natAdd 3) := rfl

theorem coefficientPairEquiv_measurePreserving :
    MeasurePreserving coefficientPairEquiv volume volume := by
  have h₁ := volume_measurePreserving_piCongrLeft (fun _ : Fin 6 => ℝ)
    (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6)
  have h₁' := MeasurePreserving.symm (MeasurableEquiv.piCongrLeft (fun _ : Fin 6 => ℝ)
    (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6)) h₁
  have h₂ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ)
  have h₃ := (PiLp.volume_preserving_toLp (Fin 3)).prod
    (PiLp.volume_preserving_toLp (Fin 3))
  exact h₃.comp (h₂.comp h₁')

noncomputable def labeledCoefficientEquiv :
    (ℕ × (Fin 6 → ℝ)) ≃ᵐ
      (ℕ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℕ) coefficientPairEquiv

theorem labeledCoefficientEquiv_measurePreserving :
    MeasurePreserving labeledCoefficientEquiv
      ((Measure.count : Measure ℕ).prod volume) ((Measure.count : Measure ℕ).prod volume) :=
  (MeasurePreserving.id Measure.count).prod coefficientPairEquiv_measurePreserving

noncomputable def rawSmoothedTrajectoryLaw {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) : Measure (ℕ × (Fin 6 → ℝ)) :=
  (indexedSmoothedTrajectoryLaw b s δ).map labeledCoefficientEquiv.symm

theorem rawSmoothedTrajectoryLaw_isProbabilityMeasure {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    IsProbabilityMeasure (rawSmoothedTrajectoryLaw b s δ) := by
  have := indexedSmoothedTrajectoryLaw_isProbabilityMeasure b s hn hδ
  change IsProbabilityMeasure ((indexedSmoothedTrajectoryLaw b s δ).map labeledCoefficientEquiv.symm)
  infer_instance

theorem rawSmoothedTrajectoryLaw_map {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    (rawSmoothedTrajectoryLaw b s δ).map labeledCoefficientEquiv =
      indexedSmoothedTrajectoryLaw b s δ := by
  rw [rawSmoothedTrajectoryLaw, Measure.map_map labeledCoefficientEquiv.measurable
    labeledCoefficientEquiv.symm.measurable]
  simp only [MeasurableEquiv.self_comp_symm, Measure.map_id]

theorem rawSmoothedTrajectoryLaw_eq {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    rawSmoothedTrajectoryLaw b s δ =
      ∑ i : Fin n, ((n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) ^ 2) •
        ((Measure.count : Measure ℕ).prod volume).restrict
          (labeledCoefficientEquiv ⁻¹'
            ({(i : ℕ)} ×ˢ (ball (b i) (δ / 4) ×ˢ ball (s i) (δ / 4)))) := by
  rw [rawSmoothedTrajectoryLaw, indexedSmoothedTrajectoryLaw_eq,
    Measure.map_finset_sum' labeledCoefficientEquiv.symm.measurable.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.map_smul _ labeledCoefficientEquiv.symm.measurable.aemeasurable]
  congr 1
  exact (MeasurePreserving.symm labeledCoefficientEquiv
    (labeledCoefficientEquiv_measurePreserving.restrict_preimage
      (measurableSet_singleton (i : ℕ) |>.prod (measurableSet_ball.prod measurableSet_ball)))).map_eq

/-- The prior is exactly a finite sum of pushed-forward six-dimensional
volume restrictions, in the form required by the frozen temperedness clause. -/
theorem rawSmoothedTrajectoryLaw_eq_maps {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    rawSmoothedTrajectoryLaw b s δ =
      ∑ i : Fin n, ENNReal.ofReal ((n : ℝ)⁻¹ * (48 / (Real.pi * δ ^ 3)) ^ 2) •
        (volume.restrict (coefficientPairEquiv ⁻¹'
          (ball (b i) (δ / 4) ×ˢ ball (s i) (δ / 4)))).map (Prod.mk (i : ℕ)) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hweight : (n : ℝ≥0∞)⁻¹ * ENNReal.ofReal (48 / (Real.pi * δ ^ 3)) ^ 2 =
      ENNReal.ofReal ((n : ℝ)⁻¹ * (48 / (Real.pi * δ ^ 3)) ^ 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hnreal,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [rawSmoothedTrajectoryLaw_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hpre : labeledCoefficientEquiv ⁻¹'
        ({(i : ℕ)} ×ˢ (ball (b i) (δ / 4) ×ˢ ball (s i) (δ / 4))) =
      {(i : ℕ)} ×ˢ (coefficientPairEquiv ⁻¹'
        (ball (b i) (δ / 4) ×ˢ ball (s i) (δ / 4))) := by
    ext z
    rfl
  rw [hpre, ← dirac_prod_restrict_count, Measure.dirac_prod, hweight]

theorem coefficientPairEquiv_slope_vector (c : Fin 6 → ℝ) :
    (coefficientPairEquiv c).2 = WithLp.toLp 2 ![c 3, c 4, c 5] := by
  ext i
  fin_cases i <;> rfl

theorem rawSmoothedTrajectoryLaw_slope {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    (rawSmoothedTrajectoryLaw b s δ).map
      (fun z => (WithLp.toLp 2 ![z.2 3, z.2 4, z.2 5] : EuclideanSpace ℝ (Fin 3))) =
        smoothedSlopeLaw s δ := by
  have hobs : (fun z : ℕ × (Fin 6 → ℝ) =>
      (WithLp.toLp 2 ![z.2 3, z.2 4, z.2 5] : EuclideanSpace ℝ (Fin 3))) =
      (fun z : ℕ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) => z.2.2) ∘
        labeledCoefficientEquiv := by
    funext z
    exact (coefficientPairEquiv_slope_vector z.2).symm
  have hproj : Measurable
      (fun z : ℕ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) => z.2.2) :=
    measurable_snd.comp measurable_snd
  rw [hobs, ← Measure.map_map hproj
    labeledCoefficientEquiv.measurable, rawSmoothedTrajectoryLaw_map]
  exact indexedSmoothedTrajectoryLaw_slope b s hn hδ

theorem rawSmoothedTrajectoryLaw_coefficients {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 < δ) :
    (rawSmoothedTrajectoryLaw b s δ).map (fun z => coefficientPairEquiv z.2) =
      smoothedTrajectoryLaw b s δ := by
  change (rawSmoothedTrajectoryLaw b s δ).map (Prod.snd ∘ labeledCoefficientEquiv) = _
  rw [← Measure.map_map measurable_snd labeledCoefficientEquiv.measurable,
    rawSmoothedTrajectoryLaw_map, indexedSmoothedTrajectoryLaw_marginal b s hδ]

theorem rawSmoothedTrajectoryLaw_label_bound {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ z ∂rawSmoothedTrajectoryLaw b s δ, z.1 < n := by
  have hS : MeasurableSet {z : ℕ × (Fin 6 → ℝ) | z.1 < n} := by measurability
  rw [rawSmoothedTrajectoryLaw,
    ae_map_iff labeledCoefficientEquiv.symm.measurable.aemeasurable hS]
  exact indexedSmoothedTrajectoryLaw_label_bound b s hδ

/-- The original-prior slope bound holds for every set, by outer measure;
no measurability of a later geometrically defined slope set is required. -/
theorem rawSmoothedTrajectoryLaw_slope_preimage_le {n : ℕ}
    (b s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ c : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) (hc : 0 < c)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (s i) (s j))
    (hmass : c ≤ (n : ℝ) * δ ^ 3) (Z : Set (EuclideanSpace ℝ (Fin 3))) :
    rawSmoothedTrajectoryLaw b s δ
      {z | (WithLp.toLp 2 ![z.2 3, z.2 4, z.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤
        ENNReal.ofReal (48 / (Real.pi * c)) * volume Z := by
  have hmeas : Measurable (fun z : ℕ × (Fin 6 → ℝ) =>
      (WithLp.toLp 2 ![z.2 3, z.2 4, z.2 5] : EuclideanSpace ℝ (Fin 3))) := by fun_prop
  calc
    _ ≤ (rawSmoothedTrajectoryLaw b s δ).map
        (fun z => (WithLp.toLp 2 ![z.2 3, z.2 4, z.2 5] : EuclideanSpace ℝ (Fin 3))) Z :=
      Measure.le_map_apply hmeas.aemeasurable Z
    _ = smoothedSlopeLaw s δ Z := by rw [rawSmoothedTrajectoryLaw_slope b s hn hδ]
    _ ≤ (ENNReal.ofReal (48 / (Real.pi * c)) • volume) Z :=
      (smoothedSlopeLaw_le_volume s hδ hc hsep hmass) Z
    _ = _ := Measure.smul_apply _ _ _

end Submission.Lib.K4ModelReduction
