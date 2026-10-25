-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/Saturation.lean
import Submission.Obl.k4_terminal_label_saturation.SatFormat
import Submission.Obl.k4_terminal_label_saturation.SatMarkov

/-!
# Saturation: terminal-observation knowledge for a true chart system

Paper Lemma 2.8, the label-knowledge part, for one sample of a true system in
the exact frozen chart format.  Keep every chart datum and restrict each
selection `F b` to the incidences whose terminal observation is compatible with
at most `H` charts of their world.  The lists `lst γ₁ o` of compatible charts
then have at most `H` entries, every retained incidence of `b` lists `b`, and
the weighted mass lost is at most

  `2 θ + 2 * cap * π κ³ (14 + 48 κ²) / (n₀ H) * (weighted mass of the F b)`,

where `θ` bounds the weighted mass above the density cap `cap` and `n₀` is the
true-floor density.
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- The charts of world `γ₁` compatible with the observation `o`. -/
def compatCharts {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T)) (κ δ : ℝ)
    (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (γ₁ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Set (Fin C') :=
  {b | γ b = γ₁ ∧ o ∈ chartCompat T ((j b : ℕ) : ℝ) κ δ (B γ₁) (c b) (u b) (Q b) (R b)}

/-- The saturated selection. -/
def satSel {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T)) (κ δ : ℝ)
    (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (H : ℝ) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (b : Fin C') :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  F b ∩ {p | (((compatCharts γ j κ δ B c u Q R (γ b) (obs (B (γ b)) δ p)).ncard : ℕ) : ℝ) ≤ H}

/-- The saturated lists. -/
noncomputable def satList {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    (κ δ : ℝ) (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (H : ℝ) (γ₁ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Finset (Fin C') := by
  classical
  exact if (((compatCharts γ j κ δ B c u Q R γ₁ o).ncard : ℕ) : ℝ) ≤ H then
    (Set.toFinite (compatCharts γ j κ δ B c u Q R γ₁ o)).toFinset else ∅

theorem satList_card_le {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    (κ δ : ℝ) (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    {H : ℝ} (hH : 0 ≤ H) (γ₁ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((satList γ j κ δ B c u Q R H γ₁ o).card : ℝ) ≤ H := by
  classical
  unfold satList
  split_ifs with h
  · rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact h
  · simpa using hH

/-- A point of a chart's selection is compatible with that chart's observation. -/
theorem obs_mem_chartCompat (T : ℕ) (j : ℝ) {κ δ B : ℝ} (hκ : 1 ≤ κ) (hδ : 0 < δ)
    (hB : 0 < B) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) (p : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (ht : p.2 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T))
    (hbox : ‖Matrix.toEuclideanLin Q⁻¹ (y p.1 p.2 - c - p.2 • u)‖ ≤ κ)
    (hval : |eval (x p.1 p.2) R| ≤ κ * δ)
    (hder : |eval (x p.1 p.2) (pderiv 3 R)| ≤ κ * B)
    (hcurv : |eval (x p.1 p.2) (pderiv 3 (pderiv 3 R))| ≤ κ * B ^ 2 / δ)
    (hfloor : B / κ ≤ |eval (x p.1 p.2) (pderiv 3 R)|) :
    obs B δ p ∈ chartCompat T j κ δ B c u Q R := by
  have hcurv' : |curvature R 3| ≤ κ * B ^ 2 / δ := by
    rw [second_pderiv_eq_curvature R hR 3, eval_C] at hcurv
    exact hcurv
  have hx : x p.1 p.2 = ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4,
      p.1.2 2 + p.2 * p.1.2 5] := rfl
  rw [hx] at hval hder hfloor
  have hbin := hiddenBinTest_of_point R hR p.2 (p.1.2 0 + p.2 * p.1.2 3)
    (p.1.2 1 + p.2 * p.1.2 4) (p.1.2 2 + p.2 * p.1.2 5) hκ hδ hB hval hder hcurv' hfloor
  refine ⟨?_, ?_, ?_⟩
  · simpa [obs] using ht
  · simpa [chartBox, obs, y, x] using hbox
  · simpa [obs, x] using hbin

/-- Each incidence lies in the selections of at most two charts of its world. -/
theorem selection_multiplicity_le_two {W C' T : ℕ} (γ : Fin C' → Fin W)
    (j : Fin C' → Fin (2 ^ T)) (A : Fin C' → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hF : ∀ b, ∀ p ∈ F b, p.1 ∈ A b ∧
      p.2 ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))
    (γ₁ : Fin W) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    ∑ b : {b : Fin C' // γ b = γ₁}, (F b).indicator
      (1 : (ℕ × (Fin 6 → ℝ)) × ℝ → ℝ≥0∞) p ≤ 2 := by
  classical
  set Sb : Finset {b : Fin C' // γ b = γ₁} := Finset.univ.filter (fun b => p ∈ F b) with hSb
  have hsum : ∑ b : {b : Fin C' // γ b = γ₁}, (F b).indicator
      (1 : (ℕ × (Fin 6 → ℝ)) × ℝ → ℝ≥0∞) p =
      (Sb.card : ℝ≥0∞) := by
    simp only [indicator_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Pi.one_apply, mul_one]
  rw [hsum]
  -- the block map is injective on `Sb` and lands in the blocks containing `p.2`
  have hinj : Set.InjOn (fun b : {b : Fin C' // γ b = γ₁} => j b) (Sb : Set _) := by
    intro b hb b' hb' hjj
    by_contra hne
    have hne' : (b : Fin C') ≠ b' := fun h => hne (Subtype.ext h)
    have hbF : p ∈ F b := by simpa [hSb] using hb
    have hbF' : p ∈ F b' := by simpa [hSb] using hb'
    exact Set.disjoint_left.mp (hdisj b b' hne' (b.2.trans b'.2.symm) hjj)
      (hF b p hbF).1 (hF b' p hbF').1
  have himage : (fun b : {b : Fin C' // γ b = γ₁} => j b) '' (Sb : Set _) ⊆
      {jj : Fin (2 ^ T) | p.2 ∈ Icc ((jj : ℝ) / (2 : ℝ) ^ T) (((jj : ℝ) + 1) / (2 : ℝ) ^ T)} := by
    rintro _ ⟨b, hb, rfl⟩
    have hbF : p ∈ F b := by simpa [hSb] using hb
    exact (hF b p hbF).2
  have hcard : (Sb.card : ℕ) ≤ 2 := by
    rw [← Set.ncard_coe_finset, ← hinj.ncard_image]
    exact (Set.ncard_le_ncard himage (Set.toFinite _)).trans (card_dyadic_blocks_le_two T p.2)
  exact_mod_cast hcard

theorem measurable_obs (B δ : ℝ) :
    Measurable (obs B δ : (ℕ × (Fin 6 → ℝ)) × ℝ → EuclideanSpace ℝ (Fin 3) × ℤ) := by
  have h1 : Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
      (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2] : EuclideanSpace ℝ (Fin 3))) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [x] <;> fun_prop
  have h2 : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => B * (x p.1 p.2) 3 / δ) := by
    have : Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => B * (x p.1 p.2) 3 / δ) := by
      simp only [x]
      fun_prop
    exact this.measurable
  exact h1.measurable.prodMk h2.floor

/-- The set of observations of world `γ₁` with at most `H` compatible charts is
measurable. -/
theorem measurableSet_compatCharts_le {W C' T : ℕ} (γ : Fin C' → Fin W)
    (j : Fin C' → Fin (2 ^ T)) (κ δ : ℝ) (B : Fin W → ℝ)
    (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C' → MvPolynomial (Fin 4) ℝ) (γ₁ : Fin W) {H : ℝ} (hH : 0 ≤ H) :
    MeasurableSet {o | (((compatCharts γ j κ δ B c u Q R γ₁ o).ncard : ℕ) : ℝ) ≤ H} := by
  classical
  set S : Fin C' → Set (EuclideanSpace ℝ (Fin 3) × ℤ) := fun b =>
    if γ b = γ₁ then chartCompat T ((j b : ℕ) : ℝ) κ δ (B γ₁) (c b) (u b) (Q b) (R b) else ∅
    with hSdef
  have hS : ∀ b, MeasurableSet (S b) := by
    intro b
    simp only [hSdef]
    split_ifs
    · exact measurableSet_chartCompat _ _ _ _ _ _ _ _ _
    · exact MeasurableSet.empty
  have hcnt : ∀ o, crossCount S o =
      (((compatCharts γ j κ δ B c u Q R γ₁ o).ncard : ℕ) : ℝ≥0∞) := by
    intro o
    rw [crossCount_eq_card]
    congr 3
    ext b
    simp only [mem_ofPred_eq, compatCharts, hSdef]
    split_ifs with h
    · simp [h]
    · simp [h]
  have hmeas : Measurable (crossCount S) :=
    Finset.measurable_sum _ (fun b _ => measurable_one.indicator (hS b))
  have heq : {o | (((compatCharts γ j κ δ B c u Q R γ₁ o).ncard : ℕ) : ℝ) ≤ H} =
      {o | crossCount S o ≤ ENNReal.ofReal H} := by
    ext o
    simp only [mem_ofPred_eq, hcnt]
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff hH]
  rw [heq]
  exact measurableSet_le hmeas measurable_const

/-- Capped crossing counts of one world, through Markov's inequality, the volume
of compatible observations and the true floors. -/
theorem capped_crossing_le {W C' T : ℕ} (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (g : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ≥0∞) {δ κ n₀ cap H : ℝ}
    (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hB : ∀ γ₁, 0 < B γ₁) (hδ : 0 < δ) (hκ : 1 ≤ κ) (hn₀ : 0 < n₀) (hcap : 0 ≤ cap)
    (hH : 0 < H) (hgm : ∀ γ₁, Measurable (g γ₁))
    (hmap : ∀ γ₁, Measure.map (obs (B γ₁) δ) (((ν γ₁).prod volume).restrict (E γ₁)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity (g γ₁))
    (hQ : ∀ b, (Q b).det ≠ 0) (hR : ∀ b, (R b).totalDegree ≤ 2)
    (hfloor : ∀ b, ENNReal.ofReal (n₀ * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
      ((ν (γ b)).prod volume) (F b)) (γ₁ : Fin W) :
    (((ν γ₁).prod volume).restrict (E γ₁))
        {p | g γ₁ (obs (B γ₁) δ p) ≤ ENNReal.ofReal cap ∧
          H < (((compatCharts γ j κ δ B c u Q R γ₁ (obs (B γ₁) δ p)).ncard : ℕ) : ℝ)} ≤
      ENNReal.ofReal (cap * (Real.pi * κ ^ 3 * (14 + 48 * κ ^ 2)) / (n₀ * H)) *
        ∑ b : {b : Fin C' // γ b = γ₁}, ((ν γ₁).prod volume) (F b) := by
  classical
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ
  set K : ℝ := Real.pi * κ ^ 3 * (14 + 48 * κ ^ 2) with hKdef
  have hK : 0 ≤ K := by positivity
  set S : Fin C' → Set (EuclideanSpace ℝ (Fin 3) × ℤ) := fun b =>
    if γ b = γ₁ then chartCompat T ((j b : ℕ) : ℝ) κ δ (B γ₁) (c b) (u b) (Q b) (R b) else ∅
    with hSdef
  have hS : ∀ b, MeasurableSet (S b) := by
    intro b
    simp only [hSdef]
    split_ifs
    · exact measurableSet_chartCompat _ _ _ _ _ _ _ _ _
    · exact MeasurableSet.empty
  have hcnt : ∀ o, crossCount S o =
      (((compatCharts γ j κ δ B c u Q R γ₁ o).ncard : ℕ) : ℝ≥0∞) := by
    intro o
    rw [crossCount_eq_card]
    congr 3
    ext b
    simp only [mem_ofPred_eq, compatCharts, hSdef]
    split_ifs with h
    · simp [h]
    · simp [h]
  have hmk := crossing_markov (((ν γ₁).prod volume).restrict (E γ₁))
    (measurable_obs (B γ₁) δ) _ (hgm γ₁) (hmap γ₁) S hS (ENNReal.ofReal cap) (ENNReal.ofReal H)
  have hset : {p | g γ₁ (obs (B γ₁) δ p) ≤ ENNReal.ofReal cap ∧
        H < (((compatCharts γ j κ δ B c u Q R γ₁ (obs (B γ₁) δ p)).ncard : ℕ) : ℝ)} =
      {p | g γ₁ (obs (B γ₁) δ p) ≤ ENNReal.ofReal cap ∧
        ENNReal.ofReal H < crossCount S (obs (B γ₁) δ p)} := by
    ext p
    simp only [mem_ofPred_eq, hcnt]
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hH.le]
  rw [hset]
  -- the volumes of compatible observations
  have hvol : ∑ b, ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) (S b) ≤
      ENNReal.ofReal (K / n₀) * ∑ b : {b : Fin C' // γ b = γ₁}, ((ν γ₁).prod volume) (F b) := by
    rw [Finset.mul_sum, ← Fintype.sum_fiberwise γ (fun b =>
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) (S b))]
    have hzero : ∀ γ₂, γ₂ ≠ γ₁ → ∑ b : {b : Fin C' // γ b = γ₂},
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) (S b) = 0 := by
      intro γ₂ hne
      apply Finset.sum_eq_zero
      intro b _
      have hb : γ b ≠ γ₁ := fun h => hne (b.2.symm.trans h)
      simp only [hSdef, hb, ite_false, measure_empty]
    rw [Finset.sum_eq_single γ₁ (fun γ₂ _ hne => hzero γ₂ hne) (by simp)]
    apply Finset.sum_le_sum
    intro b _
    have hb : γ b = γ₁ := b.2
    simp only [hSdef, hb, ite_true]
    have hv := volume_chartCompat_le T ((j b : ℕ) : ℝ) hκ hδ (hB γ₁) (c b) (u b) (Q b)
      (hQ b) (R b) (hR b)
    have hf := hfloor b
    rw [hb] at hf
    calc ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count)
          (chartCompat T ((j b : ℕ) : ℝ) κ δ (B γ₁) (c b) (u b) (Q b) (R b))
        ≤ ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (Real.pi * κ ^ 2 * |(Q b).det|) *
            (14 + 48 * κ ^ 2)) := hv
      _ = ENNReal.ofReal (K / n₀) *
            ENNReal.ofReal (n₀ * |(Q b).det| / ((2 : ℝ) ^ T * κ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hKdef]
          field_simp
      _ ≤ ENNReal.ofReal (K / n₀) * ((ν γ₁).prod volume) (F b) := mul_le_mul' le_rfl hf
  -- divide Markov's inequality by `H`
  have hHne : ENNReal.ofReal H ≠ 0 := by simpa using hH
  have hHtop : ENNReal.ofReal H ≠ ⊤ := ENNReal.ofReal_ne_top
  set X := (((ν γ₁).prod volume).restrict (E γ₁)) {p | g γ₁ (obs (B γ₁) δ p) ≤
    ENNReal.ofReal cap ∧ ENNReal.ofReal H < crossCount S (obs (B γ₁) δ p)} with hX
  set Y := ∑ b, ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) (S b)
    with hY
  set Z := ∑ b : {b : Fin C' // γ b = γ₁}, ((ν γ₁).prod volume) (F b) with hZ
  have hX' : X ≤ (ENNReal.ofReal H)⁻¹ * (ENNReal.ofReal cap * Y) := by
    calc X = (ENNReal.ofReal H)⁻¹ * (ENNReal.ofReal H * X) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hHne hHtop, one_mul]
      _ ≤ (ENNReal.ofReal H)⁻¹ * (ENNReal.ofReal cap * Y) := mul_le_mul' le_rfl hmk
  calc X ≤ (ENNReal.ofReal H)⁻¹ * (ENNReal.ofReal cap * Y) := hX'
    _ ≤ (ENNReal.ofReal H)⁻¹ * (ENNReal.ofReal cap * (ENNReal.ofReal (K / n₀) * Z)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hvol)
    _ = ENNReal.ofReal (cap * K / (n₀ * H)) * Z := by
        rw [← ENNReal.ofReal_inv_of_pos hH, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- **Saturation for one sample.**  Restricting each selection to the incidences
whose terminal observation is compatible with at most `H` charts of the world
gives lists of at most `H` charts that know every retained incidence, and loses
weighted mass at most `2 θ + 2 * cap * π κ³ (14 + 48 κ²) / (n₀ H)` times the
weighted mass of the old selections. -/
theorem saturation_sample {W C' T : ℕ} (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (g : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ≥0∞) {δ κ n₀ cap H : ℝ}
    (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (A : Fin C' → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hB : ∀ γ₁, 0 < B γ₁) (hδ : 0 < δ) (hκ : 1 ≤ κ) (hn₀ : 0 < n₀) (hcap : 0 ≤ cap)
    (hH : 0 < H) (hgm : ∀ γ₁, Measurable (g γ₁))
    (hmap : ∀ γ₁, Measure.map (obs (B γ₁) δ) (((ν γ₁).prod volume).restrict (E γ₁)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity (g γ₁))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hQ : ∀ b, (Q b).det ≠ 0) (hR : ∀ b, (R b).totalDegree ≤ 2)
    (hFm : ∀ b, MeasurableSet (F b))
    (hA : ∀ b, ∀ l ∈ A b, ∀ t ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T)
        ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T),
      ‖Matrix.toEuclideanLin (Q b)⁻¹ (y l t - c b - t • u b)‖ ≤ κ ∧
      |eval (x l t) (R b)| ≤ κ * δ ∧
      |eval (x l t) (pderiv 3 (R b))| ≤ κ * B (γ b) ∧
      |eval (x l t) (pderiv 3 (pderiv 3 (R b)))| ≤ κ * B (γ b) ^ 2 / δ)
    (hF : ∀ b, ∀ p ∈ F b, p ∈ E (γ b) ∧ p.1 ∈ A b ∧
      p.2 ∈ Icc (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧
      B (γ b) / κ ≤ |eval (x p.1 p.2) (pderiv 3 (R b))|)
    (hfloor : ∀ b, ENNReal.ofReal (n₀ * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
      ((ν (γ b)).prod volume) (F b))
    (θ : ℝ≥0∞)
    (htyp : ∑ γ₁, ENNReal.ofReal (ω γ₁) * (((ν γ₁).prod volume).restrict (E γ₁))
      {p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) δ p)} ≤ θ) :
    (∀ b, ∀ p ∈ satSel γ j κ δ B c u Q R H F b,
      b ∈ satList γ j κ δ B c u Q R H (γ b) (obs (B (γ b)) δ p)) ∧
    ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b) ≤
      ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (satSel γ j κ δ B c u Q R H F b) +
        2 * θ + 2 * ENNReal.ofReal (cap * (Real.pi * κ ^ 3 * (14 + 48 * κ ^ 2)) / (n₀ * H)) *
          ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b) := by
  classical
  set K : ℝ := Real.pi * κ ^ 3 * (14 + 48 * κ ^ 2) with hKdef
  set cK : ℝ≥0∞ := ENNReal.ofReal (cap * K / (n₀ * H)) with hcK
  -- knowledge
  have hknow : ∀ b, ∀ p ∈ satSel γ j κ δ B c u Q R H F b,
      b ∈ satList γ j κ δ B c u Q R H (γ b) (obs (B (γ b)) δ p) := by
    intro b p hp
    obtain ⟨hpF, hpH⟩ := hp
    obtain ⟨_, hpA, hpt, hpfl⟩ := hF b p hpF
    obtain ⟨hbox, hval, hder, hcurv⟩ := hA b p.1 hpA p.2 hpt
    have hmem := obs_mem_chartCompat T ((j b : ℕ) : ℝ) hκ hδ (hB (γ b)) (c b) (u b) (Q b)
      (R b) (hR b) p hpt hbox hval hder hcurv hpfl
    unfold satList
    rw [if_pos (show (((compatCharts γ j κ δ B c u Q R (γ b) (obs (B (γ b)) δ p)).ncard : ℕ) : ℝ)
      ≤ H from hpH)]
    rw [Set.Finite.mem_toFinset]
    exact ⟨rfl, hmem⟩
  refine ⟨hknow, ?_⟩
  -- the retained sets
  set G : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun γ₁ =>
    {p | (((compatCharts γ j κ δ B c u Q R γ₁ (obs (B γ₁) δ p)).ncard : ℕ) : ℝ) ≤ H} with hG
  have hGm : ∀ γ₁, MeasurableSet (G γ₁) := fun γ₁ =>
    (measurable_obs (B γ₁) δ) (measurableSet_compatCharts_le γ j κ δ B c u Q R γ₁ hH.le)
  have hsat : ∀ b, satSel γ j κ δ B c u Q R H F b = F b ∩ G (γ b) := fun b => rfl
  set μ : Fin W → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun γ₁ =>
    ((ν γ₁).prod volume).restrict (E γ₁) with hμ
  -- removed mass of one chart
  have hsplit : ∀ b, ((ν (γ b)).prod volume) (F b) =
      ((ν (γ b)).prod volume) (satSel γ j κ δ B c u Q R H F b) +
        μ (γ b) (F b ∩ (G (γ b))ᶜ) := by
    intro b
    rw [hsat, ← measure_inter_add_diff (F b) (hGm (γ b))]
    congr 1
    rw [hμ]
    simp only
    rw [Measure.restrict_apply ((hFm b).inter (hGm (γ b)).compl), diff_eq]
    congr 1
    ext p
    simp only [mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2⟩, (hF b p h1).1⟩
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨h1, h2⟩
  -- per world: multiplicity two and the two exceptional sets
  have hworld : ∀ γ₁, ∑ b : {b : Fin C' // γ b = γ₁}, μ γ₁ (F b ∩ (G γ₁)ᶜ) ≤
      2 * (μ γ₁ {p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) δ p)} +
        cK * ∑ b : {b : Fin C' // γ b = γ₁}, ((ν γ₁).prod volume) (F b)) := by
    intro γ₁
    have hmult := selection_multiplicity_le_two γ j A F hdisj
      (fun b p hp => ⟨(hF b p hp).2.1, (hF b p hp).2.2.1⟩) γ₁
    have h2 := sum_measure_inter_le_two (μ γ₁) (fun b : {b : Fin C' // γ b = γ₁} => F b)
      (fun b => hFm b) hmult ((G γ₁)ᶜ) (hGm γ₁).compl
    refine h2.trans (mul_le_mul' le_rfl ?_)
    have hsub : (G γ₁)ᶜ ⊆ {p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) δ p)} ∪
        {p | g γ₁ (obs (B γ₁) δ p) ≤ ENNReal.ofReal cap ∧
          H < (((compatCharts γ j κ δ B c u Q R γ₁ (obs (B γ₁) δ p)).ncard : ℕ) : ℝ)} := by
      intro p hp
      simp only [hG, mem_compl_iff, mem_ofPred_eq, not_le] at hp
      by_cases hc : ENNReal.ofReal cap < g γ₁ (obs (B γ₁) δ p)
      · exact Or.inl hc
      · exact Or.inr ⟨not_lt.mp hc, hp⟩
    calc μ γ₁ (G γ₁)ᶜ ≤ μ γ₁ ({p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) δ p)} ∪
        {p | g γ₁ (obs (B γ₁) δ p) ≤ ENNReal.ofReal cap ∧
          H < (((compatCharts γ j κ δ B c u Q R γ₁ (obs (B γ₁) δ p)).ncard : ℕ) : ℝ)}) :=
          measure_mono hsub
      _ ≤ μ γ₁ {p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) δ p)} +
          μ γ₁ {p | g γ₁ (obs (B γ₁) δ p) ≤ ENNReal.ofReal cap ∧
            H < (((compatCharts γ j κ δ B c u Q R γ₁ (obs (B γ₁) δ p)).ncard : ℕ) : ℝ)} :=
          measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl (capped_crossing_le ν E B g γ j c u Q R F hB hδ hκ hn₀ hcap
          hH hgm hmap hQ hR hfloor γ₁)
  -- regroup by worlds
  have hfib : ∀ f : Fin W → Fin C' → ℝ≥0∞,
      ∑ b, f (γ b) b = ∑ γ₁, ∑ b : {b : Fin C' // γ b = γ₁}, f γ₁ b := by
    intro f
    rw [← Fintype.sum_fiberwise γ (fun b => f (γ b) b)]
    apply Finset.sum_congr rfl
    intro γ₁ _
    apply Finset.sum_congr rfl
    intro b _
    rw [b.2]
  have hrem : ∑ b, ENNReal.ofReal (ω (γ b)) * μ (γ b) (F b ∩ (G (γ b))ᶜ) ≤
      2 * θ + 2 * cK * ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b) := by
    rw [hfib (fun γ₁ b => ENNReal.ofReal (ω γ₁) * μ γ₁ (F b ∩ (G γ₁)ᶜ)),
      hfib (fun γ₁ b => ENNReal.ofReal (ω γ₁) * ((ν γ₁).prod volume) (F b))]
    calc ∑ γ₁, ∑ b : {b : Fin C' // γ b = γ₁}, ENNReal.ofReal (ω γ₁) * μ γ₁ (F b ∩ (G γ₁)ᶜ)
        = ∑ γ₁, ENNReal.ofReal (ω γ₁) * ∑ b : {b : Fin C' // γ b = γ₁}, μ γ₁ (F b ∩ (G γ₁)ᶜ) := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ γ₁, ENNReal.ofReal (ω γ₁) * (2 * (μ γ₁ {p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) δ p)} +
          cK * ∑ b : {b : Fin C' // γ b = γ₁}, ((ν γ₁).prod volume) (F b))) :=
          Finset.sum_le_sum (fun γ₁ _ => mul_le_mul' le_rfl (hworld γ₁))
      _ = 2 * ∑ γ₁, ENNReal.ofReal (ω γ₁) * μ γ₁ {p | ENNReal.ofReal cap < g γ₁ (obs (B γ₁) δ p)} +
          2 * cK * ∑ γ₁, ∑ b : {b : Fin C' // γ b = γ₁},
            ENNReal.ofReal (ω γ₁) * ((ν γ₁).prod volume) (F b) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro γ₁ _
          rw [← Finset.mul_sum]
          ring
      _ ≤ 2 * θ + 2 * cK * ∑ γ₁, ∑ b : {b : Fin C' // γ b = γ₁},
            ENNReal.ofReal (ω γ₁) * ((ν γ₁).prod volume) (F b) :=
          add_le_add (mul_le_mul' le_rfl htyp) le_rfl
  calc ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b)
      = ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (satSel γ j κ δ B c u Q R H F b) +
        ∑ b, ENNReal.ofReal (ω (γ b)) * μ (γ b) (F b ∩ (G (γ b))ᶜ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        rw [hsplit b, mul_add]
    _ ≤ _ := by
        rw [add_assoc]
        exact add_le_add le_rfl hrem

/-- The saturated selections keep a fixed polynomial format: one adds the
crossing-count atoms of `fmt_crossing` to the atoms of the old selection. -/
theorem satSel_fmt {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T)) {κ δ : ℝ}
    (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (H : ℝ) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hκ : 0 ≤ κ) (hδ : 0 < δ)
    (hB : ∀ γ₁, 0 < B γ₁) (hR : ∀ b, (R b).totalDegree ≤ 2) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (b : Fin C') (hbound : ∀ p ∈ F b, |(x p.1 p.2) 3| ≤ Λ) (i : ℕ) {H₁ : ℝ} {D₁ : ℕ}
    (hfmt : fmt 7 H₁ D₁ {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ F b}) :
    fmt 7 (H₁ + (2 + ((binCount Λ (B (γ b)) δ + 1) + binCount Λ (B (γ b)) δ * (C' * 6))))
      (max D₁ 4)
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈
        satSel γ j κ δ B c u Q R H F b} := by
  have hcross := fmt_crossing T hκ hδ (hB (γ b)) hΛ H (fun b' => γ b' = γ b)
    (fun b' => ((j b' : ℕ) : ℝ)) c u Q R hR
  have heq : {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈
        satSel γ j κ δ B c u Q R H F b} =
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ F b} ∩
        {z : Fin 7 → ℝ | |z 2 + z 6 * z 5| ≤ Λ ∧
          (({b' | γ b' = γ b ∧ obsZ (B (γ b)) δ z ∈ chartCompat T ((j b' : ℕ) : ℝ) κ δ
            (B (γ b)) (c b') (u b') (Q b') (R b')}.ncard : ℕ) : ℝ) ≤ H} := by
    ext z
    simp only [satSel, mem_inter_iff, mem_ofPred_eq, compatCharts, obs_eq_obsZ]
    constructor
    · rintro ⟨hF, hH⟩
      have hb := hbound _ hF
      simp only [x] at hb
      exact ⟨hF, hb, hH⟩
    · rintro ⟨hF, _, hH⟩
      exact ⟨hF, hH⟩
  rw [heq]
  exact Submission.Lib.K4RepresentativeAssembly.fmt_inter hfmt hcross

/-! ## Lists restricted to a hidden-coordinate range

For lists whose membership must itself be in polynomial format, restrict to the
hidden bins covering `[-Λ, Λ]`; the selections of `satSel` live there whenever
their hidden coordinates are bounded by `Λ`. -/

/-- The bin index `n` lies in the range covering hidden coordinates `[-Λ, Λ]`. -/
def inBinRange (Λ B δ : ℝ) (n : ℤ) : Prop :=
  ∃ k : Fin (binCount Λ B δ), n = binLow Λ B δ + (k : ℤ)

/-- The saturated lists, restricted to the bin range. -/
noncomputable def satListR {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    (κ δ : ℝ) (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (H Λ : ℝ) (γ₁ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Finset (Fin C') := by
  classical
  exact if inBinRange Λ (B γ₁) δ o.2 ∧
      (((compatCharts γ j κ δ B c u Q R γ₁ o).ncard : ℕ) : ℝ) ≤ H then
    (Set.toFinite (compatCharts γ j κ δ B c u Q R γ₁ o)).toFinset else ∅

theorem mem_satListR_iff {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    (κ δ : ℝ) (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (H Λ : ℝ) (γ₁ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) (b : Fin C') :
    b ∈ satListR γ j κ δ B c u Q R H Λ γ₁ o ↔
      inBinRange Λ (B γ₁) δ o.2 ∧
        (((compatCharts γ j κ δ B c u Q R γ₁ o).ncard : ℕ) : ℝ) ≤ H ∧
        b ∈ compatCharts γ j κ δ B c u Q R γ₁ o := by
  classical
  unfold satListR
  split_ifs with h
  · rw [Set.Finite.mem_toFinset]
    exact ⟨fun hb => ⟨h.1, h.2, hb⟩, fun hb => hb.2.2⟩
  · simp only [Finset.notMem_empty, false_iff]
    rintro ⟨h1, h2, _⟩
    exact h ⟨h1, h2⟩

theorem satListR_card_le {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    (κ δ : ℝ) (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    {H : ℝ} (hH : 0 ≤ H) (Λ : ℝ) (γ₁ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((satListR γ j κ δ B c u Q R H Λ γ₁ o).card : ℝ) ≤ H := by
  classical
  unfold satListR
  split_ifs with h
  · rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact h.2
  · simpa using hH

/-- Range-restricted lists know the saturated incidences with bounded hidden coordinate. -/
theorem mem_satListR_of_satSel {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    {κ δ : ℝ} (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (H : ℝ) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hδ : 0 < δ)
    (hB : ∀ γ₁, 0 < B γ₁) (b : Fin C') (p : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hp : p ∈ satSel γ j κ δ B c u Q R H F b)
    (hmem : obs (B (γ b)) δ p ∈ chartCompat T ((j b : ℕ) : ℝ) κ δ (B (γ b)) (c b) (u b) (Q b) (R b))
    (hx3 : |(x p.1 p.2) 3| ≤ Λ) :
    b ∈ satListR γ j κ δ B c u Q R H Λ (γ b) (obs (B (γ b)) δ p) := by
  rw [mem_satListR_iff]
  obtain ⟨k, hk⟩ := floor_mem_binRange hΛ (hB (γ b)) hδ hx3
  exact ⟨⟨k, hk⟩, hp.2, rfl, hmem⟩

/-- Membership in a range-restricted list has a fixed polynomial format in the
seven event coordinates. -/
theorem fmt_mem_satListR {W C' T : ℕ} (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    {κ δ : ℝ} (B : Fin W → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (H Λ : ℝ) (hκ : 0 ≤ κ) (hδ : 0 < δ) (hB : ∀ γ₁, 0 < B γ₁)
    (hR : ∀ b, (R b).totalDegree ≤ 2) (γ₁ : Fin W) (b₀ : Fin C') (i : ℕ) :
    fmt 7 ((binCount Λ (B γ₁) δ + 1) + binCount Λ (B γ₁) δ * (C' * 6)) 4
      {r : Fin 7 → ℝ | b₀ ∈ satListR γ j κ δ B c u Q R H Λ γ₁
        (obs (B γ₁) δ ((i, fun e : Fin 6 => r e.castSucc), r 6))} := by
  have h := fmt_binwise T hκ hδ (hB γ₁) (fun b => ((j b : ℕ) : ℝ)) c u Q R hR
    (Λ := Λ) (fun v => (({b | γ b = γ₁ ∧ v b}.ncard : ℕ) : ℝ) ≤ H ∧ γ b₀ = γ₁ ∧ v b₀)
  convert h using 1
  ext r
  simp only [mem_ofPred_eq, mem_satListR_iff, obs_eq_obsZ, compatCharts, inBinRange]
  constructor
  · rintro ⟨⟨k, hk⟩, hH, hγ, hc⟩
    exact ⟨k, hk, hH, hγ, hc⟩
  · rintro ⟨k, hk, hH, hγ, hc⟩
    exact ⟨⟨k, hk⟩, hH, hγ, hc⟩

/-- Membership in a range-restricted list is a measurable condition on incidences. -/
theorem measurableSet_mem_satListR {W C' T : ℕ} (γ : Fin C' → Fin W)
    (j : Fin C' → Fin (2 ^ T)) (κ δ : ℝ) (B : Fin W → ℝ)
    (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C' → MvPolynomial (Fin 4) ℝ) {H : ℝ} (hH : 0 ≤ H) (Λ : ℝ) (γ₁ : Fin W)
    (b₀ : Fin C') :
    MeasurableSet {p : (ℕ × (Fin 6 → ℝ)) × ℝ |
      b₀ ∈ satListR γ j κ δ B c u Q R H Λ γ₁ (obs (B γ₁) δ p)} := by
  have hset : {o : EuclideanSpace ℝ (Fin 3) × ℤ | b₀ ∈ satListR γ j κ δ B c u Q R H Λ γ₁ o} =
      (Prod.snd ⁻¹' {n | inBinRange Λ (B γ₁) δ n}) ∩
        ({o | (((compatCharts γ j κ δ B c u Q R γ₁ o).ncard : ℕ) : ℝ) ≤ H} ∩
          {o | b₀ ∈ compatCharts γ j κ δ B c u Q R γ₁ o}) := by
    ext o
    simp only [mem_ofPred_eq, mem_satListR_iff, mem_inter_iff, mem_preimage]
  have hm : MeasurableSet {o : EuclideanSpace ℝ (Fin 3) × ℤ |
      b₀ ∈ satListR γ j κ δ B c u Q R H Λ γ₁ o} := by
    rw [hset]
    refine (measurable_snd (MeasurableSet.of_discrete)).inter
      ((measurableSet_compatCharts_le γ j κ δ B c u Q R γ₁ hH).inter ?_)
    by_cases hb : γ b₀ = γ₁
    · have : {o : EuclideanSpace ℝ (Fin 3) × ℤ | b₀ ∈ compatCharts γ j κ δ B c u Q R γ₁ o} =
          chartCompat T ((j b₀ : ℕ) : ℝ) κ δ (B γ₁) (c b₀) (u b₀) (Q b₀) (R b₀) := by
        ext o
        simp [compatCharts, hb]
      rw [this]
      exact measurableSet_chartCompat _ _ _ _ _ _ _ _ _
    · have : {o : EuclideanSpace ℝ (Fin 3) × ℤ | b₀ ∈ compatCharts γ j κ δ B c u Q R γ₁ o} =
          ∅ := by
        ext o
        simp [compatCharts, hb]
      rw [this]
      exact MeasurableSet.empty
  exact (measurable_obs (B γ₁) δ) hm

end Submission.Obl.k4_terminal_label_saturation
