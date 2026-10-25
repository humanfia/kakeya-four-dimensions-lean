import Submission.Obl.k4_scalar_conditional_crop_worlds.Definitions

/-!
# Geometry of one scalar crop

The scalar crop of label `z` at scale `a = N ^ (-u₀)` rescales the intercept and velocity
coordinates by `a⁻¹` and recentres them at `z`; the other coordinates are unchanged. It is an
affine homeomorphism, so the conditional law of a crop is computed by a change of variables.
This file proves the per-crop facts of `LiftFacts`.
-/

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

open MeasureTheory Set

noncomputable section

/-- The crop of a coefficient vector at scale `a` and label `z`. -/
def cropCoeff (a : ℝ) (z : Label) (c : Coeff) : Coeff :=
  ![c 0 / a - (z 0 : ℝ), c 1 / a - (z 1 : ℝ), c 2, c 3, c 4]

/-- The inverse of `cropCoeff a z`. -/
def uncropCoeff (a : ℝ) (z : Label) (c : Coeff) : Coeff :=
  ![(c 0 + (z 0 : ℝ)) * a, (c 1 + (z 1 : ℝ)) * a, c 2, c 3, c 4]

lemma scalarCropLine_eq (N u₀ : ℝ) (z : Label) (l : Line) :
    scalarCropLine N u₀ z l = (l.1, cropCoeff (N ^ (-u₀)) z l.2) := rfl

lemma scalarCropPoint_eq (N u₀ : ℝ) (z : Label) (q : State) :
    scalarCropPoint N u₀ z q = ((q.1.1, cropCoeff (N ^ (-u₀)) z q.1.2), q.2) := rfl

lemma uncrop_cropCoeff {a : ℝ} (ha : a ≠ 0) (z : Label) (c : Coeff) :
    uncropCoeff a z (cropCoeff a z c) = c := by
  ext i
  fin_cases i <;> simp [cropCoeff, uncropCoeff] <;> field_simp

lemma crop_uncropCoeff {a : ℝ} (ha : a ≠ 0) (z : Label) (c : Coeff) :
    cropCoeff a z (uncropCoeff a z c) = c := by
  ext i
  fin_cases i <;> simp [cropCoeff, uncropCoeff, ha]

lemma continuous_cropCoeff (a : ℝ) (z : Label) : Continuous (cropCoeff a z) := by
  unfold cropCoeff
  fun_prop

lemma continuous_uncropCoeff (a : ℝ) (z : Label) : Continuous (uncropCoeff a z) := by
  unfold uncropCoeff
  fun_prop

/-- The crop of coefficients as a homeomorphism. -/
def coeffHomeomorph {a : ℝ} (ha : a ≠ 0) (z : Label) : Coeff ≃ₜ Coeff where
  toFun := cropCoeff a z
  invFun := uncropCoeff a z
  left_inv := uncrop_cropCoeff ha z
  right_inv := crop_uncropCoeff ha z
  continuous_toFun := continuous_cropCoeff a z
  continuous_invFun := continuous_uncropCoeff a z

/-- The crop of lines as a homeomorphism. -/
def lineHomeomorph {a : ℝ} (ha : a ≠ 0) (z : Label) : Line ≃ₜ Line :=
  Homeomorph.prodCongr (Homeomorph.refl ℕ) (coeffHomeomorph ha z)

/-- The crop of incidences as a homeomorphism. -/
def pointHomeomorph {a : ℝ} (ha : a ≠ 0) (z : Label) : State ≃ₜ State :=
  Homeomorph.prodCongr (lineHomeomorph ha z) (Homeomorph.refl ℝ)

lemma scale_pos {N : ℝ} (hN : 0 < N) (u₀ : ℝ) : 0 < N ^ (-u₀) :=
  Real.rpow_pos_of_pos hN _

lemma scale_ne_zero {N : ℝ} (hN : 0 < N) (u₀ : ℝ) : N ^ (-u₀) ≠ 0 :=
  (scale_pos hN u₀).ne'

lemma lineHomeomorph_apply {N : ℝ} (hN : 0 < N) (u₀ : ℝ) (z : Label) :
    ⇑(lineHomeomorph (scale_ne_zero hN u₀) z) = scalarCropLine N u₀ z := rfl

lemma pointHomeomorph_apply {N : ℝ} (hN : 0 < N) (u₀ : ℝ) (z : Label) :
    ⇑(pointHomeomorph (scale_ne_zero hN u₀) z) = scalarCropPoint N u₀ z := rfl

lemma continuous_scalarCropLine (N u₀ : ℝ) (z : Label) :
    Continuous (scalarCropLine N u₀ z) :=
  continuous_fst.prodMk ((continuous_cropCoeff _ z).comp continuous_snd)

lemma measurable_scalarCropLine (N u₀ : ℝ) (z : Label) :
    Measurable (scalarCropLine N u₀ z) :=
  (continuous_scalarCropLine N u₀ z).measurable

lemma continuous_scalarCropPoint (N u₀ : ℝ) (z : Label) :
    Continuous (scalarCropPoint N u₀ z) :=
  ((continuous_scalarCropLine N u₀ z).comp continuous_fst).prodMk continuous_snd

lemma measurable_scalarCropPoint (N u₀ : ℝ) (z : Label) :
    Measurable (scalarCropPoint N u₀ z) :=
  (continuous_scalarCropPoint N u₀ z).measurable

lemma scalarCropLine_injective {N : ℝ} (hN : 0 < N) (u₀ : ℝ) (z : Label) :
    Function.Injective (scalarCropLine N u₀ z) :=
  (lineHomeomorph (scale_ne_zero hN u₀) z).injective

lemma scalarCropPoint_injective {N : ℝ} (hN : 0 < N) (u₀ : ℝ) (z : Label) :
    Function.Injective (scalarCropPoint N u₀ z) :=
  (pointHomeomorph (scale_ne_zero hN u₀) z).injective

lemma measurableSet_scalarCell (N u₀ : ℝ) (z : Label) :
    MeasurableSet (scalarCell N u₀ z) := by
  have h0 : Measurable fun l : Line => ⌊l.2 0 / N ^ (-u₀)⌋ :=
    Int.measurable_floor.comp (by fun_prop)
  have h1 : Measurable fun l : Line => ⌊l.2 1 / N ^ (-u₀)⌋ :=
    Int.measurable_floor.comp (by fun_prop)
  exact (measurableSet_eq_fun h0 measurable_const).inter
    (measurableSet_eq_fun h1 measurable_const)

lemma scalarCell_disjoint {N u₀ : ℝ} {z z' : Label} (h : z ≠ z') :
    Disjoint (scalarCell N u₀ z) (scalarCell N u₀ z') := by
  rw [Set.disjoint_left]
  rintro l ⟨h0, h1⟩ ⟨h0', h1'⟩
  apply h
  ext i
  fin_cases i
  · exact h0.symm.trans h0'
  · exact h1.symm.trans h1'

/-- The normalized intercept and velocity of a line of the cell lie in `[0, 1)`. -/
lemma cropCoeff_mem_Ico {N u₀ : ℝ} {z : Label} {l : Line}
    (hl : l ∈ scalarCell N u₀ z) :
    cropCoeff (N ^ (-u₀)) z l.2 0 ∈ Ico (0 : ℝ) 1 ∧
      cropCoeff (N ^ (-u₀)) z l.2 1 ∈ Ico (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hl
  have e0 := Int.floor_eq_iff.mp h0
  have e1 := Int.floor_eq_iff.mp h1
  simp only [cropCoeff, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨⟨by linarith [e0.1], by linarith [e0.2]⟩, ⟨by linarith [e1.1], by linarith [e1.2]⟩⟩

/-- A crop line lies in the cell iff its normalized intercept and velocity lie in `[0, 1)`. -/
lemma uncrop_mem_scalarCell_iff {N u₀ : ℝ} (hN : 0 < N) (z : Label) (i : ℕ) (c : Coeff) :
    (i, uncropCoeff (N ^ (-u₀)) z c) ∈ scalarCell N u₀ z ↔
      c 0 ∈ Ico (0 : ℝ) 1 ∧ c 1 ∈ Ico (0 : ℝ) 1 := by
  have ha := scale_ne_zero hN u₀
  have key : ∀ (v : ℝ) (n : ℤ), ⌊(v + (n : ℝ)) * N ^ (-u₀) / N ^ (-u₀)⌋ = n ↔
      v ∈ Ico (0 : ℝ) 1 := by
    intro v n
    rw [mul_div_assoc, div_self ha, mul_one, Int.floor_eq_iff, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  change ⌊uncropCoeff (N ^ (-u₀)) z c 0 / N ^ (-u₀)⌋ = z 0 ∧
      ⌊uncropCoeff (N ^ (-u₀)) z c 1 / N ^ (-u₀)⌋ = z 1 ↔ _
  simp only [uncropCoeff, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [key, key]

/-- The cropped event of a crop, as a preimage under the uncropping. -/
lemma mem_cropEvent_iff {N u₀ : ℝ} (hN : 0 < N) (z : Label) (E₀ : Set State) (q : State) :
    q ∈ scalarCropPoint N u₀ z '' (E₀ ∩ (scalarCell N u₀ z ×ˢ univ)) ↔
      ((q.1.1, uncropCoeff (N ^ (-u₀)) z q.1.2), q.2) ∈ E₀ ∧
        q.1.2 0 ∈ Ico (0 : ℝ) 1 ∧ q.1.2 1 ∈ Ico (0 : ℝ) 1 := by
  have ha := scale_ne_zero hN u₀
  constructor
  · rintro ⟨a, ⟨haE, hac, -⟩, rfl⟩
    rw [scalarCropPoint_eq]
    simp only [uncrop_cropCoeff ha]
    refine ⟨haE, ?_⟩
    exact cropCoeff_mem_Ico hac
  · rintro ⟨hE, h0, h1⟩
    refine ⟨((q.1.1, uncropCoeff (N ^ (-u₀)) z q.1.2), q.2), ⟨hE, ?_, mem_univ _⟩, ?_⟩
    · exact (uncrop_mem_scalarCell_iff hN z q.1.1 q.1.2).2 ⟨h0, h1⟩
    · rw [scalarCropPoint_eq]
      simp only [crop_uncropCoeff ha]

lemma measurableSet_cropEvent {N u₀ : ℝ} (hN : 0 < N) (z : Label) {E₀ : Set State}
    (hE₀ : MeasurableSet E₀) :
    MeasurableSet (scalarCropPoint N u₀ z '' (E₀ ∩ (scalarCell N u₀ z ×ˢ univ))) := by
  rw [← pointHomeomorph_apply hN u₀ z]
  exact (pointHomeomorph (scale_ne_zero hN u₀) z).toMeasurableEquiv.measurableSet_image.2
    (hE₀.inter ((measurableSet_scalarCell N u₀ z).prod MeasurableSet.univ))

lemma cropEvent_subset {N u₀ : ℝ} (z : Label) {E₀ : Set State}
    (hE₀ : E₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    scalarCropPoint N u₀ z '' (E₀ ∩ (scalarCell N u₀ z ×ˢ univ)) ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨mem_univ _, (hE₀ ha.1).2⟩

lemma cropEvent_index {N u₀ R : ℝ} (z : Label) {E₀ : Set State}
    (hE₀ : ∀ q ∈ E₀, (q.1.1 : ℝ) ≤ R) :
    ∀ q ∈ scalarCropPoint N u₀ z '' (E₀ ∩ (scalarCell N u₀ z ×ˢ univ)), (q.1.1 : ℝ) ≤ R := by
  rintro _ ⟨a, ha, rfl⟩
  exact hE₀ a ha.1

/-- The `x`-trajectory is unchanged by a crop. -/
lemma x_scalarCropLine (N u₀ : ℝ) (z : Label) (l : Line) (t : ℝ) :
    x (scalarCropLine N u₀ z l) t = x l t := rfl

/-- The `y`-trajectory of a crop is the normalized affine residual. -/
lemma y_scalarCropLine {N : ℝ} (hN : 0 < N) (u₀ : ℝ) (z : Label) (l : Line) (t : ℝ) :
    y (scalarCropLine N u₀ z l) t =
      (y l t - N ^ (-u₀) * (z 0 : ℝ) - t * (N ^ (-u₀) * (z 1 : ℝ))) / N ^ (-u₀) := by
  have ha := scale_ne_zero hN u₀
  change (l.2 0 / N ^ (-u₀) - (z 0 : ℝ)) + t * (l.2 1 / N ^ (-u₀) - (z 1 : ℝ)) =
    (l.2 0 + t * l.2 1 - N ^ (-u₀) * (z 0 : ℝ) - t * (N ^ (-u₀) * (z 1 : ℝ))) / N ^ (-u₀)
  field_simp
  ring

/-- The normalized `y`-trajectory of a crop line is bounded by `2` on `[0, 1]`. -/
lemma abs_y_scalarCropLine_le {N u₀ : ℝ} {z : Label} {l : Line}
    (hl : l ∈ scalarCell N u₀ z) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |y (scalarCropLine N u₀ z l) t| ≤ 2 := by
  obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩⟩ := cropCoeff_mem_Ico hl
  change |cropCoeff (N ^ (-u₀)) z l.2 0 + t * cropCoeff (N ^ (-u₀)) z l.2 1| ≤ 2
  obtain ⟨ht0, ht1⟩ := ht
  have hm : 0 ≤ t * cropCoeff (N ^ (-u₀)) z l.2 1 := mul_nonneg ht0 h1
  have hm' : t * cropCoeff (N ^ (-u₀)) z l.2 1 ≤ 1 := by
    calc t * cropCoeff (N ^ (-u₀)) z l.2 1 ≤ 1 * 1 :=
          mul_le_mul ht1 h1'.le h1 zero_le_one
      _ = 1 := one_mul 1
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- The product of the pushforward of the cell restriction is the pushforward of the product. -/
lemma map_crop_prod (N u₀ : ℝ) (z : Label) (ν₀ : Measure Line) [SFinite ν₀] :
    (Measure.map (scalarCropLine N u₀ z) (ν₀.restrict (scalarCell N u₀ z))).prod
        (volume : Measure ℝ) =
      Measure.map (scalarCropPoint N u₀ z) ((ν₀.restrict (scalarCell N u₀ z)).prod volume) := by
  have h := Measure.map_prod_map (ν₀.restrict (scalarCell N u₀ z)) (volume : Measure ℝ)
    (measurable_scalarCropLine N u₀ z) (measurable_id : Measurable (id : ℝ → ℝ))
  rw [Measure.map_id] at h
  exact h

/-- The exact conditional-law identity of one crop (the fourth fact of `LiftFacts`). -/
theorem selected_crop_eq {N : ℝ} (hN : 0 < N) (u₀ : ℝ) (z : Label) (ν₀ : Measure Line)
    [SFinite ν₀] {E₀ : Set State} (hE₀ : MeasurableSet E₀) {p : ℝ} (hp : 0 < p)
    {Z : Set State} (hZ : MeasurableSet Z) :
    ENNReal.ofReal p * selected ((ENNReal.ofReal p)⁻¹ •
        Measure.map (scalarCropLine N u₀ z) (ν₀.restrict (scalarCell N u₀ z)))
        (scalarCropPoint N u₀ z '' (E₀ ∩ (scalarCell N u₀ z ×ˢ univ))) Z =
      selected ν₀ E₀ {a | a.1 ∈ scalarCell N u₀ z ∧ (scalarCropLine N u₀ z a.1, a.2) ∈ Z} := by
  have hcell := measurableSet_scalarCell N u₀ z
  have hEz := measurableSet_cropEvent (u₀ := u₀) hN z hE₀
  have hpne : ENNReal.ofReal p ≠ 0 := by positivity
  change ENNReal.ofReal p * ((((ENNReal.ofReal p)⁻¹ •
      Measure.map (scalarCropLine N u₀ z) (ν₀.restrict (scalarCell N u₀ z))).prod volume).restrict
        (scalarCropPoint N u₀ z '' (E₀ ∩ (scalarCell N u₀ z ×ˢ univ)))) Z =
    ((ν₀.prod volume).restrict E₀) {a | a.1 ∈ scalarCell N u₀ z ∧
      (scalarCropLine N u₀ z a.1, a.2) ∈ Z}
  rw [Measure.prod_smul_left, Measure.restrict_smul, Measure.smul_apply, smul_eq_mul,
    ← mul_assoc, ENNReal.mul_inv_cancel hpne ENNReal.ofReal_ne_top, one_mul,
    map_crop_prod, Measure.restrict_apply hZ,
    Measure.map_apply (measurable_scalarCropPoint N u₀ z) (hZ.inter hEz),
    Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply ((measurable_scalarCropPoint N u₀ z) (hZ.inter hEz)),
    Measure.restrict_apply' hE₀]
  congr 1
  ext a
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq]
  have hinj := scalarCropPoint_injective hN u₀ z
  constructor
  · rintro ⟨⟨hZa, ⟨b, ⟨hbE, hbc, -⟩, hb⟩⟩, hac⟩
    have := hinj hb
    subst this
    exact ⟨⟨hac, hZa⟩, hbE⟩
  · rintro ⟨⟨hac, hZa⟩, haE⟩
    exact ⟨⟨hZa, a, ⟨haE, hac, mem_univ _⟩, rfl⟩, hac⟩

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
