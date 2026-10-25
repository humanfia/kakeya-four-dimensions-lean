import Submission.Lib.K4ModelReduction.SupportedAveraging

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Bounded support and finite rectangular table complexity. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Set
open scoped ENNReal

def supportedInCube {ι : Type*} (f : (ι → ℝ) → ℝ) (R : ℝ) : Prop :=
  ∀ x i, R < |x i| → f x = 0

theorem coordinateAverage_support {n : ℕ} (i : Fin (n + 1)) (M R : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : supportedInCube f.val R) :
    supportedInCube (coordinateAverage i M hρ f).val (R + ρ) := by
  intro x j hj
  rw [coordinateAverage_eq]
  apply meshAverage_eq_of_constant _ hρ (x i) 0
  intro t ht
  by_cases hji : j = i
  · subst j
    have hdist : |x i - t| ≤ ρ := by
      have h := Real.dist_le_of_mem_Icc (mem_meshCell hρ (x i)) ht
      simpa only [Real.dist_eq, add_sub_cancel_left] using h
    have htri := abs_sub_le (x i) t 0
    have htR : R < |t| := by
      simp only [sub_zero] at htri
      linarith
    exact hf _ i (by simpa only [Function.update_self] using htR)
  · exact hf _ j (by
      simpa only [Function.update_of_ne hji] using (by linarith : R < |x j|))

theorem coordinate_averaging_support {n : ℕ} (M R : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : supportedInCube f.val R) :
    supportedInCube (L.foldr (fun i g => coordinateAverage i M hρ g) f).val
      (R + (L.length : ℝ) * ρ) := by
  induction L with
  | nil => simpa only [List.foldr_nil, List.length_nil, Nat.cast_zero, zero_mul, add_zero] using hf
  | cons i L ih =>
    have h := coordinateAverage_support i M (R + (L.length : ℝ) * ρ) hρ _ ih
    have hr : R + ((L.length + 1 : ℕ) : ℝ) * ρ = R + (L.length : ℝ) * ρ + ρ := by
      push_cast
      ring
    simpa only [List.foldr_cons, List.length_cons, hr] using h

noncomputable def meshTag {ι : Type*} (ρ : ℝ) (x : ι → ℝ) : ι → ℤ := fun i => ⌊x i / ρ⌋

def meshRepresentative {ι : Type*} (ρ : ℝ) (c : ι → ℤ) : ι → ℝ := fun i => ρ * (c i : ℝ)

theorem meshTag_representative {ι : Type*} {ρ : ℝ} (hρ : 0 < ρ) (c : ι → ℤ) :
    meshTag ρ (meshRepresentative ρ c) = c := by
  funext i
  simp only [meshTag, meshRepresentative]
  have heq : ρ * (c i : ℝ) / ρ = (c i : ℝ) := by field_simp [hρ.ne']
  rw [heq, Int.floor_intCast]

noncomputable def meshCodes (ι : Type*) [Fintype ι] (ρ R : ℝ) : Finset (ι → ℤ) := by
  classical
  exact Fintype.piFinset fun _ => Finset.Icc ⌊-R / ρ⌋ ⌊R / ρ⌋

theorem meshTag_mem_codes {ι : Type*} [Fintype ι] {ρ R : ℝ} (hρ : 0 < ρ)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ R) : meshTag ρ x ∈ meshCodes ι ρ R := by
  classical
  rw [meshCodes, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hx i)).1 hρ.le),
    Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hx i)).2 hρ.le)⟩

theorem meshCodes_card {ι : Type*} [Fintype ι] (ρ R : ℝ) :
    (meshCodes ι ρ R).card = (⌊R / ρ⌋ + 1 - ⌊-R / ρ⌋).toNat ^ Fintype.card ι := by
  classical
  simp only [meshCodes, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const,
    Finset.card_univ]

theorem meshTag_eq_iff {ι : Type*} {ρ : ℝ} (hρ : 0 < ρ) (x : ι → ℝ) (c : ι → ℤ) :
    meshTag ρ x = c ↔ ∀ i, ρ * (c i : ℝ) ≤ x i ∧ x i < ρ * ((c i : ℝ) + 1) := by
  rw [funext_iff]
  apply forall_congr'
  intro i
  rw [meshTag, Int.floor_eq_iff, le_div_iff₀ hρ, div_lt_iff₀ hρ]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

theorem meshTag_measurable {ι : Type*} (ρ : ℝ) :
    Measurable (meshTag ρ : (ι → ℝ) → (ι → ℤ)) := by
  apply Measurable.of_eval
  intro i
  change Measurable (fun x : ι → ℝ => ⌊x i / ρ⌋)
  fun_prop

theorem measurableSet_meshTag {ι : Type*} [Countable ι] (ρ : ℝ) (c : ι → ℤ) :
    MeasurableSet {x : ι → ℝ | meshTag ρ x = c} :=
  (measurableSet_singleton c).preimage (meshTag_measurable ρ)

/-- A compactly supported function constant on rectangular cells is an
actual finite table, with coefficients given by its values at cell corners. -/
theorem finite_mesh_table {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (R : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hsupport : supportedInCube f R)
    (hconst : ∀ x y, (∀ i, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → f x = f y)
    (x : ι → ℝ) :
    f x = ∑ c ∈ meshCodes ι ρ R,
      if meshTag ρ x = c then f (meshRepresentative ρ c) else 0 := by
  classical
  have hvalue : f x = f (meshRepresentative ρ (meshTag ρ x)) := by
    apply hconst
    intro i
    change (meshTag ρ x) i = (meshTag ρ (meshRepresentative ρ (meshTag ρ x))) i
    rw [meshTag_representative hρ]
  by_cases hx : meshTag ρ x ∈ meshCodes ι ρ R
  · rw [Finset.sum_eq_single_of_mem (meshTag ρ x) hx]
    · simpa only [ite_true] using hvalue
    · intro c _ hc
      exact ite_eq_right (Ne.symm hc)
  · have hzero : f x = 0 := by
      by_contra h
      apply hx
      apply meshTag_mem_codes hρ
      intro i
      exact le_of_not_gt fun hi => h (hsupport x i hi)
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro c hc
    apply ite_eq_right
    intro heq
    exact hx (heq.symm ▸ hc)

theorem meshCodes_card_le {ι : Type*} [Fintype ι]
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R) :
    ((meshCodes ι ρ R).card : ℝ) ≤ (2 * R / ρ + 2) ^ Fintype.card ι := by
  have hinterval : ⌊-R / ρ⌋ ≤ ⌊R / ρ⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith : -R ≤ R) hρ.le)
  have hnonneg : 0 ≤ ⌊R / ρ⌋ + 1 - ⌊-R / ρ⌋ := by omega
  have hcast : (((⌊R / ρ⌋ + 1 - ⌊-R / ρ⌋).toNat : ℕ) : ℝ) =
      (⌊R / ρ⌋ : ℝ) + 1 - (⌊-R / ρ⌋ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have hwidth : (((⌊R / ρ⌋ + 1 - ⌊-R / ρ⌋).toNat : ℕ) : ℝ) ≤ 2 * R / ρ + 2 := by
    rw [hcast]
    have ha := Int.floor_le (R / ρ)
    have hb := Int.lt_floor_add_one (-R / ρ)
    rw [neg_div] at hb
    simp only [neg_div, mul_div_assoc]
    linarith
  rw [meshCodes_card, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hwidth _

/-- The measure of a nonnegative finite mesh table is a finite sum of
weighted restrictions to the actual rectangular cells. -/
theorem finite_mesh_table_withDensity {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (f : (ι → ℝ) → ℝ) (R : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : supportedInCube f R)
    (hconst : ∀ x y, (∀ i, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → f x = f y) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) =
      ∑ c ∈ meshCodes ι ρ R,
        ENNReal.ofReal (f (meshRepresentative ρ c)) • μ.restrict {x | meshTag ρ x = c} := by
  classical
  let G (c : ι → ℤ) : (ι → ℝ) → ℝ≥0∞ :=
    {x | meshTag ρ x = c}.indicator (fun _ => ENNReal.ofReal (f (meshRepresentative ρ c)))
  have hG (c : ι → ℤ) : Measurable (G c) :=
    measurable_const.indicator (measurableSet_meshTag ρ c)
  have hden (x : ι → ℝ) : ENNReal.ofReal (f x) = ∑ c ∈ meshCodes ι ρ R, G c x := by
    rw [finite_mesh_table f R hρ hsupport hconst x,
      ENNReal.ofReal_sum_of_nonneg (fun c _ => by
        split_ifs
        · exact hf _
        · exact le_rfl)]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : meshTag ρ x = c <;> simp [G, h]
  apply Measure.ext
  intro A hA
  rw [withDensity_apply _ hA, Measure.finsetSum_apply]
  rw [show (fun x => ENNReal.ofReal (f x)) =
    (fun x => ∑ c ∈ meshCodes ι ρ R, G c x) from funext hden]
  rw [lintegral_finsetSum _ (fun c _ => hG c)]
  apply Finset.sum_congr rfl
  intro c _
  rw [show G c = {x | meshTag ρ x = c}.indicator
      (fun _ => ENNReal.ofReal (f (meshRepresentative ρ c))) from rfl,
    lintegral_indicator_const (measurableSet_meshTag ρ c),
    Measure.restrict_apply (measurableSet_meshTag ρ c),
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA, inter_comm]

theorem coordinate_averaging_finite_table {n : ℕ} (M R : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (hL : ∀ i, i ∈ L)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : supportedInCube f.val R) (x : Fin (n + 1) → ℝ) :
    (L.foldr (fun i g => coordinateAverage i M hρ g) f).val x =
      ∑ c ∈ meshCodes (Fin (n + 1)) ρ (R + (L.length : ℝ) * ρ),
        if meshTag ρ x = c then
          (L.foldr (fun i g => coordinateAverage i M hρ g) f).val (meshRepresentative ρ c)
        else 0 :=
  finite_mesh_table _ _ hρ (coordinate_averaging_support M R hρ L f hf)
    (coordinate_averaging_same_cell M hρ L hL f) x

theorem coordinate_averaging_withDensity {n : ℕ}
    (μ : Measure (Fin (n + 1) → ℝ)) (M R : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (hL : ∀ i, i ∈ L)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : ∀ x, 0 ≤ f.val x) (hsupport : supportedInCube f.val R) :
    μ.withDensity (fun x => ENNReal.ofReal
      ((L.foldr (fun i g => coordinateAverage i M hρ g) f).val x)) =
      ∑ c ∈ meshCodes (Fin (n + 1)) ρ (R + (L.length : ℝ) * ρ),
        ENNReal.ofReal ((L.foldr (fun i g => coordinateAverage i M hρ g) f).val
          (meshRepresentative ρ c)) • μ.restrict {x | meshTag ρ x = c} :=
  finite_mesh_table_withDensity μ _ _ hρ (coordinate_averaging_nonneg M hρ L f hf)
    (coordinate_averaging_support M R hρ L f hsupport)
    (coordinate_averaging_same_cell M hρ L hL f)

theorem averaging_meshCodes_card_le {ι : Type*} [Fintype ι]
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R) (k : ℕ) :
    ((meshCodes ι ρ (R + (k : ℝ) * ρ)).card : ℝ) ≤
      (2 * R / ρ + 2 * (k : ℝ) + 2) ^ Fintype.card ι := by
  have h := meshCodes_card_le (ι := ι) hρ (by positivity : 0 ≤ R + (k : ℝ) * ρ)
  have heq : 2 * (R + (k : ℝ) * ρ) / ρ + 2 = 2 * R / ρ + 2 * (k : ℝ) + 2 := by
    field_simp
  simpa only [heq] using h

end Submission.Lib.K4ModelReduction
