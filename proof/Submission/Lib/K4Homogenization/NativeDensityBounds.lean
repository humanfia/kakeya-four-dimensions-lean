/-
Adapted from: here:o018
Written by x0048 in the o018 desk.
-/
import Submission.Lib.K4Homogenization.ObservationBounds

/-! Uniform native observation ceilings for bounded coefficient-volume pieces. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4Homogenization

/-- Split the first two intercepts from the remaining intercept and three slopes. -/
noncomputable def nativeCoefficientSplit :
    (Fin 6 → ℝ) ≃ᵐ ((Fin 2 → ℝ) × (Fin 4 → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Fin 4 => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 4 => ℝ))

theorem nativeCoefficientSplit_fst (x : Fin 6 → ℝ) (i : Fin 2) :
    (nativeCoefficientSplit x).1 i = x (Fin.castAdd 4 i) := by
  simp [nativeCoefficientSplit, MeasurableEquiv.coe_sumPiEquivProdPi,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]
  rfl

theorem nativeCoefficientSplit_snd (x : Fin 6 → ℝ) (i : Fin 4) :
    (nativeCoefficientSplit x).2 i = x (Fin.natAdd 2 i) := by
  simp [nativeCoefficientSplit, MeasurableEquiv.coe_sumPiEquivProdPi,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]
  rfl

theorem measurePreserving_nativeCoefficientSplit :
    MeasurePreserving nativeCoefficientSplit volume (volume.prod volume) := by
  exact (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 4 => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin 2 ⊕ Fin 4 => ℝ) finSumFinEquiv.symm)

noncomputable def nativeCoefficientTimeSplit :
    ((Fin 6 → ℝ) × ℝ) ≃ᵐ ((ℝ × (Fin 2 → ℝ)) × (Fin 4 → ℝ)) :=
  (MeasurableEquiv.prodComm.trans
    ((MeasurableEquiv.refl ℝ).prodCongr nativeCoefficientSplit)).trans
      MeasurableEquiv.prodAssoc.symm

theorem measurePreserving_nativeCoefficientTimeSplit :
    MeasurePreserving nativeCoefficientTimeSplit
      ((volume : Measure (Fin 6 → ℝ)).prod volume)
      (((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))).prod volume) := by
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc volume volume volume)).comp
      (((MeasurePreserving.id (volume : Measure ℝ)).prod
        measurePreserving_nativeCoefficientSplit).comp Measure.measurePreserving_swap)

noncomputable def nativeBaseCoordinates :
    (ℝ × (Fin 2 → ℝ)) ≃ᵐ EuclideanSpace ℝ (Fin 3) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm.trans
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

theorem measurePreserving_nativeBaseCoordinates :
    MeasurePreserving nativeBaseCoordinates
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) volume := by
  exact (PiLp.volume_preserving_toLp (Fin 3)).comp
    (MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0))

theorem nativeBaseCoordinates_apply (t : ℝ) (y : Fin 2 → ℝ) :
    nativeBaseCoordinates (t, y) = WithLp.toLp 2 ![t, y 0, y 1] := by
  ext i
  fin_cases i <;> rfl

def nativeFiberBox (R : ℝ) : Set (Fin 4 → ℝ) := Icc (fun _ => -R) (fun _ => R)

theorem volume_nativeFiberBox (R : ℝ) :
    volume (nativeFiberBox R) = ENNReal.ofReal (2 * R) ^ 4 := by
  simp only [nativeFiberBox, Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A bounded coefficient support becomes a uniformly bounded four-coordinate fiber.
The observed time and first two intercepts retain ordinary Lebesgue measure. -/
theorem native_component_source_le (A : Set (Fin 6 → ℝ)) (R : ℝ)
    (hA : ∀ x ∈ A, ∀ i, |x i| ≤ R) :
    (((volume.restrict A).prod (volume : Measure ℝ)).map nativeCoefficientTimeSplit) ≤
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))).prod
        (volume.restrict (nativeFiberBox R)) := by
  let B : Set ((ℝ × (Fin 2 → ℝ)) × (Fin 4 → ℝ)) := univ ×ˢ nativeFiberBox R
  have hsub : A ×ˢ (univ : Set ℝ) ⊆ nativeCoefficientTimeSplit ⁻¹' B := by
    intro p hp
    refine ⟨mem_univ _, ?_⟩
    change (fun _ : Fin 4 => -R) ≤ (nativeCoefficientSplit p.1).2 ∧
      (nativeCoefficientSplit p.1).2 ≤ (fun _ => R)
    constructor <;> intro i
    · rw [nativeCoefficientSplit_snd]
      exact (abs_le.mp (hA p.1 hp.1 (Fin.natAdd 2 i))).1
    · rw [nativeCoefficientSplit_snd]
      exact (abs_le.mp (hA p.1 hp.1 (Fin.natAdd 2 i))).2
  rw [Measure.restrict_prod_eq_prod_univ]
  calc
    _ ≤ (((volume : Measure (Fin 6 → ℝ)).prod (volume : Measure ℝ)).restrict
        (nativeCoefficientTimeSplit ⁻¹' B)).map nativeCoefficientTimeSplit :=
      Measure.map_mono (Measure.restrict_mono_set _ hsub) nativeCoefficientTimeSplit.measurable
    _ = (((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))).prod
        (volume : Measure (Fin 4 → ℝ))).restrict B := by
      rw [← nativeCoefficientTimeSplit.restrict_map,
        measurePreserving_nativeCoefficientTimeSplit.map_eq]
    _ = _ := by
      change (((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))).prod
        (volume : Measure (Fin 4 → ℝ))).restrict (univ ×ˢ nativeFiberBox R) = _
      rw [← Measure.prod_restrict, Measure.restrict_univ]

def nativeBasePoint (p : (Fin 6 → ℝ) × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p.2, p.1 0 + p.2 * p.1 3, p.1 1 + p.2 * p.1 4]

theorem nativeBasePoint_measurable : Measurable nativeBasePoint := by
  unfold nativeBasePoint
  fun_prop

def nativePositionShift (p : ℝ × (Fin 4 → ℝ)) : Fin 2 → ℝ :=
  p.1 • ![p.2 1, p.2 2]

theorem nativePositionShift_measurable : Measurable nativePositionShift := by
  unfold nativePositionShift
  fun_prop

theorem nativeBasePoint_factorization (p : (Fin 6 → ℝ) × ℝ) :
    nativeBasePoint p = nativeBaseCoordinates
      ((nativeCoefficientTimeSplit p).1.1,
        (nativeCoefficientTimeSplit p).1.2 +
          nativePositionShift ((nativeCoefficientTimeSplit p).1.1,
            (nativeCoefficientTimeSplit p).2)) := by
  rw [nativeBaseCoordinates_apply]
  ext i
  fin_cases i <;> rfl

/-- Every measurable label, including joint hidden and velocity bins, has a uniform
ceiling independent of bin depth for a bounded coefficient-volume component. -/
theorem native_component_observation_le {I : Type*} [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (A : Set (Fin 6 → ℝ)) (R : ℝ) (hA : ∀ x ∈ A, ∀ i, |x i| ≤ R)
    (q : (Fin 6 → ℝ) × ℝ → I) (hq : Measurable q) :
    (((volume.restrict A).prod (volume : Measure ℝ)).map
      (fun p => (nativeBasePoint p, q p))) ≤
        (ENNReal.ofReal (2 * R) ^ 4) •
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure I)) := by
  let ρ : Measure ((Fin 6 → ℝ) × ℝ) := (volume.restrict A).prod volume
  let ν : Measure (Fin 4 → ℝ) := volume.restrict (nativeFiberBox R)
  let O : ((ℝ × (Fin 2 → ℝ)) × (Fin 4 → ℝ)) → (ℝ × (Fin 2 → ℝ)) × I :=
    fun p => ((p.1.1, p.1.2 + nativePositionShift (p.1.1, p.2)),
      q (nativeCoefficientTimeSplit.symm p))
  let H : ((ℝ × (Fin 2 → ℝ)) × I) → EuclideanSpace ℝ (Fin 3) × I :=
    Prod.map nativeBaseCoordinates id
  have hO : Measurable O :=
    (parametricFiberTranslation nativePositionShift nativePositionShift_measurable).measurable.fst.prodMk
      (hq.comp nativeCoefficientTimeSplit.symm.measurable)
  have hH : Measurable H := nativeBaseCoordinates.measurable.prodMap measurable_id
  have hHpres : MeasurePreserving H
      (((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))).prod (Measure.count : Measure I))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure I)) :=
    measurePreserving_nativeBaseCoordinates.prod (MeasurePreserving.id _)
  have hsource : ρ.map nativeCoefficientTimeSplit ≤
      (1 : ℝ≥0∞) • ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))).prod ν := by
    simpa only [one_smul] using native_component_source_le A R hA
  have hbound : (ρ.map nativeCoefficientTimeSplit).map O ≤
      (ENNReal.ofReal (2 * R) ^ 4) •
        (((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))).prod (Measure.count : Measure I)) := by
    have h := labeled_parametric_map_le (volume : Measure ℝ) ν
      (ρ.map nativeCoefficientTimeSplit) 1 hsource nativePositionShift nativePositionShift_measurable
      (q ∘ nativeCoefficientTimeSplit.symm) (hq.comp nativeCoefficientTimeSplit.symm.measurable)
    simpa only [one_mul, ν, Measure.restrict_apply_univ, volume_nativeFiberBox, Function.comp_apply] using h
  calc
    _ = ((ρ.map nativeCoefficientTimeSplit).map O).map H := by
      rw [Measure.map_map hH hO, Measure.map_map (hH.comp hO) nativeCoefficientTimeSplit.measurable]
      congr 1
      funext p
      apply Prod.ext
      · exact nativeBasePoint_factorization p
      · simp only [Function.comp_apply, H, O, Prod.map_apply, id_eq,
          MeasurableEquiv.symm_apply_apply]
    _ ≤ ((ENNReal.ofReal (2 * R) ^ 4) •
        (((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))).prod
          (Measure.count : Measure I))).map H := Measure.map_mono hbound hH
    _ = _ := by rw [Measure.map_smul _ hH.aemeasurable, hHpres.map_eq]

/-- Finite original coefficient priors keep the sum of their original weights in
the ceiling. The copy index and the observation label may both be arbitrary. -/
theorem native_finite_observation_le {I : Type*} [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    {m : ℕ} (c : Fin m → ℝ≥0∞) (idx : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (R : ℝ)
    (hA : ∀ j x, x ∈ A j → ∀ i, |x i| ≤ R)
    (q : (ℕ × (Fin 6 → ℝ)) × ℝ → I) (hq : Measurable q) :
    (((∑ j, c j • (volume.restrict (A j)).map (fun x => (idx j, x))).prod
      (volume : Measure ℝ)).map
        (fun p => (nativeBasePoint (p.1.2, p.2), q p))) ≤
      ((∑ j, c j) * ENNReal.ofReal (2 * R) ^ 4) •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (Measure.count : Measure I)) := by
  let O : (ℕ × (Fin 6 → ℝ)) × ℝ → EuclideanSpace ℝ (Fin 3) × I :=
    fun p => (nativeBasePoint (p.1.2, p.2), q p)
  have hO : Measurable O :=
    (nativeBasePoint_measurable.comp (measurable_fst.snd.prodMk measurable_snd)).prodMk hq
  have hpiece (j : Fin m) :
      (((volume.restrict (A j)).map (fun x => (idx j, x))).prod
        (volume : Measure ℝ)).map O ≤
      (ENNReal.ofReal (2 * R) ^ 4) •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (Measure.count : Measure I)) := by
    have hi : Measurable (fun x : Fin 6 → ℝ => (idx j, x)) :=
      measurable_const.prodMk measurable_id
    have hp : Measurable (fun p : (Fin 6 → ℝ) × ℝ => ((idx j, p.1), p.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    have heq : ((volume.restrict (A j)).map (fun x => (idx j, x))).prod
        (volume : Measure ℝ) =
      ((volume.restrict (A j)).prod (volume : Measure ℝ)).map
        (fun p => ((idx j, p.1), p.2)) := by
      calc
        _ = ((volume.restrict (A j)).prod (volume : Measure ℝ)).map
            (Prod.map (fun x => (idx j, x)) id) := by
          simpa only [Measure.map_id] using
            (Measure.map_prod_map (volume.restrict (A j)) (volume : Measure ℝ) hi measurable_id)
        _ = _ := by
          congr 1
    rw [heq, Measure.map_map hO hp]
    exact native_component_observation_le (A j) R (hA j)
      (fun p => q ((idx j, p.1), p.2)) (hq.comp hp)
  change ((∑ j, c j • (volume.restrict (A j)).map (fun x => (idx j, x))).prod
    (volume : Measure ℝ)).map O ≤ _
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype]
  simp_rw [Measure.prod_smul_left]
  rw [Measure.map_finset_sum' hO.aemeasurable]
  simp_rw [Measure.map_smul _ hO.aemeasurable]
  calc
    _ ≤ ∑ j, c j • ((ENNReal.ofReal (2 * R) ^ 4) •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (Measure.count : Measure I))) := by
      apply Finset.sum_le_sum
      intro j _
      exact smul_le_smul_left (c j) (hpiece j)
    _ = (∑ j, c j) • ((ENNReal.ofReal (2 * R) ^ 4) •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (Measure.count : Measure I))) := Finset.sum_smul.symm
    _ = _ := smul_smul _ _ _

/-- Any current incidence law dominated by the original finite product prior
inherits its ceiling. This includes every further restriction. -/
theorem native_dominated_observation_le {I : Type*} [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    {m : ℕ} (c : Fin m → ℝ≥0∞) (idx : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (R : ℝ)
    (hA : ∀ j x, x ∈ A j → ∀ i, |x i| ≤ R)
    (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hρ : ρ ≤ (∑ j, c j • (volume.restrict (A j)).map (fun x => (idx j, x))).prod
      (volume : Measure ℝ))
    (q : (ℕ × (Fin 6 → ℝ)) × ℝ → I) (hq : Measurable q) :
    ρ.map (fun p => (nativeBasePoint (p.1.2, p.2), q p)) ≤
      ((∑ j, c j) * ENNReal.ofReal (2 * R) ^ 4) •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (Measure.count : Measure I)) := by
  exact (Measure.map_mono hρ
    ((nativeBasePoint_measurable.comp
      (measurable_fst.snd.prodMk measurable_snd)).prodMk hq)).trans
        (native_finite_observation_le c idx A R hA q hq)

/-- The ceiling holds for every measurable version of the selected RN density. -/
theorem native_observation_density_le {I : Type*} [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    {m : ℕ} (c : Fin m → ℝ≥0∞) (idx : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (R : ℝ)
    (hA : ∀ j x, x ∈ A j → ∀ i, |x i| ≤ R)
    (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hρ : ρ ≤ (∑ j, c j • (volume.restrict (A j)).map (fun x => (idx j, x))).prod
      (volume : Measure ℝ))
    (q : (ℕ × (Fin 6 → ℝ)) × ℝ → I) (hq : Measurable q)
    (g : EuclideanSpace ℝ (Fin 3) × I → ℝ≥0∞) (hg : Measurable g)
    (hlaw : ρ.map (fun p => (nativeBasePoint (p.1.2, p.2), q p)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (Measure.count : Measure I)).withDensity g) :
    g ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure I)]
      fun _ => (∑ j, c j) * ENNReal.ofReal (2 * R) ^ 4 := by
  apply density_le_of_measure_bound _ g hg
  rw [← hlaw]
  exact native_dominated_observation_le c idx A R hA ρ hρ q hq

theorem native_count_product {I J : Type*} [MeasurableSpace I] [MeasurableSpace J]
    [Countable I] [Countable J] [MeasurableSingletonClass I] [MeasurableSingletonClass J] :
    (Measure.count : Measure I).prod (Measure.count : Measure J) =
      (Measure.count : Measure (I × J)) := by
  apply Measure.ext_of_singleton
  rintro ⟨i, j⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp

/-- The same estimate in the nested product convention for joint hidden and
angular observations. Neither label has a depth-dependent cost. -/
theorem native_joint_observation_le {I J : Type*} [MeasurableSpace I] [MeasurableSpace J]
    [Countable I] [Countable J] [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    {m : ℕ} (c : Fin m → ℝ≥0∞) (idx : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (R : ℝ)
    (hA : ∀ j x, x ∈ A j → ∀ i, |x i| ≤ R)
    (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hρ : ρ ≤ (∑ j, c j • (volume.restrict (A j)).map (fun x => (idx j, x))).prod
      (volume : Measure ℝ))
    (q : (ℕ × (Fin 6 → ℝ)) × ℝ → I) (hq : Measurable q)
    (a : (ℕ × (Fin 6 → ℝ)) × ℝ → J) (ha : Measurable a) :
    ρ.map (fun p => ((nativeBasePoint (p.1.2, p.2), q p), a p)) ≤
      ((∑ j, c j) * ENNReal.ofReal (2 * R) ^ 4) •
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (Measure.count : Measure I)).prod (Measure.count : Measure J)) := by
  let e : (EuclideanSpace ℝ (Fin 3) × (I × J)) ≃ᵐ
      ((EuclideanSpace ℝ (Fin 3) × I) × J) := MeasurableEquiv.prodAssoc.symm
  have he : MeasurePreserving e
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure (I × J)))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (Measure.count : Measure I)).prod (Measure.count : Measure J)) := by
    rw [← native_count_product]
    exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc volume Measure.count Measure.count)
  have hflat : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
      (nativeBasePoint (p.1.2, p.2), (q p, a p))) :=
    (nativeBasePoint_measurable.comp
      (measurable_fst.snd.prodMk measurable_snd)).prodMk (hq.prodMk ha)
  calc
    _ = (ρ.map (fun p => (nativeBasePoint (p.1.2, p.2), (q p, a p)))).map e := by
      rw [Measure.map_map e.measurable hflat]
      rfl
    _ ≤ (((∑ j, c j) * ENNReal.ofReal (2 * R) ^ 4) •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (Measure.count : Measure (I × J)))).map e :=
      Measure.map_mono (native_dominated_observation_le c idx A R hA ρ hρ
        (fun p => (q p, a p)) (hq.prodMk ha)) e.measurable
    _ = _ := by rw [Measure.map_smul _ e.measurable.aemeasurable, he.map_eq]

/-- Tempered support, multiplicity and original component weights give one
polynomial ceiling, uniformly over all label depths. -/
theorem native_ceiling_polynomial_bound {m : ℕ} (c : Fin m → ℝ)
    (N : ℝ) (M : ℕ) (hN : 2 ≤ N) (hm : (m : ℝ) ≤ N ^ M)
    (hc : ∀ j, c j ≤ N ^ M) :
    (∑ j, ENNReal.ofReal (c j)) * ENNReal.ofReal (2 * N ^ M) ^ 4 ≤
      ENNReal.ofReal (N ^ (6 * M + 4)) := by
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have hsum : (∑ j, ENNReal.ofReal (c j)) ≤ ENNReal.ofReal ((m : ℝ) * N ^ M) := by
    calc
      _ ≤ ∑ _ : Fin m, ENNReal.ofReal (N ^ M) :=
        Finset.sum_le_sum (fun j _ => ENNReal.ofReal_le_ofReal (hc j))
      _ = _ := by simp [ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  have h16 : (16 : ℝ) ≤ N ^ 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hN 4
  have hreal : (m : ℝ) * N ^ M * (2 * N ^ M) ^ 4 ≤ N ^ (6 * M + 4) := by
    calc
      _ ≤ N ^ M * N ^ M * (2 * N ^ M) ^ 4 := by gcongr
      _ = 16 * (N ^ M) ^ 6 := by ring
      _ ≤ N ^ 4 * (N ^ M) ^ 6 := by gcongr
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  calc
    _ ≤ ENNReal.ofReal ((m : ℝ) * N ^ M) * ENNReal.ofReal (2 * N ^ M) ^ 4 := by
      gcongr
    _ = ENNReal.ofReal ((m : ℝ) * N ^ M * (2 * N ^ M) ^ 4) := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- A ready-to-use ceiling for every selected native density from a tempered
finite prior. No lower bound on selected mass is needed. -/
theorem native_tempered_density_le {I : Type*} [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    {m : ℕ} (c : Fin m → ℝ) (idx : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (N : ℝ) (M : ℕ)
    (hN : 2 ≤ N) (hm : (m : ℝ) ≤ N ^ M) (hc : ∀ j, c j ≤ N ^ M)
    (hA : ∀ j x, x ∈ A j → ∀ i, |x i| ≤ N ^ M)
    (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hρ : ρ ≤ (∑ j, ENNReal.ofReal (c j) •
      (volume.restrict (A j)).map (fun x => (idx j, x))).prod (volume : Measure ℝ))
    (q : (ℕ × (Fin 6 → ℝ)) × ℝ → I) (hq : Measurable q)
    (g : EuclideanSpace ℝ (Fin 3) × I → ℝ≥0∞) (hg : Measurable g)
    (hlaw : ρ.map (fun p => (nativeBasePoint (p.1.2, p.2), q p)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (Measure.count : Measure I)).withDensity g) :
    g ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure I)]
      fun _ => ENNReal.ofReal (N ^ (6 * M + 4)) := by
  filter_upwards [native_observation_density_le (fun j => ENNReal.ofReal (c j))
    idx A (N ^ M) hA ρ hρ q hq g hg hlaw] with x hx
  exact hx.trans (native_ceiling_polynomial_bound c N M hN hm hc)

end Submission.Lib.K4Homogenization
