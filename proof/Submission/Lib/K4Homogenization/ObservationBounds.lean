/-
Adapted from: here:o018
-/
import Mathlib

/-! Counting-label pushforward bounds for the observation-density ceilings in
the finite model reduction. A label is allowed to depend on every coefficient. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4Homogenization

/-- Adding a countable label to a projection costs at most the total fiber measure. -/
theorem labeled_product_map_le {X Y I : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (q : X × Y → I) (hq : Measurable q) :
    (μ.prod ν).map (fun p => (p.1, q p)) ≤
      ν univ • (μ.prod (Measure.count : Measure I)) := by
  apply Measure.le_iff.mpr
  intro A hA
  have hmap : Measurable (fun p : X × Y => (p.1, q p)) := measurable_fst.prodMk hq
  rw [Measure.map_apply hmap hA, Measure.smul_apply, smul_eq_mul,
    Measure.prod_apply (hmap hA), Measure.prod_apply hA]
  have hsec : Measurable (fun x : X => (Measure.count : Measure I) (Prod.mk x ⁻¹' A)) :=
    measurable_measure_prodMk_left hA
  calc
    _ ≤ ∫⁻ x : X, ν univ * (Measure.count : Measure I) (Prod.mk x ⁻¹' A) ∂μ := by
      apply lintegral_mono
      intro x
      change ν {y | (x, q (x, y)) ∈ A} ≤
        ν univ * (Measure.count : Measure I) (Prod.mk x ⁻¹' A)
      by_cases hempty : Prod.mk x ⁻¹' A = ∅
      · have hz : {y : Y | (x, q (x, y)) ∈ A} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          have hmem : q (x, y) ∈ Prod.mk x ⁻¹' A := hy
          simp only [hempty, mem_empty_iff_false] at hmem
        simp only [hz, hempty, measure_empty, mul_zero, le_refl]
      · obtain ⟨j, hj⟩ := Set.nonempty_iff_ne_empty.mpr hempty
        have hcount : (1 : ℝ≥0∞) ≤ (Measure.count : Measure I) (Prod.mk x ⁻¹' A) := by
          calc
            1 = (Measure.count : Measure I) {j} := by simp
            _ ≤ _ := measure_mono (singleton_subset_iff.mpr hj)
        calc
          _ ≤ ν univ := measure_mono (subset_univ _)
          _ = ν univ * 1 := (mul_one _).symm
          _ ≤ _ := by gcongr
    _ = _ := lintegral_const_mul _ hsec

/-- A bounded source density and bounded fibers give a uniform observation-density ceiling. -/
theorem labeled_map_le_of_source_bound {X Y I : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (ρ : Measure (X × Y)) (C : ℝ≥0∞) (hρ : ρ ≤ C • μ.prod ν)
    (q : X × Y → I) (hq : Measurable q) :
    ρ.map (fun p => (p.1, q p)) ≤
      (C * ν univ) • (μ.prod (Measure.count : Measure I)) := by
  have hm : Measurable (fun p : X × Y => (p.1, q p)) := measurable_fst.prodMk hq
  calc
    _ ≤ (C • μ.prod ν).map (fun p => (p.1, q p)) := Measure.map_mono hρ hm
    _ = C • (μ.prod ν).map (fun p => (p.1, q p)) := Measure.map_smul C hm.aemeasurable
    _ ≤ C • (ν univ • (μ.prod (Measure.count : Measure I))) := by
      gcongr
      exact labeled_product_map_le μ ν q hq
    _ = _ := smul_smul _ _ _

/-- A measure-preserving reparameterization before projection keeps the labeled bound.
The original label can be recovered through the measurable inverse. -/
theorem labeled_equiv_map_le_of_source_bound {X Y I : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (ρ : Measure (X × Y)) (C : ℝ≥0∞) (hρ : ρ ≤ C • μ.prod ν)
    (e : (X × Y) ≃ᵐ (X × Y)) (he : MeasurePreserving e (μ.prod ν) (μ.prod ν))
    (q : X × Y → I) (hq : Measurable q) :
    ρ.map (fun p => ((e p).1, q p)) ≤
      (C * ν univ) • (μ.prod (Measure.count : Measure I)) := by
  have hsrc : ρ.map e ≤ C • μ.prod ν := by
    calc
      _ ≤ (C • μ.prod ν).map e := Measure.map_mono hρ e.measurable
      _ = _ := by rw [Measure.map_smul C e.measurable.aemeasurable, he.map_eq]
  have hlabel := labeled_map_le_of_source_bound μ ν (ρ.map e) C hsrc
    (q ∘ e.symm) (hq.comp e.symm.measurable)
  have heq : (ρ.map e).map (fun p => (p.1, (q ∘ e.symm) p)) =
      ρ.map (fun p => ((e p).1, q p)) := by
    rw [Measure.map_map (measurable_fst.prodMk (hq.comp e.symm.measurable)) e.measurable]
    congr 1
    funext p
    simp
  rw [heq] at hlabel
  exact hlabel

/-- A measurable translation of the first coordinate, depending on the second, preserves
Lebesgue measure times any sigma-finite parameter law. -/
theorem measurePreserving_fiber_translation {d : ℕ} {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] (φ : Y → Fin d → ℝ) (hφ : Measurable φ) :
    MeasurePreserving (fun p : (Fin d → ℝ) × Y => (p.1 + φ p.2, p.2))
      ((volume : Measure (Fin d → ℝ)).prod ν) (volume.prod ν) := by
  have hskew : MeasurePreserving
      (fun p : Y × (Fin d → ℝ) => (p.1, p.2 + φ p.1))
      (ν.prod volume) (ν.prod volume) :=
    (MeasurePreserving.id ν).skew_product
      (measurable_snd.add (hφ.comp measurable_fst))
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_right volume (φ y)).map_eq)
  exact Measure.measurePreserving_swap.comp (hskew.comp Measure.measurePreserving_swap)

/-- The time coordinate is observed and retained, while spatial translation may depend
jointly on time and the hidden fiber. -/
noncomputable def parametricFiberTranslation {d : ℕ} {T Y : Type*}
    [MeasurableSpace T] [MeasurableSpace Y]
    (φ : T × Y → Fin d → ℝ) (hφ : Measurable φ) :
    ((T × (Fin d → ℝ)) × Y) ≃ᵐ ((T × (Fin d → ℝ)) × Y) where
  toFun p := ((p.1.1, p.1.2 + φ (p.1.1, p.2)), p.2)
  invFun p := ((p.1.1, p.1.2 - φ (p.1.1, p.2)), p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := ((measurable_fst.fst).prodMk
    ((measurable_fst.snd).add (hφ.comp ((measurable_fst.fst).prodMk measurable_snd)))).prodMk
      measurable_snd
  measurable_invFun := ((measurable_fst.fst).prodMk
    ((measurable_fst.snd).sub (hφ.comp ((measurable_fst.fst).prodMk measurable_snd)))).prodMk
      measurable_snd

theorem measurePreserving_parametricFiberTranslation {d : ℕ} {T Y : Type*}
    [MeasurableSpace T] [MeasurableSpace Y]
    (τ : Measure T) [SFinite τ] (ν : Measure Y) [SFinite ν]
    (φ : T × Y → Fin d → ℝ) (hφ : Measurable φ) :
    MeasurePreserving (parametricFiberTranslation φ hφ)
      ((τ.prod (volume : Measure (Fin d → ℝ))).prod ν)
      ((τ.prod (volume : Measure (Fin d → ℝ))).prod ν) := by
  have hskew : MeasurePreserving
      (fun p : T × ((Fin d → ℝ) × Y) =>
        (p.1, (p.2.1 + φ (p.1, p.2.2), p.2.2)))
      (τ.prod (volume.prod ν)) (τ.prod (volume.prod ν)) := by
    apply (MeasurePreserving.id τ).skew_product
      (g := fun t (p : (Fin d → ℝ) × Y) => (p.1 + φ (t, p.2), p.2))
      ((measurable_snd.fst.add
        (hφ.comp (measurable_fst.prodMk measurable_snd.snd))).prodMk measurable_snd.snd)
    exact Filter.Eventually.of_forall fun t =>
      (measurePreserving_fiber_translation ν (fun y => φ (t, y))
        (hφ.comp measurable_prodMk_left)).map_eq
  have ha := measurePreserving_prodAssoc τ (volume : Measure (Fin d → ℝ)) ν
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc ha).comp (hskew.comp ha)

/-- The explicit labeled ceiling with time among the observed coordinates. -/
theorem labeled_parametric_map_le {d : ℕ} {T Y I : Type*}
    [MeasurableSpace T] [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (τ : Measure T) [SFinite τ] (ν : Measure Y) [SFinite ν]
    (ρ : Measure ((T × (Fin d → ℝ)) × Y)) (C : ℝ≥0∞)
    (hρ : ρ ≤ C • (τ.prod (volume : Measure (Fin d → ℝ))).prod ν)
    (φ : T × Y → Fin d → ℝ) (hφ : Measurable φ)
    (q : (T × (Fin d → ℝ)) × Y → I) (hq : Measurable q) :
    ρ.map (fun p => ((p.1.1, p.1.2 + φ (p.1.1, p.2)), q p)) ≤
      (C * ν univ) • ((τ.prod (volume : Measure (Fin d → ℝ))).prod
        (Measure.count : Measure I)) := by
  exact labeled_equiv_map_le_of_source_bound (τ.prod volume) ν ρ C hρ
    (parametricFiberTranslation φ hφ)
    (measurePreserving_parametricFiberTranslation τ ν φ hφ) q hq

/-- Spatial graph evaluation preserves the same labeled-density ceiling as an ordinary
projection. No regularity of the labeling beyond measurability is needed. -/
theorem labeled_translated_map_le_of_source_bound {d : ℕ} {Y I : Type*}
    [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Y) [SFinite ν] (ρ : Measure ((Fin d → ℝ) × Y))
    (C : ℝ≥0∞) (hρ : ρ ≤ C • (volume : Measure (Fin d → ℝ)).prod ν)
    (φ : Y → Fin d → ℝ) (hφ : Measurable φ)
    (q : (Fin d → ℝ) × Y → I) (hq : Measurable q) :
    ρ.map (fun p => (p.1 + φ p.2, q p)) ≤
      (C * ν univ) • ((volume : Measure (Fin d → ℝ)).prod (Measure.count : Measure I)) := by
  let S : (Fin d → ℝ) × Y → (Fin d → ℝ) × Y := fun p => (p.1 + φ p.2, p.2)
  let T : (Fin d → ℝ) × Y → (Fin d → ℝ) × Y := fun p => (p.1 - φ p.2, p.2)
  have hS : Measurable S := (measurable_fst.add (hφ.comp measurable_snd)).prodMk measurable_snd
  have hT : Measurable T := (measurable_fst.sub (hφ.comp measurable_snd)).prodMk measurable_snd
  have hsrc : ρ.map S ≤ C • (volume : Measure (Fin d → ℝ)).prod ν := by
    calc
      _ ≤ (C • (volume : Measure (Fin d → ℝ)).prod ν).map S := Measure.map_mono hρ hS
      _ = _ := by
        rw [Measure.map_smul C hS.aemeasurable,
          (measurePreserving_fiber_translation ν φ hφ).map_eq]
  have hlabel := labeled_map_le_of_source_bound volume ν (ρ.map S) C hsrc
    (q ∘ T) (hq.comp hT)
  have heq : (ρ.map S).map (fun p => (p.1, (q ∘ T) p)) =
      ρ.map (fun p => (p.1 + φ p.2, q p)) := by
    rw [Measure.map_map (measurable_fst.prodMk (hq.comp hT)) hS]
    congr 1
    funext p
    simp [S, T]
  rw [heq] at hlabel
  exact hlabel

/-- The measure ceiling is also an almost-everywhere ceiling for any measurable RN density. -/
theorem density_le_of_measure_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (g : X → ℝ≥0∞) (hg : Measurable g)
    (C : ℝ≥0∞) (hbound : μ.withDensity g ≤ C • μ) : g ≤ᵐ[μ] fun _ => C := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hg
  intro A hA _
  rw [← withDensity_apply _ hA]
  simpa only [Measure.smul_apply, smul_eq_mul, lintegral_const, Measure.restrict_apply,
    MeasurableSet.univ, Set.univ_inter] using hbound A

theorem labeled_parametric_density_le {d : ℕ} {T Y I : Type*}
    [MeasurableSpace T] [MeasurableSpace Y] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (τ : Measure T) [SigmaFinite τ] (ν : Measure Y) [SFinite ν]
    (ρ : Measure ((T × (Fin d → ℝ)) × Y)) (C : ℝ≥0∞)
    (hρ : ρ ≤ C • (τ.prod (volume : Measure (Fin d → ℝ))).prod ν)
    (φ : T × Y → Fin d → ℝ) (hφ : Measurable φ)
    (q : (T × (Fin d → ℝ)) × Y → I) (hq : Measurable q)
    (g : (T × (Fin d → ℝ)) × I → ℝ≥0∞) (hg : Measurable g)
    (hlaw : ρ.map (fun p => ((p.1.1, p.1.2 + φ (p.1.1, p.2)), q p)) =
      ((τ.prod (volume : Measure (Fin d → ℝ))).prod (Measure.count : Measure I)).withDensity g) :
    g ≤ᵐ[(τ.prod (volume : Measure (Fin d → ℝ))).prod (Measure.count : Measure I)]
      fun _ => C * ν univ := by
  apply density_le_of_measure_bound _ g hg
  rw [← hlaw]
  exact labeled_parametric_map_le τ ν ρ C hρ φ hφ q hq

/-- A current labeled observation law therefore has an explicit ceiling, including after
any measurable selection already incorporated in the source measure. -/
theorem labeled_translated_density_le {d : ℕ} {Y I : Type*}
    [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (ν : Measure Y) [SFinite ν] (ρ : Measure ((Fin d → ℝ) × Y))
    (C : ℝ≥0∞) (hρ : ρ ≤ C • (volume : Measure (Fin d → ℝ)).prod ν)
    (φ : Y → Fin d → ℝ) (hφ : Measurable φ)
    (q : (Fin d → ℝ) × Y → I) (hq : Measurable q)
    (g : ((Fin d → ℝ) × I) → ℝ≥0∞) (hg : Measurable g)
    (hlaw : ρ.map (fun p => (p.1 + φ p.2, q p)) =
      ((volume : Measure (Fin d → ℝ)).prod (Measure.count : Measure I)).withDensity g) :
    g ≤ᵐ[(volume : Measure (Fin d → ℝ)).prod (Measure.count : Measure I)]
      fun _ => C * ν univ := by
  apply density_le_of_measure_bound _ g hg
  rw [← hlaw]
  exact labeled_translated_map_le_of_source_bound ν ρ C hρ φ hφ q hq

end Submission.Lib.K4Homogenization
