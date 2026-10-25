/-
Adapted from this LOT tree, o147, session x0502, commit 373d234,
Submission/Obl/k4_local_remainder_horizon_transfer/Homogenize/Transport.lean
(that session's own code).
-/
import Mathlib

/-!
# Transport of observation densities

Generic facts about densities: transport through a measurable equivalence that
scales the reference measure, and the embedding of an observation into a space
with an extra discrete label taking one fixed value. Then the affine base map of an
encoded world, `(t, y₁, y₂) ↦ (t, a y₁ + o + t/2, b y₂ + t/2)`, and its Jacobian.

-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set
open scoped ENNReal

/-- Transport of a density through a measurable equivalence multiplying the reference
measure by a constant. -/
theorem map_withDensity_equiv_smul {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (e : A ≃ᵐ B) (c : ℝ≥0∞) (he : μ.map e = c • ν)
    (g : A → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity g).map e = ν.withDensity (fun b => c * g (e.symm b)) := by
  ext S hS
  rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS]
  have h1 : ∫⁻ a in e ⁻¹' S, g a ∂μ = ∫⁻ b in S, g (e.symm b) ∂(μ.map e) := by
    rw [Measure.restrict_map e.measurable hS, lintegral_map_equiv]
    simp only [MeasurableEquiv.symm_apply_apply]
  rw [h1, he, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul c (f := fun b => g (e.symm b)) (hg.comp e.symm.measurable)]

/-- Appending a constant discrete label. -/
theorem map_pair_withDensity {A L : Type*} [MeasurableSpace A] [MeasurableSpace L]
    [MeasurableSingletonClass L] [Countable L]
    (ρ : Measure A) [SFinite ρ] (h : A → ℝ≥0∞) (hh : Measurable h) (l₀ : L) :
    (ρ.withDensity h).map (fun a => (a, l₀)) =
      (ρ.prod Measure.count).withDensity
        (fun p => h p.1 * (({l₀} : Set L).indicator (fun _ => (1 : ℝ≥0∞)) p.2)) := by
  have hdirac : (Measure.dirac l₀ : Measure L) =
      Measure.count.withDensity (({l₀} : Set L).indicator fun _ => (1 : ℝ≥0∞)) := by
    rw [withDensity_indicator (measurableSet_singleton l₀), withDensity_const, one_smul,
      Measure.restrict_singleton, Measure.count_singleton, one_smul]
  rw [← Measure.prod_dirac, hdirac, prod_withDensity hh
    ((measurable_const.indicator (measurableSet_singleton l₀)))]

/-! ## The base map of an encoded world -/

/-- The base map `(t, y₁, y₂) ↦ (t, a y₁ + o + t/2, b y₂ + t/2)`. -/
noncomputable def baseMap (a b o : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![z 0, a * z 1 + o + z 0 / 2, b * z 2 + z 0 / 2]

/-- Its inverse. -/
noncomputable def baseInv (a b o : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![z 0, (z 1 - o - z 0 / 2) / a, (z 2 - z 0 / 2) / b]

theorem baseInv_baseMap {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (o : ℝ)
    (z : EuclideanSpace ℝ (Fin 3)) : baseInv a b o (baseMap a b o z) = z := by
  ext i
  fin_cases i <;> simp [baseInv, baseMap] <;> field_simp <;> ring

theorem baseMap_baseInv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (o : ℝ)
    (z : EuclideanSpace ℝ (Fin 3)) : baseMap a b o (baseInv a b o z) = z := by
  ext i
  fin_cases i <;> simp [baseInv, baseMap] <;> field_simp <;> ring

theorem continuous_baseMap (a b o : ℝ) : Continuous (baseMap a b o) := by
  unfold baseMap
  fun_prop

theorem continuous_baseInv (a b o : ℝ) : Continuous (baseInv a b o) := by
  unfold baseInv
  fun_prop

/-- The base map as a measurable equivalence. -/
noncomputable def baseEquiv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (o : ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ᵐ EuclideanSpace ℝ (Fin 3) where
  toFun := baseMap a b o
  invFun := baseInv a b o
  left_inv := baseInv_baseMap ha hb o
  right_inv := baseMap_baseInv ha hb o
  measurable_toFun := (continuous_baseMap a b o).measurable
  measurable_invFun := (continuous_baseInv a b o).measurable

@[simp] theorem baseEquiv_apply {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (o : ℝ)
    (z : EuclideanSpace ℝ (Fin 3)) : baseEquiv ha hb o z = baseMap a b o z := rfl

@[simp] theorem baseEquiv_symm_apply {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (o : ℝ)
    (z : EuclideanSpace ℝ (Fin 3)) : (baseEquiv ha hb o).symm z = baseInv a b o z := rfl

/-- The linear part of the base map in coordinates. -/
noncomputable def baseMatrix (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 1 / 2, a, 0; 1 / 2, 0, b]

/-- The base map in coordinates `Fin 3 → ℝ`. -/
noncomputable def baseMapPi (a b o : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Matrix.toLin' (baseMatrix a b) x + ![0, o, 0]

theorem baseMap_eq_pi (a b o : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    baseMap a b o z = WithLp.toLp 2 (baseMapPi a b o (WithLp.ofLp z)) := by
  ext i
  fin_cases i <;>
    simp [baseMap, baseMapPi, baseMatrix, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_succ] <;> ring

theorem map_baseMapPi_volume {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (o : ℝ) :
    (volume : Measure (Fin 3 → ℝ)).map (baseMapPi a b o) =
      ENNReal.ofReal |a * b|⁻¹ • volume := by
  have hdet : LinearMap.det (Matrix.toLin' (baseMatrix a b)) = a * b := by
    rw [LinearMap.det_toLin', baseMatrix, Matrix.det_fin_three]
    simp
  have hdet0 : LinearMap.det (Matrix.toLin' (baseMatrix a b)) ≠ 0 := by
    rw [hdet]; exact mul_ne_zero ha hb
  have hfun : baseMapPi a b o = (fun x => x + ![0, o, 0]) ∘ (Matrix.toLin' (baseMatrix a b)) := by
    funext x; rfl
  rw [hfun, ← Measure.map_map (measurable_add_const _)
    (LinearMap.continuous_of_finiteDimensional _).measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, Measure.map_smul,
    map_add_right_eq_self, hdet, abs_inv]
  exact (measurable_add_const _).aemeasurable

/-- The base map multiplies Lebesgue measure by `|a b|⁻¹`. -/
theorem map_baseMap_volume {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (o : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).map (baseMap a b o) =
      ENNReal.ofReal |a * b|⁻¹ • volume := by
  have he := PiLp.volume_preserving_ofLp (Fin 3)
  have he' := PiLp.volume_preserving_toLp (Fin 3)
  have hfun : baseMap a b o =
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ∘ baseMapPi a b o ∘
        (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → Fin 3 → ℝ) := by
    funext z; exact baseMap_eq_pi a b o z
  have hmeas : Measurable (baseMapPi a b o) := by
    unfold baseMapPi
    exact (measurable_add_const _).comp
      (LinearMap.continuous_of_finiteDimensional _).measurable
  rw [hfun, ← Measure.map_map he'.measurable (hmeas.comp he.measurable),
    ← Measure.map_map hmeas he.measurable, he.map_eq, map_baseMapPi_volume ha hb o,
    Measure.map_smul, he'.map_eq]
  exact he'.measurable.aemeasurable

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
