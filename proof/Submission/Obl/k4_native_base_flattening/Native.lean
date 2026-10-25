import Mathlib
import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_native_base_flattening.Shear
import Submission.Obl.k4_native_base_flattening.Observation

/-!
# Native incidence laws in sheared coordinates

A native law `ν = ∑ⱼ cⱼ • (iⱼ, ·)₊(volume|Aⱼ)`, times `dt` and restricted to a measurable `S`,
is the image of the density `∑ⱼ cⱼ 1[Aⱼ, S]` in product sheared coordinates. Its observation law
at any depths therefore has the explicit density `marg` against the reference measure: native
laws have observation densities after every measurable further selection.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_native_base_flattening

open Submission.Obl.k4_profile_density_bounds (Observation reference Base State Line observe width
  measurable_observe)

lemma observe_native (N r u : ℝ) (i : ℕ) (q : (Fin 3 → ℝ) × (Fin 4 → ℝ)) :
    observe N r u ((i, (native q).1), (native q).2) = sobs (width N r) (width N u) q := by
  obtain ⟨z, w⟩ := q
  have hz : (WithLp.toLp 2 ![z 0, z 1 - z 0 * w 1 + z 0 * w 1, z 2 - z 0 * w 2 + z 0 * w 2] : Base)
      = WithLp.toLp 2 z := by
    congr 1
    funext i
    fin_cases i <;> simp
  simp only [observe, native, unshear, join, coeffs, sobs, tbin,
    Submission.Obl.k4_profile_density_bounds.base, Submission.Obl.k4_profile_density_bounds.hidden,
    Submission.Obl.k4_profile_density_bounds.velocity]
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  rw [hz, sub_add_cancel]

/-- The native component with index `i`, coefficient set `A` and selection `S`, in product sheared
coordinates. -/
def compSet (i : ℕ) (A : Set (Fin 6 → ℝ)) (S : Set State) : Set ((Fin 3 → ℝ) × (Fin 4 → ℝ)) :=
  {q | (native q).1 ∈ A ∧ ((i, (native q).1), (native q).2) ∈ S}

lemma measurableSet_compSet (i : ℕ) {A : Set (Fin 6 → ℝ)} (hA : MeasurableSet A) {S : Set State}
    (hS : MeasurableSet S) : MeasurableSet (compSet i A S) := by
  have h1 : Measurable (fun q => (native q).1) := measurable_fst.comp measurable_native
  have h2 : Measurable (fun q => (((i, (native q).1), (native q).2) : State)) := by
    have h3 : Measurable (fun q => (native q).2) := measurable_snd.comp measurable_native
    exact Measurable.prodMk (Measurable.prodMk measurable_const h1) h3
  exact (h1 hA).inter (h2 hS)

/-- The density of a native law restricted to `S`, in product sheared coordinates. -/
noncomputable def nativeDensity {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (S : Set State) (q : (Fin 3 → ℝ) × (Fin 4 → ℝ)) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (c j) * (compSet (i j) (A j) S).indicator 1 q

lemma measurable_nativeDensity {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    {A : Fin m → Set (Fin 6 → ℝ)} (hA : ∀ j, MeasurableSet (A j)) {S : Set State}
    (hS : MeasurableSet S) : Measurable (nativeDensity c i A S) := by
  unfold nativeDensity
  refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
  exact measurable_one.indicator (measurableSet_compSet (i j) (hA j) hS)

/-- The native law restricted to `S`, pushed to observations, is the observation of the native
density in sheared coordinates. -/
theorem map_observe_restrict {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    {A : Fin m → Set (Fin 6 → ℝ)} (hA : ∀ j, MeasurableSet (A j)) {S : Set State}
    (hS : MeasurableSet S) (N r u : ℝ) :
    Measure.map (observe N r u) (((∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun x => (i j, x)) ((volume : Measure (Fin 6 → ℝ)).restrict (A j))).prod
        (volume : Measure ℝ)).restrict S) =
      Measure.map (sobs (width N r) (width N u))
        (((volume : Measure (Fin 3 → ℝ)).prod (volume : Measure (Fin 4 → ℝ))).withDensity
          (nativeDensity c i A S)) := by
  ext B hB
  have hO := measurable_observe N r u
  have hsobs := measurable_sobs (width N r) (width N u)
  rw [Measure.map_apply hO hB, Measure.restrict_apply (hO hB),
    Measure.map_apply hsobs hB, withDensity_apply _ (hsobs hB)]
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    Measure.finsetSum_apply]
  simp only [nativeDensity]
  rw [lintegral_finsetSum (s := Finset.univ)
    (f := fun j q => ENNReal.ofReal (c j) * (compSet (i j) (A j) S).indicator 1 q)
    (fun j _ => measurable_const.mul
      (measurable_one.indicator (measurableSet_compSet (i j) (hA j) hS)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hφ : Measurable (fun x : Fin 6 → ℝ => (i j, x)) := by fun_prop
  have hψ : Measurable (Prod.map (fun x : Fin 6 → ℝ => (i j, x)) (id : ℝ → ℝ)) :=
    hφ.prodMap measurable_id
  have hZ : MeasurableSet (observe N r u ⁻¹' B ∩ S) := (hO hB).inter hS
  rw [Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul,
    lintegral_const_mul _ (measurable_one.indicator (measurableSet_compSet (i j) (hA j) hS))]
  congr 1
  rw [← Measure.map_id (μ := (volume : Measure ℝ)), Measure.map_prod_map _ _ hφ measurable_id,
    Measure.map_apply hψ hZ, Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply (hψ hZ),
    ← measurePreserving_native.measure_preimage
      ((hψ hZ).inter ((hA j).prod MeasurableSet.univ)).nullMeasurableSet,
    lintegral_indicator_one (measurableSet_compSet (i j) (hA j) hS),
    Measure.restrict_apply (measurableSet_compSet (i j) (hA j) hS)]
  congr 1
  ext q
  have hpm : Prod.map (fun x : Fin 6 → ℝ => (i j, x)) (id : ℝ → ℝ) (native q) =
      ((i j, (native q).1), (native q).2) := rfl
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true, compSet, mem_ofPred_eq,
    hpm]
  rw [observe_native]
  tauto

/-- Native laws have observation densities after every measurable further selection. -/
theorem exists_density {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    {A : Fin m → Set (Fin 6 → ℝ)} (hA : ∀ j, MeasurableSet (A j)) {S : Set State}
    (hS : MeasurableSet S) (N r u : ℝ) :
    Measure.map (observe N r u) (((∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun x => (i j, x)) ((volume : Measure (Fin 6 → ℝ)).restrict (A j))).prod
        (volume : Measure ℝ)).restrict S) =
      reference.withDensity (marg (width N r) (width N u) (nativeDensity c i A S)) := by
  rw [map_observe_restrict c i hA hS, map_sobs_withDensity _ _ (measurable_nativeDensity c i hA hS)]

end Submission.Obl.k4_native_base_flattening
