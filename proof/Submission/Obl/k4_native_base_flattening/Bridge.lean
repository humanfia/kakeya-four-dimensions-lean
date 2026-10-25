import Mathlib
import Submission.Obl.k4_native_base_flattening.Native
import Submission.Obl.k4_native_base_flattening.Charge
import Submission.Obl.k4_native_base_flattening.UniformAveraging
import Submission.Obl.k4_native_base_flattening.AveragingBridge

/-!
# The native density in the averaging format

The sheared native density of `Native.lean` is the sum of the component densities of
`PolynomialAveraging.lean` (with the event fibres of the selection), read through `join`. Hence the
`L¹` distance of the marginals to the marginals of any approximant is at most the `L¹` distance
in sheared coordinates controlled by `uniform_native_flattening`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_native_base_flattening

open Submission.Obl.k4_profile_density_bounds (Observation reference Base State Line)
open Submission.Lib.K4ModelReduction (densityL1Distance)

/-- The fibre of a selection at a native index, in the seven variables of the frozen format. -/
def eventFiber (S : Set State) (i : ℕ) : Set (Fin 7 → ℝ) :=
  {x₁ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ S}

lemma nativeEventPoint_mem_eventFiber (S : Set State) (i : ℕ) (x : Fin 7 → ℝ) :
    nativeEventPoint x ∈ eventFiber S i ↔ ((i, nativeCoefficients x), x 0) ∈ S := by
  have h : (fun j₁ : Fin 6 => nativeEventPoint x j₁.castSucc) = nativeCoefficients x := by
    funext j₁
    simp [nativeEventPoint, Fin.snoc_castSucc]
  simp only [eventFiber, mem_ofPred_eq, h, nativeEventPoint_last]

lemma nativeDensity_eq {m : ℕ} (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (S : Set State) (q : (Fin 3 → ℝ) × (Fin 4 → ℝ)) :
    nativeDensity c i A S q = ENNReal.ofReal
      (∑ j, nativeComponentDensity (c j) (A j) (eventFiber S (i j)) (join q)) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hiff : (nativeCoefficients (join q) ∈ A j ∧
        nativeEventPoint (join q) ∈ eventFiber S (i j)) ↔ q ∈ compSet (i j) (A j) S := by
      rw [nativeEventPoint_mem_eventFiber]
      rfl
    unfold nativeComponentDensity
    by_cases hq : q ∈ compSet (i j) (A j) S
    · rw [ite_cond_eq_true _ _ (eq_true (hiff.mpr hq)), indicator_of_mem hq, Pi.one_apply, mul_one]
    · rw [ite_cond_eq_false _ _ (eq_false (fun h => hq (hiff.mp h))), indicator_of_notMem hq, mul_zero,
        ENNReal.ofReal_zero]
  · intro j _
    unfold nativeComponentDensity
    split_ifs
    · exact hc j
    · exact le_rfl

/-- The `L¹` distance of the observation marginals is at most the sheared `L¹` distance. -/
theorem lintegral_ediff_marg_native_le {m : ℕ} (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (i : Fin m → ℕ) {A : Fin m → Set (Fin 6 → ℝ)} (hA : ∀ j, MeasurableSet (A j))
    {S : Set State} (hS : MeasurableSet S) (a b : ℝ)
    {h : (Fin 7 → ℝ) → ℝ} (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x) :
    ∫⁻ y, ediff (marg a b (nativeDensity c i A S) y)
        (marg a b (fun q => ENNReal.ofReal (h (join q))) y) ∂reference ≤
      densityL1Distance volume h
        (fun x => ∑ j, nativeComponentDensity (c j) (A j) (eventFiber S (i j)) x) := by
  classical
  have hhj : Measurable (fun q => ENNReal.ofReal (h (join q))) :=
    ENNReal.measurable_ofReal.comp (hh.comp measurable_join)
  refine (lintegral_ediff_marg_le a b (measurable_nativeDensity c i hA hS) hhj).trans ?_
  set f : (Fin 7 → ℝ) → ℝ :=
    fun x => ∑ j, nativeComponentDensity (c j) (A j) (eventFiber S (i j)) x with hfdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => Finset.sum_nonneg fun j _ => by
    unfold nativeComponentDensity
    split_ifs
    · exact hc j
    · exact le_rfl
  have hfm : Measurable f := by
    refine Finset.measurable_sum _ fun j _ => ?_
    unfold nativeComponentDensity
    refine Measurable.ite ?_ measurable_const measurable_const
    refine (nativeCoefficients_measurable (hA j)).inter ?_
    have hm : Measurable (fun x : Fin 7 → ℝ =>
        (((i j, nativeCoefficients x), x 0) : State)) :=
      (measurable_const.prodMk nativeCoefficients_measurable).prodMk (measurable_pi_apply 0)
    have hset : {x : Fin 7 → ℝ | nativeEventPoint x ∈ eventFiber S (i j)} =
        (fun x : Fin 7 → ℝ => (((i j, nativeCoefficients x), x 0) : State)) ⁻¹' S := by
      ext x
      exact nativeEventPoint_mem_eventFiber S (i j) x
    change MeasurableSet {x : Fin 7 → ℝ | nativeEventPoint x ∈ eventFiber S (i j)}
    rw [hset]
    exact hm hS
  refine le_of_eq ?_
  calc
    _ = ∫⁻ q, ENNReal.ofReal |f (join q) - h (join q)| ∂((volume : Measure (Fin 3 → ℝ)).prod
          (volume : Measure (Fin 4 → ℝ))) := by
      congr 1
      funext q
      rw [nativeDensity_eq c hc i A S q, ediff_ofReal _ _ (hf0 _) (hh0 _)]
    _ = ∫⁻ x, ENNReal.ofReal |f x - h x| := by
      refine measurePreserving_join.lintegral_comp
        (f := fun x => ENNReal.ofReal |f x - h x|) ?_
      exact ENNReal.measurable_ofReal.comp ((hfm.sub hh).abs)
    _ = densityL1Distance volume h f := by
      rw [densityL1Distance]
      congr 1
      funext x
      rw [abs_sub_comm]

end Submission.Obl.k4_native_base_flattening
