/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 28c9ca5,
Submission/Obl/k4_scalar_mesh_projection/SwitchTimes.lean.
-/

import Mathlib

namespace Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory

/-- The triangular change from endpoint times to consecutive signed
increments, before translating the fixed starting time. -/
def incrementLinearEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun t := ![t 0, t 1 - t 0, t 2 - t 1, t 3 - t 2]
  invFun δ := ![δ 0, δ 0 + δ 1, δ 0 + δ 1 + δ 2, δ 0 + δ 1 + δ 2 + δ 3]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

theorem incrementLinearEquiv_det :
    LinearMap.det (incrementLinearEquiv : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) = 1 := by
  rw [← LinearMap.det_toMatrix']
  let M : Matrix (Fin 4) (Fin 4) ℝ :=
    !![1, 0, 0, 0; -1, 1, 0, 0; 0, -1, 1, 0; 0, 0, -1, 1]
  have hm : LinearMap.toMatrix'
      (incrementLinearEquiv : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) = M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix'_apply, incrementLinearEquiv, M]
  have htri : M.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> simp_all [M]
  rw [hm, Matrix.det_of_isLowerTriangular M htri]
  norm_num [M, Fin.prod_univ_succ]

def signedIncrements (start : ℝ) (t : Fin 4 → ℝ) : Fin 4 → ℝ :=
  incrementLinearEquiv t - ![start, 0, 0, 0]

theorem signedIncrements_apply (start : ℝ) (t : Fin 4 → ℝ) :
    signedIncrements start t = ![t 0 - start, t 1 - t 0, t 2 - t 1, t 3 - t 2] := by
  ext i
  fin_cases i <;> simp [signedIncrements, incrementLinearEquiv]

theorem measurePreserving_incrementLinearEquiv :
    MeasurePreserving incrementLinearEquiv := by
  have hm : Measurable incrementLinearEquiv :=
    incrementLinearEquiv.toContinuousLinearEquiv.continuous.measurable
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hm hS]
  have h := volume.addHaar_image_linearMap
    (incrementLinearEquiv : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (incrementLinearEquiv ⁻¹' S)
  change volume (incrementLinearEquiv '' (incrementLinearEquiv ⁻¹' S)) =
    ENNReal.ofReal |LinearMap.det
      (incrementLinearEquiv : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))| *
        volume (incrementLinearEquiv ⁻¹' S) at h
  rw [Set.image_preimage_eq S incrementLinearEquiv.surjective,
    incrementLinearEquiv_det, abs_one, ENNReal.ofReal_one, one_mul] at h
  exact h.symm

/-- Signed increments have the same Lebesgue density ceiling as endpoint
times. In particular, taking increments does not assert independence of a
law after conditioning it on path success. -/
theorem measurePreserving_signedIncrements (start : ℝ) :
    MeasurePreserving (signedIncrements start) := by
  change MeasurePreserving
    (fun t : Fin 4 → ℝ => incrementLinearEquiv t - ![start, 0, 0, 0])
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_right volume (-(![start, 0, 0, 0] : Fin 4 → ℝ))).comp
      measurePreserving_incrementLinearEquiv

theorem map_signedIncrements_le (start : ℝ) (μ : Measure (Fin 4 → ℝ))
    (C : ENNReal) (hμ : μ ≤ C • volume) :
    μ.map (signedIncrements start) ≤ C • volume := by
  have h := Measure.map_mono hμ (measurePreserving_signedIncrements start).measurable
  rw [Measure.map_smul, (measurePreserving_signedIncrements start).map_eq] at h
  exact h
  exact (measurePreserving_signedIncrements start).measurable.aemeasurable

theorem signedIncrements_mem_cube {a h start : ℝ}
    (hstart : start ∈ Icc a (a + h)) (t : Fin 4 → ℝ)
    (ht : ∀ i, t i ∈ Icc a (a + h)) :
    signedIncrements start t ∈ Icc (fun _ => -h) (fun _ => h) := by
  rw [signedIncrements_apply]
  constructor <;> intro i <;> fin_cases i <;> simp <;>
    linarith [(ht 0).1, (ht 0).2, (ht 1).1, (ht 1).2,
      (ht 2).1, (ht 2).2, (ht 3).1, (ht 3).2, hstart.1, hstart.2]

end Submission.Lib.K4ScalarSwitching.Switching
