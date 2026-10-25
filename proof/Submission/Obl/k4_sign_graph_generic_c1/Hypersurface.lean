import Mathlib

noncomputable section

open Set Filter Module
open scoped Topology ContDiff

namespace Submission.Obl.k4_sign_graph_generic_c1

/-- A regular analytic level set is locally covered by an analytic map with fewer parameters.
The chart may be chosen to take values in any prescribed neighborhood. -/
theorem exists_analytic_hypersurface_chart
    {n : ℕ} {q : (Fin n → ℝ) → ℝ} {a : Fin n → ℝ} {U : Set (Fin n → ℝ)}
    (hq : AnalyticAt ℝ q a) (hqa : q a = 0) (hD : fderiv ℝ q a ≠ 0) (hU : U ∈ 𝓝 a) :
    ∃ (d : ℕ) (_ : d < n) (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → (Fin n → ℝ))
      (V : Set (Fin n → ℝ)),
      IsOpen W ∧ AnalyticOnNhd ℝ φ W ∧ MapsTo φ W U ∧ IsOpen V ∧ a ∈ V ∧
        ∀ x ∈ V, q x = 0 → x ∈ φ '' W := by
  classical
  let D := fderiv ℝ q a
  have hDlin : D.toLinearMap ≠ 0 := by
    intro h
    apply hD
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun T : (Fin n → ℝ) →ₗ[ℝ] ℝ => T x) h
  have hsurj : D.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hDlin
  let hker := D.ker_closedComplemented_of_finiteDimensional_range
  let hs := hq.hasStrictFDerivAt
  let P := HasStrictFDerivAt.implicitFunctionDataOfComplemented q D hs hsurj hker
  let d := finrank ℝ D.ker
  have hd : d < n := by
    have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hDlin
    simp only [Module.finrank_fin_fun] at hdim
    dsimp [d]
    omega
  let e : (Fin d → ℝ) ≃L[ℝ] D.ker := ContinuousLinearEquiv.ofFinrankEq (by simp [d])
  let φ : (Fin d → ℝ) → (Fin n → ℝ) := fun y => P.implicitFunction 0 (e y)
  have hPa : P.rightFun a = 0 := by simp [P]
  have hPprod : P.prodFun P.pt = (0, 0) := by simp [P, ImplicitFunctionData.prodFun, hqa]
  have hφ0 : φ 0 = a := by
    change P.implicitFunction 0 (e 0) = a
    rw [map_zero]
    change hs.implicitFunctionOfComplemented q D hsurj hker 0 0 = a
    simpa only [hqa] using hs.implicitFunctionOfComplemented_apply_image hsurj hker
  have hPc : ContDiffAt ℝ ω P.implicitFunction.uncurry (0, 0) := by
    rw [← hPprod]
    apply ImplicitFunctionData.contDiffAt_implicitFunction
    · exact hq.contDiffAt
    · dsimp [P]
      fun_prop
    · simp
  have hφc : ContDiffAt ℝ ω φ 0 := by
    have hpair : ContDiffAt ℝ ω (fun y : Fin d → ℝ => ((0 : ℝ), e y)) 0 := by fun_prop
    have hPc' : ContDiffAt ℝ ω P.implicitFunction.uncurry
        ((fun y : Fin d → ℝ => ((0 : ℝ), e y)) 0) := by simpa using hPc
    exact ContDiffAt.comp (g := P.implicitFunction.uncurry)
      (f := fun y : Fin d → ℝ => ((0 : ℝ), e y)) 0 hPc' hpair
  have hφan : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), AnalyticAt ℝ φ y :=
    (hφc.eventually (by simp)).mono fun _ h => h.analyticAt
  have hφU : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), φ y ∈ U := by
    apply hφc.continuousAt.preimage_mem_nhds
    simpa only [hφ0] using hU
  obtain ⟨W, hW, hWo, hW0⟩ := eventually_nhds_iff.mp (hφan.and hφU)
  have hcoordc : ContinuousAt (fun x => e.symm (P.rightFun x)) a := by
    dsimp [P]
    fun_prop
  have hcoord0 : e.symm (P.rightFun a) = 0 := by rw [hPa, map_zero]
  have hcoordW : ∀ᶠ x in 𝓝 a, e.symm (P.rightFun x) ∈ W := by
    apply hcoordc.preimage_mem_nhds
    simpa only [hcoord0] using hWo.mem_nhds hW0
  obtain ⟨V, hV, hVo, hVa⟩ := eventually_nhds_iff.mp
    (P.implicitFunction_apply_image.and hcoordW)
  refine ⟨d, hd, W, φ, V, hWo, (fun y hy => (hW y hy).1),
    (fun y hy => (hW y hy).2), hVo, hVa, ?_⟩
  intro x hx hqx
  refine ⟨e.symm (P.rightFun x), (hV x hx).2, ?_⟩
  change P.implicitFunction 0 (e (e.symm (P.rightFun x))) = x
  rw [e.apply_symm_apply]
  have hleft := (hV x hx).1
  change P.implicitFunction (q x) (P.rightFun x) = x at hleft
  rwa [hqx] at hleft

end Submission.Obl.k4_sign_graph_generic_c1
