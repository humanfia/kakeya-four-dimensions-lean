import Mathlib

noncomputable section

open Set Filter Module
open scoped Topology ContDiff

namespace Submission.Obl.k4_sign_graph_generic_c1

/-- A coordinate of an iterated derivative, with all arguments in the standard basis. -/
def partialComponent {n : ℕ} (f : (Fin n → ℝ) → ℝ) (k : ℕ) (v : Fin k → Fin n)
    (x : Fin n → ℝ) : ℝ :=
  iteratedFDeriv ℝ k f x (fun j => Pi.single (v j) 1)

/-- A nonzero analytic germ has a nonzero iterated derivative. -/
theorem exists_iteratedFDeriv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {a : E} (hf : AnalyticAt ℝ f a)
    (hne : ¬ f =ᶠ[𝓝 a] 0) : ∃ k, iteratedFDeriv ℝ k f a ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, r, hp⟩ := hf
  apply hne
  filter_upwards [hp.eventually_hasSum_sub] with x hx
  have hpzero : ∀ k, p k (fun _ => x - a) = 0 := by
    intro k
    have heq := hp.factorial_smul (x - a) k
    rw [h k, zero_apply] at heq
    simpa only [nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, Nat.factorial_ne_zero,
      false_or] using heq
  apply hx.unique
  simp only [hpzero, Pi.zero_apply]
  exact hasSum_zero

/-- Nonzero multilinear maps on a finite coordinate space are nonzero on some tuple of basis
vectors. -/
theorem exists_basis_component_ne_zero {n k : ℕ}
    (T : (Fin n → ℝ) [×k]→L[ℝ] ℝ) (hT : T ≠ 0) :
    ∃ v : Fin k → Fin n, T (fun j => Pi.single (v j) 1) ≠ 0 := by
  by_contra h
  push Not at h
  apply hT
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin k => Pi.basisFun ℝ (Fin n))
  intro v
  simpa using h v

/-- At any nonflat zero of an analytic function, a coordinate of one of its iterated derivatives
vanishes and has a nonzero derivative. -/
theorem exists_regular_partialComponent {n : ℕ} {f : (Fin n → ℝ) → ℝ} {a : Fin n → ℝ}
    (hf : AnalyticAt ℝ f a) (ha : f a = 0) (hne : ¬ f =ᶠ[𝓝 a] 0) :
    ∃ (k : ℕ) (v : Fin k → Fin n),
      partialComponent f k v a = 0 ∧ fderiv ℝ (partialComponent f k v) a ≠ 0 := by
  classical
  obtain h := exists_iteratedFDeriv_ne_zero hf hne
  let m := Nat.find h
  have hm : iteratedFDeriv ℝ m f a ≠ 0 := Nat.find_spec h
  have hmlow : ∀ j < m, iteratedFDeriv ℝ j f a = 0 := by
    intro j hj
    exact not_ne_iff.mp (Nat.find_min h hj)
  have hmpos : 0 < m := by
    by_contra hm0
    have hmzero : m = 0 := by omega
    apply hm
    rw [hmzero]
    apply ContinuousMultilinearMap.ext
    intro v
    simpa only [iteratedFDeriv_zero_apply, zero_apply] using ha
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
  rw [hk] at hm hmlow
  obtain ⟨v, hv⟩ := exists_basis_component_ne_zero (iteratedFDeriv ℝ (k + 1) f a) hm
  refine ⟨k, Fin.tail v, ?_, ?_⟩
  · unfold partialComponent
    rw [hmlow k (Nat.lt_succ_self k), zero_apply]
  · intro hzero
    apply hv
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) a :=
      (hf.contDiffAt : ContDiffAt ℝ ω f a).differentiableAt_iteratedFDeriv (by simp)
    rw [hd.iteratedFDeriv_succ_apply_left']
    change fderiv ℝ (partialComponent f k (Fin.tail v)) a (Pi.single (v 0) 1) = 0
    rw [hzero, zero_apply]


/-- Coordinate derivatives of analytic functions are analytic on the same domain. -/
theorem analyticOnNhd_partialComponent {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} (hf : AnalyticOnNhd ℝ f U) (k : ℕ) (v : Fin k → Fin n) :
    AnalyticOnNhd ℝ (partialComponent f k v) U := by
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin n → ℝ) ℝ
    (fun j => Pi.single (v j) 1)
  exact ev.comp_analyticOnNhd (hf.iteratedFDeriv k)

end Submission.Obl.k4_sign_graph_generic_c1
