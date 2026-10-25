/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/LinearScalar.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/LinearScalar.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

section Linear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If a vector forms a basis with all but one of the old basis vectors, its
coordinate in the omitted direction is nonzero. -/
theorem basis_repr_ne_zero_of_independent_delete
    (b : Module.Basis (Fin 3) ℝ E) (v : E) (i : Fin 3)
    (h : LinearIndependent ℝ (Fin.snoc (fun j : Fin 2 => b (i.succAbove j)) v)) :
    b.repr v i ≠ 0 := by
  intro hz
  apply (linearIndependent_finSnoc.mp h).2
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range (fun j : Fin 2 => b (i.succAbove j)))
  have hsum : ∑ j : Fin 3, b.repr v j • b j ∈ S := by
    apply Submodule.sum_mem
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [hz]
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨k, congrArg b hk⟩
  exact (b.sum_repr v) ▸ hsum

/-- Three basis eigenvectors and a fourth eigenvector with no zero coordinate
force a linear map to be scalar. -/
theorem linearMap_eq_scalar_of_basis_eigenvectors
    (b : Module.Basis (Fin 3) ℝ E) (f : E →ₗ[ℝ] E)
    (v : E) (hv : ∀ i, b.repr v i ≠ 0) (r : Fin 3 → ℝ) (s : ℝ)
    (hb : ∀ i, f (b i) = r i • b i) (hfv : f v = s • v) :
    f = s • LinearMap.id := by
  have hexp : f v = ∑ i : Fin 3, b.repr v i • (r i • b i) := by
    calc
      f v = f (∑ i : Fin 3, b.repr v i • b i) := congrArg f (b.sum_repr v).symm
      _ = _ := by simp only [map_sum, map_smul, hb]
  have hr (i : Fin 3) : r i = s := by
    have h := congrArg (fun z => b.repr z i) hfv
    rw [hexp] at h
    simp [map_sum, map_smul, smul_eq_mul, Finsupp.single_apply] at h
    apply mul_right_cancel₀ (hv i)
    nlinarith [h]
  apply b.ext
  intro i
  simp [hb i, hr i]

/-- Four projectively general eigenvectors determine a scalar endomorphism. -/
theorem linearMap_eq_scalar_of_four_eigenvectors
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    (p : Fin 4 → E)
    (hp : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → LinearIndependent ℝ ![p i, p j, p k])
    (f : E →ₗ[ℝ] E) (r : Fin 4 → ℝ) (hf : ∀ i, f (p i) = r i • p i) :
    f = r 3 • LinearMap.id := by
  have hvec : (fun i : Fin 3 => p i.castSucc) = ![p 0, p 1, p 2] := by
    funext i
    fin_cases i <;> simp
  have hlin : LinearIndependent ℝ (fun i : Fin 3 => p i.castSucc) := by
    rw [hvec]
    exact hp 0 1 2 (by decide) (by decide) (by decide)
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E := by simp [hdim]
  let b : Module.Basis (Fin 3) ℝ E := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hb (i : Fin 3) : b i = p i.castSucc :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin hcard) i
  have hv (i : Fin 3) : b.repr (p 3) i ≠ 0 := by
    apply basis_repr_ne_zero_of_independent_delete b (p 3) i
    have hp' := hp (i.succAbove 0).castSucc (i.succAbove 1).castSucc 3
      (fun h => (by simpa using Fin.succAbove_right_injective (Fin.castSucc_injective 3 h) : False))
      (Fin.castSucc_lt_last _).ne (Fin.castSucc_lt_last _).ne
    convert hp' using 1
    funext j
    fin_cases j <;> simp [hb, Fin.snoc]
  exact linearMap_eq_scalar_of_basis_eigenvectors b f (p 3) hv
    (fun i => r i.castSucc) (r 3) (fun i => by simpa only [hb] using hf i.castSucc) (hf 3)

end Linear

/-- Vanishing pairwise cross-relations make a vector proportional to a nonzero vector. -/
theorem exists_smul_of_cross_relations (g v : Fin 3 → ℝ) (hg : g ≠ 0)
    (hcross : ∀ j k : Fin 3, g k * v j = g j * v k) :
    ∃ r : ℝ, v = r • g := by
  obtain ⟨k, hk⟩ : ∃ k, g k ≠ 0 := by
    by_contra! h
    apply hg
    funext i
    exact h i
  refine ⟨v k / g k, funext fun j => ?_⟩
  change v j = (v k / g k) * g j
  field_simp [hk]
  nlinarith [hcross j k]

/-- A linear vector field parallel to an invertible linear field at four general
points is a scalar multiple of that field. -/
theorem linearMap_proportional_of_four_cross_tests
    (p : Fin 4 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → LinearIndependent ℝ ![p i, p j, p k])
    (hp0 : ∀ i, p i ≠ 0)
    (B : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (A : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hcross : ∀ i : Fin 4, ∀ j k : Fin 3,
      B (p i) k * A (p i) j = B (p i) j * A (p i) k) :
    ∃ r : ℝ, A = r • B.toLinearMap := by
  have hB0 (i : Fin 4) : B (p i) ≠ 0 := by
    intro h
    apply hp0 i
    apply B.injective
    simpa using h
  choose r hr using fun i => exists_smul_of_cross_relations (B (p i)) (A (p i)) (hB0 i) (hcross i)
  let f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := B.symm.toLinearMap.comp A
  have hf (i : Fin 4) : f (p i) = r i • p i := by
    simp [f, hr i]
  have hscalar := linearMap_eq_scalar_of_four_eigenvectors (by simp) p hp f r hf
  refine ⟨r 3, ?_⟩
  apply LinearMap.ext
  intro x
  have h := congrArg B (LinearMap.congr_fun hscalar x)
  simpa [f] using h

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
