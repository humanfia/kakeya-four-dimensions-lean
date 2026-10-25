import Submission.Obl.k4_sign_graph_generic_c1.SmoothCover

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Submission.Obl.k4_sign_graph_generic_c1

abbrev graphIndex : (Fin 3 ⊕ Fin 3) ≃ Fin 6 := finSumFinEquiv

/-- The slope coordinates of a six-dimensional graph point. -/
def graphBase : (Fin 6 → ℝ) →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k =>
      ContinuousLinearMap.proj (graphIndex (Sum.inl k)))

/-- The value coordinates of a six-dimensional graph point. -/
def graphValue : (Fin 6 → ℝ) →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k =>
      ContinuousLinearMap.proj (graphIndex (Sum.inr k)))

/-- A pair of Euclidean three-vectors, written in six ordinary coordinates. -/
def graphPoint (s y : Space) : Fin 6 → ℝ :=
  fun j => Sum.elim (fun k : Fin 3 => s k) (fun k : Fin 3 => y k)
    (graphIndex.symm j)

@[simp] theorem graphBase_graphPoint (s y : Space) : graphBase (graphPoint s y) = s := by
  ext k
  simp [graphBase, graphPoint]

@[simp] theorem graphValue_graphPoint (s y : Space) : graphValue (graphPoint s y) = y := by
  ext k
  simp [graphValue, graphPoint]

/-- Polynomial graph sign conditions are analytic functions of six real coordinates. -/
theorem analyticOnNhd_graph_polynomial (p : MvPolynomial (Fin 3 ⊕ Fin 3) ℝ) :
    AnalyticOnNhd ℝ
      (fun x : Fin 6 → ℝ => MvPolynomial.eval (fun j => x (graphIndex j)) p)
      univ := by
  let L : (Fin 3 ⊕ Fin 3) → (Fin 6 → ℝ) →L[ℝ] ℝ :=
    fun j => ContinuousLinearMap.proj (graphIndex j)
  exact AnalyticOnNhd.eval_continuousLinearMap' L p

/-- Converts a smooth cover of the coordinate sign graph into the exact generic-C1 conclusion. -/
theorem exists_open_c1_of_coordinate_sign_graph_cover
    {m : ℕ} {p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ}
    {B : Set (Fin m → SignType)} {Sigma : Set Space} {b : Space → Space}
    (hgraph : ∀ s y : Space,
      (fun i => SignType.sign (MvPolynomial.eval
        (Sum.elim (fun k : Fin 3 => s k) (fun k : Fin 3 => y k)) (p i))) ∈ B ↔
        s ∈ Sigma ∧ b s = y)
    {ι : Type*} [Countable ι] (d : ι → ℕ)
    (U : ∀ i, Set (Fin (d i) → ℝ))
    (φ : ∀ i, (Fin (d i) → ℝ) → (Fin 6 → ℝ))
    (hU : ∀ i, IsOpen (U i))
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (U i))
    (himage : ∀ i x, x ∈ U i →
      (fun k => SignType.sign (MvPolynomial.eval
        (fun j => φ i x (graphIndex j)) (p k))) ∈ B)
    (hcover : ∀ x : Fin 6 → ℝ,
      (fun k => SignType.sign (MvPolynomial.eval
        (fun j => x (graphIndex j)) (p k))) ∈ B → ∃ i z, z ∈ U i ∧ φ i z = x) :
    ∃ S : Set Space, IsOpen S ∧ ContDiffOn ℝ 1 b S ∧ S ⊆ Sigma ∧
      volume (Sigma \ S) = 0 := by
  apply exists_open_c1_of_countable_smooth_graph_cover d U
    (fun i => graphBase ∘ φ i) (fun i => graphValue ∘ φ i) Sigma b hU
  · intro i
    exact graphBase.contDiff.comp_contDiffOn (hφ i)
  · intro i
    exact graphValue.contDiff.comp_contDiffOn (hφ i)
  · intro i x hx
    apply (hgraph _ _).mp
    dsimp only [Function.comp_apply]
    have heq : Sum.elim
        (fun k : Fin 3 => graphBase (φ i x) k)
        (fun k : Fin 3 => graphValue (φ i x) k) =
        (fun j => φ i x (graphIndex j)) := by
      funext j
      cases j <;> rfl
    rw [heq]
    exact himage i x hx
  · intro s hs
    have hpoint :
        (fun k => SignType.sign (MvPolynomial.eval
          (fun j => graphPoint s (b s) (graphIndex j)) (p k))) ∈ B := by
      simpa [graphPoint] using (hgraph s (b s)).mpr ⟨hs, rfl⟩
    obtain ⟨i, z, hz, heq⟩ := hcover (graphPoint s (b s)) hpoint
    refine mem_iUnion.mpr ⟨i, z, hz, ?_⟩
    change graphBase (φ i z) = s
    rw [heq, graphBase_graphPoint]

end Submission.Obl.k4_sign_graph_generic_c1
