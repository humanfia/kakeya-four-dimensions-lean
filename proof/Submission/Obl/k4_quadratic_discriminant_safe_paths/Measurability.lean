import Mathlib

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric MeasureTheory

abbrev RealSpace := EuclideanSpace ℝ (Fin 3)
abbrev ComplexSpace := EuclideanSpace ℂ (Fin 3)

def emb (x : RealSpace) : ComplexSpace :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

theorem continuous_emb : Continuous emb := by
  unfold emb
  fun_prop

def brokenPath (a x : RealSpace) (τ : ℂ) : Set ComplexSpace :=
  segment ℝ (emb a) (emb a + τ • (emb x - emb a)) ∪
    segment ℝ (emb a + τ • (emb x - emb a)) (emb x)

/-- An arbitrary target set meets an open tube around moving segments on an open
set of parameters. No regularity of the target set is needed. -/
theorem isOpen_tube_hits {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : X → E) (ha : Continuous a) (hb : Continuous b)
    (r : ℝ) (U : Set E) :
    IsOpen {p | ∃ z ∈ thickening r (segment ℝ (a p) (b p)), z ∈ U} := by
  have heq : {p | ∃ z ∈ thickening r (segment ℝ (a p) (b p)), z ∈ U} =
      ⋃ z ∈ U, ⋃ t ∈ Icc (0 : ℝ) 1,
        {p | dist z ((1 - t) • a p + t • b p) < r} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_thickening_iff, segment_eq_image,
      mem_image]
    constructor
    · rintro ⟨z, ⟨w, ⟨t, ht, rfl⟩, hdist⟩, hz⟩
      exact ⟨z, hz, t, ht, hdist⟩
    · rintro ⟨z, hz, t, ht, hdist⟩
      exact ⟨z, ⟨_, ⟨t, ht, rfl⟩, hdist⟩, hz⟩
  rw [heq]
  apply isOpen_iUnion
  intro z
  apply isOpen_iUnion
  intro hz
  apply isOpen_iUnion
  intro t
  apply isOpen_iUnion
  intro ht
  exact isOpen_lt (continuous_const.dist
    ((ha.const_smul (1 - t)).add (hb.const_smul t))) continuous_const

def badSet (a : RealSpace) (P P' : MvPolynomial (Fin 3) ℝ) (r : ℝ) :
    Set (RealSpace × ℂ) :=
  {p | p.1 ∈ closedBall (0 : RealSpace) (1 / 8) ∧
    p.2 ∈ closedBall (1 / 2 : ℂ) (1 / 4) ∧
    ∃ z ∈ thickening r (brokenPath a p.1 p.2),
      ‖MvPolynomial.eval (fun i => z i) (P.map (algebraMap ℝ ℂ))‖ < r ∨
      ‖MvPolynomial.eval (fun i => z i) (P'.map (algebraMap ℝ ℂ))‖ < r}

theorem measurableSet_badSet (a : RealSpace)
    (P P' : MvPolynomial (Fin 3) ℝ) (r : ℝ) :
    MeasurableSet (badSet a P P' r) := by
  let U : Set ComplexSpace :=
    {z | ‖MvPolynomial.eval (fun i => z i) (P.map (algebraMap ℝ ℂ))‖ < r ∨
      ‖MvPolynomial.eval (fun i => z i) (P'.map (algebraMap ℝ ℂ))‖ < r}
  have hc : Continuous (fun p : RealSpace × ℂ => emb p.1) :=
    continuous_emb.comp continuous_fst
  have hb : Continuous (fun p : RealSpace × ℂ =>
      emb a + p.2 • (emb p.1 - emb a)) := by fun_prop
  have h₁ := isOpen_tube_hits (fun _ : RealSpace × ℂ => emb a)
    (fun p => emb a + p.2 • (emb p.1 - emb a)) continuous_const hb r U
  have h₂ := isOpen_tube_hits
    (fun p : RealSpace × ℂ => emb a + p.2 • (emb p.1 - emb a))
    (fun p => emb p.1) hb hc r U
  have heq : badSet a P P' r =
      ((closedBall (0 : RealSpace) (1 / 8)) ×ˢ
        (closedBall (1 / 2 : ℂ) (1 / 4))) ∩
      ({p | ∃ z ∈ thickening r (segment ℝ (emb a)
          (emb a + p.2 • (emb p.1 - emb a))), z ∈ U} ∪
       {p | ∃ z ∈ thickening r (segment ℝ
          (emb a + p.2 • (emb p.1 - emb a)) (emb p.1)), z ∈ U}) := by
    ext p
    change (_ ∧ _ ∧ ∃ z, z ∈ thickening r (_ ∪ _) ∧ z ∈ U) ↔
      ((_ ∧ _) ∧ ((∃ z, z ∈ thickening r _ ∧ z ∈ U) ∨
        (∃ z, z ∈ thickening r _ ∧ z ∈ U)))
    rw [thickening_union]
    constructor
    · rintro ⟨hx, hτ, z, hz, hU⟩
      exact ⟨⟨hx, hτ⟩, hz.elim (fun h => Or.inl ⟨z, h, hU⟩)
        (fun h => Or.inr ⟨z, h, hU⟩)⟩
    · rintro ⟨⟨hx, hτ⟩, h⟩
      rcases h with ⟨z, hz, hU⟩ | ⟨z, hz, hU⟩
      · exact ⟨hx, hτ, z, Or.inl hz, hU⟩
      · exact ⟨hx, hτ, z, Or.inr hz, hU⟩
  rw [heq]
  exact (isClosed_closedBall.measurableSet.prod isClosed_closedBall.measurableSet).inter
    (h₁.union h₂).measurableSet

end Submission.Obl.k4_quadratic_discriminant_safe_paths
