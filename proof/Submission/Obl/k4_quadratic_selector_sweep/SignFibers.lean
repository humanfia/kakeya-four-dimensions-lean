import Mathlib
import Submission.Obl.k4_bounded_fiber_volume

namespace Submission.Obl.k4_quadratic_selector_sweep

noncomputable section

open MvPolynomial Set

abbrev SlopeSpace := EuclideanSpace ℝ (Fin 3)

/-- Sign vectors for a relation between slopes and intercepts. -/
def graphSigns {m : ℕ} (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
    (s y : SlopeSpace) : Fin m → SignType :=
  fun i => SignType.sign (eval (Sum.elim (fun k => s k) (fun k => y k)) (p i))

/-- Affine substitution preserves a polynomial's total-degree bound. -/
theorem totalDegree_bind_affine {σ τ : Type*}
    (v : σ → MvPolynomial τ ℝ) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (p : MvPolynomial σ ℝ) : (bind₁ v p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [bind₁, aeval_monomial]
  change (C (p.coeff m) * m.support.prod (fun i => v i ^ m i)).totalDegree ≤ _
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ i ∈ m.support, (v i ^ m i).totalDegree
        ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m i) (hv i))
    _ ≤ p.totalDegree := le_totalDegree hm

/-- Insert the affine equation of a sweep fiber into graph coordinates. -/
def fiberSubstitution (t : ℝ) (x : SlopeSpace) :
    (Fin 3 ⊕ Fin 3) → MvPolynomial (Fin 3) ℝ :=
  Sum.elim X (fun i => C (x i) + C (-t) * X i)

theorem fiberSubstitution_degree (t : ℝ) (x : SlopeSpace)
    (i : Fin 3 ⊕ Fin 3) : (fiberSubstitution t x i).totalDegree ≤ 1 := by
  rcases i with i | i
  · simp [fiberSubstitution]
  · change (C (x i) + C (-t) * X i : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · simpa only [totalDegree_C, totalDegree_X, zero_add] using
        totalDegree_mul (C (-t) : MvPolynomial (Fin 3) ℝ) (X i)

theorem eval_fiberSubstitution (p : MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
    (t : ℝ) (x s : SlopeSpace) :
    eval (fun k => s k) (bind₁ (fiberSubstitution t x) p) =
      eval (Sum.elim (fun k => s k) (fun k => (x - t • s) k)) p := by
  change eval₂Hom (RingHom.id ℝ) (fun k => s k) _ =
    eval₂Hom (RingHom.id ℝ) _ p
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : (Fin 3 ⊕ Fin 3) → ℝ => eval₂Hom (RingHom.id ℝ) f p)
  funext i
  rcases i with i | i <;> simp [fiberSubstitution, sub_eq_add_neg]

/-- Isolated points are measured in the full set, which may have other components. -/
def isolatedPoints (T : Set SlopeSpace) : Set SlopeSpace :=
  {s | s ∈ T ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ T, dist z s < ε → z = s}

/-- The full sweep fiber has the same sign complexity as the selector graph. -/
theorem sweep_fiber_sign_description {m d : ℕ}
    (g : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ)
    (A : Set (Fin m → SignType)) (Sigma : Set SlopeSpace) (b : SlopeSpace → SlopeSpace)
    (hdeg : ∀ i, (g i).totalDegree ≤ d)
    (hgraph : ∀ s y, graphSigns g s y ∈ A ↔ s ∈ Sigma ∧ b s = y)
    (t : ℝ) (x : SlopeSpace) :
    ∃ p : Fin m → MvPolynomial (Fin 3) ℝ,
      (∀ i, (p i).totalDegree ≤ d) ∧
      {s | s ∈ Sigma ∧ b s + t • s = x} =
        {s : SlopeSpace | (fun i => SignType.sign (eval (fun k => s k) (p i))) ∈ A} := by
  refine ⟨fun i => bind₁ (fiberSubstitution t x) (g i), ?_, ?_⟩
  · intro i
    exact (totalDegree_bind_affine _ (fiberSubstitution_degree t x) _).trans (hdeg i)
  · ext s
    simp only [mem_ofPred_eq, eval_fiberSubstitution]
    change (s ∈ Sigma ∧ b s + t • s = x) ↔ graphSigns g s (x - t • s) ∈ A
    rw [hgraph, eq_sub_iff_add_eq]

/-- At a regular point, the inverse function theorem isolates the full fiber. -/
theorem regular_sweep_fiber_isolated (S Sigma : Set SlopeSpace)
    (b : SlopeSpace → SlopeSpace) (hS : IsOpen S) (hb : ContDiffOn ℝ 1 b S)
    (hsub : S ⊆ Sigma) (t : ℝ) (x s : SlopeSpace) (hs : s ∈ S)
    (hx : b s + t • s = x)
    (hdet : (fderiv ℝ (fun z => b z + t • z) s).det ≠ 0) :
    s ∈ isolatedPoints {z | z ∈ Sigma ∧ b z + t • z = x} := by
  have hf : ContDiffOn ℝ 1 (fun z => b z + t • z) S :=
    hb.add (contDiffOn_id.const_smul t)
  obtain ⟨V, hVo, hsV, hinj⟩ :=
    Submission.Obl.k4_bounded_fiber_volume.exists_open_injOn_of_contDiffAt_det_ne_zero
      (fun z => b z + t • z) s (hf.contDiffAt (hS.mem_nhds hs)) hdet
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo s hsV
  refine ⟨⟨hsub hs, hx⟩, ε, hε, ?_⟩
  intro z hz hzs
  exact hinj (hball hzs) hsV (hz.2.trans hx.symm)

end

end Submission.Obl.k4_quadratic_selector_sweep
