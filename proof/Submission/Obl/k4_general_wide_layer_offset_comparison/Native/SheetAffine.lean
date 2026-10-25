-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/SheetAffine.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0864, commit 5c0e35361a930b6b45f8a28b47b4450b032af8f9,
   Submission/Obl/k4_finite_projected_horizontal_candidates/SheetAffine.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.NativeMeshAlgebra

/-!
# Sheets under real affine changes of the base

A native sheet of a true label lives in that label's frame (`SheetOn`). The comparison runs in
the normalized coordinates of a common cell. `SheetOn.isSheet_affine` composes a frame sheet
with a real affine map `v ↦ b + M v` (`M` invertible) sending the complex ball of radius `4` into
the frame ball: the result is an `IsSheet` of the same degree, bounded by the frame bound.
`lipschitz_of_bounded` turns that bound into the Lipschitz bound on the real ball of radius
`1/2` used for jittering inside comparison cells (accepted o149 `holomorphic_inner_lipschitz`).
`isSheet_cev` is the constructor for polynomial sheets (projected labels).
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set MvPolynomial

noncomputable section

/-- Affine substitution does not increase the total degree (any commutative ring; adapted from
accepted o033 `k4_eligibility_sign_description.degree_aeval_le`). -/
theorem degree_aeval_le' {R : Type*} [CommRing R] {σ τ : Type*} (p : MvPolynomial τ R)
    (f : τ → MvPolynomial σ R) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  change (MvPolynomial.C (p.coeff d) * ∏ i ∈ d.support, f i ^ d i).totalDegree ≤ p.totalDegree
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ d.support, (f i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

/-! ### The complexified affine map -/

/-- The complexified real affine map `v ↦ b + M v`. -/
def affC (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (v : EuclideanSpace ℂ (Fin 3)) :
    EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun i => (b i : ℂ) + ∑ j, (M i j : ℂ) * v j)

/-- The real affine map. -/
def affR (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => b i + ∑ j, M i j * x j)

theorem affC_emb (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    affC b M (emb x) = emb (affR b M x) := by
  ext i
  simp [affC, affR, emb]

theorem differentiable_affC (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Differentiable ℂ (affC b M) := by
  have h : affC b M = fun v => (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)).symm
      (fun i => (b i : ℂ) + ∑ j, (M i j : ℂ) * v j) := rfl
  rw [h]
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.differentiable.comp
  rw [differentiable_pi]
  intro i
  apply (differentiable_const _).add
  apply Differentiable.fun_sum
  intro j _
  exact (differentiable_const _).mul
    ((PiLp.proj 2 (fun _ : Fin 3 => ℂ) j).differentiable)

/-- The substitution polynomials of the affine map, with the hidden variable kept. -/
def affSub (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : Fin 4 → MvPolynomial (Fin 4) ℂ :=
  Fin.lastCases (X (Fin.last 3))
    (fun i : Fin 3 => C (b i : ℂ) + ∑ j : Fin 3, C (M i j : ℂ) * X (Fin.castSucc j))

theorem affSub_last (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    affSub b M (Fin.last 3) = X (Fin.last 3) := by
  unfold affSub; rw [Fin.lastCases_last]

theorem affSub_castSucc (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    affSub b M i.castSucc = C (b i : ℂ) + ∑ j : Fin 3, C (M i j : ℂ) * X (Fin.castSucc j) := by
  unfold affSub; rw [Fin.lastCases_castSucc]

theorem affSub_degree (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 4) :
    (affSub b M i).totalDegree ≤ 1 := by
  induction i using Fin.lastCases with
  | last => rw [affSub_last, totalDegree_X]
  | cast i =>
    rw [affSub_castSucc]
    refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_X]

theorem eval_affSub (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (v : EuclideanSpace ℂ (Fin 3)) (t : ℂ) (i : Fin 4) :
    eval (Fin.snoc (fun j : Fin 3 => v j) t) (affSub b M i) =
      (Fin.snoc (fun j : Fin 3 => (affC b M v) j) t : Fin 4 → ℂ) i := by
  induction i using Fin.lastCases with
  | last => rw [affSub_last, eval_X, Fin.snoc_last, Fin.snoc_last]
  | cast i =>
    rw [affSub_castSucc, Fin.snoc_castSucc]
    simp only [eval_add, eval_C, eval_sum, eval_mul, eval_X, Fin.snoc_castSucc, affC]

/-- The relation pulled back by the affine map. -/
def affRel (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (R : MvPolynomial (Fin 4) ℂ) :
    MvPolynomial (Fin 4) ℂ :=
  aeval (affSub b M) R

theorem eval_affRel (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (R : MvPolynomial (Fin 4) ℂ)
    (v : EuclideanSpace ℂ (Fin 3)) (t : ℂ) :
    eval (Fin.snoc (fun j : Fin 3 => v j) t) (affRel b M R) =
      eval (Fin.snoc (fun j : Fin 3 => (affC b M v) j) t) R := by
  unfold affRel
  induction R using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval_mul, eval_mul, hp, aeval_X, eval_X, eval_affSub]

theorem affRel_degree (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (R : MvPolynomial (Fin 4) ℂ) : (affRel b M R).totalDegree ≤ R.totalDegree :=
  degree_aeval_le' R (affSub b M) (affSub_degree b M)

/-- The complexified affine map of an invertible matrix is onto. -/
theorem affC_surjective (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det)
    (z : EuclideanSpace ℂ (Fin 3)) : ∃ v, affC b M v = z := by
  set Mi := M⁻¹ with hMi
  have hMM : M * Mi = 1 := Matrix.mul_nonsing_inv M hM
  refine ⟨WithLp.toLp 2 (fun j => ∑ k, (Mi j k : ℂ) * (z k - (b k : ℂ))), ?_⟩
  ext i
  simp only [affC]
  have h1 : ∑ j, (M i j : ℂ) * ∑ k, (Mi j k : ℂ) * (z k - (b k : ℂ)) =
      ∑ k, (∑ j, (M i j : ℂ) * (Mi j k : ℂ)) * (z k - (b k : ℂ)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    ring
  have h2 : ∀ k, (∑ j, (M i j : ℂ) * (Mi j k : ℂ)) = ((1 : Matrix (Fin 3) (Fin 3) ℝ) i k : ℂ) := by
    intro k
    rw [← hMM, Matrix.mul_apply]
    push_cast
    rfl
  simp only [PiLp.toLp_apply] at *
  rw [h1]
  simp_rw [h2]
  simp only [Matrix.one_apply, apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one,
    Complex.ofReal_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem affRel_ne_zero (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : IsUnit M.det)
    {R : MvPolynomial (Fin 4) ℂ} (hR : R ≠ 0) : affRel b M R ≠ 0 := by
  intro h
  apply hR
  apply MvPolynomial.funext
  intro x
  obtain ⟨v, hv⟩ := affC_surjective b M hM (WithLp.toLp 2 (fun j : Fin 3 => x (Fin.castSucc j)))
  have hx : x = Fin.snoc (fun j : Fin 3 => (affC b M v) j) (x (Fin.last 3)) := by
    rw [hv]
    funext i
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]
    | cast j => rw [Fin.snoc_castSucc]
  have := eval_affRel b M R v (x (Fin.last 3))
  rw [h, map_zero, ← hx] at this
  rw [← this, map_zero]

/-! ### Composition -/

/-- **A frame sheet in common coordinates.** -/
theorem SheetOn.isSheet_affine {R : MvPolynomial (Fin 4) ℂ} {g : EuclideanSpace ℂ (Fin 3) → ℂ}
    {c : EuclideanSpace ℝ (Fin 3)} {r V : ℝ} (h : SheetOn R g c r V) (hR : R ≠ 0) {D : ℕ}
    (hRd : R.totalDegree ≤ D) (b : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : IsUnit M.det)
    (hball : ∀ v ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, affC b M v ∈ ball (emb c) r) :
    IsSheet D (fun v => g (affC b M v)) ∧
      ∀ v ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, ‖g (affC b M v)‖ ≤ V := by
  obtain ⟨hd, hrel, hbd, hreal⟩ := h
  refine ⟨⟨affRel b M R, affRel_ne_zero b M hM hR, (affRel_degree b M R).trans hRd, ?_, ?_, ?_⟩,
    fun v hv => hbd _ (hball v hv)⟩
  · intro v hv
    exact (hd.differentiableAt (isOpen_ball.mem_nhds (hball v hv))).comp v
      ((differentiable_affC b M) v) |>.differentiableWithinAt
  · intro v hv
    rw [eval_affRel]
    exact hrel _ (hball v hv)
  · intro x hx
    have hxb : emb x ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4 := by
      rw [mem_ball, dist_zero_right, norm_emb]; linarith
    have hin := hball _ hxb
    rw [affC_emb, mem_ball, dist_emb, dist_eq_norm] at hin
    show (g (affC b M (emb x))).im = 0
    rw [affC_emb]
    exact hreal _ hin

/-- **Lipschitz bound** on the real ball of radius `1/2` from a bound on the complex ball. -/
theorem lipschitz_of_bounded {f : EuclideanSpace ℂ (Fin 3) → ℂ} {V : ℝ} (hV : 0 ≤ V)
    (hf : DifferentiableOn ℂ f (ball 0 4)) (hb : ∀ v ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      ‖f v‖ ≤ V) :
    LipschitzOnWith ⟨4 * V, by positivity⟩ (fun x : EuclideanSpace ℝ (Fin 3) => f (emb x))
      (closedBall 0 (1 / 2)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [mem_closedBall, dist_zero_right] at hx hy
  have hb2 : ∀ z : EuclideanSpace ℂ (Fin 3), ‖z‖ ≤ 2 → ‖f z‖ ≤ V := fun z hz =>
    hb z (by rw [mem_ball, dist_zero_right]; linarith)
  have h := Submission.Obl.k4_algebraic_real_jet_comparison.holomorphic_inner_lipschitz hf hb2
    (x := emb y) (y := emb x) (by rw [norm_emb]; linarith) (by rw [norm_emb]; linarith)
  show dist (f (emb x)) (f (emb y)) ≤ 4 * V * dist x y
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖f (emb x) - f (emb y)‖ ≤ 4 * V * ‖emb x - emb y‖ := h
    _ = 4 * V * ‖x - y‖ := by rw [← emb_sub, norm_emb]

/-- **Polynomial sheets.** A real base polynomial of degree `≤ 2` is a sheet of degree `2`. -/
theorem isSheet_cev {G : MvPolynomial (Fin 3) ℝ} (hG : G.totalDegree ≤ 2) :
    IsSheet 2 (cev G) := by
  refine ⟨relLin G, relLin_ne_zero G, ?_, (differentiable_cev G).differentiableOn, ?_, ?_⟩
  · unfold relLin
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_X]; norm_num
    · exact (totalDegree_renameMap_le G).trans hG
  · intro z _; rw [eval_relLin, sub_self]
  · intro x _; rw [cev_emb]; exact Complex.ofReal_im _

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
