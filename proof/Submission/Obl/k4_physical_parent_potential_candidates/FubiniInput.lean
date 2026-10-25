import Submission.Obl.k4_physical_parent_potential_candidates.FubiniRestoration

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MvPolynomial FubiniJets FubiniHessian

noncomputable section

/-- Coordinate jets inherit the operator norm bound without a dimension loss. -/
theorem coordinate_jet_bound {f : FubiniBase → ℝ} {n : ℕ} {x : FubiniBase} {K : ℝ}
    (hb : ‖iteratedFDeriv ℝ n f x‖ ≤ K) (α : Fin n → Fin 3) :
    |jet f n α x| ≤ K := by
  have hh := (iteratedFDeriv ℝ n f x).le_opNorm (fun i => basis (α i))
  simpa [jet, basis, EuclideanSpace.basisFun_apply, Real.norm_eq_abs] using hh.trans
    (mul_le_mul_of_nonneg_right hb (by positivity))

/-- The natural operator-norm and Hessian-determinant hypotheses imply all
conditioning assumptions used by the canonical restoration. -/
theorem hessianPatchBounds_of_norms
    {f : FubiniBase → ℝ} {K : ℝ} (hK : 1 ≤ K)
    (hb : ∀ n : ℕ, n ≤ 4 → ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
      ‖iteratedFDeriv ℝ n f x‖ ≤ K)
    (hdet : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
      K⁻¹ ≤ |(hessian f x).det|) : HessianPatchBounds f (2*K^3) := by
  have hK0 : 0 < K := by linarith
  have hK3 : K ≤ 2*K^3 := by
    have hh : K ≤ K^3 := by simpa using pow_le_pow_right₀ hK (by decide : 1 ≤ 3)
    nlinarith [pow_nonneg hK0.le 3]
  have hj (n : ℕ) (hn : n ≤ 4) (x : FubiniBase)
      (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) (α : Fin n → Fin 3) :
      |jet f n α x| ≤ 2*K^3 := (coordinate_jet_bound (hb n hn x hx) α).trans hK3
  refine {
    value := ?_
    gradient := fun x hx i => hj 1 (by decide) x hx ![i]
    hessian := fun x hx i j => hj 2 (by decide) x hx ![i,j]
    cubic := fun x hx i j k => hj 3 (by decide) x hx ![i,j,k]
    fourth := fun x hx i j k l => hj 4 (by decide) x hx ![i,j,k,l]
    inverse := ?_
  }
  · intro x hx
    simpa [jet] using hj 0 (by decide) x hx (fun i => Fin.elim0 i)
  · intro x hx i j
    have hh := Submission.Lib.K4CubicTests.matrix_inverse_three_abs_le (hessian f x) K K⁻¹
      hK0.le (inv_pos.mpr hK0)
      (fun i j => coordinate_jet_bound (hb 2 (by decide) x hx) ![i,j]) (hdet x hx) i j
    simpa [div_eq_mul_inv, pow_succ, mul_assoc] using hh

/-- Restrict any smooth graph to an open Hessian-regular neighbourhood of
its unit ball; nonvanishing is needed only on that closed ball initially. -/
theorem exists_regular_hessian_neighbourhood
    {f : FubiniBase → ℝ} {V : Set FubiniBase} (hV : IsOpen V)
    (hf : ContDiffOn ℝ 6 f V) (hdom : Metric.closedBall (0:FubiniBase) 1 ⊆ V)
    (hdet : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, (hessian f x).det ≠ 0) :
    ∃ U : Set FubiniBase, IsOpen U ∧ Metric.closedBall (0:FubiniBase) 1 ⊆ U ∧
      U ⊆ V ∧ ∀ x ∈ U, (hessian f x).det ≠ 0 := by
  let U := V ∩ interior {x | (hessian f x).det ≠ 0}
  refine ⟨U, hV.inter isOpen_interior, ?_, fun _ hx => hx.1, ?_⟩
  · intro x hx
    refine ⟨hdom hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    have hc (i j : Fin 3) : ContinuousAt (fun y => hessian f y i j) x :=
      (contDiffOn_jet hV hf (M := 0) (by norm_num) ![i,j]).continuousOn.continuousAt
        (hV.mem_nhds (hdom hx))
    have hd : ContinuousAt (fun y => (hessian f y).det) x := by
      simp only [Matrix.det_fin_three]
      fun_prop
    exact hd.preimage_mem_nhds (isOpen_ne.mem_nhds (hdet x hx))
  · intro x hx
    exact interior_subset hx.2

/-- A local quadratic certificate with the natural smoothness, jet norm,
and determinant assumptions on the graph. -/
theorem restoration_of_graph_jets
    {f : FubiniBase → ℝ} {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hf : ContDiffOn ℝ 6 f (Metric.ball (0:FubiniBase) 2))
    (hb : ∀ n : ℕ, n ≤ 4 → ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
      ‖iteratedFDeriv ℝ n f x‖ ≤ K)
    (hdet : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
      K⁻¹ ≤ |(hessian f x).det|)
    (hE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j k, |cubicError f x i j k| ≤ ε)
    (hDE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p i j k, |cubicErrorPartial f x p i j k| ≤ ε)
    (hDDE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p l i j k, |cubicErrorSecond f x p l i j k| ≤ ε)
    (hsmall : 3000000*(frameBudget (2*K^3))^9*ε ≤ 1) :
    ∃ Q : MvPolynomial (Fin 4) ℝ,
      Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ 74*(frameBudget (2*K^3))^4) ∧
      ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
        |eval (Fin.snoc (fun i => x i) (f x)) Q| ≤ 3000000*(frameBudget (2*K^3))^8*ε ∧
        (frameBudget (2*K^3))⁻¹ ≤ eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) Q) ∧
        eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) Q) ≤ 3*frameBudget (2*K^3) ∧
        |eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q))| ≤
          2*(frameBudget (2*K^3))^2 := by
  have hK0 : 0 < K := by linarith
  have hnz (x : FubiniBase) (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) :
      (hessian f x).det ≠ 0 := abs_pos.mp ((inv_pos.mpr hK0).trans_le (hdet x hx))
  obtain ⟨U, hU, hdom, hUV, hreg⟩ := exists_regular_hessian_neighbourhood Metric.isOpen_ball hf
    (Metric.closedBall_subset_ball (by norm_num : (1:ℝ) < 2)) hnz
  have hK3 : 1 ≤ 2*K^3 := by
    have hh := one_le_pow₀ hK (n := 3)
    linarith
  exact restoration_of_cubic_error hU (hf.mono hUV) hdom hreg hK3 hε
    (hessianPatchBounds_of_norms hK hb hdet) hE hDE hDDE hsmall

end

end Submission.Obl.k4_physical_parent_potential_candidates
