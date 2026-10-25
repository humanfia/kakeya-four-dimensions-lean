-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/TimedFiberFits.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.BinnedFiberFits

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set

/-- Bins stay in normalized time. The fiber model is obtained by the
actual affine time substitution, preserving its degree. -/
theorem exists_timed_fiber_polynomial_of_common_bins {Ω X Y : Type*}
    (A : Set Ω) (cell : Ω → X × Y) (v : X → ℝ) (offset : Y → ℝ)
    (f : X → Y → ℝ) (G : Ω → ℝ) (P : Ω → Polynomial ℝ)
    (D : ℕ) (ε Bt E₀ E₁ : ℝ) (hε : 0 < ε) (hBt : 1 ≤ Bt)
    (hdegree : ∀ ω ∈ A, (P ω).natDegree ≤ D)
    (htime : ∀ ω ∈ A, |offset (cell ω).2+v (cell ω).1| ≤ Bt)
    (hfield : ∀ ω ∈ A, |f (cell ω).1 (cell ω).2-G ω| ≤ E₀)
    (hfit : ∀ ω ∈ A, |G ω-(P ω).eval (offset (cell ω).2+v (cell ω).1)| ≤ E₁)
    (hbins : ∀ ω ∈ A, ∀ ω' ∈ A, (cell ω).2=(cell ω').2 →
      ∀ k : Fin (D+1), ⌊(P ω).coeff k/ε⌋=⌊(P ω').coeff k/ε⌋) :
    ∀ y, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      ∀ x, (∃ ω ∈ A, cell ω=(x,y)) →
        |f x y-p.eval (v x)| ≤ E₀+E₁+2*((D : ℝ)+1)*ε*Bt^D := by
  classical
  intro y
  by_cases hex : ∃ ω ∈ A, (cell ω).2=y
  · obtain ⟨ω₀,hω₀,hy₀⟩ := hex
    let q := (P ω₀).comp (Polynomial.X+Polynomial.C (offset y))
    have hq : q.natDegree ≤ D := by
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
      exact hdegree ω₀ hω₀
    refine ⟨q,hq,?_⟩
    intro x hx
    obtain ⟨ω,hω,hcell⟩ := hx
    have hsame : (cell ω).2=(cell ω₀).2 := by simpa only [hcell] using hy₀.symm
    have ht := htime ω hω
    rw [hcell] at ht
    have hpoly := polynomial_eval_difference_of_common_bins D (P ω) (P ω₀)
      (hdegree ω hω) (hdegree ω₀ hω₀) ε Bt hε hBt (hbins ω hω ω₀ hω₀ hsame)
      (offset y+v x) ht
    have hf := hfield ω hω
    have hp := hfit ω hω
    rw [hcell] at hf hp
    have heval : q.eval (v x)=(P ω₀).eval (offset y+v x) := by
      simp only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, add_comm]
    rw [heval]
    exact (abs_sub_le (f x y) (G ω) ((P ω₀).eval (offset y+v x))).trans
      (add_le_add hf ((abs_sub_le (G ω) ((P ω).eval (offset y+v x))
        ((P ω₀).eval (offset y+v x))).trans (add_le_add hp hpoly))) |>.trans_eq (by ring)
  · refine ⟨0,by simp,?_⟩
    intro x hx
    obtain ⟨ω,hω,hcell⟩ := hx
    exact (hex ⟨ω,hω,by rw [hcell]⟩).elim

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
