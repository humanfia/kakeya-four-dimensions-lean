import Mathlib

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/RealJets.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open Set Metric Filter
open scoped Topology

/-- Restrict a holomorphic function to the real axis, then apply a real linear map. -/
theorem iteratedDeriv_real_restriction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℂ →L[ℝ] F) {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (n : ℕ) {t : ℝ} (ht : (t : ℂ) ∈ U) :
    iteratedDeriv n (fun x : ℝ => L (g x)) t = L (iteratedDeriv n g (t : ℂ)) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hlocal : deriv (fun x : ℝ => L (g x)) =ᶠ[𝓝 t]
          (fun x : ℝ => L (deriv g x)) := by
        have hpre : (fun x : ℝ => (x : ℂ)) ⁻¹' U ∈ 𝓝 t :=
          (Complex.continuous_ofReal.tendsto t) (hU.mem_nhds ht)
        filter_upwards [hpre] with x hx
        have hd := (hg x hx).differentiableAt (hU.mem_nhds hx)
        exact (L.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt.comp_ofReal).deriv
      rw [hlocal.iteratedDeriv_eq n]
      exact ih (hg.deriv hU)

lemma contDiffOn_real_restriction {U : Set ℂ} (hU : IsOpen U) {V : Set ℝ}
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (n : WithTop ℕ∞)
    (hmap : MapsTo (fun x : ℝ => (x : ℂ)) V U) :
    ContDiffOn ℝ n (fun x : ℝ => (g x).re) V := by
  intro x hx
  exact (((hg.contDiffOn hU).contDiffAt (hU.mem_nhds (hmap hx))).real_of_complex).contDiffWithinAt

/-- Cauchy estimates control the derivatives of the real restriction as well. -/
lemma abs_iteratedDeriv_real_le {g : ℂ → ℂ} {t R C : ℝ}
    (hg : DifferentiableOn ℂ g (ball (t : ℂ) (R + 1))) (hR : 0 < R)
    (hC : ∀ z ∈ sphere (t : ℂ) R, ‖g z‖ ≤ C) (n : ℕ) :
    |iteratedDeriv n (fun x : ℝ => (g x).re) t| ≤ (n.factorial : ℝ) * C / R ^ n := by
  have hdc : DiffContOnCl ℂ g (ball (t : ℂ) R) :=
    ⟨hg.mono (ball_subset_ball (by linarith)),
      hg.continuousOn.mono (by
        rw [closure_ball _ hR.ne']
        exact closedBall_subset_ball (by linarith))⟩
  have he : iteratedDeriv n (fun x : ℝ => (g x).re) t =
      (iteratedDeriv n g (t : ℂ)).re := by
    simpa using iteratedDeriv_real_restriction Complex.reCLM isOpen_ball hg n
      (by simp; linarith)
  rw [he]
  exact (Complex.abs_re_le_norm _).trans
    (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hdc hC)

end Submission.Obl.k4_algebraic_real_jet_comparison
