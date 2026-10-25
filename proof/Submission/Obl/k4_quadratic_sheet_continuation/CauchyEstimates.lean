import Mathlib

/-!
# Quantitative estimates for complex Fréchet derivatives

Iterating the first-order Schwarz estimate on concentric balls controls the
operator norms of all fixed Fréchet derivatives. Constants are deliberately
loose; only their independence from the function and radius matters here.
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Set Metric Filter
open scoped Topology ContDiff

/-- The first Fréchet derivative is bounded by twice the supremum norm divided
by the radius. -/
theorem norm_fderiv_le_of_ball_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {a : E} {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball a r))
    (hM : ∀ z ∈ ball a r, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f a‖ ≤ 2 * M / r := by
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball hf _ hr
  intro z hz
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_sub_le _ _).trans (by linarith [hM z hz, hM a (mem_ball_self hr)])

/-- On an open set the iterated Fréchet derivatives of a smooth function are
complex differentiable. -/
theorem differentiableOn_iteratedFDeriv_of_isOpen
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℂ ∞ f U) (j : ℕ) :
    DifferentiableOn ℂ (iteratedFDeriv ℂ j f) U := by
  have hd := hf.differentiableOn_iteratedFDerivWithin (m := j) (by exact_mod_cast ENat.natCast_lt_top j)
    hU.uniqueDiffOn
  exact hd.congr (fun z hz => (iteratedFDerivWithin_of_isOpen j hU hz).symm)

/-- For each fixed order, a bound on a ball controls the derivative at its
center, with the expected inverse power of the radius. -/
theorem exists_iteratedFDeriv_ball_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
        [NormedAddCommGroup F] [NormedSpace ℂ F]
        (f : E → F) (a : E) (r M : ℝ), 0 < r → 0 ≤ M →
        ContDiffOn ℂ ∞ f (ball a (2 * r)) →
        (∀ z ∈ ball a r, ‖f z‖ ≤ M) →
        ‖iteratedFDeriv ℂ j f a‖ ≤ C * M / r ^ j := by
  induction j with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro E F _ _ _ _ f a r M hr hM hf hb
    simpa only [norm_iteratedFDeriv_zero, pow_zero, div_one, one_mul] using
      hb a (mem_ball_self hr)
  | succ j ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    refine ⟨4 * 2 ^ j * C, by positivity, ?_⟩
    intro E F _ _ _ _ f a r M hr hM hf hb
    let B := C * M / (r / 2) ^ j
    have hB (z : E) (hz : z ∈ ball a (r / 2)) :
        ‖iteratedFDeriv ℂ j f z‖ ≤ B := by
      apply hbound f z (r / 2) M (by positivity) hM
      · apply hf.mono
        intro w hw
        have hdist := dist_triangle w z a
        rw [mem_ball] at hz hw ⊢
        linarith
      · intro w hw
        apply hb w
        have hdist := dist_triangle w z a
        rw [mem_ball] at hz hw ⊢
        linarith
    have hd : DifferentiableOn ℂ (iteratedFDeriv ℂ j f) (ball a (r / 2)) :=
      (differentiableOn_iteratedFDeriv_of_isOpen isOpen_ball hf j).mono
        (ball_subset_ball (by linarith))
    have hder := norm_fderiv_le_of_ball_bound (by positivity : 0 < r / 2) hd hB
    rw [norm_fderiv_iteratedFDeriv] at hder
    calc
      ‖iteratedFDeriv ℂ (j + 1) f a‖ ≤ 2 * B / (r / 2) := hder
      _ = (4 * 2 ^ j * C) * M / r ^ (j + 1) := by
        dsimp [B]
        rw [div_pow, pow_succ]
        field_simp
        ring

end Submission.Obl.k4_quadratic_sheet_continuation
