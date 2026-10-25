import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Jets

/-! Taylor estimates for restrictions to radial segments. -/

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivatives of a radial restriction are diagonal contractions of the full jet. -/
lemma line_iteratedDeriv {n : ℕ} {f : E → ℝ} {s : Set E}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n f s) (u : E) {t : ℝ}
    (ht : t • u ∈ s) {j : ℕ} (hj : j ≤ n) :
    iteratedDeriv j (fun t : ℝ => f (t • u)) t =
      iteratedFDeriv ℝ j f (t • u) (fun _ => u) := by
  let g : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight u
  have hopen : IsOpen (g ⁻¹' s) := hs.preimage g.continuous
  have hg : g t ∈ s := ht
  have he := g.iteratedFDerivWithin_comp_right hf hs.uniqueDiffOn hopen.uniqueDiffOn hg
    (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen j hopen hg,
    iteratedFDerivWithin_of_isOpen j hs hg] at he
  change (iteratedFDeriv ℝ j (f ∘ g) t) (fun _ => 1) = _
  rw [he]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, g]

lemma norm_smul_le_one {u : E} (hu : ‖u‖ ≤ 1) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖t • u‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg u)).trans (by simpa using hu)

/-- Taylor's estimate on the unit ball, with the full derivative norm as remainder bound. -/
theorem abs_sub_radial_taylor_le {n : ℕ} (hn : 0 < n) {f : E → ℝ}
    (hf : ContDiffOn ℝ n f (Metric.ball (0 : E) 3)) {B : ℝ}
    (hB : ∀ v ∈ Metric.closedBall (0 : E) 1, ‖iteratedFDeriv ℝ n f v‖ ≤ B)
    {u : E} (hu : u ∈ Metric.closedBall (0 : E) 1) :
    |f u - ∑ j ∈ Finset.range n,
      iteratedFDeriv ℝ j f 0 (fun _ => u) / (j.factorial : ℝ)| ≤
        B / (n.factorial : ℝ) := by
  have hu' : ‖u‖ ≤ 1 := by simpa using hu
  let g : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight u
  let U : Set ℝ := g ⁻¹' Metric.ball (0 : E) 3
  have hU : IsOpen U := Metric.isOpen_ball.preimage g.continuous
  have hfU : ContDiffOn ℝ n (fun t : ℝ => f (t • u)) U :=
    hf.comp_continuousLinearMap g
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, t • u ∈ Metric.closedBall (0 : E) 1 := by
    intro t ht
    simpa using norm_smul_le_one hu' ht
  have hseg : uIcc (0 : ℝ) 1 ⊆ U := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    change g t ∈ Metric.ball (0 : E) 3
    simpa [g, Metric.mem_ball, dist_zero_right] using
      lt_of_le_of_lt (norm_smul_le_one hu' ht') (by norm_num : (1 : ℝ) < 3)
  have hbound : ∀ t ∈ uIcc (0 : ℝ) 1,
      |iteratedDeriv n (fun t : ℝ => f (t • u)) t| ≤ B := by
    intro t ht
    have hball : t • u ∈ Metric.ball (0 : E) 3 := hseg ht
    rw [line_iteratedDeriv Metric.isOpen_ball hf u (t := t) hball le_rfl]
    calc
      |iteratedFDeriv ℝ n f (t • u) (fun _ => u)| ≤
          ‖iteratedFDeriv ℝ n f (t • u)‖ * ‖u‖ ^ n := by
        simpa using (iteratedFDeriv ℝ n f (t • u)).le_opNorm (fun _ => u)
      _ ≤ B * 1 := mul_le_mul (hB _ (hline t (by simpa using ht)))
        (pow_le_one₀ (norm_nonneg u) hu') (by positivity) (by
          exact (norm_nonneg _).trans (hB 0 (by simp)))
      _ = B := mul_one B
  have h := Submission.Obl.k4_matching_switching_target_certificate.taylor_iteratedDeriv_bound
    hU hfU hseg hbound (j := 0) hn
  simp only [iteratedDeriv_zero, one_smul, Nat.sub_zero, zero_add, sub_zero, abs_one,
    one_pow, mul_one] at h
  convert h using 2
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  have hj' : j ≤ n := (Finset.mem_range.mp hj).le
  simpa using (line_iteratedDeriv Metric.isOpen_ball hf u
    (t := 0) (by simp) hj').symm

/-- In particular, a third derivative bound controls the quadratic Taylor error. -/
theorem abs_sub_quadratic_taylor_le {f : E → ℝ}
    (hf : ContDiffOn ℝ 3 f (Metric.ball (0 : E) 3)) {B : ℝ}
    (hB : ∀ v ∈ Metric.closedBall (0 : E) 1, ‖iteratedFDeriv ℝ 3 f v‖ ≤ B)
    {u : E} (hu : u ∈ Metric.closedBall (0 : E) 1) :
    |f u - (f 0 + fderiv ℝ f 0 u + iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2)| ≤ B / 6 := by
  simpa [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    Nat.factorial] using abs_sub_radial_taylor_le (by norm_num : 0 < 3) hf hB hu

end Submission.Obl.k4_seven_direction_local_degree_restoration
