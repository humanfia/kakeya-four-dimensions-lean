import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.HolomorphicBounds
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry

namespace Submission.Obl.k4_algebraic_sheet_remez

open Set Metric
open Submission.Obl.k4_algebraic_real_jet_comparison

/-- Real restrictions along a unit ray are smooth on a fixed neighborhood. -/
theorem contDiffOn_slice {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 4))
    (x v : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ (1 : ℝ) / 2)
    (hv : ‖v‖ ≤ 1) (q : WithTop ℕ∞) :
    ContDiffOn ℝ q
      (fun t : ℝ => (f (realEmbedding n x + (t : ℂ) • realEmbedding n v)).re)
      (Ioo (-2 : ℝ) 2) := by
  have hg : DifferentiableOn ℂ
      (fun t : ℂ => f (realEmbedding n x + t • realEmbedding n v)) (ball 0 3) := by
    apply hf.comp (show Differentiable ℂ
      (fun t : ℂ => realEmbedding n x + t • realEmbedding n v) by fun_prop).differentiableOn
    intro t ht
    rw [mem_ball, dist_zero_right] at ht ⊢
    have hnorm := norm_add_le (realEmbedding n x) (t • realEmbedding n v)
    rw [norm_smul, LinearIsometry.norm_map, LinearIsometry.norm_map] at hnorm
    have hmul := mul_le_of_le_one_right (norm_nonneg t) hv
    linarith
  apply contDiffOn_real_restriction isOpen_ball hg
  intro t ht
  rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_lt.mpr ht).trans (by norm_num : (2 : ℝ) < 3)

/-- Along a segment that stays in the half-ball, Cauchy's estimate has a
geometric decay factor strictly below one after division by the factorial. -/
theorem slice_derivative_decay {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 4)) {M : ℝ}
    (hbound : ∀ z, ‖z‖ ≤ 2 → ‖f z‖ ≤ M)
    (x v : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ (1 : ℝ) / 2)
    (hv : ‖v‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (hend : ‖x + T • v‖ ≤ (1 : ℝ) / 2) (q : ℕ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      |iteratedDeriv q
        (fun s : ℝ => (f (realEmbedding n x + (s : ℂ) • realEmbedding n v)).re) t|
        ≤ (q.factorial : ℝ) * M * (4 / 5 : ℝ) ^ q := by
  intro t ht
  have hpos := norm_line_le_of_endpoints x v hT ht hx hend
  have hin : ‖realEmbedding n x + (t : ℂ) • realEmbedding n v‖ + (5 : ℝ) / 4 ≤ 2 := by
    rw [← realEmbedding_line, LinearIsometry.norm_map]
    linarith
  have hh := directional_real_jet_bound hf hbound (realEmbedding n x) (realEmbedding n v)
    (by simpa only [LinearIsometry.norm_map] using hv) t
    (by norm_num : (0 : ℝ) < 5 / 4) hin q
  convert hh using 1
  rw [div_eq_mul_inv ((q.factorial : ℝ) * M) ((5 / 4 : ℝ) ^ q), ← inv_pow]
  norm_num

end Submission.Obl.k4_algebraic_sheet_remez
