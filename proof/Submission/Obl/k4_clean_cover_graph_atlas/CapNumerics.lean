-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b,
-- Submission/Obl/k4_greedy_cover_graph_atlas/CapNumerics.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/CapNumerics.lean.

import Mathlib

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- The original prior floor cancels the determinant in the common candidate cap.
No normalization by the candidate's own incidence mass occurs. -/
theorem candidate_cap_prior_cancellation {N n a fri fq τtail u τ J κ prior : ℝ}
    (hN : 1 ≤ N) (hn : 0 ≤ n) (hcount : n ≤ N ^ a)
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (hκ : 0 < κ) (hp : 0 ≤ prior)
    (hprior : N ^ (-fri) * J / κ ≤ prior) :
    n * (N ^ (-fq + τtail) * (16 * (1 + (N ^ u) ^ 2)) * (τ * J)) ≤
      (τ * prior) * (32 * κ) * N ^ (a + fri - fq + τtail + 2 * u) := by
  have hNpos : 0 < N := by linarith
  have hU : 1 ≤ N ^ u := Real.one_le_rpow hN hu
  have hbins : 16 * (1 + (N ^ u) ^ 2) ≤ 32 * (N ^ u) ^ 2 := by nlinarith
  have hdet : J ≤ prior * κ * N ^ fri := by
    have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ hκ).mp hprior)
      (Real.rpow_pos_of_pos hNpos fri).le
    have hc : N ^ fri * (N ^ (-fri) * J) = J := by
      rw [← mul_assoc, ← Real.rpow_add hNpos, add_neg_cancel, Real.rpow_zero, one_mul]
    rw [hc] at hm
    convert hm using 1 <;> ring
  have hpower : N ^ (a + fri - fq + τtail + 2 * u) =
      N ^ a * N ^ (-fq + τtail) * (N ^ u) ^ 2 * N ^ fri := by
    have he : a + fri - fq + τtail + 2 * u = (a + (-fq + τtail) + u * 2) + fri := by ring
    rw [he, Real.rpow_add hNpos _ fri, Real.rpow_add hNpos _ (u * 2),
      Real.rpow_add hNpos a (-fq + τtail), Real.rpow_mul hNpos.le u 2, Real.rpow_two]
  calc
    _ ≤ N ^ a * (N ^ (-fq + τtail) * (32 * (N ^ u) ^ 2) *
        (τ * (prior * κ * N ^ fri))) := by gcongr
    _ = _ := by rw [hpower]; ring

/-- The actual gain exponent disappears after the fixed-depth profile increment. -/
theorem candidate_cap_exponent_cancellation {d h ρ gain L ε δ0 τtail fri fq : ℝ}
    (hprofile : d * h * L - 5 * δ0 * L ≤ fq - fri) :
    ((d * h + 4 * ρ * gain) * L + 4 * ε) + fri - fq + τtail +
        2 * (4 * ρ * gain * L + 4 * ε) ≤
      (12 * ρ * gain + 5 * δ0) * L + 12 * ε + τtail := by
  nlinarith

/-- A common marginal ceiling times the candidate count is charged to the original
packet scale, with only the small profile and fit slacks remaining. -/
theorem candidate_cap_uniform_budget {N n d h ρ gain L ε δ0 τtail fri fq τ J κ prior : ℝ}
    (hN : 1 ≤ N) (hn : 0 ≤ n)
    (hcount : n ≤ N ^ ((d * h + 4 * ρ * gain) * L + 4 * ε))
    (hslack : 0 ≤ 4 * ρ * gain * L + 4 * ε)
    (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (hκ : 0 < κ) (hp : 0 ≤ prior)
    (hprior : N ^ (-fri) * J / κ ≤ prior)
    (hprofile : d * h * L - 5 * δ0 * L ≤ fq - fri) :
    n * (N ^ (-fq + τtail) * (16 * (1 + (N ^ (4 * ρ * gain * L + 4 * ε)) ^ 2)) * (τ * J)) ≤
      (τ * prior) * (32 * κ) *
        N ^ ((12 * ρ * gain + 5 * δ0) * L + 12 * ε + τtail) := by
  apply (candidate_cap_prior_cancellation hN hn hcount hslack hτ hJ hκ hp hprior).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hN (candidate_cap_exponent_cancellation hprofile))
    (by positivity)

/-- A candidate's original relative floor dominates its normalized base ceiling
by an amount independent of its own mass. The chart determinant and time length cancel. -/
theorem candidate_projection_floor_algebra
    {N J len prior κ fri fq a τ u : ℝ}
    (hN : 0 < N) (hJ : 0 ≤ J) (hlen : 0 < len) (hκ : 0 < κ)
    (hprior : N ^ (-fri) * J / κ ≤ prior) :
    (32 * N ^ (-fq + τ + 2 * u) * (J / len)) *
        (N ^ (fq - fri - a - τ - 2 * u) / (64 * κ)) ≤
      N ^ (-a) / (2 * len) * prior := by
  have he : (32 * N ^ (-fq + τ + 2 * u) * (J / len)) *
        (N ^ (fq - fri - a - τ - 2 * u) / (64 * κ)) =
      N ^ (-a) / (2 * len) * (N ^ (-fri) * J / κ) := by
    have hp : N ^ (-fq + τ + 2 * u) * N ^ (fq - fri - a - τ - 2 * u) =
        N ^ (-a) * N ^ (-fri) := by
      rw [← Real.rpow_add hN, ← Real.rpow_add hN]
      congr 1
      ring
    field_simp
    nlinarith [hp]
  rw [he]
  exact mul_le_mul_of_nonneg_left hprior (by positivity)

/-- The projection loss after the dimension/profile cancellation. -/
theorem candidate_projection_loss_exponent
    {d h ρ gain L ε δ₀ τ fri fq : ℝ}
    (hprofile : d * h * L - 5 * δ₀ * L ≤ fq - fri) :
    -((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ) ≤
      fq - fri - ((d * h + 4 * ρ * gain) * L + 4 * ε) - τ -
        2 * (4 * ρ * gain * L + 4 * ε) := by
  nlinarith

/-- A uniform original projection floor for every raw candidate, before any subbox
is selected. It uses the full old-packet prior and the fixed-menu profile increment. -/
theorem original_candidate_projection_floor
    {N J len prior κ d h ρ gain L ε δ₀ τ fri fq : ℝ}
    (hN : 1 ≤ N) (hJ : 0 ≤ J) (hlen : 0 < len) (hκ : 0 < κ)
    (hprior : N ^ (-fri) * J / κ ≤ prior)
    (hprofile : d * h * L - 5 * δ₀ * L ≤ fq - fri) :
    (32 * N ^ (-fq + τ + 2 * (4 * ρ * gain * L + 4 * ε)) * (J / len)) *
        (N ^ (-((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ)) / (64 * κ)) ≤
      N ^ (-((d * h + 4 * ρ * gain) * L + 4 * ε)) / (2 * len) * prior := by
  have hN0 : 0 < N := by linarith
  apply le_trans ?_ (candidate_projection_floor_algebra (fq := fq) (τ := τ)
    (u := 4 * ρ * gain * L + 4 * ε) (a := (d * h + 4 * ρ * gain) * L + 4 * ε)
    hN0 hJ hlen hκ hprior)
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hN
    (candidate_projection_loss_exponent hprofile)

/-- The old packet's retained saturation floor controls its original projection
before subbox refinement. Its only profile loss is the old menu-depth tolerance. -/
theorem old_packet_projection_floor
    {N J len κ fri fq loss τ : ℝ}
    (hN : 1 ≤ N) (hJ : 0 ≤ J) (hlen : 0 < len) (hκ : 0 < κ)
    (hprofile : fri - fq ≤ loss) :
    (32 * κ ^ 2 * N ^ (-fq + τ) * (J / len)) *
        (N ^ (-loss - τ) / (64 * κ ^ 3)) ≤
      N ^ (-fri) * J / (2 * len * κ) := by
  have hN0 : 0 < N := by linarith
  have he : (32 * κ ^ 2 * N ^ (-fq + τ) * (J / len)) *
        (N ^ (-loss - τ) / (64 * κ ^ 3)) =
      N ^ (-fq - loss) * J / (2 * len * κ) := by
    have hp : N ^ (-fq + τ) * N ^ (-loss - τ) = N ^ (-fq - loss) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    field_simp
    nlinarith [hp]
  rw [he]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hJ

end Submission.Obl.k4_clean_cover_graph_atlas
