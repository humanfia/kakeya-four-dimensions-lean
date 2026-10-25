import Submission.Lib.K4MeshListRecovery.MassDiagonal

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open Filter

noncomputable def restrictionLoss (N K ε : ℕ → ℝ) (k : ℕ) : ℝ :=
  2 * ε k + 2 * (Real.log (K k) / Real.log (N k))

lemma restrictionLoss_bounds (N K ε : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hK : ∀ k, 1 ≤ K k) (hε : ∀ k, 0 < ε k) (k : ℕ) :
    0 < restrictionLoss N K ε k ∧ ε k ≤ restrictionLoss N K ε k := by
  have hlog : 0 ≤ Real.log (K k) / Real.log (N k) :=
    div_nonneg (Real.log_nonneg (hK k)) (Real.log_nonneg (by linarith [hN k]))
  dsimp [restrictionLoss]
  constructor <;> linarith [hε k]

lemma restrictionLoss_tendsto_zero (N K ε : ℕ → ℝ)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, K k ≤ N k ^ η)
    (hεt : Tendsto ε atTop (nhds 0)) :
    Tendsto (restrictionLoss N K ε) atTop (nhds 0) := by
  have hlog := Submission.Lib.K4MeshListRecovery.subpower_log_ratio_tendsto_zero N K hNt hK hsub
  change Tendsto (fun k => 2 * ε k + 2 * (Real.log (K k) / Real.log (N k))) atTop (nhds 0)
  simpa only [mul_zero, add_zero] using
    (hεt.const_mul 2).add (hlog.const_mul 2)

lemma rpow_log_ratio {N K : ℝ} (hN : 1 < N) (hK : 0 < K) :
    N ^ (Real.log K / Real.log N) = K := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < N)]
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  rw [mul_div_cancel₀ _ hlog, Real.exp_log hK]

lemma restrictionLoss_power (N K ε : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hK : ∀ k, 1 ≤ K k) (k : ℕ) :
    N k ^ (-restrictionLoss N K ε k) = N k ^ (-2 * ε k) / K k ^ (2 : ℕ) := by
  have hN0 : 0 < N k := by linarith [hN k]
  have hK0 : 0 < K k := by linarith [hK k]
  have hlog := rpow_log_ratio (by linarith [hN k] : 1 < N k) hK0
  have he : N k ^ (-(2 * (Real.log (K k) / Real.log (N k)))) = (K k ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hN0.le, mul_comm (2 : ℝ), Real.rpow_mul hN0.le, hlog]
    norm_cast
  rw [restrictionLoss, neg_add, Real.rpow_add hN0, he, div_eq_mul_inv]
  congr 2
  ring

end Submission.Obl.k4_scalar_normalized_exact_refinement
