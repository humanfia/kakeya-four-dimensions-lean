import Mathlib

open Filter

namespace Submission.Obl.k4_affine_skew_row_fit

/-- All fixed losses in the edge-to-row recovery fit inside the requested power. -/
theorem exists_recovery_budget {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      1 ≤ N ^ δ ∧
      23328 * (N ^ δ) ^ 12 ≤ N ^ ε ∧
      81 * (N ^ δ) ^ 6 ≤ N ^ ε ∧
      N ^ (-ε) ≤ 1 / (3 * (N ^ δ) ^ 2) := by
  let δ : ℝ := ε / 48
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ ε := by dsimp [δ]; linarith
  have ht : ∀ᶠ N : ℝ in atTop, (23328 : ℝ) ≤ N ^ δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop _)
  obtain ⟨M, hM⟩ := eventually_atTop.mp ht
  refine ⟨δ, hδ, hδle, max 2 M, le_max_left _ _, ?_⟩
  intro N hN
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by linarith
  let K := N ^ δ
  have hKbig : 23328 ≤ K := hM N ((le_max_right _ _).trans hN)
  have hK : 1 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hpower : K ^ 48 = N ^ ε := by
    dsimp [K]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1
    dsimp [δ]
    ring
  have hcoef : 23328 * K ^ 12 ≤ N ^ ε := by
    calc
      _ ≤ K * K ^ 12 := mul_le_mul_of_nonneg_right hKbig (by positivity)
      _ = K ^ 13 := by ring
      _ ≤ K ^ 48 := pow_le_pow_right₀ hK (by omega)
      _ = _ := hpower
  have herr : 81 * K ^ 6 ≤ N ^ ε := by
    calc
      _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = K ^ 7 := by ring
      _ ≤ K ^ 48 := pow_le_pow_right₀ hK (by omega)
      _ = _ := hpower
  have hden : 3 * K ^ 2 ≤ N ^ ε := by
    calc
      _ ≤ K * K ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = K ^ 3 := by ring
      _ ≤ K ^ 48 := pow_le_pow_right₀ hK (by omega)
      _ = _ := hpower
  refine ⟨hK, hcoef, herr, ?_⟩
  rw [Real.rpow_neg hNpos.le]
  simpa only [one_div] using one_div_le_one_div_of_le
    (by positivity : 0 < 3 * K ^ 2) hden

/-- Fine-mesh powers are exactly fixed powers of the ambient scale. -/
theorem mesh_rpow {N : ℝ} (hN : 0 < N) (a t : ℝ) :
    (N ^ (-a)) ^ t = N ^ (-a * t) :=
  (Real.rpow_mul hN.le (-a) t).symm

theorem mesh_negative_rpow {N : ℝ} (hN : 0 < N) (a t : ℝ) :
    (N ^ (-a)) ^ (-t) = N ^ (a * t) := by
  rw [mesh_rpow hN]
  congr 1
  ring

/-- The common loss budget dominates all smaller exponents supplied by the graph engine. -/
theorem mesh_loss_le {N a t δ : ℝ} (hN : 1 ≤ N) (hat : a * t ≤ δ) :
    (N ^ (-a)) ^ (-t) ≤ N ^ δ := by
  rw [mesh_negative_rpow (by linarith : 0 < N)]
  exact Real.rpow_le_rpow_of_exponent_le hN hat

end Submission.Obl.k4_affine_skew_row_fit
