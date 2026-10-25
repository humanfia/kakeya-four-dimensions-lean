import Submission.Obl.k4_scalar_grid_density_extension.GridTypical

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- A typical density cannot have a smaller exponent than a power-small upper
ceiling on the same nonnegligible selected law. -/
theorem typical_exponent_ge_of_upper {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Ω k)) (g : (k : ℕ) → Ω k → ENNReal)
    {e u : ℝ} (hmass : ¬ IsPowerSmall N (fun k => μ k univ))
    (htyp : HasTypicalDensity N μ g e)
    (hupper : ∀ τ : ℝ, 0 < τ → IsPowerSmall N (fun k =>
      μ k {x | ENNReal.ofReal (N k ^ (-u + τ)) < g k x})) : u ≤ e := by
  by_contra! he
  let τ : ℝ := (u - e) / 3
  have hτ : 0 < τ := by dsimp [τ]; linarith
  apply hmass
  have hbad : IsPowerSmall N (fun k => μ k
      {x | g k x < ENNReal.ofReal (N k ^ (-e - τ)) ∨
        ENNReal.ofReal (N k ^ (-e + τ)) < g k x}) := htyp τ hτ
  apply (hbad.add hN (hupper τ hτ)).mono
  apply Eventually.of_forall
  intro k
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro x _
  by_contra hx
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hx
  have hp := hx.1.1.trans hx.2
  have hh := Submission.Obl.k4_scalar_grid_density_extension.le_of_ofReal_rpow_le
    (by linarith [hN₂ k] : 1 < N k) hp
  dsimp [τ] at hh
  linarith

/-- Equality at the terminal depth and the intermediate upper-density
comparison transfer the original local slope cap exactly. -/
theorem cap_of_shifted_profile_comparison {f F : ℝ → ℝ} {L r α cap : ℝ}
    (hterminal : F (L - r) = f L - α)
    (hintermediate : ∀ s, 0 ≤ s → s ≤ L - r → f (r + s) - α ≤ F s)
    (hcap : ∀ t, r ≤ t → t ≤ L → f L - f t ≤ cap * (L - t)) :
    ∀ s, 0 ≤ s → s ≤ L - r → F (L - r) - F s ≤ cap * (L - r - s) := by
  intro s hs hsL
  have hi := hintermediate s hs hsL
  have hc := hcap (r + s) (by linarith) (by linarith)
  rw [hterminal]
  nlinarith

/-- The uniform ratio ceiling is exactly the terminal floor comparison after
identifying the normalized endpoint exponent. -/
theorem terminal_floor_of_ratio {N a J fL FL α ε : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hterminal : FL = fL - α)
    (hratio : J / a ≤ N ^ (α + ε)) :
    N ^ (-fL) * J ≤ N ^ ε * a * N ^ (-FL) := by
  have hJ : J ≤ N ^ (α + ε) * a := (div_le_iff₀ ha).mp hratio
  calc
    N ^ (-fL) * J ≤ N ^ (-fL) * (N ^ (α + ε) * a) :=
      mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hN.le _)
    _ = N ^ (-fL + (α + ε)) * a := by rw [← mul_assoc, ← Real.rpow_add hN]
    _ = N ^ ε * a * N ^ (-FL) := by
      rw [mul_right_comm, ← Real.rpow_add hN, hterminal]
      congr 2
      ring

end Submission.Obl.k4_remainder_pure_profile_normalization
