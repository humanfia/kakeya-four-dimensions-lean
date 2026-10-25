/- Adapted from this LOT tree, obligation o202, session x0952,
branch x0952 at 0d95340d1d1b9c2275f07ef34537d5922f0aef11, file `Submission/Obl/k4_horizontal_subcritical_rate_candidates/Native/PreparationNumerics.lean`.
Only the finest-mesh theorem is used; its original provenance is retained. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics
import Submission.Obl.k4_horizontal_strict_parameter_step.ComparisonMeshStatement

/-!
Pure power estimates for the native comparison constructor from this LOT tree,
obligation o245, session x0852, commita653e961, file
k4_horizontal_interior_parameter_bootstrap/NativeComparisonPreparation.lean.
The constructor itself is not repeated here. These estimates verify its finest
mesh and original witness hypotheses uniformly over bounded depths.
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Filter

/-- A single fixed buffer controls the finest mesh error at all the subsequent
coarse, hidden and matching depths. The original subpower constant is unchanged. -/
theorem eventually_finest_mesh_error
    {N K : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hKsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {sMax e₀ R : ℝ} (hsMax : 0 < sMax)
    (he₀ : 100 * sMax ≤ e₀) (hR : 100 * sMax ≤ R) :
    ∀ᶠ k in atTop, ∀ s u ε zexp : ℝ,
      0 ≤ s → s ≤ sMax → 0 ≤ u → u ≤ 1 → ε ≤ sMax → zexp ≤ sMax →
      (200 * (N k ^ ε + 8 * K k ^ 4 * (1 + 6 * K k)) / N k ^ (-u * s)) *
        (N k ^ (-e₀) + K k * N k ^ (-R)) ≤ N k ^ (-s) * N k ^ (-zexp) := by
  have hev := hNt.eventually
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      22800 (a := -93 * sMax) (b := -2 * sMax) (by linarith))
  filter_upwards [hKsmall sMax hsMax, hev] with k hk hbudget
  intro s u ε zexp hs hs' hu hu' hε hzexp
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hN0 : 0 < N k := by linarith [hN k]
  let X : ℝ := N k ^ sMax
  let w : ℝ := N k ^ (-100 * sMax)
  have hX : 1 ≤ X := Real.one_le_rpow hN1 hsMax.le
  have hX0 : 0 ≤ X := by linarith
  have hK0 : 0 ≤ K k := by linarith [hK k]
  have hw0 : 0 ≤ w := Real.rpow_nonneg hN0.le _
  have hεX : N k ^ ε ≤ X := Real.rpow_le_rpow_of_exponent_le hN1 hε
  have hχ : N k ^ (-e₀) ≤ w := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hδ : N k ^ (-R) ≤ w := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hDinv : (N k ^ (-u * s))⁻¹ ≤ X := by
    rw [← Real.rpow_neg hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    nlinarith only [mul_le_mul_of_nonneg_right hu' hs, hs']
  have hB : N k ^ ε + 8 * K k ^ 4 * (1 + 6 * K k) ≤ 57 * X ^ 5 := by
    have hX5 : X ≤ X ^ 5 := by simpa using pow_le_pow_right₀ hX (show 1 ≤ 5 by norm_num)
    calc
      _ ≤ X + 8 * X ^ 4 * (7 * X) := by gcongr <;> linarith only [hk, hX]
      _ ≤ 57 * X ^ 5 := by nlinarith only [hX5]
  have herror : N k ^ (-e₀) + K k * N k ^ (-R) ≤ 2 * X * w := by
    calc
      _ ≤ w + X * w := add_le_add hχ (mul_le_mul hk hδ (by positivity) hX0)
      _ ≤ 2 * X * w := by nlinarith only [mul_le_mul_of_nonneg_right hX hw0]
  calc
    _ ≤ (200 * (57 * X ^ 5) * X) * (2 * X * w) := by
      rw [div_eq_mul_inv]
      gcongr
    _ = 22800 * X ^ 7 * w := by ring
    _ = 22800 * N k ^ (-93 * sMax) := by
      dsimp [X, w]
      rw [← Real.rpow_mul_natCast hN0.le, mul_assoc, ← Real.rpow_add hN0]
      congr 2
      ring
    _ ≤ N k ^ (-2 * sMax) := hbudget
    _ ≤ N k ^ (-s) * N k ^ (-zexp) := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

theorem uniformComparisonMesh : UniformComparisonMesh := by
  intro N K hN hNt hK hsub sMax e₀ R hsMax he₀ hR
  filter_upwards [eventually_finest_mesh_error hN hNt hK hsub hsMax he₀ hR] with k hk
  intro s u ε E hs hsMax hu hu1 hε hεMax hE hEMax
  exact hk s u ε E hs hsMax hu hu1 hεMax hEMax

end Submission.Obl.k4_horizontal_strict_parameter_step
