/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/UniformBudgets.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.SpatialBudget
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Filter

/-- The strict parameter gap pays the ordinary spatial-gradient error at
EVERY child width above the fixed preparation floor.  The q-bound is the
original atlas lower time-length bound; no current child mass is used. -/
theorem eventually_all_child_spatial_budget {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {κ u s₀ E : ℝ} (hE : 0 < E)
    (hroom : -u * s₀ + 2 * κ * (s₀ + E) ≤ -8 * E) :
    ∀ᶠ k in atTop, ∀ q w : ℝ, 0 < q → N k ^ (-E) ≤ w →
      N k ^ (-κ * (s₀ + E)) / K k ≤ q →
      14155776 * K k ^ 10 * N k ^ (-u * s₀) ≤ w * q ^ 2 := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 12 (a := -8 * E) (b := -E) (by linarith)
    (A := 14155776) (by norm_num)
  filter_upwards [hsmall] with k hk q w hq hw hqmin
  exact child_spatial_budget_of_floor (hN k) (hK k) hroom hk.le hq hw hqmin

/-- The original velocity/contact defect is negligible at every normalized
child width above the same floor. -/
theorem eventually_original_velocity_budget {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {s₀ E e₀ : ℝ} (hgap : s₀ + E < e₀) :
    ∀ᶠ k in atTop, 16 * K k ^ 4 * N k ^ (-e₀) ≤ N k ^ (-E) * N k ^ (-s₀) := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 4 (a := -e₀) (b := -(E + s₀)) (by linarith)
    (A := 16) (by norm_num)
  filter_upwards [hsmall] with k hk
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  rw [← Real.rpow_add hNp]
  convert hk.le using 1 <;> congr 1 <;> ring

end Submission.Obl.k4_horizontal_strict_parameter_step
