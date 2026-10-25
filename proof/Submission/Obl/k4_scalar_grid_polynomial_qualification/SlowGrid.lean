import Submission.Lib.K4ModelReduction.Diagonal
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Filter
open Submission.Lib.K4ModelReduction
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_profile_density_bounds

/-- Choose one slowly growing grid so that all its fixed-stage requirements
hold, its total selection cost stays subpower, and its maximal exponent gap
also has subpower scale ratio. No requirement is imposed at a continuum of
grid widths. -/
theorem exists_slow_grid_with_subpower_cost {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hK : Subpower N K)
    (P : ℕ → ℕ → Prop) (hP : ∀ m, ∀ᶠ k in atTop, P m k) :
    ∃ J : ℕ → ℕ, Monotone J ∧ Tendsto J atTop atTop ∧ (∀ k, 1 ≤ J k) ∧
      Subpower N (fun k => K k ^ J k) ∧
      Subpower N (fun k => N k ^ ((1 : ℝ) / (J k : ℝ))) ∧
      ∀ᶠ k in atTop, ∀ m < J k, P m k := by
  have hstage (m : ℕ) : ∀ᶠ k in atTop,
      P m k ∧ K k ^ (m + 1) ≤ N k ^ ((1 : ℝ) / ((m : ℝ) + 1)) :=
    (hP m).and (eventually_subpower_pow_le hN hK.1 hK.2 (m + 1) (by positivity))
  obtain ⟨j, hjmono, hjt, hjle, hev⟩ := exists_slow_diagonal _ hstage
  let J : ℕ → ℕ := fun k => j k + 1
  have hJmono : Monotone J := fun a b hab => Nat.succ_le_succ (hjmono hab)
  have hJt : Tendsto J atTop atTop := by
    apply tendsto_atTop.2
    intro m
    filter_upwards [hjt.eventually_ge_atTop m] with k hk
    dsimp [J]
    omega
  have hJpos (k : ℕ) : 1 ≤ J k := Nat.succ_le_succ (Nat.zero_le _)
  have hgap (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ k in atTop, (1 : ℝ) / (J k : ℝ) ≤ ε := by
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    filter_upwards [hjt.eventually_ge_atTop m] with k hk
    have hdenom : (m : ℝ) + 1 ≤ (J k : ℝ) := by
      change (m : ℝ) + 1 ≤ ((j k + 1 : ℕ) : ℝ)
      exact_mod_cast Nat.succ_le_succ hk
    exact (one_div_le_one_div_of_le (by positivity) hdenom).trans hm.le
  have hcost : Subpower N (fun k => K k ^ J k) := by
    refine ⟨fun k => one_le_pow₀ (hK.1 k), ?_⟩
    intro ε hε
    filter_upwards [hev, hgap ε hε] with k hk hgapk
    have hpower : K k ^ J k ≤ N k ^ ((1 : ℝ) / (J k : ℝ)) := by
      simpa [J] using (hk (j k) le_rfl).2
    exact hpower.trans (Real.rpow_le_rpow_of_exponent_le (hN k) hgapk)
  refine ⟨J, hJmono, hJt, hJpos, hcost, ⟨?_, ?_⟩, ?_⟩
  · intro k
    apply Real.one_le_rpow (hN k)
    positivity
  · intro ε hε
    exact (hgap ε hε).mono fun k hk => Real.rpow_le_rpow_of_exponent_le (hN k) hk
  · filter_upwards [hev] with k hk
    intro m hm
    exact (hk m (by dsimp [J] at hm; omega)).1

end Submission.Obl.k4_scalar_grid_polynomial_qualification
