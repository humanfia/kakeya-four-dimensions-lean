import Submission.Obl.k4_scalar_grid_polynomial_qualification.SlowGrid
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ExponentGrid

/- The input cost K is fixed before the diagonal output J is chosen. Feeding
   the interpolation cost N^(1/J) of that same output grid back into K would
   instead give K^J = N. In a two-grid common-choice argument, construct the
   raw second-grid lists at exact power widths and round only to the supplied
   preparation mesh. Pay the second grid's all-scale interpolation cost after
   the choice, rather than raising it through all its levels.
   Quantitative caution: x0797, o229, DM 2026-10-21 14:40:24Z. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_profile_density_bounds

/-- The frozen preparation controls the mesh step, without imposing an
upper bound on the grid denominator itself. -/
theorem grid_denominator_tendsto {N H : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hH : Subpower N H)
    (M : ℕ → ℕ) (hM : ∀ k, 1 ≤ M k)
    (hcost : ∀ k, N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) :
    Tendsto M atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hε : 0 < (1 : ℝ) / ((b + 1 : ℕ) : ℝ) := by positivity
  filter_upwards [eventually_grid_step_le hN hH M hcost hε] with k hk
  have hMpos : 0 < (M k : ℝ) := by exact_mod_cast (by have := hM k; omega : 0 < M k)
  have hden : ((b + 1 : ℕ) : ℝ) ≤ (M k : ℝ) :=
    (one_div_le_one_div hMpos (by positivity)).mp hk
  have : b + 1 ≤ M k := by exact_mod_cast hden
  omega

/-- Pick a controlled number of levels inside a possibly much finer
supplied grid. Both the number of levels and the accumulated selection
cost are subpower; all fixed-stage requirements hold on the chosen grid. -/
theorem exists_slow_subgrid_with_subpower_cardinality {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : Subpower N K)
    (M : ℕ → ℕ) (hMt : Tendsto M atTop atTop)
    (P : ℕ → ℕ → Prop) (hP : ∀ m, ∀ᶠ k in atTop, P m k) :
    ∃ J : ℕ → ℕ, Monotone J ∧ Tendsto J atTop atTop ∧ (∀ k, 1 ≤ J k) ∧
      Subpower N (fun k => (J k : ℝ)) ∧
      Subpower N (fun k => K k ^ J k) ∧
      Subpower N (fun k => N k ^ ((1 : ℝ) / (J k : ℝ))) ∧
      ∀ᶠ k in atTop, J k ≤ M k ∧ ∀ m < J k, P m k := by
  have hstage (m : ℕ) : ∀ᶠ k in atTop,
      P m k ∧ m + 1 ≤ M k ∧
        ((m + 1 : ℕ) : ℝ) ≤ N k ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    have hpow := eventually_subpower_mul_rpow_lt hN hNt hK.1 hK.2 0
      (a := 0) (b := (1 : ℝ) / ((m + 1 : ℕ) : ℝ)) (by positivity)
      (A := ((m + 1 : ℕ) : ℝ)) (by positivity)
    filter_upwards [hP m, hMt.eventually_ge_atTop (m + 1), hpow] with k hp hm hk
    refine ⟨hp, hm, ?_⟩
    simpa only [pow_zero, Real.rpow_zero, mul_one] using hk.le
  obtain ⟨J, hmono, hJt, hJone, hcost, hgap, hev⟩ :=
    exists_slow_grid_with_subpower_cost hN hK
      (fun m k => P m k ∧ m + 1 ≤ M k ∧
        ((m + 1 : ℕ) : ℝ) ≤ N k ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))) hstage
  have hev' : ∀ᶠ k in atTop, J k ≤ M k ∧
      (J k : ℝ) ≤ N k ^ ((1 : ℝ) / (J k : ℝ)) ∧ ∀ m < J k, P m k := by
    filter_upwards [hev] with k hk
    have hj : (J k - 1) + 1 = J k := Nat.sub_add_cancel (hJone k)
    have hs := hk (J k - 1) (by have := hJone k; omega)
    refine ⟨?_, ?_, fun m hm => (hk m hm).1⟩
    · simpa only [hj] using hs.2.1
    · simpa only [hj] using hs.2.2
  have hcount : Subpower N (fun k => (J k : ℝ)) := by
    refine ⟨?_, ?_⟩
    · intro k
      change (1 : ℝ) ≤ (J k : ℝ)
      exact_mod_cast hJone k
    · intro ε hε
      filter_upwards [hev', hgap.2 ε hε] with k hk he
      exact hk.2.1.trans he
  refine ⟨J, hmono, hJt, hJone, hcount, hcost, hgap, ?_⟩
  exact hev'.mono fun k hk => ⟨hk.1, hk.2.2⟩

end Submission.Obl.k4_scalar_grid_polynomial_qualification
