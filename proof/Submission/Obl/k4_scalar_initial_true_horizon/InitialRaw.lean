import Submission.Obl.k4_scalar_initial_true_horizon.InitialBudgets
import Submission.Obl.k4_scalar_initial_true_horizon.InitialCovExtraction
import Submission.Obl.k4_scalar_initial_true_horizon.SplitInterface
import Submission.Obl.k4_scalar_initial_true_horizon.Monotonicity
import Submission.Obl.k4_scalar_initial_true_horizon.InitialReadout

/-!
# The raw true initial atlas

For every exact problem, with the fixed exponent `Bpar`, every loss `ε` and every large
sample, the maximal good cells form a raw true atlas at time exponent `L + ε`: the selected
original mass is at least `N^-ε` by the covering estimate, and all other clauses follow
from the per-sample budgets.  Losses above one are reduced to `min ε 1` by monotonicity.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem floorPar_eq {p : Data} (hp : Exact p) (k : ℕ) (ε : ℝ) :
    floorPar p k ε = N p k ^ (-profile p (L p)) * (1 / (2 : ℝ) ^ Tpar p k) / N p k ^ ε := by
  unfold floorPar qPar
  rw [Real.rpow_neg (hp.N_pos k).le ε, div_eq_mul_inv, div_eq_mul_inv]

/-- **The raw true initial atlas** (the statement of the child `o161`). -/
theorem rawInitial : RawInitial := by
  intro p hp
  refine ⟨Bpar p, Bpar_ge_one p, ?_⟩
  intro ε hε
  set ε' := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hev : ∀ᶠ k in atTop, RawChart p (Bpar p) (L p) (L p) (L p + ε) ε true k := by
    filter_upwards [eventually_initial_mass hp hε'pos hε'1, eventually_param_budget hp,
      eventually_slack_budget hp hε'pos, eventually_time_budget hp hε'pos]
      with k hmass hparam hslack htime
    have hcount : (worlds p k : ℝ) / (floorPar p k ε' * cellJ (1 / (2 : ℝ) ^ Tpar p k)
        (kmaxPar p k)) ≤ N p k ^ (Bpar p : ℝ) :=
      count_budget hp k hε'pos.le hε'1
    have hraw : RawChart p (Bpar p) (L p) (L p) (L p + ε') ε' true k :=
      rawChart_of_covInc hp (Bpar_ge_one p) (M_le_Bpar p) (D_le_Bpar p) htime
        (qPar_le_aL hp k) (format_budget hp k) hslack hparam (floorPar_eq hp k ε')
        (inverse_width_budget hp k) hcount hmass
    obtain ⟨T, n, γ, j, A, C, u, v, J, P, hd⟩ := hraw
    exact ⟨T, n, γ, j, A, C, u, v, J, P,
      hd.mono (hp.N_one_le k) le_rfl (by linarith) hε'ε⟩
  exact hev.frequently

/-- **The frozen statement of `o130`** follows with the accepted terminal-list theorem. -/
theorem initial : Initial := initial_of_raw rawInitial

end Submission.Obl.k4_scalar_initial_true_horizon
