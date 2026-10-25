/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ChartMonotonicity.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SharedGuard

/-! Monotonicity of the literal scalar atlas budgets. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open MeasureTheory
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Enlarge horizon and subpower-loss budgets while retaining the entire
atlas, original selected incidence sets and observation-list table. -/
theorem chartData_mono (p : Code) (B k T n : ℕ)
    (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n))
    (r b h h' ε ε' : ℝ) (isTrue : Bool)
    (hN : 1 ≤ N p k) (hh : h ≤ h') (hε : ε ≤ ε')
    (hc : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ChartData p B r b h' ε' isTrue k T n γ j A C u v J P Λ := by
  exact Submission.Lib.K4ScalarFiniteGuard.chartData_mono (guardModel p) B k T n γ j A C u v J P Λ
    r b h h' ε ε' isTrue hN hh hε hc

/-- Atlas-budget monotonicity does not change assignments or labels. -/
theorem chart_mono (p : Code) (B k : ℕ) (r b h h' ε ε' : ℝ) (isTrue : Bool)
    (hN : 1 ≤ N p k) (hh : h ≤ h') (hε : ε ≤ ε')
    (hc : Chart p B r b h ε isTrue k) : Chart p B r b h' ε' isTrue k := by
  exact Submission.Lib.K4ScalarFiniteGuard.chart_mono (guardModel p) B k r b h h' ε ε' isTrue hN hh hε hc

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
