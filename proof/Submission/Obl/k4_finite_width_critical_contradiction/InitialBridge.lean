/- Adapted from same-tree o105, session x0351, commit 735310f,
   Submission/Obl/k4_critical_path_framework/Bridge.lean. -/
import Submission.Obl.k4_finite_width_critical_contradiction.Horizon
import Submission.Obl.k4_finite_width_critical_contradiction.Inputs

/-! Definitional bridges from the frozen statements to the named predicates. -/

namespace Submission.Obl.k4_finite_width_critical_contradiction

open MeasureTheory Filter

/-- Expanding the record of chart data reproduces the frozen sample conclusion. -/
theorem terminalAt_iff_expanded (p : Data) (M D : ℕ) (h ε : ℝ) (k : ℕ) :
    TerminalAt p M D h ε k ↔
      ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧
      ∃ T C : ℕ, ∃ (γ : Fin C → Fin (p.W k)) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → Spatial) (Q : Fin C → Frame) (R : Fin C → Test)
      (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence),
      (2 : ℝ) ^ T ≤ p.N k ^ h ∧ (C : ℝ) ≤ p.N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ b, Chart (p.N k) M D κ T (j b : ℝ) p.L (p.B k (γ b)) (p.E k (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F b)
        (ENNReal.ofReal (p.N k ^ (-p.f p.L) * |Matrix.det (Q b)| /
          ((2 : ℝ) ^ T * κ)) ≤ ((p.ν k (γ b)).prod volume) (F b))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (p.ω k (γ b)) *
        ((p.ν k (γ b)).prod volume) (F b) := by
  constructor
  · rintro ⟨a, hκ, hK, hε, hT, hC, hdis, hcharts, hmass⟩
    exact ⟨a.κ, hκ, hK, hε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R,
      a.A, a.F, hT, hC, hdis, hcharts, hmass⟩
  · rintro ⟨κ, hκ, hK, hε, T, C, γ, j, c, u, Q, R, A, F,
      hT, hC, hdis, hcharts, hmass⟩
    exact ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩,
      hκ, hK, hε, hT, hC, hdis, hcharts, hmass⟩

/-- The initial horizon hypothesis has exactly the named interface. -/
theorem initialHorizon_iff : InitialHorizonExpanded ↔ InitialHorizon := by
  constructor
  · intro hi p hp h hh
    obtain ⟨M, D, hs⟩ := hi p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B
      p.f p.g p.G hp h hh
    refine ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk => ?_⟩
    exact (terminalAt_iff_expanded p M D h ε k).mpr hk
  · intro hi N K L d S η W ω ν E P B f g G hp h hh
    let p : Data := ⟨N, K, L, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
    obtain ⟨M, D, hs⟩ := hi p hp h hh
    refine ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk => ?_⟩
    exact (terminalAt_iff_expanded p M D h ε k).mp hk

end Submission.Obl.k4_finite_width_critical_contradiction
