/-
Adapted from: here:o093
Original proofs by session x0535 in this LOT workspace. The scalar atlas
interface was written in the same o093 tree by x0364; this package retains
its literal fields while requiring only the sampling hypotheses used here.
-/

import Submission.Lib.K4ScalarFiniteGuard.Model

/-! Monotonicity of the literal scalar atlas budgets. -/

set_option autoImplicit false

namespace Submission.Lib.K4ScalarFiniteGuard

open MeasureTheory

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
  rcases hc with ⟨ht, hn, hm, hd, hC, hg, hsize, hmeas, hlist, hmass⟩
  have hpow : N p k ^ ε ≤ N p k ^ ε' :=
    Real.rpow_le_rpow_of_exponent_le hN hε
  have hNpos : 0 < N p k := lt_of_lt_of_le zero_lt_one hN
  refine ⟨ht.trans (Real.rpow_le_rpow_of_exponent_le hN hh), hn, hm, hd, hC,
    ?_, ?_, hmeas, hlist, ?_⟩
  · intro i
    rcases hg i with ⟨hpos, hJ, hinv, hwidth, hcenter, hdegree, hcoeff, hsupport,
      hAfmt, hCfmt, hfit, hfloor⟩
    refine ⟨hpos, hJ, hinv, hwidth.trans ?_, hcenter.trans hpow, hdegree,
      hcoeff, ?_, hAfmt, hCfmt, ?_, ?_⟩
    · exact div_le_div_of_nonneg_right hpow (by positivity)
    · intro l hl
      exact ⟨(hsupport l hl).1, fun e => ((hsupport l hl).2 e).trans hpow⟩
    · intro l hl t ht
      exact ⟨(hfit l hl t ht).1.trans (mul_le_mul_of_nonneg_right hpow hJ.le),
        (hfit l hl t ht).2.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hNpos.le _))⟩
    · intro hisTrue
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hfloor hisTrue)
      apply div_le_div_of_nonneg_left
        (mul_nonneg (Real.rpow_nonneg hNpos.le _) hJ.le)
        (mul_pos (Real.rpow_pos_of_pos hNpos _) (by positivity))
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
  · intro a z
    exact (hsize a z).trans hpow
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hε)

/-- Atlas-budget monotonicity does not change assignments or labels. -/
theorem chart_mono (p : Code) (B k : ℕ) (r b h h' ε ε' : ℝ) (isTrue : Bool)
    (hN : 1 ≤ N p k) (hh : h ≤ h') (hε : ε ≤ ε')
    (hc : Chart p B r b h ε isTrue k) : Chart p B r b h' ε' isTrue k := by
  rcases hc with ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hc⟩
  exact ⟨T, n, γ, j, A, C, u, v, J, P, Λ,
    chartData_mono p B k T n γ j A C u v J P Λ r b h h' ε ε' isTrue hN hh hε hc⟩

end Submission.Lib.K4ScalarFiniteGuard
