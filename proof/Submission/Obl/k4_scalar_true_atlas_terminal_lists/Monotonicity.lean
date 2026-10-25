import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Raw
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

theorem chartData_iff_raw_and_lists {p : Data} {B : ℕ} {r b h ε : ℝ} {isTrue : Bool}
    {k T n : ℕ} {γ : Fin n → Fin (worlds p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Trajectory} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (worlds p k) → Observation → Finset (Fin n)} :
    ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ ↔
      RawChartData p B r b h ε isTrue k T n γ j A C u v J P ∧
      (∀ a z, ((Λ a z).card : ℝ) ≤ N p k ^ ε) ∧
      (∀ a i, MeasurableSet {z | i ∈ Λ a z}) ∧
      (∀ i, mu p k (γ i) {q | q ∈ C i ∧
        i ∉ Λ (γ i) ((![q.2, y q.1 q.2] : Fin 2 → ℝ), ⌊x q.1 q.2 / (N p k ^ (-b))⌋)} = 0) := by
  constructor
  · rintro ⟨hT, hn, hm, hd, hs, hc, hcard, hmeas, hlist, hmass⟩
    exact ⟨⟨hT, hn, hm, hd, hs, hc, hmass⟩, hcard, hmeas, hlist⟩
  · rintro ⟨⟨hT, hn, hm, hd, hs, hc, hmass⟩, hcard, hmeas, hlist⟩
    exact ⟨hT, hn, hm, hd, hs, hc, hcard, hmeas, hlist, hmass⟩

/-- Enlarging the complexity, horizon, or loss weakens all raw clauses,
including the original-law true floors and retained-mass requirement. -/
theorem RawChartData.mono {p : Data} {B B' : ℕ} {r b h h' ε ε' : ℝ} {isTrue : Bool}
    {k T n : ℕ} {γ : Fin n → Fin (worlds p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Trajectory} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    (hN : 1 ≤ N p k) (hB : B ≤ B') (hh : h ≤ h') (he : ε ≤ ε')
    (hd : RawChartData p B r b h ε isTrue k T n γ j A C u v J P) :
    RawChartData p B' r b h' ε' isTrue k T n γ j A C u v J P := by
  have hepow := Real.rpow_le_rpow_of_exponent_le hN he
  have hBpow := Real.rpow_le_rpow_of_exponent_le hN (show (B : ℝ) ≤ B' by exact_mod_cast hB)
  have hN0 : 0 < N p k := zero_lt_one.trans_le hN
  rcases hd with ⟨hT, hn, hm, hdisj, hsub, hchart, hmass⟩
  refine ⟨hT.trans (Real.rpow_le_rpow_of_exponent_le hN hh), hn.trans hBpow,
    hm, hdisj, hsub, ?_, ?_⟩
  · intro i
    rcases hchart i with ⟨hμ, hJ, hJinv, hJup, hctr, hdeg, hcoef, hA, hAf, hCf, hfit, hfloor⟩
    refine ⟨hμ, hJ, hJinv.trans hBpow, ?_, hctr.trans hepow, hdeg,
      fun a => (hcoef a).trans hBpow, ?_, ?_, ?_, ?_, ?_⟩
    · exact hJup.trans (div_le_div_of_nonneg_right hepow (by positivity))
    · intro l hl
      exact ⟨(hA l hl).1.trans hBpow, fun e => ((hA l hl).2 e).trans hepow⟩
    · intro z
      exact (hAf z).mono hBpow hB
    · intro z
      exact (hCf z).mono hBpow hB
    · intro l hl t ht
      exact ⟨(hfit l hl t ht).1.trans (mul_le_mul_of_nonneg_right hepow hJ.le),
        (hfit l hl t ht).2.trans
          (mul_le_mul_of_nonneg_right hepow (Real.rpow_pos_of_pos hN0 _).le)⟩
    · intro ht
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hfloor ht)
      apply div_le_div_of_nonneg_left (mul_nonneg (Real.rpow_pos_of_pos hN0 _).le hJ.le)
        (mul_pos (Real.rpow_pos_of_pos hN0 _) (by positivity))
      exact mul_le_mul_of_nonneg_right hepow (by positivity)
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg he)

theorem ChartData.mono {p : Data} {B B' : ℕ} {r b h h' ε ε' : ℝ} {isTrue : Bool}
    {k T n : ℕ} {γ : Fin n → Fin (worlds p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Trajectory} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (worlds p k) → Observation → Finset (Fin n)}
    (hN : 1 ≤ N p k) (hB : B ≤ B') (hh : h ≤ h') (he : ε ≤ ε')
    (hd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ChartData p B' r b h' ε' isTrue k T n γ j A C u v J P Λ := by
  rw [chartData_iff_raw_and_lists] at hd ⊢
  exact ⟨hd.1.mono hN hB hh he,
    fun a z => (hd.2.1 a z).trans (Real.rpow_le_rpow_of_exponent_le hN he),
    hd.2.2⟩

theorem Chart.mono {p : Data} {B B' : ℕ} {r b h h' ε ε' : ℝ} {isTrue : Bool} {k : ℕ}
    (hN : 1 ≤ N p k) (hB : B ≤ B') (hh : h ≤ h') (he : ε ≤ ε')
    (hd : Chart p B r b h ε isTrue k) : Chart p B' r b h' ε' isTrue k := by
  obtain ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hd⟩ := hd
  exact ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hd.mono hN hB hh he⟩

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
