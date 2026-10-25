import Submission.Obl.k4_unbounded_width_exclusion.Width

noncomputable section

namespace Submission.Obl.k4_unbounded_width_exclusion

open Filter

/-- The finite sample condition in a true terminal system. -/
def Problem.TerminalSample (p : Problem) (M D : ℕ) (ε h : ℝ) (k : ℕ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (p.W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ p.N k ^ h ∧ (C' : ℝ) ≤ p.N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, chart (p.N k) M D κ T ((j b : ℕ) : ℝ) p.L (p.B k (γ b)) (p.E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (p.N k ^ (-p.f p.L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((p.ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (p.ω k (γ b)) * (((p.ν k (γ b)).prod MeasureTheory.volume) (F b))

theorem Problem.terminal_iff (p : Problem) (h : ℝ) :
    p.Terminal h ↔ ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ᶠ k in atTop, p.TerminalSample M D ε h k := Iff.rfl

theorem Problem.Terminal.nonneg {p : Problem} (hN : ∀ k, 2 ≤ p.N k)
    {h : ℝ} (hterm : p.Terminal h) : 0 ≤ h := by
  obtain ⟨M, D, hMD⟩ := hterm
  obtain ⟨k, κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    htime, _⟩ := (hMD 1 (by norm_num)).exists
  by_contra hn
  have hlt : p.N k ^ h < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hN k]) (lt_of_not_ge hn)
  have hone : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  linarith

theorem Problem.Terminal.mono {p : Problem} (hN : ∀ k, 1 ≤ p.N k)
    {h h' : ℝ} (hterm : p.Terminal h) (hh : h ≤ h') : p.Terminal h' := by
  obtain ⟨M, D, hMD⟩ := hterm
  refine ⟨M, D, fun ε hε => (hMD ε hε).mono fun k hk => ?_⟩
  obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    htime, hrest⟩ := hk
  exact ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    htime.trans (Real.rpow_le_rpow_of_exponent_le (hN k) hh), hrest⟩

theorem Problem.terminal_bddBelow (p : Problem) (hN : ∀ k, 2 ≤ p.N k) :
    BddBelow {h : ℝ | p.Terminal h} :=
  ⟨0, fun _ hh => hh.nonneg hN⟩

theorem Problem.horizon_le_of_terminal {p : Problem} (hN : ∀ k, 2 ≤ p.N k)
    {h : ℝ} (hterm : p.Terminal h) : p.horizon ≤ h :=
  csInf_le (p.terminal_bddBelow hN) hterm

theorem Problem.Narrow.terminal {p : Problem} (hN : ∀ k, 1 ≤ p.N k)
    {h w ρ : ℝ} (hnt : p.Narrow h w) (hρ : 0 < ρ) : p.Terminal (h + ρ) := by
  obtain ⟨M, D, hMD⟩ := hnt
  refine ⟨M, D, fun ε hε => ?_⟩
  have he : 0 < min ε ρ := lt_min hε hρ
  apply (hMD (min ε ρ) he).mono
  intro k hk
  obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    htime, hwidth, hcount, hdisj, hcharts, hmass⟩ := hk
  refine ⟨κ, hκ, hKκ, hκN.trans ?_, T, C, γ, j, c, u, Q, R, A, F,
    htime.trans ?_, hcount, hdisj, hcharts, hmass⟩
  · exact Real.rpow_le_rpow_of_exponent_le (hN k) (min_le_left _ _)
  · exact Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith [min_le_right ε ρ])

theorem Problem.Narrow.horizon_le {p : Problem} (hN : ∀ k, 2 ≤ p.N k)
    {h w : ℝ} (hnt : p.Narrow h w) : p.horizon ≤ h := by
  apply le_of_forall_pos_le_add
  intro ρ hρ
  exact p.horizon_le_of_terminal hN
    (hnt.terminal (fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hN k)) hρ)

/-- A fixed forbidden horizon excludes all sufficiently late samples at
some fixed tolerance, for each prechosen pair of complexity bounds. -/
theorem Problem.finite_guard {p : Problem} {h : ℝ} (hnot : ¬ p.Terminal h)
    (M D : ℕ) : ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ k in atTop, ¬ p.TerminalSample M D ε h k := by
  classical
  have hn : ¬ (∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, p.TerminalSample M D ε h k) := by
    intro hall
    exact hnot ⟨M, D, hall⟩
  push Not at hn
  obtain ⟨ε, hε, hbad⟩ := hn
  exact ⟨ε, hε, hbad⟩

end Submission.Obl.k4_unbounded_width_exclusion
