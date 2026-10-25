import Submission.Obl.k4_scalar_normalized_exact_refinement.ChartPruning

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Filter
open k4_scalar_linear_critical_extremizers.Split

noncomputable section

def PrunedChart (p : Code) (B : ℕ) (r b h ε : ℝ) (k : ℕ) : Prop :=
  ∃ (T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set Line) (C : Fin n → Set (Line × ℝ))
    (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)),
    ChartData p B r b h ε false k T n γ j A C u v J P Λ ∧
      ∀ i, N p k ^ (-((B : ℝ) + 2)) ≤ (ν p k (γ i) (A i)).toReal

/-- A known atlas supplies a single increasing sequence with vanishing losses
and a fixed polynomial lower bound on every full assigned prior. -/
lemma known_pruned_sequence {p : Code} {r b h : ℝ}
    (hN : ∀ k, 2 ≤ N p k) (hNt : Tendsto (N p) atTop atTop)
    (hprob : ∀ k g, IsProbabilityMeasure (ν p k g))
    (hw0 : ∀ k g, 0 ≤ ω p k g) (hwsum : ∀ k, ∑ g, ω p k g = 1)
    (hk : Known p r b h) :
    ∃ (φ : ℕ → ℕ) (ε : ℕ → ℝ) (B : ℕ),
      StrictMono φ ∧ (∀ k, 0 < ε k) ∧ Tendsto ε atTop (nhds 0) ∧
      (∀ k, ε k ≤ 1) ∧ 1 ≤ B ∧
      ∀ k, PrunedChart p B r b (h + ε k) (ε k) (φ k) := by
  obtain ⟨_, B, hB, hknown⟩ := hk
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε0 n : 0 < ε n := by dsimp [ε]; positivity
  have hε1 n : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hf n : ∃ᶠ k in atTop, PrunedChart p B r b (h + ε n) (ε n) k := by
    have hη : 0 < ε n / 2 := by positivity
    have hg : ∀ᶠ k in atTop, 2 ≤ N p k ^ (ε n / 2) :=
      ((tendsto_rpow_atTop hη).comp hNt).eventually (eventually_ge_atTop 2)
    apply ((hknown (ε n / 2) hη).and_eventually hg).mono
    intro k hk
    obtain ⟨T, m, γ, j, A, C, u, v, J, P, Λ, hd⟩ := hk.1
    obtain ⟨m', e, he, hd'⟩ := chartData_prune_prior (hN k) hη.le
      (by linarith [hε1 n]) hk.2 (hprob k) (hw0 k) (hwsum k) hd
    refine ⟨T, m', γ ∘ e, j ∘ e, A ∘ e, C ∘ e, u ∘ e, v ∘ e, J ∘ e, P ∘ e,
      restrictedChartList e Λ, ?_, he⟩
    convert hd' using 1 <;> ring
  obtain ⟨φ, hφ, hφgood⟩ := extraction_forall_of_frequently hf
  exact ⟨φ, ε, B, hφ, hε0, tendsto_one_div_add_atTop_nhds_zero_nat, hε1, hB, hφgood⟩

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
