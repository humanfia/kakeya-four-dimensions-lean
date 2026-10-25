import Mathlib

namespace Submission.Obl.k4_cap_class_terminal_charts

open Filter

/-- The exact subpower convention used by the terminal-chart assertion. -/
def Subpower (N K : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε

/-- A fixed power tolerance can tend to zero along a subsequence while a single
format bound remains fixed. The predicate may encode an entire finite chart system. -/
theorem subpower_diagonal {N K : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (P : ℕ → ℝ → Prop)
    (hP : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ C : ℝ, 1 ≤ C ∧ K k ≤ C ∧ C ≤ N k ^ ε ∧ P k C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C : ℕ → ℝ,
      Subpower (N ∘ ψ) C ∧ (∀ k, K (ψ k) ≤ C k) ∧ ∀ k, P (ψ k) (C k) := by
  classical
  have htol (m : ℕ) : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
  obtain ⟨ψ, hψ, hchoice⟩ := extraction_forall_of_frequently
    (fun m => hP (1 / ((m : ℝ) + 1)) (htol m))
  choose C hC hKC hCN hPC using hchoice
  refine ⟨ψ, hψ, C, ⟨hC, ?_⟩, hKC, hPC⟩
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop m] with k hk
  apply (hCN k).trans
  apply Real.rpow_le_rpow_of_exponent_le (hN (ψ k))
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  have hmk : (m : ℝ) ≤ k := by exact_mod_cast hk
  apply (div_le_iff₀ hkpos).mpr
  have hh : 1 < (m : ℝ) * ε := (div_lt_iff₀ hε).mp hm
  nlinarith

/-- Subpower bounds survive passage to any increasing subsequence. -/
theorem Subpower.comp {N K : ℕ → ℝ} (h : Subpower N K)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) : Subpower (N ∘ ψ) (K ∘ ψ) := by
  refine ⟨fun k => h.1 (ψ k), ?_⟩
  intro ε hε
  exact hψ.tendsto_atTop.eventually (h.2 ε hε)

end Submission.Obl.k4_cap_class_terminal_charts
