import Submission.Obl.k4_scalar_normalized_exact_refinement.Coordinates
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Monotonicity

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory
open k4_scalar_linear_critical_extremizers.Split

noncomputable section

def restrictedChartList {Γ : Type*} {n m : ℕ} (e : Fin m ↪ Fin n)
    (Λ : Γ → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)) :
    Γ → ((Fin 2 → ℝ) × ℤ) → Finset (Fin m) :=
  fun a z => Finset.univ.filter (fun i => e i ∈ Λ a z)

lemma restrictedChartList_card {Γ : Type*} {n m : ℕ} (e : Fin m ↪ Fin n)
    (Λ : Γ → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)) (a : Γ) (z : (Fin 2 → ℝ) × ℤ) :
    (restrictedChartList e Λ a z).card ≤ (Λ a z).card := by
  have hsub : (restrictedChartList e Λ a z).map e ⊆ Λ a z := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact (Finset.mem_filter.mp hj).2
  simpa using Finset.card_le_card hsub

/-- Restrict an atlas to any injectively indexed subfamily. The full prior
assignments and the list recovery property are unchanged. -/
lemma chartData_restrict {p : Code} {B : ℕ} {r b h ε : ℝ} {isTrue : Bool}
    {k T n m : ℕ} {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Line} {C : Fin n → Set (Line × ℝ)} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (e : Fin m ↪ Fin n)
    (hmass : ENNReal.ofReal (N p k ^ (-ε)) ≤ ∑ a : Fin (W p k),
      ENNReal.ofReal (ω p k a) * mu p k a {q | ∃ i : Fin m, γ (e i) = a ∧ q ∈ C (e i)}) :
    ChartData p B r b h ε isTrue k T m (γ ∘ e) (j ∘ e) (A ∘ e) (C ∘ e)
      (u ∘ e) (v ∘ e) (J ∘ e) (P ∘ e) (restrictedChartList e Λ) := by
  obtain ⟨hT, hn, hmeas, hdisj, hsub, hc, hcard, hmeasΛ, hlist, _⟩ := hd
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective e e.injective
  refine ⟨hT, (show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn).trans hn,
    fun i => hmeas (e i), ?_, fun i => hsub (e i), fun i => hc (e i), ?_, ?_, ?_, hmass⟩
  · intro i i' hii hγ hj
    exact hdisj (e i) (e i') (fun he => hii (e.injective he)) hγ hj
  · intro a z
    exact (show ((restrictedChartList e Λ a z).card : ℝ) ≤ ((Λ a z).card : ℝ) by
      exact_mod_cast restrictedChartList_card e Λ a z).trans (hcard a z)
  · intro a i
    simpa only [restrictedChartList, Finset.mem_filter, Finset.mem_univ, true_and] using hmeasΛ a (e i)
  · intro i
    simpa only [Function.comp_apply, restrictedChartList, Finset.mem_filter, Finset.mem_univ,
      true_and] using hlist (e i)

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
