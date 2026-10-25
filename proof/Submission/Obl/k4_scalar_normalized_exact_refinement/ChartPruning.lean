import Submission.Obl.k4_scalar_normalized_exact_refinement.AtlasPruning
import Submission.Obl.k4_scalar_normalized_exact_refinement.RawPruning

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open k4_scalar_linear_critical_extremizers.Split

/-- Remove tiny full-prior assignments, retaining all geometric and list
clauses after doubling the tolerance. -/
lemma chartData_prune_prior {p : Code} {B : ℕ} {r b h ε : ℝ} {isTrue : Bool}
    {k T n : ℕ} {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Line} {C : Fin n → Set (Line × ℝ)} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hN : 2 ≤ N p k) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hNε : 2 ≤ N p k ^ ε)
    (hprob : ∀ g, IsProbabilityMeasure (ν p k g))
    (hw0 : ∀ g, 0 ≤ ω p k g) (hwsum : ∑ g, ω p k g = 1)
    (hd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ∃ (m : ℕ) (e : Fin m ↪ Fin n),
      (∀ i, N p k ^ (-((B : ℝ) + 2)) ≤ (ν p k (γ (e i)) (A (e i))).toReal) ∧
      ChartData p B r b (h + ε) (2 * ε) isTrue k T m
        (γ ∘ e) (j ∘ e) (A ∘ e) (C ∘ e) (u ∘ e) (v ∘ e) (J ∘ e) (P ∘ e)
        (restrictedChartList e Λ) := by
  have hN1 : 1 ≤ N p k := by linarith
  have hdt1 : ((2 : ℝ) ^ T)⁻¹ ≤ 1 := by
    have hpow : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hpow
  have hC i : C i ⊆ A i ×ˢ Icc
      (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹)
      (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹ + ((2 : ℝ) ^ T)⁻¹) := by
    intro z hz
    have hz' := (hd.2.2.2.2.1 i hz).2
    simpa only [I, div_eq_mul_inv, add_mul, one_mul] using hz'
  have hmass := hd.2.2.2.2.2.2.2.2.2
  obtain ⟨m, e, he, hm⟩ := finite_prior_pruning (ν p k) (mu p k)
    (fun g => ENNReal.ofReal (ω p k g)) γ A C
    (fun i => ((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹)
    (N p k) ε (B : ℝ) hN hε1 hNε hd.2.1 hprob
    (fun g => Measure.restrict_le_self)
    (fun g => by simpa using ENNReal.ofReal_le_ofReal (probability_weight_le_one (ω p k) hw0 hwsum g))
    hdt1 hC hmass
  refine ⟨m, e, he, ?_⟩
  have hd' : ChartData p B r b (h + ε) (2 * ε) isTrue k T n γ j A C u v J P Λ :=
    k4_scalar_true_atlas_terminal_lists.ChartData.mono hN1 le_rfl (by linarith) (by linarith) hd
  apply chartData_restrict hd' e
  simpa only [neg_mul] using hm

end Submission.Obl.k4_scalar_normalized_exact_refinement
