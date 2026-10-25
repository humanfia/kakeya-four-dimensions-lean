import Submission.Obl.k4_scalar_normalized_exact_refinement.PolynomialCoordinates
import Submission.Obl.k4_scalar_normalized_exact_refinement.AtlasPruning

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open k4_scalar_linear_critical_extremizers.Split

/-- The whole-trajectory identities in a refinement determine its coordinate
map uniquely. This supplies the polynomial inverse needed after restriction. -/
lemma normalizeLine_unique (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (θ : Line → Line)
    (hlabel : ∀ l, (θ l).1 = l.1)
    (hy : ∀ l t, y (θ l) ((t - t₀) / dt) = (y l t - u - t * v) / J)
    (hx : ∀ l t, x (θ l) ((t - t₀) / dt) =
      (x l t - MvPolynomial.eval ![t, y l t] P) / δ) :
    θ = normalizeLine P t₀ dt u v J δ := by
  funext l
  apply line_ext ((hlabel l).trans (normalizeLine_label ..).symm)
  · intro s
    have ht : (t₀ + dt * s - t₀) / dt = s := by field_simp; ring
    have h := (hy l (t₀ + dt * s)).trans
      (y_normalizeLine_at P t₀ dt u v J δ hdt l (t₀ + dt * s)).symm
    simpa only [ht] using h
  · intro s
    have ht : (t₀ + dt * s - t₀) / dt = s := by field_simp; ring
    have h := (hx l (t₀ + dt * s)).trans
      (x_normalizeLine_at P hP t₀ dt u v J δ hdt l (t₀ + dt * s)).symm
    simpa only [ht] using h

/-- Selected events can be shrunk and zero-mass worlds removed while all
full assignments and observable lists are retained. -/
lemma chartData_shrink_restrict {p : Code} {B B' : ℕ} {r b h h' ε ε' : ℝ}
    {k T n m : ℕ} {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Line} {C : Fin n → Set (Line × ℝ)} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hd : ChartData p B r b h ε false k T n γ j A C u v J P Λ)
    (hN : 1 ≤ N p k) (hB : B ≤ B') (hh : h ≤ h') (he : ε ≤ ε')
    (e : Fin m ↪ Fin n) (C' : Fin m → Set (Line × ℝ))
    (hCm : ∀ i, MeasurableSet (C' i)) (hC : ∀ i, C' i ⊆ C (e i))
    (hpos : ∀ i, 0 < mu p k (γ (e i)) (C' i))
    (hfmt : ∀ i label, Format 6 (N p k ^ (B' : ℝ)) B'
      {a | ((label, fun z : Fin 5 => a z.castSucc), a 5) ∈ C' i})
    (hmass : ENNReal.ofReal (N p k ^ (-ε')) ≤ ∑ a : Fin (W p k),
      ENNReal.ofReal (ω p k a) * mu p k a {q | ∃ i : Fin m, γ (e i) = a ∧ q ∈ C' i}) :
    ChartData p B' r b h' ε' false k T m (γ ∘ e) (j ∘ e) (A ∘ e) C'
      (u ∘ e) (v ∘ e) (J ∘ e) (P ∘ e) (restrictedChartList e Λ) := by
  have hd' : ChartData p B' r b h' ε' false k T n γ j A C u v J P Λ :=
    k4_scalar_true_atlas_terminal_lists.ChartData.mono hN hB hh he hd
  obtain ⟨hT, hn, hmeas, hdisj, hsub, hc, hcard, hmeasΛ, hlist, _⟩ := hd'
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective e e.injective
  refine ⟨hT, (show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn).trans hn,
    fun i => ⟨(hmeas (e i)).1, hCm i⟩, ?_, fun i => (hC i).trans (hsub (e i)), ?_, ?_, ?_, ?_, hmass⟩
  · intro i i' hii hγ hj
    exact hdisj (e i) (e i') (fun heq => hii (e.injective heq)) hγ hj
  · intro i
    obtain ⟨_, hJ, hJi, hJu, huv, hP, hPc, hA, hFA, _, hfit, _⟩ := hc (e i)
    exact ⟨hpos i, hJ, hJi, hJu, huv, hP, hPc, hA, hFA, hfmt i, hfit, by simp⟩
  · intro a z
    exact (show ((restrictedChartList e Λ a z).card : ℝ) ≤ ((Λ a z).card : ℝ) by
      exact_mod_cast restrictedChartList_card e Λ a z).trans (hcard a z)
  · intro a i
    simpa only [restrictedChartList, Finset.mem_filter, Finset.mem_univ, true_and] using hmeasΛ a (e i)
  · intro i
    apply le_antisymm _ zero_le
    rw [← hlist (e i)]
    apply measure_mono
    intro q hq
    exact ⟨hC i hq.1, by simpa only [Function.comp_apply, restrictedChartList, Finset.mem_filter,
      Finset.mem_univ, true_and] using hq.2⟩

end Submission.Obl.k4_scalar_normalized_exact_refinement
