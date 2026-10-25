import Submission.Obl.k4_scalar_true_terminal_lifting.Poly

/-!
# Monotonicity and sub-selection of scalar charts

`ChartData` is monotone in its integer budget `B`, its time exponent `h` and its loss `ε`
(for `N ≥ 1`). A chart may be restricted to an injectively indexed subfamily of its pieces,
provided the weighted selected mass of the subfamily still clears the loss floor.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

theorem chartData_mono {p : Code} {B B' : ℕ} {r b h h' ε ε' : ℝ} {isTrue : Bool} {k T n : ℕ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))} {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hcd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (hN : 1 ≤ N p k) (hB : B ≤ B') (hh : h ≤ h') (hε : ε ≤ ε') :
    ChartData p B' r b h' ε' isTrue k T n γ j A C u v J P Λ := by
  unfold ChartData at hcd ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hcd
  have hN0 : 0 < N p k := lt_of_lt_of_le one_pos hN
  have hpowB : N p k ^ (B : ℝ) ≤ N p k ^ (B' : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by exact_mod_cast hB)
  have hpowε : N p k ^ ε ≤ N p k ^ ε' := Real.rpow_le_rpow_of_exponent_le hN hε
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  refine ⟨h1.trans (Real.rpow_le_rpow_of_exponent_le hN hh), h2.trans hpowB, h3, h4, h5,
    ?_, ?_, h8, h9, ?_⟩
  · intro i
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := h6 i
    refine ⟨c1, c2, c3.trans hpowB, c4.trans (div_le_div_of_nonneg_right hpowε hT.le),
      c5.trans hpowε, c6, fun a => (c7 a).trans hpowB,
      fun l hl => ⟨((c8 l hl).1).trans hpowB, fun e => ((c8 l hl).2 e).trans hpowε⟩,
      fun z => Format.mono (c9 z) hpowB hB, fun z => Format.mono (c10 z) hpowB hB,
      fun l hl t ht => ⟨?_, ?_⟩, fun hTr => ?_⟩
    · exact ((c11 l hl t ht).1).trans (mul_le_mul_of_nonneg_right hpowε c2.le)
    · exact ((c11 l hl t ht).2).trans
        (mul_le_mul_of_nonneg_right hpowε (Real.rpow_pos_of_pos hN0 _).le)
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (c12 hTr)
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (Real.rpow_pos_of_pos hN0 _).le c2.le
      · exact mul_pos (Real.rpow_pos_of_pos hN0 _) hT
      · exact mul_le_mul_of_nonneg_right hpowε hT.le
  · intro a z
    exact (h7 a z).trans hpowε
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) h10
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- Restriction of a chart to an injectively indexed subfamily of its pieces. -/
theorem chartData_select {p : Code} {B : ℕ} {r b h ε : ℝ} {isTrue : Bool} {k T n n' : ℕ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))} {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hcd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (σ : Fin n' → Fin n) (hσ : Function.Injective σ)
    (hmass : ENNReal.ofReal (N p k ^ (-ε)) ≤ ∑ a : Fin (W p k),
      ENNReal.ofReal (ω p k a) * mu p k a {q | ∃ i, γ (σ i) = a ∧ q ∈ C (σ i)}) :
    ChartData p B r b h ε isTrue k T n' (fun i => γ (σ i)) (fun i => j (σ i))
      (fun i => A (σ i)) (fun i => C (σ i)) (fun i => u (σ i)) (fun i => v (σ i))
      (fun i => J (σ i)) (fun i => P (σ i))
      (fun a z => Finset.univ.filter (fun i => σ i ∈ Λ a z)) := by
  classical
  unfold ChartData at hcd ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hcd
  have hnn : (n' : ℝ) ≤ n := by
    have := Fintype.card_le_of_injective σ hσ
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  refine ⟨h1, hnn.trans h2, fun i => h3 (σ i), ?_, fun i => h5 (σ i), fun i => h6 (σ i),
    ?_, ?_, ?_, hmass⟩
  · intro i i' hii' hγ hj
    exact h4 (σ i) (σ i') (fun h => hii' (hσ h)) hγ hj
  · intro a z
    refine le_trans ?_ (h7 a z)
    have : (Finset.univ.filter (fun i => σ i ∈ Λ a z)).card ≤ (Λ a z).card := by
      apply Finset.card_le_card_of_injOn σ
      · intro i hi
        simpa using hi
      · intro i _ i' _ hii'
        exact hσ hii'
    exact_mod_cast this
  · intro a i
    simpa using h8 a (σ i)
  · intro i
    simpa using h9 (σ i)

open Classical in
/-- The weighted selected mass splits into the part on worlds that are not bad and a
bound by the whole weighted mass of the bad worlds. -/
theorem mass_le_good_add_bad {p : Code} {k n : ℕ} (γ : Fin n → Fin (W p k))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (bad : Fin (W p k) → Prop) :
    ∑ a : Fin (W p k), ENNReal.ofReal (ω p k a) * mu p k a {q | ∃ i, γ i = a ∧ q ∈ C i} ≤
      ∑ a : Fin (W p k), ENNReal.ofReal (ω p k a) *
          mu p k a {q | ∃ i, γ i = a ∧ ¬ bad (γ i) ∧ q ∈ C i} +
        ∑ a : Fin (W p k), (if bad a then ENNReal.ofReal (ω p k a) * mu p k a Set.univ
          else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : bad a
  · simp only [ha, ↓reduceIte]
    refine le_trans ?_ le_add_self
    exact mul_le_mul_right (measure_mono (Set.subset_univ _)) _
  · simp only [ha, ↓reduceIte, add_zero]
    refine le_of_eq ?_
    congr 2
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, hq⟩
      exact ⟨i, hi, by rw [hi]; exact ha, hq⟩
    · rintro ⟨i, hi, -, hq⟩
      exact ⟨i, hi, hq⟩

end Submission.Obl.k4_scalar_true_terminal_lifting
