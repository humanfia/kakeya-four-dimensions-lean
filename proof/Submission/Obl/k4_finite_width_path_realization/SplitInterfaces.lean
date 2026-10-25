import Submission.Obl.k4_finite_width_path_realization.Toolkit.SplitStatements

namespace Submission.Obl.k4_finite_width_path_realization

set_option linter.unusedVariables false

noncomputable def CoreExpanded : (N K : ℕ → ℝ) → (W : ℕ → ℕ) → (ω : (k : ℕ) → Fin (W k) → ℝ) → (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → (B : (k : ℕ) → Fin (W k) → ℝ) → (f : ℝ → ℝ) → (M D k m : ℕ) → (r : ℕ → ℝ) → (T : ℕ → ℕ) → (κ : ℝ) → (C : ℕ) → (lev : Fin C → ℕ) → (par : Fin C → Fin C) → (γ : Fin C → Fin (W k)) → (j : Fin C → ℕ) → (c u : Fin C → EuclideanSpace ℝ (Fin 2)) → (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) → (R : Fin C → MvPolynomial (Fin 4) ℝ) → (A : Fin C → Set (ℕ × (Fin 6 → ℝ))) → (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → Prop :=
  fun N K W ω ν E B f M D k m r T κ C lev par γ j c u Q R A F =>
  1 ≤ κ ∧ K k ≤ κ ∧ (C : ℝ) ≤ N k ^ M ∧
  (∀ i, i < m → ENNReal.ofReal κ⁻¹ ≤ ∑ b, if lev b = i then ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod MeasureTheory.volume) (F b) else 0) ∧
  (∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
  (∀ b, lev b < m ∧ j b < 2 ^ T (lev b) ∧
    Chart (N k) M D κ (T (lev b)) (j b : ℝ) (r (lev b)) (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b)
      (ENNReal.ofReal (N k ^ (-f (r (lev b))) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T (lev b) * κ)) ≤ ((ν k (γ b)).prod MeasureTheory.volume) (F b)) ∧
    (0 < lev b → lev (par b) + 1 = lev b ∧ γ (par b) = γ b ∧ A b ⊆ A (par b) ∧ F b ⊆ F (par b) ∧
      (j (par b) : ℝ) / (2 : ℝ) ^ T (lev (par b)) ≤ (j b : ℝ) / (2 : ℝ) ^ T (lev b) ∧
      ((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b) ≤ ((j (par b) : ℝ) + 1) / (2 : ℝ) ^ T (lev (par b))))

noncomputable def ForestPreparationExpanded : Prop :=
  ∀ N K L d S η W ω ν E P B f g G, Problem N K L d S η W ω ν E P B f g G →
∀ (m : ℕ) (r : ℕ → ℝ), 0 < m → (∀ i, i < m → 0 < r i ∧ r i ≤ L) →
∀ M D : ℕ, ∃ M' D' : ℕ, M ≤ M' ∧ D ≤ D' ∧
∀ σ : ℝ, 0 < σ → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ σ ∧
∀ᶠ k in Filter.atTop, ∀ (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin (W k)) (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
(∀ i, i < m → (2 : ℝ) ^ T i ≤ N k ^ M) →
CoreExpanded N K W ω ν E B f M D k m r T (N k ^ ρ) C lev par γ j c u Q R A F →
∃ (C' : ℕ) (emb : Fin C' ↪ Fin C) (par' : Fin C' → Fin C') (F' : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
(lst : ℕ → Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')),
C' ≤ C ∧ CoreExpanded N K W ω ν E B f M' D' k m r T (N k ^ σ) C' (fun b => lev (emb b)) par' (fun b => γ (emb b)) (fun b => j (emb b)) (fun b => c (emb b)) (fun b => u (emb b)) (fun b => Q (emb b)) (fun b => R (emb b)) (fun b => A (emb b)) F' ∧
(∀ b, F' b ⊆ F (emb b) ∧ (0 < lev (emb b) → emb (par' b) = par (emb b))) ∧
(∀ i γ₁ o, ((lst i γ₁ o).card : ℝ) ≤ N k ^ σ) ∧
(∀ b, ν k (γ (emb b)) (A (emb b)) ≤ ENNReal.ofReal (N k ^ σ * N k ^ (-f (r (lev (emb b)))) * |Matrix.det (Q (emb b))|) ∧
  ∀ p ∈ F' b, b ∈ lst (lev (emb b)) (γ (emb b)) (obs (B k (γ (emb b))) (δ (N k) (r (lev (emb b)))) p)) ∧
(∀ b, ENNReal.ofReal (ω k (γ (emb b))) * ((ν k (γ (emb b))).prod MeasureTheory.volume) (F' b) ≠ ⊤) ∧
(∀ a, (∑ b, if 0 < lev (emb b) ∧ par' b = a then ENNReal.ofReal (ω k (γ (emb b))) * ((ν k (γ (emb b))).prod MeasureTheory.volume) (F' b) else 0) ≤ ENNReal.ofReal (ω k (γ (emb a))) * ((ν k (γ (emb a))).prod MeasureTheory.volume) (F' a))

noncomputable def RawCriticalForestsExpanded : Prop :=
  ForestPreparationExpanded → ((∀ N K L d S η W ω ν E P B f g G, Problem N K L d S η W ω ν E P B f g G → ∀ r h w : ℝ, 0 ≤ r → r < L → (∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C : ℕ, ∃ (γ : Fin C → Fin (W k)) (j : Fin C → Fin (2 ^ T)) (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)), (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (∀ b, |Matrix.det (Q b)| * (4 : ℝ) ^ T ≤ N k ^ (-w + ε)) ∧ (C : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ κ) ∧ (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) r (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (∀ p ∈ F b, b ∈ lst (γ b) (obs (B k (γ b)) (δ (N k) L) p))) ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod MeasureTheory.volume) (F b)) → ∃ N' K' W' ω' ν' E' P' B' f' g' G', Problem N' K' (L - r) d S η W' ω' ν' E' P' B' f' g' G' ∧ (∀ h' e : ℝ, 0 < e → ExpandedTerminal N' K' (L - r) W' ω' ν' E' B' f' h' → ExpandedTerminal N K L W ω ν E B f (h + h' + e)) ∧ (∀ h' w' : ℝ, ExpandedNarrowTerminal N' K' (L - r) W' ω' ν' E' B' f' h' w' → ExpandedNarrowTerminal N K L W ω ν E B f (h + h') (w + w')))) → ((∀ N K L d S η W ω ν E P B f g G, Problem N K L d S η W ω ν E P B f g G → ∀ h : ℝ, L < h → ExpandedTerminal N K L W ω ν E B f h)) →
∀ ds kr S η w : ℝ, 0 < S → 0 < η → ExpandedExtremalSetup ds kr S η → 0 ≤ w → UniformWidthExpanded ds kr S η w →
∀ (m : ℕ) (s : ℕ → ℝ), (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) →
∀ ε q : ℝ, 0 < ε → ε ≤ 1 → 0 < q → ∃ t : ℝ, 0 < t ∧
∀ N K d W ω ν E P B f g G, Problem N K 1 d S η W ω ν E P B f g G → d < ds + t → kr - t < ExpandedHorizon N K 1 W ω ν E B f →
∃ (r : ℕ → ℝ) (M D : ℕ), r (m - 1) = 1 ∧
(∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ 1) ∧
∀ σ : ℝ, 0 < σ → ∃ᶠ k in Filter.atTop,
∃ (κ : ℝ) (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin (W k)) (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (vwidth : Fin C → ℝ),
κ ≤ N k ^ σ ∧ CoreExpanded N K W ω ν E B f M D k m r T κ C lev par γ j c u Q R A F ∧
(∀ i, i < m → N k ^ (kr * s i - ε) ≤ (2 : ℝ) ^ T i ∧ (2 : ℝ) ^ T i ≤ N k ^ (kr * s i + ε) ∧ (2 : ℝ) ^ T i ≤ N k ^ M) ∧
(∀ b, |vwidth b| ≤ (M : ℝ) ∧ N k ^ (-vwidth b) = |Matrix.det (Q b)| * (4 : ℝ) ^ T (lev b) ∧
 (lev b = 0 → w * r 0 - q ≤ vwidth b) ∧
 (0 < lev b → vwidth (par b) + w * (r (lev b) - r (lev (par b))) - q ≤ vwidth b))

noncomputable def ForestWidthSelectionExpanded : Prop :=
  ∀ (m M : ℕ) (ε : ℝ), 0 < m → 0 < ε → ∃ B : ℕ, 0 < B ∧
∀ (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C) (vwidth : Fin C → ℝ) (mass : Fin C → ENNReal) (r : ℕ → ℝ) (w q : ℝ),
0 ≤ q → (∀ b, lev b < m ∧ |vwidth b| ≤ (M : ℝ)) →
(∀ b, 0 < lev b → lev (par b) + 1 = lev b) →
(∀ b, mass b ≠ ⊤) →
(∀ a, (∑ b, if 0 < lev b ∧ par b = a then mass b else 0) ≤ mass a) →
0 < (∑ b, if lev b = m - 1 then mass b else 0) →
(∀ b, (lev b = 0 → w * r 0 - q ≤ vwidth b) ∧ (0 < lev b → vwidth (par b) + w * (r (lev b) - r (lev (par b))) - q ≤ vwidth b)) →
∃ (C' : ℕ) (emb : Fin C' ↪ Fin C) (par' : Fin C' → Fin C') (nw : ℕ → ℝ),
C' ≤ C ∧ (∀ b, 0 < lev (emb b) → emb (par' b) = par (emb b)) ∧
(∀ b, |vwidth (emb b) - nw (lev (emb b))| ≤ ε) ∧
(∀ i, i < m → (∑ b, if lev b = m - 1 then mass b else 0) / (B : ENNReal) ≤ ∑ b, if lev (emb b) = i then mass (emb b) else 0) ∧
(∀ i, i < m → w * r i - (m : ℝ) * (q + 2 * ε) ≤ nw i ∧ nw i + w * (r (m - 1) - r i) - (m : ℝ) * (q + 2 * ε) ≤ nw (m - 1))

end Submission.Obl.k4_finite_width_path_realization
