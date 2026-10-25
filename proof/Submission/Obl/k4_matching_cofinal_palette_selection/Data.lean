/- Adapted from this LOT tree, o040, session x0115, commit 9f7e9a910e7de423611a55b624313eab3641558f,
   Submission/Obl/k4_matching_refinement_exponent/Interfaces.lean. -/
import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_matching_cofinal_palette_selection

def BetaValid (D J : ℕ) (β : ℕ → ℝ) : Prop := (∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0)

noncomputable def radius (J : ℕ) (β : ℕ → ℝ) : ℝ → ℝ := (fun a : ℝ => sSup (Set.image (fun j : ℕ => (a - β j) / (j : ℝ)) (Set.Icc 1 J)))

noncomputable def accuracy (r : ℝ → ℝ) : ℕ → ℝ → ℝ := (fun (j : ℕ) (a : ℝ) => sSup (Set.image (fun x : ℝ => x - (j : ℝ) * r x) (Set.Icc 0 a)))

def Cofinal (P : ℝ → ℝ → Prop) : Prop := (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ P ε N)

def Records (J : ℕ) (d : ℝ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ)
    (q : ℕ) (u : ℕ → ℝ) (ε N : ℝ)
    (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
    (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ))
    (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)) : Prop :=
  (fun c : ℕ → ℝ → ℝ => (n₁ : ℝ) ≤ N ^ (d + ε) ∧ (n₂ : ℝ) ≤ N ^ (d + ε) ∧
  (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧
  (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧
  (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ ε) ∧
  (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ ε) ∧
  (∀ i : Fin n₁, 0 ≤ π₁ i) ∧ (∀ i : Fin n₂, 0 ≤ π₂ i) ∧
  (∑ i : Fin n₁, π₁ i) = 1 ∧ (∑ i : Fin n₂, π₂ i) = 1 ∧ MeasureTheory.IsProbabilityMeasure μ ∧
  (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₁ i) * MeasureTheory.volume E) ∧
  (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₂ i) * MeasureTheory.volume E) ∧ MeasurableSet S ∧ μ Sᶜ = 0 ∧ (∀ p ∈ S, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧
  ∀ j : ℕ, 1 ≤ j → j ≤ J →
    |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧
    (β j < 2 → N ^ (-β j - ε) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)) ∧
  (∀ a b : ℕ, a ≤ b → b ≤ q → h a ≤ h b) ∧
  (∀ k : ℕ, k ≤ q → N ^ (r ((k : ℝ) / (q : ℝ))) ≤ (2 : ℝ) ^ h k ∧
    (2 : ℝ) ^ h k ≤ 2 * N ^ (r ((k : ℝ) / (q : ℝ)))) ∧
  (∀ k : ℕ, k ≤ q → Measurable (F k) ∧ (F k '' S).Finite) ∧
  (∀ k : ℕ, k ≤ q → ∀ x ∈ S, ∀ y ∈ S,
    F k x = F k y ↔ ∀ v : ℕ, v ≤ k →
      Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) ∧
      ∀ j : ℕ, j ≤ J →
        Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ x.1.1) (c v x.2)) =
          Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ y.1.1) (c v y.2)) ∧
        Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ x.1.2) (c v x.2)) =
          Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ y.1.2) (c v y.2))) ∧
  (∀ k : ℕ, k ≤ q → ((F k '' S).ncard : ℝ) ≤ N ^ (u k + ε)) ∧
  (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ S,
    ((F b '' {y | y ∈ S ∧ F a y = F a x}).ncard : ℝ) ≤ N ^ (u b - u a + ε)))
  (fun v t => ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v)

def RecordData (J : ℕ) (d : ℝ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ)
    (q : ℕ) (u : ℕ → ℝ) (ε N : ℝ) : Prop :=
  ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
    (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ))
    (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)),
    Records J d β r l q u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S

def Admissible (J : ℕ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ) :
    ℕ → Finset ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℝ → Prop := fun (q : ℕ) (A : Finset ℕ) (m z : ℕ → ℕ) (γ : ℝ) =>
  A ⊆ Finset.range q ∧ ∀ k ∈ A,
    k + 6 * (J + 1) ≤ q ∧ 1 ≤ m k ∧ m k ≤ J ∧ β (m k) < 2 ∧ z (m k) ≤ k ∧
    γ ≤ (z (m k) : ℝ) / (q : ℝ) ∧
    ∀ x ∈ Set.Icc ((z (m k) : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)),
      r x = (x - β (m k)) / (m k : ℝ) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ J → j ≠ m k → (x - β j) / (j : ℝ) < r x) ∧
      (∀ j : ℕ, j ≤ J → γ ≤ ((J : ℝ) + 1 - (j : ℝ)) * r x - l j x) ∧
      (∀ i : ℕ, 1 ≤ i → m k + i ≤ J → γ ≤ l (m k + i) x + (i : ℝ) * r x - β (m k))

noncomputable def center (h : ℕ → ℕ) (v : ℕ) (t : ℝ) : ℝ :=
  ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v

noncomputable def referencePalette {n₁ n₂ : ℕ} (q v z : ℕ) (β : ℕ → ℝ)
    (N : ℝ) (h : ℕ → ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (x : (Fin n₁ × Fin n₂) × ℝ) : ℤ × ℤ :=
  (Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₁ x.1.1) (center h z x.2)),
   Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₂ x.1.2) (center h z x.2)))

noncomputable def supportLikelihood {Ω Ζ : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ)
    (k : ℕ) (x : Ω) : ℝ :=
  (μ {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x}).toReal /
    (μ {y | y ∈ S ∧ F k y = F k x}).toReal

def PaletteGood {n₁ n₂ : ℕ} (J q v z k : ℕ) (β : ℕ → ℝ) (N θ : ℝ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ))
    (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)) : Prop :=
  μ {x | x ∈ S ∧
    N ^ θ * supportLikelihood μ S F (referencePalette q v z β N h f₁ f₂) k x <
      supportLikelihood μ S F (referencePalette q v z β N h f₁ f₂) (k + 6 * (J + 1)) x} ≤
    ENNReal.ofReal (1 / (2 : ℝ) ^ (J + 10))

def GoodRecordData (J : ℕ) (d : ℝ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ)
    (q : ℕ) (u : ℕ → ℝ) (ε N : ℝ)
    (m z : ℕ → ℕ) (G : Finset ℕ) (θ : ℝ) : Prop :=
  ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
    (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ))
    (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ)),
    Records J d β r l q u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S ∧
    ∀ k ∈ G, PaletteGood J q (m k) (z (m k)) k β N θ f₁ f₂ μ h F S

end Submission.Obl.k4_matching_cofinal_palette_selection
