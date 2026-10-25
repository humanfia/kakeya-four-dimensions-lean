import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_matching_good_step_increment

-- These are definitional abbreviations of the frozen o056 data.
def PaletteBound : Prop := (∀ (n L C M : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ), 1 ≤ C → 1 ≤ M → (∀ x : Fin n, 0 ≤ p x) → (∑ x : Fin n, p x) = 1 → (∀ (k : ℕ) (x y : Fin n), F (k + 1) x = F (k + 1) y → F k x = F k y) → (∀ x : Fin n, ((Finset.univ.filter (fun y : Fin n => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M) → (fun q : ℕ → Fin n → ℝ => (∑ a ∈ Finset.range L, ∑ x : Fin n, p x * max 0 (Real.log (q (a + C) x / q a x))) ≤ (C : ℝ) * Real.log (M : ℝ) + (L : ℝ)) (fun k x => (∑ y ∈ Finset.univ.filter (fun y : Fin n => F k y = F k x ∧ Z y = Z x), p y) / (∑ y ∈ Finset.univ.filter (fun y : Fin n => F k y = F k x), p y)))
def EndpointBound : Prop := (∀ m : ℕ, 1 ≤ m → ∃ A : ℕ, 1 ≤ A ∧ ∀ K : ℝ, 2 ≤ K → ∀ (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin m → ℝ))), (∀ p : Fin (m + 1), |U p| ≤ K) → |s₀| ≤ 1 → (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) → MeasurableSet T → (fun Φ : (ℝ × (Fin m → ℝ)) → (ℝ × (Fin m → ℝ)) => MeasureTheory.volume {x : ℝ × (Fin m → ℝ) | |x.1| ≤ 1 ∧ (∀ p : Fin m, |x.2 p| ≤ 1) ∧ (∀ p q : Fin m, p ≠ q → K⁻¹ ≤ |x.2 p - x.2 q|) ∧ Φ x ∈ T} ≤ ENNReal.ofReal (K ^ A) * MeasureTheory.volume T) (fun x => (x.1, fun j : Fin m => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) + ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) / (((j : ℕ) + 1).factorial : ℝ))))
def BetaValid (D J : ℕ) (β : ℕ → ℝ) : Prop := ((∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0))
noncomputable def radius (J : ℕ) (β : ℕ → ℝ) : ℝ → ℝ := (fun a : ℝ => sSup (Set.image (fun j : ℕ => (a - β j) / (j : ℝ)) (Set.Icc 1 J)))
noncomputable def accuracy (r : ℝ → ℝ) : ℕ → ℝ → ℝ := (fun (j : ℕ) (a : ℝ) => sSup (Set.image (fun x : ℝ => x - (j : ℝ) * r x) (Set.Icc 0 a)))
def Admissible (J : ℕ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ) :
 ℕ → Finset ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℝ → Prop := (fun (q : ℕ) (A : Finset ℕ) (m z : ℕ → ℕ) (γ : ℝ) => A ⊆ Finset.range q ∧ ∀ k ∈ A, k + 6 * (J + 1) ≤ q ∧ 1 ≤ m k ∧ m k ≤ J ∧ β (m k) < 2 ∧ z (m k) ≤ k ∧ γ ≤ (z (m k) : ℝ) / (q : ℝ) ∧ ∀ x ∈ Set.Icc ((z (m k) : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)), r x = (x - β (m k)) / (m k : ℝ) ∧ (∀ j : ℕ, 1 ≤ j → j ≤ J → j ≠ m k → (x - β j) / (j : ℝ) < r x) ∧ (∀ j : ℕ, j ≤ J → γ ≤ ((J : ℝ) + 1 - (j : ℝ)) * r x - l j x) ∧ (∀ i : ℕ, 1 ≤ i → m k + i ≤ J → γ ≤ l (m k + i) x + (i : ℝ) * r x - β (m k)))
def StepAdmissible (J : ℕ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ)
 (q k v z : ℕ) (γ : ℝ) : Prop := k + 6 * (J + 1) ≤ q ∧ 1 ≤ v ∧ v ≤ J ∧ β (v) < 2 ∧ z ≤ k ∧ γ ≤ (z : ℝ) / (q : ℝ) ∧ ∀ x ∈ Set.Icc ((z : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)), r x = (x - β (v)) / (v : ℝ) ∧ (∀ j : ℕ, 1 ≤ j → j ≤ J → j ≠ v → (x - β j) / (j : ℝ) < r x) ∧ (∀ j : ℕ, j ≤ J → γ ≤ ((J : ℝ) + 1 - (j : ℝ)) * r x - l j x) ∧ (∀ i : ℕ, 1 ≤ i → v + i ≤ J → γ ≤ l (v + i) x + (i : ℝ) * r x - β (v))
def RecordAt (J q : ℕ) (d : ℝ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ)
 (u : ℕ → ℝ) (ε N : ℝ) (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)) (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)) : Prop := (fun c : ℕ → ℝ → ℝ => (n₁ : ℝ) ≤ N ^ (d + ε) ∧ (n₂ : ℝ) ≤ N ^ (d + ε) ∧ (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ ε) ∧ (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ ε) ∧ (∀ i : Fin n₁, 0 ≤ π₁ i) ∧ (∀ i : Fin n₂, 0 ≤ π₂ i) ∧ (∑ i : Fin n₁, π₁ i) = 1 ∧ (∑ i : Fin n₂, π₂ i) = 1 ∧ MeasureTheory.IsProbabilityMeasure μ ∧ (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₁ i) * MeasureTheory.volume E) ∧ (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₂ i) * MeasureTheory.volume E) ∧ MeasurableSet S ∧ μ Sᶜ = 0 ∧ (∀ p ∈ S, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧ ∀ j : ℕ, 1 ≤ j → j ≤ J → |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧ (β j < 2 → N ^ (-β j - ε) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → h a ≤ h b) ∧ (∀ k : ℕ, k ≤ q → N ^ (r ((k : ℝ) / (q : ℝ))) ≤ (2 : ℝ) ^ h k ∧ (2 : ℝ) ^ h k ≤ 2 * N ^ (r ((k : ℝ) / (q : ℝ)))) ∧ (∀ k : ℕ, k ≤ q → Measurable (F k) ∧ (F k '' S).Finite) ∧ (∀ k : ℕ, k ≤ q → ∀ x ∈ S, ∀ y ∈ S, F k x = F k y ↔ ∀ v : ℕ, v ≤ k → Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) ∧ ∀ j : ℕ, j ≤ J → Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ x.1.1) (c v x.2)) = Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ y.1.1) (c v y.2)) ∧ Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ x.1.2) (c v x.2)) = Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ y.1.2) (c v y.2))) ∧ (∀ k : ℕ, k ≤ q → ((F k '' S).ncard : ℝ) ≤ N ^ (u k + ε)) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ S, ((F b '' {y | y ∈ S ∧ F a y = F a x}).ncard : ℝ) ≤ N ^ (u b - u a + ε))) (fun v t => ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v)
def RecordData (J : ℕ) (d : ℝ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ) :
 ℕ → (ℕ → ℝ) → ℝ → ℝ → Prop := (fun (q : ℕ) (u : ℕ → ℝ) (ε N : ℝ) => ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)) (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)), (fun c : ℕ → ℝ → ℝ => (n₁ : ℝ) ≤ N ^ (d + ε) ∧ (n₂ : ℝ) ≤ N ^ (d + ε) ∧ (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ ε) ∧ (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ ε) ∧ (∀ i : Fin n₁, 0 ≤ π₁ i) ∧ (∀ i : Fin n₂, 0 ≤ π₂ i) ∧ (∑ i : Fin n₁, π₁ i) = 1 ∧ (∑ i : Fin n₂, π₂ i) = 1 ∧ MeasureTheory.IsProbabilityMeasure μ ∧ (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₁ i) * MeasureTheory.volume E) ∧ (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₂ i) * MeasureTheory.volume E) ∧ MeasurableSet S ∧ μ Sᶜ = 0 ∧ (∀ p ∈ S, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧ ∀ j : ℕ, 1 ≤ j → j ≤ J → |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧ (β j < 2 → N ^ (-β j - ε) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → h a ≤ h b) ∧ (∀ k : ℕ, k ≤ q → N ^ (r ((k : ℝ) / (q : ℝ))) ≤ (2 : ℝ) ^ h k ∧ (2 : ℝ) ^ h k ≤ 2 * N ^ (r ((k : ℝ) / (q : ℝ)))) ∧ (∀ k : ℕ, k ≤ q → Measurable (F k) ∧ (F k '' S).Finite) ∧ (∀ k : ℕ, k ≤ q → ∀ x ∈ S, ∀ y ∈ S, F k x = F k y ↔ ∀ v : ℕ, v ≤ k → Int.floor (x.2 * (2 : ℝ) ^ h v) = Int.floor (y.2 * (2 : ℝ) ^ h v) ∧ ∀ j : ℕ, j ≤ J → Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ x.1.1) (c v x.2)) = Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ y.1.1) (c v y.2)) ∧ Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ x.1.2) (c v x.2)) = Int.floor (N ^ (l j ((v : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ y.1.2) (c v y.2))) ∧ (∀ k : ℕ, k ≤ q → ((F k '' S).ncard : ℝ) ≤ N ^ (u k + ε)) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ S, ((F b '' {y | y ∈ S ∧ F a y = F a x}).ncard : ℝ) ≤ N ^ (u b - u a + ε))) (fun v t => ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v))
noncomputable def palette (q v z n₁ n₂ : ℕ) (β : ℕ → ℝ) (N : ℝ)
 (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ :=
 (fun c : ℕ → ℝ → ℝ => fun x : ((Fin n₁ × Fin n₂) × ℝ) =>
 (Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₁ x.1.1) (c z x.2)),
  Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₂ x.1.2) (c z x.2)))) (fun v t => ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v)
noncomputable def posterior (n₁ n₂ : ℕ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ))
 (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (Z : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ) : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℝ := (fun k (x : ((Fin n₁ × Fin n₂) × ℝ)) =>
 (μ {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x}).toReal /
 (μ {y | y ∈ S ∧ F k y = F k x}).toReal)
def PaletteGood (J q v z n₁ n₂ : ℕ) (β : ℕ → ℝ) (N θ : ℝ)
 (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
 (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)) (h : ℕ → ℕ)
 (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (k : ℕ) : Prop :=
 (fun Z : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ =>
 (fun P : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℝ =>
 μ {x | x ∈ S ∧ N ^ θ * P k x < P (k + 6 * (J + 1)) x} ≤
 ENNReal.ofReal (1 / (2 : ℝ) ^ (J + 10))) (fun k (x : ((Fin n₁ × Fin n₂) × ℝ)) =>
 (μ {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x}).toReal /
 (μ {y | y ∈ S ∧ F k y = F k x}).toReal)) ((fun c : ℕ → ℝ → ℝ => fun x : ((Fin n₁ × Fin n₂) × ℝ) =>
 (Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₁ x.1.1) (c z x.2)),
  Int.floor (N ^ (β v + 6 / (q : ℝ)) * iteratedDeriv v (f₂ x.1.2) (c z x.2)))) (fun v t => ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v))
def GoodRecordData (J : ℕ) (d : ℝ) (β : ℕ → ℝ) (r : ℝ → ℝ) (l : ℕ → ℝ → ℝ)
 (q : ℕ) (u : ℕ → ℝ) (m z : ℕ → ℕ) (G : Finset ℕ) (θ ε N : ℝ) : Prop :=
 ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)) (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)), RecordAt J q d β r l u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S ∧
 ∀ k ∈ G, PaletteGood J q (m k) (z (m k)) n₁ n₂ β N θ f₁ f₂ μ h F S k

def Certificate (v q : ℕ) (Δ θ κ N : ℝ) : Prop := ∃ (K : ℝ) (n : ℕ) (w : Fin n → ℝ)
 (U : Fin n → Fin (v + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin v → ℝ))),
 2 ≤ K ∧ K ≤ N ^ κ ∧ (∀ i : Fin n, 0 ≤ w i) ∧ (∑ i : Fin n, w i) ≤ 1 ∧
 (∀ (i : Fin n) (p : Fin (v + 1)), |U i p| ≤ K) ∧ |s₀| ≤ 1 ∧
 (∀ (i : Fin n) (p : Fin v), K⁻¹ ≤ |U i p.succ - U i p.castSucc|) ∧
 MeasurableSet T ∧ MeasureTheory.volume T ≤ ENNReal.ofReal (K * N ^ (Δ - (1 / (v : ℝ) + ((v : ℝ) + 1) / 2) / (q : ℝ))) ∧
 1 / 4 ≤ K * N ^ (((v : ℝ) + 1) * θ) *
 (∑ i : Fin n, w i * (MeasureTheory.volume {x : ℝ × (Fin v → ℝ) | |x.1| ≤ 1 ∧
 (∀ p : Fin v, |x.2 p| ≤ 1) ∧
 (∀ p r : Fin v, p ≠ r → K⁻¹ ≤ |x.2 p - x.2 r|) ∧
 (fun x : ℝ × (Fin v → ℝ) => (x.1, fun j : Fin v =>
 (U i 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) +
 ∑ p : Fin v, (U i p.succ - U i p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) /
 (((j : ℕ) + 1).factorial : ℝ))) x ∈ T}).toReal)

end Submission.Obl.k4_matching_good_step_increment
