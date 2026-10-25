-- Adapted from this LOT tree, o070/x0242 split s028, Interfaces.lean.
import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_matching_switching_target_certificate

abbrev GeometricCoverStatement : Prop :=
∀ (D J : ℕ), 1 ≤ D → D < J → ∀ β : ℕ → ℝ,
 ((∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0)) →
 (fun r : ℝ → ℝ => (fun l : ℕ → ℝ → ℝ => ∀ γ : ℝ, 0 < γ → ∀ q : ℕ, 1 ≤ q → 4 ≤ γ * (q : ℝ) → ∀ (k m z : ℕ) (u : ℕ → ℝ),
 (k + 6 * (J + 1) ≤ q ∧ 1 ≤ m ∧ m ≤ J ∧ β m < 2 ∧ z ≤ k ∧ γ ≤ (z : ℝ) / (q : ℝ) ∧
 ∀ x ∈ Set.Icc ((z : ℝ) / (q : ℝ)) (((k + 6 * (J + 1) : ℕ) : ℝ) / (q : ℝ)),
 r x = (x - β m) / (m : ℝ) ∧
 (∀ j : ℕ, 1 ≤ j → j ≤ J → j ≠ m → (x - β j) / (j : ℝ) < r x) ∧
 (∀ j : ℕ, j ≤ J → γ ≤ ((J : ℝ) + 1 - (j : ℝ)) * r x - l j x) ∧
 (∀ i : ℕ, 1 ≤ i → m + i ≤ J → γ ≤ l (m + i) x + (i : ℝ) * r x - β m)) →
 ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R : ℝ, 2 ≤ R ∧
 ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ N : ℝ, R ≤ N →
 ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ)
 (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)),
 ((fun c : ℕ → ℝ → ℝ => (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧
 (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧
 (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ ε) ∧
 (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ ε) ∧
 (∀ p ∈ S, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧
 ∀ j : ℕ, 1 ≤ j → j ≤ J → |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧
 (β j < 2 → N ^ (-β j - ε) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)) ∧
 (∀ a b : ℕ, a ≤ b → b ≤ q → h a ≤ h b) ∧
 (∀ a : ℕ, a ≤ q → N ^ (r ((a : ℝ) / (q : ℝ))) ≤ (2 : ℝ) ^ h a ∧ (2 : ℝ) ^ h a ≤ 2 * N ^ (r ((a : ℝ) / (q : ℝ)))) ∧
 (∀ a : ℕ, a ≤ q → Measurable (F a) ∧ (F a '' S).Finite) ∧
 (∀ a : ℕ, a ≤ q → ∀ x ∈ S, ∀ y ∈ S, F a x = F a y ↔ ∀ b : ℕ, b ≤ a →
 Int.floor (x.2 * (2 : ℝ) ^ h b) = Int.floor (y.2 * (2 : ℝ) ^ h b) ∧
 ∀ j : ℕ, j ≤ J → Int.floor (N ^ (l j ((b : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ x.1.1) (c b x.2)) =
 Int.floor (N ^ (l j ((b : ℝ) / (q : ℝ))) * iteratedDeriv j (f₁ y.1.1) (c b y.2)) ∧
 Int.floor (N ^ (l j ((b : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ x.1.2) (c b x.2)) =
 Int.floor (N ^ (l j ((b : ℝ) / (q : ℝ))) * iteratedDeriv j (f₂ y.1.2) (c b y.2))) ∧
 (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ S, ((F b '' {y | y ∈ S ∧ F a y = F a x}).ncard : ℝ) ≤ N ^ (u b - u a + ε))) (fun b t => ((Int.floor (t * (2 : ℝ) ^ h b) : ℝ) + 1 / 2) / (2 : ℝ) ^ h b)) →
  (fun H : ℕ => (fun F₀ : ((Fin n₁ × Fin n₂) × ℝ) → ℕ => (fun F₁ : ((Fin n₁ × Fin n₂) × ℝ) → ℕ => (fun Z : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ => (fun σ : ((Fin n₁ × Fin n₂) × ℝ) → ((Fin n₁ × Fin n₂) × ℝ) → ℝ => (fun Φ : (Fin (m + 1) → ℝ) → ℝ → (ℝ × (Fin m → ℝ)) → (ℝ × (Fin m → ℝ)) => (fun V : ℝ => ∃ K δ : ℝ, 2 ≤ K ∧ K ≤ N ^ η ∧ 0 < δ ∧ (∀ a ∈ S, ∃ (A : Finset ℕ) (C : ℕ → (ℤ × ℤ) → Bool → ℝ) (T : Set (ℝ × (Fin m → ℝ))),
 |σ a a| ≤ 1 ∧ (A.card : ℝ) ≤ K ∧
 (∀ e ∈ S, F₀ e ∈ A → ∀ c : Bool, |C (F₀ e) (Z e) c| ≤ K) ∧
 (∀ e ∈ S, F₀ e ∈ A → 2 / K ≤ |C (F₀ e) (Z e) true - C (F₀ e) (Z e) false|) ∧
 MeasurableSet T ∧ MeasureTheory.volume T ≤ ENNReal.ofReal (K * V) ∧
 ∀ (E W : ℕ → ((Fin n₁ × Fin n₂) × ℝ)) (c : ℕ → Bool), E 0 = a →
 (∀ p : ℕ, p ≤ m + 1 → E p ∈ S) →
 (∀ p : ℕ, p ≤ m → W p ∈ S ∧ F₁ (W p) = F₁ (E p) ∧
   (if c p then (W p).1.1 = (E (p + 1)).1.1 else (W p).1.2 = (E (p + 1)).1.2) ∧
   Int.floor ((W p).2 * (2 : ℝ) ^ H) = Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ H)) →
 (∀ p : ℕ, p ≤ m + 1 → F₀ (E p) ∈ A) ∧
 (∀ p : ℕ, p ≤ m → F₀ (W p) ∈ A) ∧
 ∀ x : ℝ × (Fin m → ℝ), |x.1 - σ a (E (m + 1))| ≤ δ →
 (∀ p : Fin m, |x.2 p - σ a (E ((p : ℕ) + 1))| ≤ δ) →
 Φ (fun p : Fin (m + 1) => C (F₀ (W p)) (Z (W p)) (c p)) (σ a a) x ∈ T)) (N ^ (u (k + 1) - u k - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ)))) ((fun (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (x : ℝ × (Fin m → ℝ)) => (x.1, fun j : Fin m => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) + ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) / (((j : ℕ) + 1).factorial : ℝ))))) ((fun (a e : ((Fin n₁ × Fin n₂) × ℝ)) => (e.2 - (((Int.floor (a.2 * (2 : ℝ) ^ H) : ℝ) + 1 / 2) / (2 : ℝ) ^ H)) * (2 : ℝ) ^ H))) (fun x =>
 (Int.floor (N ^ (β m + 6 / (q : ℝ)) * iteratedDeriv m (f₁ x.1.1) (((Int.floor (x.2 * (2 : ℝ) ^ h z) : ℝ) + 1 / 2) / (2 : ℝ) ^ h z)),
 Int.floor (N ^ (β m + 6 / (q : ℝ)) * iteratedDeriv m (f₂ x.1.2) (((Int.floor (x.2 * (2 : ℝ) ^ h z) : ℝ) + 1 / 2) / (2 : ℝ) ^ h z))))) (F (k + 6 * (J + 1)))) (F k)) (h k)) (fun j a => sSup (Set.image (fun x : ℝ => x - (j : ℝ) * r x) (Set.Icc 0 a)))) (fun a => sSup (Set.image (fun j : ℕ => (a - β j) / (j : ℝ)) (Set.Icc 1 J)))

abbrev AbstractSwitchingStatement : Prop :=
∀ m : ℕ, 1 ≤ m → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
 ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, 2 ≤ R ∧ ∀ N : ℝ, R ≤ N →
 ∀ B K δ V : ℝ, 1 ≤ B → B ≤ N ^ η → 2 ≤ K → K ≤ N ^ η → 0 < δ → 0 ≤ V →
 ∀ n₁ n₂ : ℕ, 
 ∀ (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ))
 (H : ℕ) (F₀ F₁ : ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (Z : ((Fin n₁ × Fin n₂) × ℝ) → ℤ × ℤ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)),
 (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) →
 (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ →
 (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₁ i) * MeasureTheory.volume E) →
 (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₂ i) * MeasureTheory.volume E) →
 MeasurableSet S → μ Sᶜ = 0 → (∀ e ∈ S, e.2 ∈ Set.Ico (0 : ℝ) 1) →
 (∀ x ∈ S, ∀ y ∈ S, F₁ x = F₁ y → F₀ x = F₀ y) →
 (∀ x ∈ S, ∀ y ∈ S, F₀ x = F₀ y → Int.floor (x.2 * (2 : ℝ) ^ H) = Int.floor (y.2 * (2 : ℝ) ^ H)) →
 (∃ H' : ℕ, H ≤ H' ∧ ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 →
 Int.floor (x.2 * (2 : ℝ) ^ H') = Int.floor (y.2 * (2 : ℝ) ^ H') → F₀ x = F₀ y ∧ F₁ x = F₁ y ∧ Z x = Z y) →
 ((fun P : (((Fin n₁ × Fin n₂) × ℝ) → ℕ) → ((Fin n₁ × Fin n₂) × ℝ) → ℝ => μ {x | x ∈ S ∧ N ^ θ * P F₀ x < P F₁ x} ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ (m + 10))) (fun (F : ((Fin n₁ × Fin n₂) × ℝ) → ℕ) (x : ((Fin n₁ × Fin n₂) × ℝ)) =>
 (μ {y | y ∈ S ∧ F y = F x ∧ Z y = Z x}).toReal / (μ {y | y ∈ S ∧ F y = F x}).toReal)) →
 (fun σ : ((Fin n₁ × Fin n₂) × ℝ) → ((Fin n₁ × Fin n₂) × ℝ) → ℝ => (fun Φ : (Fin (m + 1) → ℝ) → ℝ → (ℝ × (Fin m → ℝ)) → (ℝ × (Fin m → ℝ)) => (∀ a ∈ S, ∃ (A : Finset ℕ) (C : ℕ → (ℤ × ℤ) → Bool → ℝ) (T : Set (ℝ × (Fin m → ℝ))),
 |σ a a| ≤ 1 ∧ (A.card : ℝ) ≤ K ∧
 (∀ e ∈ S, F₀ e ∈ A → ∀ c : Bool, |C (F₀ e) (Z e) c| ≤ K) ∧
 (∀ e ∈ S, F₀ e ∈ A → 2 / K ≤ |C (F₀ e) (Z e) true - C (F₀ e) (Z e) false|) ∧
 MeasurableSet T ∧ MeasureTheory.volume T ≤ ENNReal.ofReal (K * V) ∧
 ∀ (E W : ℕ → ((Fin n₁ × Fin n₂) × ℝ)) (c : ℕ → Bool), E 0 = a →
 (∀ p : ℕ, p ≤ m + 1 → E p ∈ S) →
 (∀ p : ℕ, p ≤ m → W p ∈ S ∧ F₁ (W p) = F₁ (E p) ∧
   (if c p then (W p).1.1 = (E (p + 1)).1.1 else (W p).1.2 = (E (p + 1)).1.2) ∧
   Int.floor ((W p).2 * (2 : ℝ) ^ H) = Int.floor ((E (p + 1)).2 * (2 : ℝ) ^ H)) →
 (∀ p : ℕ, p ≤ m + 1 → F₀ (E p) ∈ A) ∧
 (∀ p : ℕ, p ≤ m → F₀ (W p) ∈ A) ∧
 ∀ x : ℝ × (Fin m → ℝ), |x.1 - σ a (E (m + 1))| ≤ δ →
 (∀ p : Fin m, |x.2 p - σ a (E ((p : ℕ) + 1))| ≤ δ) →
 Φ (fun p : Fin (m + 1) => C (F₀ (W p)) (Z (W p)) (c p)) (σ a a) x ∈ T) → ∃ (L : ℝ) (n : ℕ) (w : Fin n → ℝ) (U : Fin n → Fin (m + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin m → ℝ))),
 2 ≤ L ∧ L ≤ N ^ κ ∧ (∀ i : Fin n, 0 ≤ w i) ∧ (∑ i : Fin n, w i) ≤ 1 ∧
 (∀ (i : Fin n) (p : Fin (m + 1)), |U i p| ≤ L) ∧ |s₀| ≤ 1 ∧
 (∀ (i : Fin n) (p : Fin m), L⁻¹ ≤ |U i p.succ - U i p.castSucc|) ∧ MeasurableSet T ∧
 MeasureTheory.volume T ≤ ENNReal.ofReal (L * V) ∧
 1 / 4 ≤ L * N ^ (((m : ℝ) + 1) * θ) *
 (∑ i : Fin n, w i * (MeasureTheory.volume {x : ℝ × (Fin m → ℝ) | |x.1| ≤ 1 ∧
 (∀ p : Fin m, |x.2 p| ≤ 1) ∧ (∀ p r : Fin m, p ≠ r → L⁻¹ ≤ |x.2 p - x.2 r|) ∧ Φ (U i) s₀ x ∈ T}).toReal)) ((fun (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (x : ℝ × (Fin m → ℝ)) => (x.1, fun j : Fin m => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) + ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) / (((j : ℕ) + 1).factorial : ℝ))))) ((fun (a e : ((Fin n₁ × Fin n₂) × ℝ)) => (e.2 - (((Int.floor (a.2 * (2 : ℝ) ^ H) : ℝ) + 1 / 2) / (2 : ℝ) ^ H)) * (2 : ℝ) ^ H))

end Submission.Obl.k4_matching_switching_target_certificate
