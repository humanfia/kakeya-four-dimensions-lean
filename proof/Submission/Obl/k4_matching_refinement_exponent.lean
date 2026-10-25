import Mathlib
import ChallengeDeps
import Submission.Obl.k4_matching_palette_likelihood
import Submission.Obl.k4_matching_endpoint_volume
import Submission.Obl.k4_matching_gap_regularization
import Submission.Obl.k4_matching_homogeneous_records
import Submission.Obl.k4_matching_good_step_increment
import Submission.Obl.k4_matching_trimmed_grid
import Submission.Obl.k4_matching_refinement_exponent.Interfaces
import Submission.Obl.k4_matching_refinement_exponent.Numerics

open Submission.Obl.k4_matching_refinement_exponent

theorem Submission.k4_matching_refinement_exponent : (∀ (n L C M : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ), 1 ≤ C → 1 ≤ M → (∀ x : Fin n, 0 ≤ p x) → (∑ x : Fin n, p x) = 1 → (∀ (k : ℕ) (x y : Fin n), F (k + 1) x = F (k + 1) y → F k x = F k y) → (∀ x : Fin n, ((Finset.univ.filter (fun y : Fin n => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M) → (fun q : ℕ → Fin n → ℝ => (∑ a ∈ Finset.range L, ∑ x : Fin n, p x * max 0 (Real.log (q (a + C) x / q a x))) ≤ (C : ℝ) * Real.log (M : ℝ) + (L : ℝ)) (fun k x => (∑ y ∈ Finset.univ.filter (fun y : Fin n => F k y = F k x ∧ Z y = Z x), p y) / (∑ y ∈ Finset.univ.filter (fun y : Fin n => F k y = F k x), p y))) → (∀ m : ℕ, 1 ≤ m → ∃ A : ℕ, 1 ≤ A ∧ ∀ K : ℝ, 2 ≤ K → ∀ (U : Fin (m + 1) → ℝ) (s₀ : ℝ) (T : Set (ℝ × (Fin m → ℝ))), (∀ p : Fin (m + 1), |U p| ≤ K) → |s₀| ≤ 1 → (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) → MeasurableSet T → (fun Φ : (ℝ × (Fin m → ℝ)) → (ℝ × (Fin m → ℝ)) => MeasureTheory.volume {x : ℝ × (Fin m → ℝ) | |x.1| ≤ 1 ∧ (∀ p : Fin m, |x.2 p| ≤ 1) ∧ (∀ p q : Fin m, p ≠ q → K⁻¹ ≤ |x.2 p - x.2 q|) ∧ Φ x ∈ T} ≤ ENNReal.ofReal (K ^ A) * MeasureTheory.volume T) (fun x => (x.1, fun j : Fin m => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) + ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) / (((j : ℕ) + 1).factorial : ℝ)))) → ∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → (fun Bad : ℝ → ℝ → Prop => (∃ N : ℕ → ℝ, ∀ k : ℕ, (k : ℝ) + 2 ≤ N k ∧ Bad (1 / ((k : ℝ) + 1)) (N k)) → 1 ≤ d) (fun (η N : ℝ) => ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) ∧ (n₂ : ℝ) ≤ N ^ (d + η) ∧ (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) ∧ (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) ∧ (∀ i : Fin n₁, 0 ≤ π₁ i) ∧ (∀ i : Fin n₂, 0 ≤ π₂ i) ∧ (∑ i : Fin n₁, π₁ i) = 1 ∧ (∑ i : Fin n₂, π₂ i) = 1 ∧ MeasureTheory.IsProbabilityMeasure μ ∧ (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) ∧ (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) ∧ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0) := by
  intro hPalette hEndpoint D J hD hDJ d hd hseq
  obtain ⟨β, hβ, hgap⟩ :=
    Submission.k4_matching_gap_regularization D J hD hDJ d hd hseq
  let r : ℝ → ℝ := radius J β
  let l : ℕ → ℝ → ℝ := accuracy r
  have hg : Cofinal (GapData J d β) := hgap
  by_contra hf
  have hdlt : d < 1 := lt_of_not_ge hf
  let δ : ℝ := (1 - d) / 8
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨γ, hγ, hgrid⟩ :=
    Submission.k4_matching_trimmed_grid D J hD hDJ β hβ δ hδ
  obtain ⟨Q, hQ⟩ :=
    Submission.k4_matching_good_step_increment hPalette hEndpoint D J hD hDJ d hd
      β hβ γ hγ δ hδ
  obtain ⟨q, hQq, hq, A, m, z, hAdm, hcoverage⟩ := hgrid Q
  obtain ⟨u, ⟨hunonneg, humono, huupper⟩, hrecords⟩ :=
    Submission.k4_matching_homogeneous_records D J hD hDJ d hd β hβ hg q hq
  obtain ⟨G, hGA, hbad, hinc⟩ := hQ q hQq hq A m z u hAdm hrecords
  have hAd : Admissible J β r l q A m z γ := hAdm
  have hm : ∀ k ∈ A, 1 ≤ m k := fun k hk => (hAd.2 k hk).2.1
  have hsum := sum_good_increments q hq A G m u δ hδ.le hAd.1 hGA hm humono hbad hinc
  have hz : 0 ≤ u 0 := hunonneg 0 (Nat.zero_le q)
  change u q ≤ d + r 1 at huupper
  change 1 + r 1 - δ ≤ ∑ k ∈ A, (1 + 1 / (m k : ℝ)) / (q : ℝ) at hcoverage
  dsimp [δ] at hsum hcoverage
  linarith
