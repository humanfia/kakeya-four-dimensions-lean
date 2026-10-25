import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_scalar_marked_packet_recovery

noncomputable abbrev Subpower := (fun (N K : ℕ → ℝ) => ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε))

noncomputable abbrev Noise := (fun (σ : ℝ) => (MeasureTheory.Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) σ))))

noncomputable abbrev MarkedPrior := (fun (σ : ℝ) (H : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) => (∑ j, ENNReal.ofReal (w j) • MeasureTheory.Measure.map (fun u : Fin 5 → ℝ => ((j : ℕ), b₀ j + u)) (Noise σ)))

noncomputable abbrev MarkedEvent := (fun (H J : ℕ) (mark : Fin H → Fin J → Bool) => ({p : (ℕ × (Fin 5 → ℝ)) × ℝ | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧ ∃ z : Fin J, mark j z = true ∧ p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))}))

noncomputable abbrev MarkedLaw := (fun (σ : ℝ) (H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => (((MarkedPrior σ H b₀ w).prod MeasureTheory.volume).restrict (MarkedEvent H J mark)))

noncomputable abbrev Tables := (fun (N K m : ℝ) (M H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => (1 ≤ J ∧ (H : ℝ) ≤ N ^ (M : ℝ) ∧ (J : ℝ) ≤ N ^ (M : ℝ) ∧ 1 ≤ (J : ℝ) * N ^ (-m) ∧ (J : ℝ) * N ^ (-m) ≤ 2 ∧ (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ (∀ j e, |b₀ j e| ≤ K) ∧ ENNReal.ofReal (K⁻¹) ≤ MarkedLaw (N ^ (-m)) H J b₀ w mark Set.univ))

noncomputable abbrev Coupling := (fun (N K s m : ℝ) (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => (Measurable tag ∧ (∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}) ∧ (∀ l e, |b l e - b₀ (tag l) e| ≤ N ^ (-10 * (m + s + 1))) ∧ (∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤ μ {p | tag p.1 = j ∧ p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))})))

noncomputable abbrev NoisyOutput := (fun (N d s m c ε : ℝ) (angular : Bool) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) => (((fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => ((fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => ∃ (n : ℕ) (β t₀ q : ℝ) (A : Fin n → Set (ℕ × (Fin 5 → ℝ))) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), N ^ (-ε) ≤ q ∧ 0 ≤ t₀ ∧ t₀ + q ≤ 1 ∧ N ^ (-m) / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc t₀ (t₀ + q), |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-s)) ∧ ENNReal.ofReal (q * c * (N ^ (-s)) ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc t₀ (t₀ + q))) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | (∃ i, p.1 ∈ A i) ∧ p.2 ∈ Set.Icc t₀ (t₀ + q)}) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4))) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 0 + t * l.2 1))))

noncomputable abbrev BlockOutput := (fun (N d s m c ε : ℝ) (angular : Bool) (α : Type) [MeasurableSpace α] (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) => (((fun (y : α → ℝ → ℝ) => ((fun (x : α → ℝ → ℝ) => ∃ (n : ℕ) (β t₀ q : ℝ) (A : Fin n → Set α) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), N ^ (-ε) ≤ q ∧ 0 ≤ t₀ ∧ t₀ + q ≤ 1 ∧ N ^ (-m) / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc t₀ (t₀ + q), |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-s)) ∧ ENNReal.ofReal (c * (N ^ (-s)) ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i, p.1 ∈ A i}) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4))) (fun l t => b l 0 + t * b l 1))))

end Submission.Obl.k4_scalar_marked_packet_recovery
