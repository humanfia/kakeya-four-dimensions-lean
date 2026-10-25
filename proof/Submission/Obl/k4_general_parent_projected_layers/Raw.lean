import Mathlib

/-!
# From ordinary preparation to the frozen statement

`Scalar` is the frozen scalar hypothesis and `RawLayer` the frozen `Layer`
proposition, both verbatim (`RawLayer` with the trajectory `x` as a parameter).
`rawLayer_of_preparation` turns ordinary projected preparation of a prepared
model into `RawLayer ... false`; `main_of_preparation` is the frozen theorem from
the principle that Scalar gives ordinary preparation for every valid model.
-/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial

set_option linter.unusedVariables false

/-- The frozen scalar hypothesis, verbatim. -/
def Scalar : Prop :=
  (∀ d s m C S U ε:ℝ,0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m → 0 < ε → ∃ η:ℝ,0 < η ∧ ∃ N₀:ℝ,2 ≤ N₀ ∧ ∀ N:ℝ,N₀ ≤ N → ∀ (α:Type) [MeasurableSpace α] (ν:MeasureTheory.Measure α) (μ:MeasureTheory.Measure (α × ℝ)) (b:α → Fin 5 → ℝ) (c:ℝ) (angular:Bool),(fun a:ℝ => (fun σ:ℝ => (fun y:α → ℝ → ℝ => (fun x:α → ℝ → ℝ => (fun z:α × ℝ → Fin 2 → ℤ => Measurable b → MeasureTheory.IsProbabilityMeasure ν → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0:ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ l i,|b l i| ≤ N ^ η) → N ^ (-C) ≤ c → c ≤ N ^ C → (∀ (r:ℝ) (q:Fin 2 → ℤ) (j:ℤ),0 ≤ r → r ≤ s → μ {p | z p = q ∧ ⌊x p.1 p.2 / (N ^ (-r))⌋ = j} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * (N ^ (-r)) ^ d)) → (∃ F:Finset ((Fin 2 → ℤ) × ℤ),(F.card:ℝ) * σ ^ 2 ≤ N ^ η * c⁻¹ * a ^ (-d) ∧ ∀ᵐ p ∂μ,(z p,⌊x p.1 p.2 / a⌋) ∈ F) → (angular = true → ∀ (r:ℝ) (q:Fin 2 → ℤ) (j k:ℤ),0 < r → r ≤ U → μ {p | z p = q ∧ ⌊x p.1 p.2 / a⌋ = j ∧ ⌊b p.1 1 / (N ^ (-r))⌋ = k} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * a ^ d * N ^ (-S * r))) → ∃ (n:ℕ) (β:ℝ) (A:Fin n → Set α) (u v:Fin n → ℝ) (P:Fin n → MvPolynomial (Fin 2) ℝ),σ / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i,MeasurableSet (A i)) ∧ (∀ i j,i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i,|u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (0:ℝ) 1,∀ w ∈ Set.Icc (-1:ℝ) 1,|MvPolynomial.eval ![t,u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i,∀ t ∈ Set.Icc (0:ℝ) 1,|y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t,y l t] (P i)| ≤ N ^ ε * a) ∧ ENNReal.ofReal (c * a ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc (0:ℝ) 1)) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i,p.1 ∈ A i}) (fun p => ![⌊p.2 / σ⌋,⌊y p.1 p.2 / σ⌋])) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4)) (fun l t => b l 0 + t * b l 1)) (N ^ (-m))) (N ^ (-s)))

/-- The frozen `Layer wide` proposition, verbatim, for the trajectory `x`. -/
def RawLayer {α : Type} [MeasurableSpace α] (N K : ℕ → ℝ) (d ℓ U : ℝ)
    (ρ : ℕ → MeasureTheory.Measure (α × ℝ)) (π : ℕ → MeasureTheory.Measure ℝ)
    (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ)
    (x : ℕ → α → ℝ → Fin 4 → ℝ) (wide : Bool) : Prop :=
  ∃ L:ℝ,2 < L ∧ ∀ a:ℝ,0 < a → (if wide then L else 2) * a < U → ∀ D:Finset ℝ,(∀ s ∈ D,a ≤ s ∧ s ≤ 2 * a) → ∀ m:ℝ,L * a < m → ∃ τ:ℕ → ℕ,StrictMono τ ∧ ∃ H:ℕ → ℝ,(∀ k,1 ≤ H k ∧ K (τ k) ≤ H k) ∧ (∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,H k ≤ N (τ k) ^ ε) ∧ ∃ (ρ':ℕ → MeasureTheory.Measure (α × ℝ)) (β:ℕ → ℝ → ℝ) (n':ℕ → ℝ → ℕ) (C:(k:ℕ) → (s:ℝ) → Fin (n' k s) → Set α) (tag:(k:ℕ) → (s:ℝ) → Fin (n' k s) → Fin 2 → ℤ) (u v:(k:ℕ) → (s:ℝ) → Fin (n' k s) → ℝ) (G:(k:ℕ) → (s:ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),(∀ k,ρ' k ≤ ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ) ∧ ∀ k s,s ∈ D → 0 < β k s ∧ (N (τ k) ^ (-ℓ * s) * (if wide then 1 else N (τ k) ^ (-L * a))) / H k ≤ β k s ∧ β k s ≤ H k * N (τ k) ^ (-ℓ * s) ∧ (∀ i,MeasurableSet (C k s i)) ∧ (∀ i i',i ≠ i' → Disjoint (C k s i) (C k s i')) ∧ (∀ i,|u k s i| + |v k s i| ≤ H k ∧ (G k s i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (0:ℝ) 1,∀ w ∈ Set.Icc (-1:ℝ) 1,|MvPolynomial.eval ![t,u k s i + t * v k s i + β k s * w] (G k s i)| ≤ H k) ∧ (∀ l ∈ C k s i,⌊b (τ k) l 3 / (N (τ k) ^ (-m))⌋ = tag k s i 0 ∧ ⌊b (τ k) l 0 / (N (τ k) ^ (-m))⌋ = tag k s i 1 ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,|(x (τ k) l t) 2 - u k s i - t * v k s i| ≤ H k * β k s ∧ |MvPolynomial.eval (x (τ k) l t) (P (τ k)) - MvPolynomial.eval ![t,(x (τ k) l t) 2] (G k s i)| ≤ H k * N (τ k) ^ (-s)) ∧ ENNReal.ofReal (N (τ k) ^ (-m) * (N (τ k) ^ (-s)) ^ d * β k s / H k) * π (τ k) {w:ℝ | ⌊w / (N (τ k) ^ (-m))⌋ = tag k s i 0} ≤ ρ (τ k) (C k s i ×ˢ Set.Icc (0:ℝ) 1)) ∧ (∑ i:Fin (n' k s),ENNReal.ofReal (N (τ k) ^ (-m) * (N (τ k) ^ (-s)) ^ d * β k s) * π (τ k) {w:ℝ | ⌊w / (N (τ k) ^ (-m))⌋ = tag k s i 0}) ≤ ENNReal.ofReal (H k) ∧ (∀ᵐ p ∂ρ' k,∃ i,p.1 ∈ C k s i)

end Submission.Obl.k4_general_parent_projected_layers
