/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/Dichotomy.lean. -/
import Submission.Obl.k4_narrow_projected_row_parents.Model

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter

namespace Model

variable {α : Type} [MeasurableSpace α]

/-- One requested depth of a projected-layer output, exactly as in the frozen type. -/
def Slice (cfg : Model α) (wide : Bool) (L a m : ℝ) (τ : ℕ → ℕ) (H : ℕ → ℝ)
    (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ) (n' : ℕ → ℝ → ℕ)
    (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
    (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
    (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
    (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ)
    (k : ℕ) (s : ℝ) : Prop :=
  0 < β k s ∧ (cfg.N (τ k) ^ (-cfg.ℓ * s) * (if wide then 1 else cfg.N (τ k) ^ (-L * a))) / H k ≤ β k s ∧ β k s ≤ H k * cfg.N (τ k) ^ (-cfg.ℓ * s) ∧ (∀ i,MeasurableSet (C k s i)) ∧ (∀ i i',i ≠ i' → Disjoint (C k s i) (C k s i')) ∧ (∀ i,|u k s i| + |v k s i| ≤ H k ∧ (G k s i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (0:ℝ) 1,∀ w ∈ Set.Icc (-1:ℝ) 1,|MvPolynomial.eval ![t,u k s i + t * v k s i + β k s * w] (G k s i)| ≤ H k) ∧ (∀ l ∈ C k s i,⌊cfg.b (τ k) l 3 / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0 ∧ ⌊cfg.b (τ k) l 0 / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 1 ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,|(cfg.x (τ k) l t) 2 - u k s i - t * v k s i| ≤ H k * β k s ∧ |MvPolynomial.eval (cfg.x (τ k) l t) (cfg.P (τ k)) - MvPolynomial.eval ![t,(cfg.x (τ k) l t) 2] (G k s i)| ≤ H k * cfg.N (τ k) ^ (-s)) ∧ ENNReal.ofReal (cfg.N (τ k) ^ (-m) * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H k) * cfg.π (τ k) {w:ℝ | ⌊w / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0} ≤ cfg.ρ (τ k) (C k s i ×ˢ Set.Icc (0:ℝ) 1)) ∧ (∑ i:Fin (n' k s),ENNReal.ofReal (cfg.N (τ k) ^ (-m) * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s) * cfg.π (τ k) {w:ℝ | ⌊w / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0}) ≤ ENNReal.ofReal (H k) ∧ (∀ᵐ p ∂ρ' k,∃ i,p.1 ∈ C k s i)

/-- A projected-layer output for fixed `(L, a, D, m)`, exactly as in the frozen type. -/
def LayerOutput (cfg : Model α) (wide : Bool) (L a : ℝ) (D : Finset ℝ) (m : ℝ) : Prop :=
  ∃ τ:ℕ → ℕ,StrictMono τ ∧ ∃ H:ℕ → ℝ,(∀ k,1 ≤ H k ∧ cfg.K (τ k) ≤ H k) ∧ (∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,H k ≤ cfg.N (τ k) ^ ε) ∧ ∃ (ρ':ℕ → MeasureTheory.Measure (α × ℝ)) (β:ℕ → ℝ → ℝ) (n':ℕ → ℝ → ℕ) (C:(k:ℕ) → (s:ℝ) → Fin (n' k s) → Set α) (tag:(k:ℕ) → (s:ℝ) → Fin (n' k s) → Fin 2 → ℤ) (u v:(k:ℕ) → (s:ℝ) → Fin (n' k s) → ℝ) (G:(k:ℕ) → (s:ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),(∀ k,ρ' k ≤ cfg.ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ) ∧ ∀ k s,s ∈ D → Slice cfg wide L a m τ H ρ' β n' C tag u v G k s

/-- The narrow alternative at one requested depth `s` of an ordinary output:
`β_s` is smaller than `g_s = N^(-ℓ s)` by a fixed power, frequently. -/
structure NarrowWitness (cfg : Model α) (L a m s : ℝ) (τ : ℕ → ℕ) (H : ℕ → ℝ)
    (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ) (n' : ℕ → ℝ → ℕ)
    (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
    (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
    (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
    (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ) : Prop where
  mono : StrictMono τ
  loss : ∀ k, 1 ≤ H k ∧ cfg.K (τ k) ≤ H k
  loss_subpower : ∀ ε:ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ cfg.N (τ k) ^ ε
  retained : ∀ k, ρ' k ≤ cfg.ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ
  slice : ∀ k, Slice cfg false L a m τ H ρ' β n' C tag u v G k s
  narrow : ∃ e : ℝ, 0 < e ∧
    ∃ᶠ k in Filter.atTop, cfg.N (τ k) ^ e * β k s < cfg.N (τ k) ^ (-cfg.ℓ * s)


end Model

end Submission.Obl.k4_narrow_projected_row_parents
