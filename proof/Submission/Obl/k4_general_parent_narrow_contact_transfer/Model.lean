/- Retained from this obligation, o255, branch x0901 at commit 0f8ba410.
   Earlier source attributions in this file are preserved. -/
import Submission.Obl.k4_critical_intercept_concentration.PreparedModel
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.Model

/-!
The general data use the accepted prepared-data record from o212. The atlas
below removes its horizontal premise; its other fields are the frozen ones.
-/

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

abbrev Model (α : Type) [MeasurableSpace α] :=
  Submission.Obl.k4_critical_intercept_concentration.Data α

abbrev Row := Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.Row
abbrev Match := Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.Match

namespace Model

variable {α : Type} [MeasurableSpace α]

def Atlas (cfg : Model α) : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → (fun (q : ℝ) (a g : ℝ → ℝ) => cfg.N k ^ (cfg.κ * s) / cfg.K k ≤ (2 : ℝ) ^ cfg.T k s ∧ (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) ∧ (∀ i, MeasurableSet (cfg.A k s i) ∧ MeasurableSet (cfg.B k s i) ∧ cfg.B k s i ⊆ cfg.A k s i) ∧ (∀ i i', i ≠ i' → cfg.j k s i = cfg.j k s i' → Disjoint (cfg.A k s i) (cfg.A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ cfg.d * q ^ 2 * g s / cfg.K k) ≤ cfg.ν k (cfg.A k s i) ∧ cfg.ν k (cfg.A k s i) ≤ ENNReal.ofReal (cfg.K k * a s ^ cfg.d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / cfg.K k) * cfg.ν k (cfg.A k s i) ≤ cfg.μ k (cfg.B k s i ×ˢ Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k s) (cfg.j k s i)) ∧ (∀ e, |cfg.c k s i e| ≤ cfg.K k) ∧ (cfg.F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ cfg.A k s i, ∀ t ∈ Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k s) (cfg.j k s i), |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤ cfg.K k * q ∧ |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤ cfg.K k * q * g s ∧ |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤ cfg.K k * g s) ∧ (∀ l ∈ cfg.B k s i, cfg.fit k (cfg.K k) (a s) (cfg.F k s i) l (Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k s) (cfg.j k s i))) ∧ (∀ᵐ p ∂cfg.μ k, p.1 ∈ cfg.B k s i → p.2 ∈ Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k s) (cfg.j k s i) → (cfg.K k)⁻¹ ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (cfg.F k s i))|) ∧ ((false : Bool) = true → cfg.P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) ∧ |cfg.c k s i 3 + cfg.c k s i 0 + ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q * cfg.c k s i 1| + |cfg.c k s i 4 - ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ cfg.K k * q ∧ (∃ L : Fin 4 → ℝ, cfg.F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ cfg.K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ cfg.B k s i, ∀ t ∈ Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k s) (cfg.j k s i), |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ cfg.K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k s) (cfg.j k s i)) ∧ (∀ (i : Fin (cfg.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k s) (cfg.j k s i) ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (cfg.K k * q) * cfg.ν k (cfg.A k s i) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(cfg.T k s : ℤ))) (fun s => cfg.N k ^ (-s)) (fun s => cfg.N k ^ (-cfg.ℓ * s)))

/-- All original assumptions, with no horizontal equation imposed. -/
structure Valid (cfg : Model α) : Prop where
  scale : ∀ k, 2 ≤ cfg.N k
  scale_limit : Tendsto cfg.N atTop atTop
  subpower : (∀ k, 1 ≤ cfg.K k) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε
  dimension_nonneg : 0 ≤ cfg.d
  dimension_lt_one : cfg.d < 1
  rate_pos : 0 < cfg.κ
  rate_le_one : cfg.κ ≤ 1
  transverse_pos : 0 < cfg.ℓ
  palette_pos : 0 < cfg.S
  palette_le_one : cfg.S ≤ 1
  depth_pos : 0 < cfg.U
  defect_pos : 0 < cfg.e₀
  basic : cfg.Basic
  caps : cfg.Caps
  atlas : Atlas cfg
  nested : cfg.Nested

/-- The extra premise supplied to mode 3. -/
def Contact (cfg : Model α) : Prop :=
  ∀ k, ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)

/-- The exact full-time projected-layer conclusion. -/
def Layers (cfg : Model α) : Bool → Prop :=
  (fun wide => ∃ L:ℝ,2 < L ∧ ∀ a:ℝ,0 < a → (if wide then L else 2) * a < cfg.U → ∀ D:Finset ℝ,(∀ s ∈ D,a ≤ s ∧ s ≤ 2 * a) → ∀ m:ℝ,L * a < m → ∃ τ:ℕ → ℕ,StrictMono τ ∧ ∃ H:ℕ → ℝ,(∀ k,1 ≤ H k ∧ cfg.K (τ k) ≤ H k) ∧ (∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,H k ≤ cfg.N (τ k) ^ ε) ∧ ∃ (ρ':ℕ → MeasureTheory.Measure (α × ℝ)) (β:ℕ → ℝ → ℝ) (n':ℕ → ℝ → ℕ) (C:(k:ℕ) → (s:ℝ) → Fin (n' k s) → Set α) (tag:(k:ℕ) → (s:ℝ) → Fin (n' k s) → Fin 2 → ℤ) (u v:(k:ℕ) → (s:ℝ) → Fin (n' k s) → ℝ) (G:(k:ℕ) → (s:ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),(∀ k,ρ' k ≤ cfg.ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ) ∧ ∀ k s,s ∈ D → 0 < β k s ∧ (cfg.N (τ k) ^ (-cfg.ℓ * s) * (if wide then 1 else cfg.N (τ k) ^ (-L * a))) / H k ≤ β k s ∧ β k s ≤ H k * cfg.N (τ k) ^ (-cfg.ℓ * s) ∧ (∀ i,MeasurableSet (C k s i)) ∧ (∀ i i',i ≠ i' → Disjoint (C k s i) (C k s i')) ∧ (∀ i,|u k s i| + |v k s i| ≤ H k ∧ (G k s i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (0:ℝ) 1,∀ w ∈ Set.Icc (-1:ℝ) 1,|MvPolynomial.eval ![t,u k s i + t * v k s i + β k s * w] (G k s i)| ≤ H k) ∧ (∀ l ∈ C k s i,⌊cfg.b (τ k) l 3 / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0 ∧ ⌊cfg.b (τ k) l 0 / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 1 ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,|(cfg.x (τ k) l t) 2 - u k s i - t * v k s i| ≤ H k * β k s ∧ |MvPolynomial.eval (cfg.x (τ k) l t) (cfg.P (τ k)) - MvPolynomial.eval ![t,(cfg.x (τ k) l t) 2] (G k s i)| ≤ H k * cfg.N (τ k) ^ (-s)) ∧ ENNReal.ofReal (cfg.N (τ k) ^ (-m) * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H k) * cfg.π (τ k) {w:ℝ | ⌊w / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0} ≤ cfg.ρ (τ k) (C k s i ×ˢ Set.Icc (0:ℝ) 1)) ∧ (∑ i:Fin (n' k s),ENNReal.ofReal (cfg.N (τ k) ^ (-m) * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s) * cfg.π (τ k) {w:ℝ | ⌊w / (cfg.N (τ k) ^ (-m))⌋ = tag k s i 0}) ≤ ENNReal.ofReal (H k) ∧ (∀ᵐ p ∂ρ' k,∃ i,p.1 ∈ C k s i))

/-- The output chosen by the frozen mode. -/
def Outcome (cfg : Model α) (mode : Fin 4) : Prop :=
  if mode = 0 then Layers cfg false else
    if mode = 1 then Layers cfg true → cfg.Candidates else cfg.Candidates

end Model

end Submission.Obl.k4_general_parent_narrow_contact_transfer
