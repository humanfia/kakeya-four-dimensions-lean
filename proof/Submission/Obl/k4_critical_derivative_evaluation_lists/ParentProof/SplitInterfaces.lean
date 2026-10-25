/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, SplitInterfaces.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.PreparedRow

/-! From this LOT tree, obligation o211, session x0761,
`SplitInterfaces.lean` (commit c26b99fcb8). These are definitions only. -/

/-! Interfaces for the three independent remaining arguments in o211.
Restoration helpers were merged from this LOT tree's o211/x0736,
commits 72523115 and d5bebbf4; their original source attributions remain.
These definitions contain no unproved assertion. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

/-- Continuous Row hypotheses with derivative-evaluation lists and a conditional
velocity cap in place of the conclusion's finite row lists. -/
def PreRowInputs (S a η N : ℝ) (α : Type) [MeasurableSpace α]
    (prior : MeasureTheory.Measure α) (active : MeasureTheory.Measure (α × ℝ))
    (intercept velocity evaluation : α → ℝ) (row : α × ℝ → Fin 2 → ℝ)
    (palette : MeasureTheory.Measure ℝ) (error : ℝ)
    (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ) : Prop :=
  (fun (ξ : ℝ) =>
  (fun (position : α × ℝ → Fin 2 → ℤ) =>
    Measurable intercept ∧ Measurable velocity ∧ Measurable evaluation ∧ Measurable row ∧
    MeasureTheory.IsProbabilityMeasure prior ∧ MeasureTheory.IsProbabilityMeasure palette ∧
    ξ ≤ error ∧ error ≤ 1 ∧
    (∀ l, |intercept l| + |velocity l| ≤ N ^ η) ∧
    active ≤ ENNReal.ofReal (N ^ η) • (prior.prod MeasureTheory.volume) ∧
    active (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
    ENNReal.ofReal (N ^ (-η)) ≤ active Set.univ ∧
    (∀ x r : ℝ, ξ ≤ r → r ≤ 1 →
      palette (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) ∧
    (∀ (q : Fin 2 → ℤ) (j : ℤ),
      active {p | position p = q ∧ ⌊velocity p.1 / ξ⌋ = j} ≤
        ENNReal.ofReal (N ^ η * ξ ^ 2) *
          palette (Set.Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ))) ∧
    (∀ᵐ p ∂active, (∀ j, |row p j| ≤ N ^ η) ∧
      |row p 0 + velocity p.1 * row p 1 - evaluation p.1| ≤ N ^ η * error) ∧
    (∀ (q : Fin 2 → ℤ) (j : ℤ), ((lists q j).card : ℝ) ≤ N ^ η) ∧
    (∀ᵐ p ∂active, ⌊evaluation p.1 / error⌋ ∈
      lists (position p) ⌊velocity p.1 / ξ⌋) ∧
    (∀ (q r : Fin 2 → ℤ) (j : ℤ),
      active {p | position p = q ∧ (fun e => ⌊row p e / error⌋) = r ∧
        ⌊velocity p.1 / ξ⌋ = j} ≤
        ENNReal.ofReal (N ^ η) *
          palette (Set.Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ)) *
          active {p | position p = q ∧ (fun e => ⌊row p e / error⌋) = r}))
    (fun p e => ⌊(![p.2, intercept p.1 + p.2 * velocity p.1] : Fin 2 → ℝ) e / ξ⌋))
  (N ^ (-a))

/-- Two-velocity interpolation is independent of the critical model. -/
def RowListCompletion : Prop :=
  ∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε →
  ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
  ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
    (prior : MeasureTheory.Measure α) (active : MeasureTheory.Measure (α × ℝ))
    (intercept velocity evaluation : α → ℝ) (row : α × ℝ → Fin 2 → ℝ)
    (palette : MeasureTheory.Measure ℝ) (error : ℝ)
    (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ),
    PreRowInputs S a η N α prior active intercept velocity evaluation row palette error lists →
    ∃ bins : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ),
      (∀ q, ((bins q).card : ℝ) ≤ N ^ ε) ∧
      ∀ᵐ p ∂active, (fun e => ⌊row p e / error⌋) ∈ bins
        (fun e => ⌊(![p.2, intercept p.1 + p.2 * velocity p.1] : Fin 2 → ℝ) e /
          (N ^ (-a))⌋)

namespace Data

variable {α : Type} [MeasurableSpace α]

/-- Scalar derivative lists at the true-label normalized base and velocity mesh. -/
def EvaluationListsAt (cfg : Data α) (k : ℕ) (s η : ℝ) : Prop :=
  ∃ (σ : MeasureTheory.Measure (α × ℝ))
    (lists : Fin (cfg.n k s) → (Fin 2 → ℤ) → ℤ → Finset ℤ),
  σ ≤ cfg.ρ k ∧ ENNReal.ofReal (cfg.N k ^ (-η)) ≤ σ Set.univ ∧
  (∀ (i : Fin (cfg.n k s)) (q : Fin 2 → ℤ) (v : ℤ),
    ((lists i q v).card : ℝ) ≤ cfg.N k ^ η) ∧
  ∀ i : Fin (cfg.n k s), ∀ᵐ p ∂σ,
    p.1 ∈ cfg.B k s i → p.2 ∈ I (cfg.T k s) (cfg.j k s i) →
    ⌊cfg.b k p.1 5 / (cfg.N k ^ (-s))⌋ ∈
      lists i
        ((fun (H t₀ Z₀ : ℝ) => fun e : Fin 2 =>
          ⌊(![(p.2 - t₀) / H,
            (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - Z₀) / H] : Fin 2 → ℝ) e /
              (cfg.N k ^ (-(200 * s)))⌋)
          (((2 : ℝ) ^ cfg.T k s)⁻¹)
          (((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s)
          (cfg.c k s i 0 + (((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s) * cfg.c k s i 1))
        ⌊cfg.b k p.1 3 / (cfg.N k ^ (-(200 * s)))⌋

/-- The depth is fixed before the loss is requested. -/
def DerivativeListsAtDepth (cfg : Data α) (s : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ᶠ k in Filter.atTop, cfg.EvaluationListsAt k s η

/-- All original-law data needed for Row, except its finite row list. -/
def ConditionalRowAt (cfg : Data α) (k : ℕ) (s η : ℝ) : Prop :=
  ∃ (i : Fin (cfg.n k s)) (current : MeasureTheory.Measure (α × ℝ))
    (t₀ Z₀ : ℝ) (intercept velocity evaluation : α → ℝ)
    (row : α × ℝ → Fin 2 → ℝ) (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ),
  (fun (H : ℝ) =>
    PreRowInputs cfg.S (200 * s) η (cfg.N k) α
      ((cfg.ν k (cfg.A k s i))⁻¹ • (cfg.ν k).restrict (cfg.A k s i))
      (ENNReal.ofReal (H * (cfg.ν k).real (cfg.A k s i))⁻¹ •
        current.map (fun p : α × ℝ => (p.1, (p.2 - t₀) / H)))
      intercept velocity evaluation row (cfg.π k) (cfg.N k ^ (-s)) lists ∧
    |t₀| ≤ 4 * cfg.K k ∧ |Z₀| ≤ 4 * cfg.K k ∧
    0 < H * (cfg.ν k).real (cfg.A k s i) ∧
    current ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) ∧
    (∀ᵐ p ∂current,
      intercept p.1 = (cfg.b k p.1 0 + t₀ * cfg.b k p.1 3 - Z₀) / H ∧
      velocity p.1 = cfg.b k p.1 3 ∧ evaluation p.1 = cfg.b k p.1 5) ∧
    (∀ᵐ p ∂current, |cfg.b k p.1 3| ≤ 4 * cfg.K k ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ (4 * cfg.K k) * cfg.N k ^ (-cfg.e₀)) ∧
    H⁻¹ ≤ (4 * cfg.K k) * cfg.N k ^ (s / 2))
      (((2 : ℝ) ^ cfg.T k s)⁻¹)

end Data

/-- First remaining geometric and scalar-counting argument. -/
def DerivativeListPreparation : Prop :=
  Row → Match → ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Valid →
    ∃ s : ℝ, 0 < s ∧ 1000 * s < cfg.U ∧ 1000 * s < cfg.e₀ ∧ s < 1 ∧
      cfg.DerivativeListsAtDepth s

/-- Conditional-state pruning, exact cap integration, and continuous normalization. -/
def ConditionalRowPreparation : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Valid →
    ∀ s : ℝ, 0 < s → 1000 * s < cfg.U → 1000 * s < cfg.e₀ → s < 1 →
      cfg.DerivativeListsAtDepth s →
      ∀ η : ℝ, 0 < η → ∃ᶠ k in Filter.atTop, cfg.ConditionalRowAt k s η

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
