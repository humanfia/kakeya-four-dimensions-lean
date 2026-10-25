import Submission.Obl.k4_finite_path_candidate_conversion.Interface

/-!
Intermediate interfaces for the split of o199. The path predicate is the
frozen one, including positive cumulative narrowness. Candidate losses
are proportional to the actual gain, and the grid is fine relative to
the requested gain; these two choices allow tangent discovery to be
returned at the original requested output loss.

The named base predicates below are imported from accepted o170. The
positive-narrowness path is adapted from that file's isotropic path,
replacing only its zero narrowness by the parameter ell.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_path_candidate_conversion

noncomputable section

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Observation := EuclideanSpace ℝ (Fin 3) × ℤ
abbrev x := k4_quadratic_finite_greedy_cover.x
abbrev y := k4_quadratic_finite_greedy_cover.y
abbrev v := k4_quadratic_finite_greedy_cover.v
abbrev δ := k4_quadratic_finite_greedy_cover.δ
abbrev obs := k4_quadratic_finite_greedy_cover.obs
abbrev fmt := k4_quadratic_finite_greedy_cover.fmt
abbrev chart := k4_quadratic_finite_greedy_cover.chart
abbrev prob := k4_quadratic_finite_greedy_cover.prob
abbrev Output := k4_quadratic_finite_greedy_cover.ImprovementAt

def PositivePath (ℓ : ℝ) : ℝ → ℝ → (W : ℕ) → (Fin W → ℝ) → (Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → (Fin W → ℝ) → (ℝ → ℝ) → ℝ → ℕ → (ℕ → ℝ) → ℝ → ℕ → ℕ → ℝ → (ℕ → ℝ) → (ℕ → ℕ) → (ℕ → ℝ) → ℝ → (C : ℕ) → (Fin C → ℕ) → (Fin C → Fin C) → (Fin C → Fin W) → (Fin C → ℕ) → (Fin C → EuclideanSpace ℝ (Fin 2)) → (Fin C → EuclideanSpace ℝ (Fin 2)) → (Fin C → Matrix (Fin 2) (Fin 2) ℝ) → (Fin C → MvPolynomial (Fin 4) ℝ) → (Fin C → Set (ℕ × (Fin 6 → ℝ))) → (Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → (ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)) → Prop :=
  fun Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst => (1 ≤ κ) ∧ (κ ≤ Nk ^ σ) ∧ ((C : ℝ) ≤ Nk ^ Mp) ∧ (r (m - 1) = L) ∧ ((∀ i, i < m → |r i - s i * L| ≤ δ₀ * L ∧ 0 < r i ∧ Nk ^ ((κ₁ * s i - δ₀) * L) ≤ (2 : ℝ) ^ T i ∧ (2 : ℝ) ^ T i ≤ Nk ^ ((κ₁ * s i + δ₀) * L) ∧ |nw i - ℓ * s i * L| ≤ δ₀ * L ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, if lev b = i then ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod MeasureTheory.volume) (F b) else 0)) ∧ ((∀ i γ₁ o, ((lst i γ₁ o).card : ℝ) ≤ κ)) ∧ ((∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))) ∧ ((∀ b, lev b < m ∧ j b < 2 ^ T (lev b) ∧ chart (Nk) Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) (E (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (Nk ^ (-f (r (lev b))) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T (lev b) * κ)) ≤ ((ν (γ b)).prod MeasureTheory.volume) (F b) ∧ ν (γ b) (A b) ≤ ENNReal.ofReal (κ * Nk ^ (-f (r (lev b))) * |Matrix.det (Q b)|) ∧ Nk ^ (-(nw (lev b) + δ₀ * L)) ≤ |Matrix.det (Q b)| * (4 : ℝ) ^ T (lev b) ∧ |Matrix.det (Q b)| * (4 : ℝ) ^ T (lev b) ≤ Nk ^ (-(nw (lev b) - δ₀ * L)) ∧ (∀ p ∈ F b, b ∈ lst (lev b) (γ b) (obs (B (γ b)) (δ (Nk) (r (lev b))) p)) ∧ (0 < lev b → lev (par b) + 1 = lev b ∧ γ (par b) = γ b ∧ A b ⊆ A (par b) ∧ F b ⊆ F (par b) ∧ (j (par b) : ℝ) / (2 : ℝ) ^ T (lev (par b)) ≤ (j b : ℝ) / (2 : ℝ) ^ T (lev b) ∧ ((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b) ≤ ((j (par b) : ℝ) + 1) / (2 : ℝ) ^ T (lev (par b))))))


/-- An increasing finite grid with a uniformly small first depth and mesh. -/
def FineGrid (m : ℕ) (s : ℕ → ℝ) (gain ρ : ℝ) : Prop :=
  (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) ∧
  s 0 ≤ ρ * gain ∧ ∀ i, i + 1 < m → s (i + 1) - s i ≤ ρ * gain

/-- A whole-block quadratic fit in the original hidden-derivative unit. -/
def Fits (H a Bv : ℝ) (R : MvPolynomial (Fin 4) ℝ)
    (l : Trajectory) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, |MvPolynomial.eval (x l t) R| ≤ H * a ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ H * Bv ∧
    |MvPolynomial.eval (x l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤
        H * Bv ^ 2 / a

/-- A unit-normal strip in the actual normalized velocity frame of an old chart. -/
def InStrip (T : ℕ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (z width : ℝ)
    (l : Trajectory) : Prop :=
  |(∑ e : Fin 2, a e * ((2 : ℝ) ^ T)⁻¹ *
    (Matrix.toEuclideanLin Q⁻¹ (v l - u)) e) - z| ≤ width

/-- One residual candidate; its lower bound uses the full old assignment. -/
def MixedCandidate (Nk L : ℝ) (W : ℕ)
    (ν : Fin W → MeasureTheory.Measure Trajectory) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (H : Fin W → Set Incidence) : Prop :=
  ∃ (b : Fin C) (h : ℝ), gain ≤ h ∧ h ≤ 1 / 8 ∧
    r (lev b) + 2 * h * L ≤ L ∧ 0 < ν (γ b) (A b) ∧
    ((∃ R : MvPolynomial (Fin 4) ℝ, R.totalDegree ≤ 2 ∧
      (∀ e, |R.coeff e| ≤ Nk ^ Mc) ∧
      ENNReal.ofReal (Nk ^ (-((d₁ + ρ) * h * L) - ε) / (2 : ℝ) ^ T (lev b)) *
        ν (γ b) (A b) ≤ ((ν (γ b)).prod MeasureTheory.volume)
          {p | p ∈ H (γ b) ∧ p.1 ∈ A b ∧
            p.2 ∈ Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
              (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
            Fits (Nk ^ (ρ * h * L + ε)) (δ Nk (r (lev b) + h * L))
              (B (γ b)) R p.1
              (Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
                (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b))) ∧
            B (γ b) / Nk ^ (ρ * h * L + ε) ≤
              |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|}) ∨
    (∃ (a : Fin 2 → ℝ) (z : ℝ), (∑ e, (a e) ^ 2) = 1 ∧ |z| ≤ Nk ^ Mc ∧
      ENNReal.ofReal (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ T (lev b)) *
        ν (γ b) (A b) ≤ ((ν (γ b)).prod MeasureTheory.volume)
          {p | p ∈ H (γ b) ∧ p.1 ∈ A b ∧
            p.2 ∈ Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
              (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
            InStrip (T (lev b)) (u b) (Q b) a z
              (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) p.1}))

/-- The complete supplied terminal path, in its unchanged original world. -/
def TerminalInc (W C m : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (F : Fin C → Set Incidence) (w : Fin W) : Set Incidence :=
  {p | ∃ b : Fin C, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b}

/-- Uniform discovery on every substantial original final-path residual. -/
def Discovery (d₁ κ₁ ℓ S η ρ : ℝ) (m : ℕ) (s : ℕ → ℝ)
    (gain δ₀ : ℝ) : Prop :=
  ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mc : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    ∀ r T nw κ C lev par γ j c u Q R A F lst,
      PositivePath ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀
        Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧
          H w ⊆ TerminalInc (W k) C m lev γ F w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod MeasureTheory.volume) (TerminalInc (W k) C m lev γ F w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) →
        MixedCandidate (N k) L (W k) (ν k) (B k) Mc d₁ ρ gain ε
          r T C lev γ j u Q A H

/-- A finite priority cover at one old node, one menu gain, and one candidate type. -/
def MixedCover (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence)
    (Mg Dg : ℕ) (ε : ℝ) : Prop :=
  ∃ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C)
    (R' : Fin n → MvPolynomial (Fin 4) ℝ) (a : Fin n → Fin 2 → ℝ)
    (z : Fin n → ℝ) (A' : Fin n → Set Trajectory) (V : Fin n → Set Incidence)
    (time : Bool),
    i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧
    (∃ e : ℕ, h = gain * (1 + ρ) ^ e) ∧
    r i + 2 * h * L ≤ L ∧ (n : ℝ) ≤ Nk ^ Mg ∧
    (∀ b, lev (old b) = i ∧ 0 < ν (γ (old b)) (A (old b)) ∧
      MeasurableSet (A' b) ∧ A' b ⊆ A (old b) ∧
      (∀ q, fmt 6 (Nk ^ Mg) Dg {w | (q, w) ∈ A' b}) ∧
      MeasurableSet (V b) ∧
      V b ⊆ {p | p ∈ TerminalInc W C m lev γ F (γ (old b)) ∧
        p.1 ∈ A' b ∧ p.2 ∈ Set.Icc ((j (old b) : ℝ) / (2 : ℝ) ^ T i)
          (((j (old b) : ℝ) + 1) / (2 : ℝ) ^ T i)} ∧
      (if time then
        (R' b).totalDegree ≤ 2 ∧ (∀ e, |(R' b).coeff e| ≤ Nk ^ Mg) ∧
        (∀ l ∈ A' b, Fits (Nk ^ (4 * ρ * h * L + 4 * ε))
          (δ Nk (r i + h * L)) (B (γ (old b))) (R' b) l
          (Set.Icc ((j (old b) : ℝ) / (2 : ℝ) ^ T i)
            (((j (old b) : ℝ) + 1) / (2 : ℝ) ^ T i))) ∧
        (∀ p ∈ V b, B (γ (old b)) / Nk ^ (4 * ρ * h * L + 4 * ε) ≤
          |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R' b))|) ∧
        ENNReal.ofReal (Nk ^ (-((d₁ + 4 * ρ) * h * L) - 4 * ε) / (2 : ℝ) ^ T i) *
          ν (γ (old b)) (A (old b)) ≤
            ((ν (γ (old b))).prod MeasureTheory.volume) (V b)
      else
        (∑ e, (a b e) ^ 2) = 1 ∧ |z b| ≤ Nk ^ Mg ∧
        (∀ l ∈ A' b, InStrip (T i) (u (old b)) (Q (old b)) (a b) (z b)
          (Nk ^ (4 * ρ * h * L + 4 * ε) * Nk ^ (-h * L)) l) ∧
        ENNReal.ofReal (Nk ^ (-4 * ρ * h * L - 4 * ε) / (2 : ℝ) ^ T i) *
          ν (γ (old b)) (A (old b)) ≤
            ((ν (γ (old b))).prod MeasureTheory.volume) (V b))) ∧
    (∀ b b', b ≠ b' → old b = old b' → Disjoint (A' b) (A' b')) ∧
    (∀ b : Fin C, ((Finset.univ.filter (fun b' => old b' = b)).card : ℝ) ≤
      Nk ^ ((if time then (d₁ + 4 * ρ) else 4 * ρ) * h * L + 4 * ε)) ∧
    (∀ b b', b ≠ b' → γ (old b) = γ (old b') → Disjoint (V b) (V b')) ∧
    ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (ω (γ (old b))) *
      ((ν (γ (old b))).prod MeasureTheory.volume) (V b)

/-- E supplies the uniform residual-discovery assertion on a fine finite grid. -/
def PreparationStatement : Prop :=
  CandidatePrinciple false (fun _ => True) →
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ),
      FineGrid m s gain ρ ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ₀ ∧
      δ₀ ≤ ρ * gain ∧ Discovery d₁ κ₁ ℓ S η ρ m s gain δ₀

/-- Pure finite greedy selection, retaining the unchanged full-assignment priors. -/
def GreedyStatement : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), FineGrid m s gain ρ →
    0 < gain → gain ≤ 1 / 8 → 0 < δ₀ → δ₀ ≤ ρ * gain →
    Discovery d₁ κ₁ ℓ S η ρ m s gain δ₀ →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mg Dg : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    ∀ r T nw κ C lev par γ j c u Q R A F lst,
      PositivePath ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀
        Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      MixedCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T
        C lev γ j u Q A F Mg Dg ε

/-- Finite covered candidates yield an atlas with the original requested slack. -/
def RealizationStatement : Prop :=
  Matching →
  ∀ d₁ κ₁ ℓ S η : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η →
    ∃ α ρ : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 < ρ ∧ ρ ≤ 1 / 4 ∧
      d₁ + 8 * ρ < 1 ∧
    ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), FineGrid m s gain ρ →
    0 < gain → gain ≤ 1 / 8 → 0 < δ₀ → δ₀ ≤ ρ * gain →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp Mg Dg : ℕ, ∃ Mi Di : ℕ, ∀ τ : ℝ, 0 < τ →
    ∃ ε σ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    ∀ r T nw κ C lev par γ j c u Q R A F lst,
      PositivePath ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀
        Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      MixedCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T
        C lev γ j u Q A F Mg Dg ε →
      Output (N k) L (W k) (ω k) (ν k) (E k) (B k)
        κ₁ (α * gain) m r T nw Mi Di τ

end

end Submission.Obl.k4_finite_path_candidate_conversion
