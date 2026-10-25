-- Adapted from this LOT tree, o206, session x0709, commit f7d6ac58,
-- Submission/Obl/k4_coarse_pair_frame_preparation/SplitStatements.lean.
import Submission.Obl.k4_homogeneous_native_pair_preparation.Interface

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

set_option linter.unusedVariables false

noncomputable def col0 (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Q 0 0, Q 1 0]

noncomputable def col1 (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Q 0 1, Q 1 1]

noncomputable def longCol (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  if ‖col1 Q‖ ≤ ‖col0 Q‖ then col0 Q else col1 Q

noncomputable def r₁ (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ‖longCol Q‖

noncomputable def r₂ (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := |Q.det| / r₁ Q

noncomputable def nrm (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (r₁ Q)⁻¹ • WithLp.toLp 2 ![-longCol Q 1, longCol Q 0]

noncomputable def wedge (n m : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  n 0 * m 1 - n 1 * m 0

noncomputable def coarseInterval (T s j : ℕ) : Set ℝ :=
  Set.Icc (((j / 2 ^ s : ℕ) : ℝ) / (2 : ℝ) ^ T)
    ((((j / 2 ^ s : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

/-- One unconditioned two-time sample in the original chart coordinates.
`aligned` adds only a normal-angle condition on surviving pairs. -/
noncomputable def NativeAt (aligned : Prop) (lam Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ)
    (νk : Fin Wk → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Pk : Fin Wk → MvPolynomial (Fin 4) ℝ) (Bk : Fin Wk → ℝ)
    (f : ℝ → ℝ)
    (gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (L S a e u h : ℝ) (M D : ℕ) (depths : Finset ℝ) (ε : ℝ) : Prop :=
  ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ Nk ^ ε ∧
  ∃ T s C : ℕ, ∃ R₁ R₂ : ℝ,
  ∃ (γ : Fin C → Fin Wk) (j : Fin C → Fin (2 ^ (T + s)))
    (c v₀ : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    (H : Fin C → Fin C → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)))
    (Good : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
  (2 : ℝ) ^ T ≤ Nk ^ (h + ε) ∧
  (C : ℝ) ≤ Nk ^ M ∧
  Nk ^ e ≤ (2 : ℝ) ^ s ∧ (2 : ℝ) ^ s ≤ 2 * Nk ^ e ∧
  0 < R₂ ∧ R₂ ≤ R₁ ∧ R₁ ≤ Nk ^ M ∧ R₂⁻¹ ≤ Nk ^ M ∧
  (∀ b, R₁ ≤ r₁ (Q b) ∧ r₁ (Q b) < 2 * R₁ ∧
    R₂ ≤ r₂ (Q b) ∧ r₂ (Q b) < 2 * R₂) ∧
  (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
  (∀ b, chart Nk M D κ (T + s) ((j b : ℕ) : ℝ) L (Bk (γ b)) (Ek (γ b))
    (c b) (v₀ b) (Q b) (R b) (A b) (F b)
    (ENNReal.ofReal (Nk ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ (T + s) * κ)) ≤
      ((νk (γ b)).prod MeasureTheory.volume) (F b) ∧
      ∀ p ∈ F b, b ∈ lst (γ b) (obs (Bk (γ b)) (δ Nk L) p))) ∧
  (∀ b, ∀ p ∈ F b, p.2 < (((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s)) ∧
  (∀ b, ∀ l ∈ A b, ∀ t ∈ coarseInterval T s (j b : ℕ),
    ‖Matrix.toEuclideanLin (Q b)⁻¹ (y l t - c b - t • v₀ b)‖ ≤
      3 * κ * (2 : ℝ) ^ s ∧
    |MvPolynomial.eval (x l t) (R b)| ≤ δ Nk L * Nk ^ a ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R b))| ≤
      Bk (γ b) * Nk ^ a) ∧
  (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ) ∧
  (∀ γ₀ b, MeasurableSet {p | b ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L) p)} ∧
    ∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ |
      b ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L)
        ((i, fun z : Fin 6 => r z.castSucc), r 6))}) ∧
  (∀ γ₀, MeasurableSet (Good γ₀) ∧ Good γ₀ ⊆ Ek γ₀ ∧
    ∀ p ∈ Good γ₀,
      ‖y p.1 p.2‖ + ‖v p.1‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) (Pk γ₀)| ≤ κ ∧
      Bk γ₀ / κ ≤
        |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (Pk γ₀))| ∧
      (∀ r ∈ depths, gk γ₀ r (obs (Bk γ₀) (δ Nk r) p) ≤
        ENNReal.ofReal (Nk ^ (-f r + a))) ∧
      Gk γ₀ u (obs (Bk γ₀) (δ Nk L) p,
        fun i : Fin 2 => ⌊v p.1 i / δ Nk u⌋) ≤
        ENNReal.ofReal (Nk ^ (-f L - S * u + a))) ∧
  (∀ b b', MeasurableSet (H b b') ∧
    ∀ p ∈ H b b', γ b = γ b' ∧
      (j b : ℕ) / 2 ^ s = (j b' : ℕ) / 2 ^ s ∧
      (p.1, p.2.1) ∈ F b ∧ (p.1, p.2.2) ∈ F b' ∧
      (p.1, p.2.1) ∈ Good (γ b) ∧ (p.1, p.2.2) ∈ Good (γ b) ∧
      (∀ R' : MvPolynomial (Fin 4) ℝ, R' = R b ∨ R' = R b' →
        ∀ t : ℝ, t = p.2.1 ∨ t = p.2.2 →
          Bk (γ b) * Nk ^ (-a) ≤
            |MvPolynomial.eval (x p.1 t) (MvPolynomial.pderiv (3 : Fin 4) R')|) ∧
      (aligned → R₁ ≤ 8 * Nk ^ a * R₂ ∨
        |wedge (nrm (Q b)) (nrm (Q b'))| ≤
          min (1 / 8 : ℝ) (Nk ^ a * R₂ / R₁))) ∧
  ENNReal.ofReal (lam * κ⁻¹) ≤
    ∑ b, ENNReal.ofReal (ωk (γ b) * (2 : ℝ) ^ T) *
      ((νk (γ b)).prod (MeasureTheory.volume.prod MeasureTheory.volume))
        {p | ∃ b', p ∈ H b b'}

/-- The cofinal native package. The pure-depth grid is fixed before the slack. -/
noncomputable def NativeSequence (aligned : Prop) (lam : ℝ)
    (N : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (L S a e u h : ℝ) : Prop :=
  ∃ M D : ℕ, ∃ depths : Finset ℝ,
    (0 : ℝ) ∈ depths ∧ L ∈ depths ∧
    (∀ r ∈ depths, 0 ≤ r ∧ r ≤ L) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) L, ∃ r' ∈ depths, r' ≤ r ∧ r ≤ r' + e) ∧
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      NativeAt aligned lam (N k) (W k) (ω k) (ν k) (E k) (P k) (B k)
        f (g k) (G k) L S a e u h M D depths ε

/-- Homogenization, two-time sampling, extrapolation, derivative deletions and caps. -/
noncomputable def NativePreparationStatement : Prop :=
  ∃ A : ℝ, 0 < A ∧
    ∀ N K L d S η W ω ν E P B f g G,
      prob N K L d S η W ω ν E P B f g G →
      ∀ h e u : ℝ, 0 < e → e < h → 0 < u → u ≤ η * L →
      known N W ω ν E B f L h →
      NativeSequence False 8 N W ω ν E P B f g G L S (A * e) e u (h - e)

end Submission.Obl.k4_homogeneous_native_pair_preparation
