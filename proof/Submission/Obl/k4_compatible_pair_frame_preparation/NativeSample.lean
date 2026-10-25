import Submission.Obl.k4_compatible_pair_frame_preparation.SplitStatements

namespace Submission.Obl.k4_compatible_pair_frame_preparation

structure NativeSample (aligned : Prop) (lam Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ)
    (νk : Fin Wk → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Pk : Fin Wk → MvPolynomial (Fin 4) ℝ) (Bk : Fin Wk → ℝ)
    (f : ℝ → ℝ)
    (gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (L S a e u h : ℝ) (M D : ℕ) (depths : Finset ℝ) (ε : ℝ) where
  κ : ℝ
  κ_one : 1 ≤ κ
  κ_le : κ ≤ Nk ^ ε
  T : ℕ
  s : ℕ
  C : ℕ
  R₁ : ℝ
  R₂ : ℝ
  γ : Fin C → Fin Wk
  j : Fin C → Fin (2 ^ (T + s))
  c : Fin C → EuclideanSpace ℝ (Fin 2)
  v₀ : Fin C → EuclideanSpace ℝ (Fin 2)
  Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  R : Fin C → MvPolynomial (Fin 4) ℝ
  A : Fin C → Set (ℕ × (Fin 6 → ℝ))
  F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)
  H : Fin C → Fin C → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ))
  Good : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  hT : (2 : ℝ) ^ T ≤ Nk ^ (h + ε)
  hC : (C : ℝ) ≤ Nk ^ M
  hgainlo : Nk ^ e ≤ (2 : ℝ) ^ s
  hgainhi : (2 : ℝ) ^ s ≤ 2 * Nk ^ e
  hR₂pos : 0 < R₂
  hR21 : R₂ ≤ R₁
  hR₁le : R₁ ≤ Nk ^ M
  hR₂inv : R₂⁻¹ ≤ Nk ^ M
  hscales : (∀ b, R₁ ≤ r₁ (Q b) ∧ r₁ (Q b) < 2 * R₁ ∧
      R₂ ≤ r₂ (Q b) ∧ r₂ (Q b) < 2 * R₂)
  hdisj : (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
  hchart : (∀ b, chart Nk M D κ (T + s) ((j b : ℕ) : ℝ) L (Bk (γ b)) (Ek (γ b))
      (c b) (v₀ b) (Q b) (R b) (A b) (F b)
      (ENNReal.ofReal (Nk ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ (T + s) * κ)) ≤
        ((νk (γ b)).prod MeasureTheory.volume) (F b) ∧
        ∀ p ∈ F b, b ∈ lst (γ b) (obs (Bk (γ b)) (δ Nk L) p)))
  hhalf : (∀ b, ∀ p ∈ F b, p.2 < (((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s))
  hwhole : (∀ b, ∀ l ∈ A b, ∀ t ∈ coarseInterval T s (j b : ℕ),
      ‖Matrix.toEuclideanLin (Q b)⁻¹ (y l t - c b - t • v₀ b)‖ ≤
        3 * κ * (2 : ℝ) ^ s ∧
      |MvPolynomial.eval (x l t) (R b)| ≤ δ Nk L * Nk ^ a ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R b))| ≤
        Bk (γ b) * Nk ^ a)
  hlst : (∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ)
  hlstfmt : (∀ γ₀ b, MeasurableSet {p | b ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L) p)} ∧
      ∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ |
        b ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L)
          ((i, fun z : Fin 6 => r z.castSucc), r 6))})
  hGood : (∀ γ₀, MeasurableSet (Good γ₀) ∧ Good γ₀ ⊆ Ek γ₀ ∧
      ∀ p ∈ Good γ₀,
        ‖y p.1 p.2‖ + ‖v p.1‖ ≤ κ ∧
        |MvPolynomial.eval (x p.1 p.2) (Pk γ₀)| ≤ κ ∧
        Bk γ₀ / κ ≤
          |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (Pk γ₀))| ∧
        (∀ r ∈ depths, gk γ₀ r (obs (Bk γ₀) (δ Nk r) p) ≤
          ENNReal.ofReal (Nk ^ (-f r + a))) ∧
        Gk γ₀ u (obs (Bk γ₀) (δ Nk L) p,
          fun i : Fin 2 => ⌊v p.1 i / δ Nk u⌋) ≤
          ENNReal.ofReal (Nk ^ (-f L - S * u + a)))
  hH : (∀ b b', MeasurableSet (H b b') ∧
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
            min (1 / 8 : ℝ) (Nk ^ a * R₂ / R₁)))
  hcoverage : ENNReal.ofReal (lam * κ⁻¹) ≤
      ∑ b, ENNReal.ofReal (ωk (γ b) * (2 : ℝ) ^ T) *
        ((νk (γ b)).prod (MeasureTheory.volume.prod MeasureTheory.volume))
          {p | ∃ b', p ∈ H b b'}

theorem nativeAt_iff (aligned : Prop) (lam Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ)
    (νk : Fin Wk → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Pk : Fin Wk → MvPolynomial (Fin 4) ℝ) (Bk : Fin Wk → ℝ)
    (f : ℝ → ℝ)
    (gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (L S a e u h : ℝ) (M D : ℕ) (depths : Finset ℝ) (ε : ℝ) :
    NativeAt aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε ↔ Nonempty (NativeSample aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε) := by
  constructor
  · rintro ⟨κ, κ_one, κ_le, T, s, C, R₁, R₂, γ, j, c, v₀, Q, R, A, F, lst, H, Good, hT, hC, hgainlo, hgainhi, hR₂pos, hR21, hR₁le, hR₂inv, hscales, hdisj, hchart, hhalf, hwhole, hlst, hlstfmt, hGood, hH, hcoverage⟩
    exact ⟨⟨κ, κ_one, κ_le, T, s, C, R₁, R₂, γ, j, c, v₀, Q, R, A, F, lst, H, Good, hT, hC, hgainlo, hgainhi, hR₂pos, hR21, hR₁le, hR₂inv, hscales, hdisj, hchart, hhalf, hwhole, hlst, hlstfmt, hGood, hH, hcoverage⟩⟩
  · rintro ⟨p⟩
    exact ⟨p.κ, p.κ_one, p.κ_le, p.T, p.s, p.C, p.R₁, p.R₂, p.γ, p.j, p.c, p.v₀, p.Q, p.R, p.A, p.F, p.lst, p.H, p.Good, p.hT, p.hC, p.hgainlo, p.hgainhi, p.hR₂pos, p.hR21, p.hR₁le, p.hR₂inv, p.hscales, p.hdisj, p.hchart, p.hhalf, p.hwhole, p.hlst, p.hlstfmt, p.hGood, p.hH, p.hcoverage⟩

end Submission.Obl.k4_compatible_pair_frame_preparation
