-- Adapted from this LOT tree, o206, session x0709, commit f7d6ac58,
-- Submission/Obl/k4_coarse_pair_frame_preparation/NativeSample.lean.
import Submission.Obl.k4_homogeneous_native_pair_preparation.Model

/-! A record for the exact native sample in the proposed preparation split. -/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory
open scoped ENNReal BigOperators

structure NativeSample (aligned : Prop) (lam Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ)))
    (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Pk : Fin Wk → MvPolynomial (Fin 4) ℝ) (Bk : Fin Wk → ℝ) (f : ℝ → ℝ)
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
  scale_lo : Nk ^ e ≤ (2 : ℝ) ^ s
  scale_hi : (2 : ℝ) ^ s ≤ 2 * Nk ^ e
  R₂_pos : 0 < R₂
  R₂_le : R₂ ≤ R₁
  R₁_le : R₁ ≤ Nk ^ M
  R₂_inv : R₂⁻¹ ≤ Nk ^ M
  classes : ∀ b, R₁ ≤ r₁ (Q b) ∧ r₁ (Q b) < 2 * R₁ ∧
    R₂ ≤ r₂ (Q b) ∧ r₂ (Q b) < 2 * R₂
  disj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')
  charts : ∀ b, chart Nk M D κ (T + s) ((j b : ℕ) : ℝ) L (Bk (γ b)) (Ek (γ b))
    (c b) (v₀ b) (Q b) (R b) (A b) (F b)
    (ENNReal.ofReal (Nk ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ (T + s) * κ)) ≤
      ((νk (γ b)).prod volume) (F b) ∧
      ∀ p ∈ F b, b ∈ lst (γ b) (obs (Bk (γ b)) (δ Nk L) p))
  halfopen : ∀ b, ∀ p ∈ F b, p.2 < (((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s)
  whole : ∀ b, ∀ l ∈ A b, ∀ t ∈ coarseInterval T s (j b : ℕ),
    ‖Matrix.toEuclideanLin (Q b)⁻¹ (y l t - c b - t • v₀ b)‖ ≤ 3 * κ * (2 : ℝ) ^ s ∧
    |MvPolynomial.eval (x l t) (R b)| ≤ δ Nk L * Nk ^ a ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R b))| ≤ Bk (γ b) * Nk ^ a
  list_card : ∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ
  list_format : ∀ γ₀ b, MeasurableSet {p | b ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L) p)} ∧
    ∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ |
      b ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L) ((i, fun z : Fin 6 => r z.castSucc), r 6))}
  good : ∀ γ₀, MeasurableSet (Good γ₀) ∧ Good γ₀ ⊆ Ek γ₀ ∧
    ∀ p ∈ Good γ₀, ‖y p.1 p.2‖ + ‖v p.1‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) (Pk γ₀)| ≤ κ ∧
      Bk γ₀ / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (Pk γ₀))| ∧
      (∀ r ∈ depths, gk γ₀ r (obs (Bk γ₀) (δ Nk r) p) ≤ ENNReal.ofReal (Nk ^ (-f r + a))) ∧
      Gk γ₀ u (obs (Bk γ₀) (δ Nk L) p, fun i : Fin 2 => ⌊v p.1 i / δ Nk u⌋) ≤
        ENNReal.ofReal (Nk ^ (-f L - S * u + a))
  pairs : ∀ b b', MeasurableSet (H b b') ∧
    ∀ p ∈ H b b', γ b = γ b' ∧ (j b : ℕ) / 2 ^ s = (j b' : ℕ) / 2 ^ s ∧
      (p.1, p.2.1) ∈ F b ∧ (p.1, p.2.2) ∈ F b' ∧
      (p.1, p.2.1) ∈ Good (γ b) ∧ (p.1, p.2.2) ∈ Good (γ b) ∧
      (∀ R' : MvPolynomial (Fin 4) ℝ, R' = R b ∨ R' = R b' →
        ∀ t : ℝ, t = p.2.1 ∨ t = p.2.2 →
          Bk (γ b) * Nk ^ (-a) ≤
            |MvPolynomial.eval (x p.1 t) (MvPolynomial.pderiv (3 : Fin 4) R')|) ∧
      (aligned → R₁ ≤ 8 * Nk ^ a * R₂ ∨
        |wedge (nrm (Q b)) (nrm (Q b'))| ≤ min (1 / 8 : ℝ) (Nk ^ a * R₂ / R₁))
  coverage : ENNReal.ofReal (lam * κ⁻¹) ≤
    ∑ b, ENNReal.ofReal (ωk (γ b) * (2 : ℝ) ^ T) *
      ((νk (γ b)).prod (volume.prod volume)) {p | ∃ b', p ∈ H b b'}

theorem nativeSample_nonempty_iff (aligned : Prop) (lam Nk : ℝ) (Wk : ℕ)
    (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ)))
    (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Pk : Fin Wk → MvPolynomial (Fin 4) ℝ) (Bk : Fin Wk → ℝ) (f : ℝ → ℝ)
    (gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (L S a e u h : ℝ) (M D : ℕ) (depths : Finset ℝ) (ε : ℝ) :
    Nonempty (NativeSample aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε) ↔
      NativeAt aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε := by
  constructor
  · rintro ⟨q⟩
    exact ⟨q.κ, q.κ_one, q.κ_le, q.T, q.s, q.C, q.R₁, q.R₂, q.γ, q.j, q.c, q.v₀,
      q.Q, q.R, q.A, q.F, q.lst, q.H, q.Good, q.hT, q.hC, q.scale_lo, q.scale_hi,
      q.R₂_pos, q.R₂_le, q.R₁_le, q.R₂_inv, q.classes, q.disj, q.charts, q.halfopen,
      q.whole, q.list_card, q.list_format, q.good, q.pairs, q.coverage⟩
  · rintro ⟨κ, hκ1, hκε, T, s, C, R₁, R₂, γ, j, c, v₀, Q, R, A, F, lst, H, Good,
      hT, hC, hlo, hhi, hR₂, h21, hR₁, hR₂inv, hclass, hdisj, hchart, hhalf,
      hwhole, hlist, hlistfmt, hgood, hpairs, hcov⟩
    exact ⟨{
      κ := κ, κ_one := hκ1, κ_le := hκε, T := T, s := s, C := C,
      R₁ := R₁, R₂ := R₂, γ := γ, j := j, c := c, v₀ := v₀, Q := Q, R := R, A := A,
      F := F, lst := lst, H := H, Good := Good, hT := hT, hC := hC,
      scale_lo := hlo, scale_hi := hhi, R₂_pos := hR₂, R₂_le := h21, R₁_le := hR₁,
      R₂_inv := hR₂inv, classes := hclass, disj := hdisj, charts := hchart,
      halfopen := hhalf, whole := hwhole, list_card := hlist, list_format := hlistfmt,
      good := hgood, pairs := hpairs, coverage := hcov }⟩

end Submission.Obl.k4_homogeneous_native_pair_preparation
