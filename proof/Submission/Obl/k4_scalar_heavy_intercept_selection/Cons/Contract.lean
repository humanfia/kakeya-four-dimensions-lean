/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/Cons/Contract.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.Cons.Geometry

/-!
# The conservativity contract

`FieldAt` is the per-sample body of the Cartesian field certificate of o231,
written with `yL`, `xL` for the frozen abbreviations `y`, `x`; for the
packet `i` of sample `k` it is definitionally the frozen body with
`ν k (γ k 1 i)`, `π k (γ k 1 i)`, `ρ k (γ k 1 i)`, `A k 1 i`, `T k 1`, `j k 1 i`.

`PotAt` is the potential that the conservativity step adds on the same
packet: a polynomial `P` in normalized coordinates and a bounded measurable
intercept `c`, with `|X_l(t) - P(u_l(t)) - c(l)| ≤ H' N^(-1-2c*)` throughout
the block, `μ`-almost everywhere.

`ConservativityContract` is the sequence-level statement: the field
certificate upgrades to one that also carries such a potential, with the
same `H, D, Z, B` and the same packet data.
-/

namespace Submission.Obl.k4_scalar_heavy_intercept_selection.Cons

open MeasureTheory

/-- The per-sample body of the Cartesian field certificate. -/
def FieldAt (Nk Hk d κ S Z B R : ℝ) (D : ℕ) (νg : Measure (ℕ × (Fin 5 → ℝ))) (πg : Measure ℝ)
    (ρg : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (Ag : Set (ℕ × (Fin 5 → ℝ))) (Tk : ℕ)
    (jj : Fin (2 ^ Tk)) (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ)
    (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) : Prop :=
  (fun (h : ℝ) => MeasurableSet Ag ∧ MeasureTheory.IsProbabilityMeasure νg ∧
    MeasureTheory.IsProbabilityMeasure πg ∧ (∀ᵐ l ∂νg, ∀ e, |l.2 e| ≤ Hk) ∧
    Nk ^ (-κ) / Hk ≤ h ∧ h ≤ Hk * Nk ^ (-κ) ∧ 0 < h ∧ h ≤ 1 ∧
    ENNReal.ofReal (Nk ^ (-d) * h / Hk) ≤ νg Ag ∧ νg Ag ≤ ENNReal.ofReal (Hk * Nk ^ (-d) * h) ∧
    μ ≤ ρg ∧ μ ≤ ENNReal.ofReal Hk • (νg.prod MeasureTheory.volume) ∧
    μ {p | p.1 ∈ Ag ∧ p.2 ∈ Set.Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk)
      ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk)}ᶜ = 0 ∧
    ENNReal.ofReal (h / Hk) * νg Ag ≤ μ Set.univ ∧
    z₀ 0 = (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ∧ (∀ e, |z₀ e| ≤ Hk) ∧
    (∀ᵐ p ∂μ, ∀ t ∈ Set.Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk),
      ∀ e : Fin 2, |(![t, yL p.1 t] e - z₀ e) / h| ≤ Hk) ∧
    (∀ q : Fin 2 → ℤ, μ {p | (fun e : Fin 2 =>
      (⌊((![p.2, yL p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (Nk ^ (-Z))⌋ : ℤ)) = q} ≤
        ENNReal.ofReal ((Hk * h) * Nk ^ (-2 * Z)) * νg Ag) ∧
    (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R →
      (∀ c : ℤ, πg {v : ℝ | (⌊v / (Nk ^ (-r))⌋ : ℤ) = c} ≤ ENNReal.ofReal (Hk * Nk ^ (-S * r))) ∧
      ∀ (q : Fin 3 → ℤ) (c : ℤ),
        μ {p | (fun e => (⌊(![p.2, yL p.1 p.2, xL p.1 p.2] : Fin 3 → ℝ) e / (Nk ^ (-B))⌋ : ℤ)) = q ∧
          p.1.2 1 ∈ {v : ℝ | (⌊v / (Nk ^ (-r))⌋ : ℤ) = c}} ≤
        ENNReal.ofReal Hk *
          μ {p | (fun e => (⌊(![p.2, yL p.1 p.2, xL p.1 p.2] : Fin 3 → ℝ) e / (Nk ^ (-B))⌋ : ℤ)) =
            q} * πg {v : ℝ | (⌊v / (Nk ^ (-r))⌋ : ℤ) = c}) ∧
    (∀ e, (𝒯 e).totalDegree ≤ D ∧ ∀ b, |(𝒯 e).coeff b| ≤ Hk) ∧
    (∀ᵐ p ∂μ, ∀ t ∈ Set.Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk),
      |p.1.2 3 + 2 * t * p.1.2 4 - ∑ e : Fin 2, MvPolynomial.eval
        (fun e : Fin 2 => ((![t, yL p.1 t] : Fin 2 → ℝ) e - z₀ e) / h) (𝒯 e) *
          (![1, p.1.2 1] : Fin 2 → ℝ) e| ≤ Hk * Nk ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4)) ∧
    (∀ w : ℝ, Nk ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8) ≤ w → w ≤ Nk ^ (-1 : ℝ) →
      Set.Finite {q : (Fin 2 → ℤ) × ℤ | μ {p | (fun e : Fin 2 =>
        (⌊((![p.2, yL p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (Nk ^ (-Z))⌋ : ℤ)) = q.1 ∧
          (⌊xL p.1 p.2 / w⌋ : ℤ) = q.2} ≠ 0} ∧
      ({q : (Fin 2 → ℤ) × ℤ | μ {p | (fun e : Fin 2 =>
        (⌊((![p.2, yL p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (Nk ^ (-Z))⌋ : ℤ)) = q.1 ∧
          (⌊xL p.1 p.2 / w⌋ : ℤ) = q.2} ≠ 0}.ncard : ℝ) ≤
        Hk * Nk ^ (2 * Z) * (Nk ^ (-1 : ℝ) / w) ^ d)) (((2 : ℝ) ^ Tk)⁻¹)

/-- The potential carried by the same packet. -/
def PotAt (Nk Hk' cstar : ℝ) (D' : ℕ) (Tk : ℕ) (jj : Fin (2 ^ Tk))
    (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (c : ℕ × (Fin 5 → ℝ) → ℝ) : Prop :=
  P.totalDegree ≤ D' ∧ (∀ b, |P.coeff b| ≤ Hk') ∧ Measurable c ∧ (∀ l, |c l| ≤ Hk') ∧
    ∀ᵐ p ∂μ, ∀ t ∈ Set.Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk),
      |xL p.1 t - MvPolynomial.eval
        (fun e : Fin 2 => ((![t, yL p.1 t] : Fin 2 → ℝ) e - z₀ e) / ((2 : ℝ) ^ Tk)⁻¹) P - c p.1| ≤
        Hk' * Nk ^ (-1 - 2 * cstar)

/-- The sequence-level conservativity contract. -/
def ConservativityContract : Prop :=
  ∀ (N : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop →
  ∀ d κ S : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S →
  ∀ (W : ℕ → ℕ) (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) (T n : ℕ → ℝ → ℕ)
    (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k))
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ)))
    (H : ℕ → ℝ) (D : ℕ) (Z B : ℝ),
    ((∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ N k ^ ε) →
    10 ≤ Z → Z + 10 ≤ B →
    (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∃ (i : Fin (n k 1))
      (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ) (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ),
      FieldAt (N k) (H k) d κ S Z B R D (ν k (γ k 1 i)) (π k (γ k 1 i)) (ρ k (γ k 1 i))
        (A k 1 i) (T k 1) (j k 1 i) μ z₀ 𝒯) →
    ∃ (H' : ℕ → ℝ) (D' : ℕ),
      ((∀ k, 1 ≤ H' k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H' k ≤ N k ^ ε) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∃ (i : Fin (n k 1))
        (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ)
        (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℝ)
        (c : ℕ × (Fin 5 → ℝ) → ℝ),
        FieldAt (N k) (H k) d κ S Z B R D (ν k (γ k 1 i)) (π k (γ k 1 i)) (ρ k (γ k 1 i))
          (A k 1 i) (T k 1) (j k 1 i) μ z₀ 𝒯 ∧
        PotAt (N k) (H' k) (κ * (1 - d) / 1000) D' (T k 1) (j k 1 i) μ z₀ P c

end Submission.Obl.k4_scalar_heavy_intercept_selection.Cons
