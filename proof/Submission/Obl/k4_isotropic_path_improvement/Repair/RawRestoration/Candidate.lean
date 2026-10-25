-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawRestoration/Candidate.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
-- Adapted from this LOT tree o143/x0542, commit f027eb90,
-- Submission/Obl/k4_isotropic_discovery_of_local_restoration/Candidate.lean.
import Mathlib

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration

noncomputable section

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Event := Line × ℝ

/-- The original affine trajectory, in the exact order of the frozen variables. -/
def graphPoint (l : Line) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

/-- The problem's dyadic thickness, including its prescribed floor. -/
def dyadicThickness (N r : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

/-- The original-law residual candidate assertion, with no auxiliary analytic law. -/
def residualCandidate (Nk L : ℝ) (W : ℕ)
    (ν : Fin W → MeasureTheory.Measure Line) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Line) (H : Fin W → Set Event) : Prop :=
  ∃ (b : Fin C) (actualGain : ℝ), gain ≤ actualGain ∧ actualGain ≤ 1 / 8 ∧
    r (lev b) + 2 * actualGain * L ≤ L ∧
    ∃ (R : MvPolynomial (Fin 4) ℝ) (A' : Set Line),
      R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Nk ^ Mc) ∧
      MeasurableSet A' ∧ A' ⊆ A b ∧
      (∀ l ∈ A', ∀ t ∈ Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
          (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)),
        |MvPolynomial.eval (graphPoint l t) R| ≤
            Nk ^ (ρ * gain * L + ε) * dyadicThickness Nk (r (lev b) + actualGain * L) ∧
        |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv 3 R)| ≤
            Nk ^ (ρ * gain * L + ε) * B (γ b) ∧
        |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R))| ≤
            Nk ^ (ρ * gain * L + ε) * B (γ b) ^ 2 /
              dyadicThickness Nk (r (lev b) + actualGain * L)) ∧
      ENNReal.ofReal (Nk ^ (-((d₁ * actualGain + ρ * gain) * L) - ε) /
          (2 : ℝ) ^ T (lev b)) * ν (γ b) (A b) ≤
        ((ν (γ b)).prod MeasureTheory.volume)
          {p | p ∈ H (γ b) ∧ p.1 ∈ A' ∧
            p.2 ∈ Set.Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
              (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
            B (γ b) / Nk ^ (ρ * gain * L + ε) ≤
              |MvPolynomial.eval (graphPoint p.1 p.2) (MvPolynomial.pderiv 3 R)|}

/-- A trajectory on a dyadic block, with its time parameter normalized to `[0,1]`. -/
def blockOrigin (l : Line) (t₀ : ℝ) : Fin 4 → ℝ := graphPoint l t₀

def blockVelocity (l : Line) (q : ℝ) : Fin 4 → ℝ :=
  ![q, q * l.2 3, q * l.2 4, q * l.2 5]

lemma graphPoint_on_block (l : Line) (t₀ q s : ℝ) :
    graphPoint l (t₀ + q * s) = fun i => blockOrigin l t₀ i + s * blockVelocity l q i := by
  funext i
  fin_cases i <;> simp [graphPoint, blockOrigin, blockVelocity] <;> ring

/-- Every point of the dyadic block has a normalized parameter in `[0,1]`. -/
lemma mem_dyadic_block_iff (j T : ℕ) (t : ℝ) :
    t ∈ Set.Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T) ↔
      ∃ s ∈ Set.Icc (0 : ℝ) 1,
        t = (j : ℝ) / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ * s := by
  have hq : 0 < (2 : ℝ) ^ T := by positivity
  constructor
  · intro ht
    refine ⟨(2 : ℝ) ^ T * t - j, ?_, ?_⟩
    · constructor
      · have h := (div_le_iff₀ hq).mp ht.1
        nlinarith
      · have h := (le_div_iff₀ hq).mp ht.2
        nlinarith
    · field_simp
      ring
  · rintro ⟨s, hs, rfl⟩
    constructor
    · have h := mul_nonneg (inv_nonneg.mpr hq.le) hs.1
      linarith
    · have h := mul_le_mul_of_nonneg_left hs.2 (inv_nonneg.mpr hq.le)
      simp only [mul_one] at h
      rw [add_div, one_div]
      linarith

end

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration
