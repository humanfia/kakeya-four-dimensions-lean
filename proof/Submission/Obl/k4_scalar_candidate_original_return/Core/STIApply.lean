import Submission.Obl.k4_scalar_candidate_original_return.Prepared

/-!
# Applying the supplied scalar tangent improvement

`STI` is quantified over every scalar tangent input.  We record the curried
application to an arbitrary input satisfying `TangentInput`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter

/-- The conclusion of `STI` for one tangent input. -/
def STIConclusion (rN : ℕ → ℝ) (rd : ℝ) (rW : ℕ → ℕ)
    (rν : (k : ℕ) → Fin (rW k) → Measure Line)
    (ρ : (k : ℕ) → Fin (rW k) → Measure Inc)
    (T n : ℕ → ℝ → ℕ)
    (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (rW k))
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set Line) : Prop :=
  ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ (s c : ℝ) (i : Fin (n k s)) (P : Poly),
      R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ c ∧ c ≤ R ∧ P.totalDegree ≤ 2 ∧
      (∀ b, |P.coeff b| ≤ rN k ^ R) ∧
      ENNReal.ofReal (rN k ^ (-rd * c - ε) / (2 : ℝ) ^ T k s) *
          rν k (γ k s i) (A k s i) ≤
        ρ k (γ k s i) {p | p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧
          ∀ t ∈ I (T k s) (j k s i),
            |x p.1 t - MvPolynomial.eval ![t, y p.1 t] P| ≤ rN k ^ ε * rN k ^ (-s - c)}

/-- The supplied `STI` applies to every input satisfying `TangentInput`. -/
theorem STI.apply (hSTI : STI) {rN rK : ℕ → ℝ} {rd κ rS : ℝ}
    {rW : ℕ → ℕ} {rω : (k : ℕ) → Fin (rW k) → ℝ}
    {rν : (k : ℕ) → Fin (rW k) → Measure Line}
    {ρ : (k : ℕ) → Fin (rW k) → Measure Inc}
    {π : (k : ℕ) → Fin (rW k) → Measure ℝ}
    {T n : ℕ → ℝ → ℕ}
    {γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (rW k)}
    {j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)}
    {A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set Line}
    {u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ}
    {F : (k : ℕ) → (s : ℝ) → Fin (n k s) → Poly}
    (hTI : TangentInput rN rK rd κ rS rW rω rν ρ π T n γ j A u v F) :
    STIConclusion rN rd rW rν ρ T n γ j A := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hb1, hb2, hb3⟩ := hTI
  exact hSTI rN rK h1 h2 h3 rd κ rS h4 h5 h6 h7 h8 rW rω rν ρ π T n γ j A u v F hb1 hb2 hb3

end Submission.Obl.k4_scalar_candidate_original_return
