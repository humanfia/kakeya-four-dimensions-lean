import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.Pullback
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ResidualFields

/-!
# Residual candidates at an index with a frame

The candidate statement of the residual model at an index `k` whose frame is
`f`, written with the frame's own fields: residual depth `s` is served by grid
level `gridLevel (U' / m) m s`, whose residual labels are the retained nodes.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted

open MeasureTheory Set Filter MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
open Submission.Lib.K4ContactNormalization

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}

/-- The grid level of a residual depth. -/
def gl (f : Frame D k s₀ U') (s : ℝ) : ℕ := gridLevel (U' / f.m) f.m s

/-- A residual candidate at index `k`, in frame terms. -/
def FrameCand (f : Frame D k s₀ U') (R ε : ℝ) : Prop :=
  ∃ (s v : ℝ) (i : Fin (f.level (gl f s)).n), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ U' ∧
    ((∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤ D.N k ^ R *
        ((1 + ∑ e ∈ ((f.level (gl f s)).F i).support, |((f.level (gl f s)).F i).coeff e|) +
          ∑ e ∈ (X 3 : MvPolynomial (Fin 4) ℝ).support, |(X 3 : MvPolynomial (Fin 4) ℝ).coeff e|) ^ R) ∧
      ENNReal.ofReal (D.N k ^ (-D.d * v - ε) / (2 : ℝ) ^ (f.level (gl f s)).T) *
          cond (D.ν k) f.parentSet ((f.level (gl f s)).A i) ≤
        f.resρ {p | p.1 ∈ (f.level (gl f s)).B i ∧
          p.2 ∈ Data.I (f.level (gl f s)).T ((f.level (gl f s)).j i) ∧
          (∀ τ ∈ Data.I (f.level (gl f s)).T ((f.level (gl f s)).j i),
            |eval (point (f.coeff p.1) τ) Q| ≤ D.N k ^ ε * D.N k ^ (-s - v) ∧
            |eval (point (f.coeff p.1) τ) (pderiv 3 Q)| ≤ D.N k ^ ε ∧
            |eval (point (f.coeff p.1) τ) (pderiv 3 (pderiv 3 Q))| ≤
              D.N k ^ ε / D.N k ^ (-s - v)) ∧
          D.N k ^ (-ε) ≤ |eval (point (f.coeff p.1) p.2) (pderiv 3 Q)|}) ∨
    (∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ D.N k ^ R) ∧
      ENNReal.ofReal (D.N k ^ (-ε) / (2 : ℝ) ^ (f.level (gl f s)).T) *
          cond (D.ν k) f.parentSet ((f.level (gl f s)).A i) ≤
        f.resρ {p | p.1 ∈ (f.level (gl f s)).B i ∧
          p.2 ∈ Data.I (f.level (gl f s)).T ((f.level (gl f s)).j i) ∧
          |f.coeff p.1 4 - z 0 - z 1 * f.coeff p.1 3| ≤
            D.N k ^ ε * D.N k ^ (-D.κ * s - v)}))

/-- The candidate statement of the residual model at an index with a frame. -/
theorem frameCand_of_residual {e₀' : ℝ} {K' : ℕ → ℝ}
    {fr : (k : ℕ) → Option (Frame D k s₀ U')} {f : Frame D k s₀ U'} (hfr : fr k = some f)
    {R ε : ℝ}
    (hc : ∃ (s v : ℝ) (i : Fin ((residualData D s₀ U' e₀' K' fr).n k s)),
      R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ (residualData D s₀ U' e₀' K' fr).U ∧
      ((∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ e, |Q.coeff e| ≤ (residualData D s₀ U' e₀' K' fr).N k ^ R *
          ((1 + ∑ e ∈ ((residualData D s₀ U' e₀' K' fr).F k s i).support,
            |((residualData D s₀ U' e₀' K' fr).F k s i).coeff e|) +
            ∑ e ∈ ((residualData D s₀ U' e₀' K' fr).P k).support,
              |((residualData D s₀ U' e₀' K' fr).P k).coeff e|) ^ R) ∧
        ENNReal.ofReal ((residualData D s₀ U' e₀' K' fr).N k ^
            (-(residualData D s₀ U' e₀' K' fr).d * v - ε) /
            (2 : ℝ) ^ (residualData D s₀ U' e₀' K' fr).T k s) *
            (residualData D s₀ U' e₀' K' fr).ν k ((residualData D s₀ U' e₀' K' fr).A k s i) ≤
          (residualData D s₀ U' e₀' K' fr).ρ k {p |
            p.1 ∈ (residualData D s₀ U' e₀' K' fr).B k s i ∧
            p.2 ∈ Data.I ((residualData D s₀ U' e₀' K' fr).T k s)
              ((residualData D s₀ U' e₀' K' fr).j k s i) ∧
            (residualData D s₀ U' e₀' K' fr).fit k
              ((residualData D s₀ U' e₀' K' fr).N k ^ ε)
              ((residualData D s₀ U' e₀' K' fr).N k ^ (-s - v)) Q p.1
              (Data.I ((residualData D s₀ U' e₀' K' fr).T k s)
                ((residualData D s₀ U' e₀' K' fr).j k s i)) ∧
            (residualData D s₀ U' e₀' K' fr).N k ^ (-ε) ≤
              |eval ((residualData D s₀ U' e₀' K' fr).x k p.1 p.2) (pderiv (3 : Fin 4) Q)|}) ∨
      (∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ (residualData D s₀ U' e₀' K' fr).N k ^ R) ∧
        ENNReal.ofReal ((residualData D s₀ U' e₀' K' fr).N k ^ (-ε) /
            (2 : ℝ) ^ (residualData D s₀ U' e₀' K' fr).T k s) *
            (residualData D s₀ U' e₀' K' fr).ν k ((residualData D s₀ U' e₀' K' fr).A k s i) ≤
          (residualData D s₀ U' e₀' K' fr).ρ k {p |
            p.1 ∈ (residualData D s₀ U' e₀' K' fr).B k s i ∧
            p.2 ∈ Data.I ((residualData D s₀ U' e₀' K' fr).T k s)
              ((residualData D s₀ U' e₀' K' fr).j k s i) ∧
            |(residualData D s₀ U' e₀' K' fr).b k p.1 4 - z 0 -
                z 1 * (residualData D s₀ U' e₀' K' fr).b k p.1 3| ≤
              (residualData D s₀ U' e₀' K' fr).N k ^ ε *
                (residualData D s₀ U' e₀' K' fr).N k ^
                  (-(residualData D s₀ U' e₀' K' fr).ℓ * s - v)}))) :
    FrameCand f R ε := by
  simp only [residualData, withLevels, residualBase, residualLevels, residualSteps, Data.fit,
    Data.x] at hc
  rw [hfr] at hc
  dsimp only at hc
  obtain ⟨s, v, i, h1, h2, h3, h4, h5, halt⟩ := hc
  refine ⟨s, v, i, h1, h2, h3, h4, h5, ?_⟩
  rcases halt with ⟨Q, hQ1, hQ2, hQ3⟩ | ⟨z, hz1, hz2⟩
  · left
    refine ⟨Q, hQ1, hQ2, ?_⟩
    exact hQ3
  · right
    refine ⟨z, hz1, ?_⟩
    exact hz2

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted
