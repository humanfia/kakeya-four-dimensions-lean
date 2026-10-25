import Submission.Obl.k4_scalar_true_terminal_lifting.LiftAlg
import Submission.Obl.k4_scalar_true_terminal_lifting.LiftFormat
import Submission.Obl.k4_scalar_true_terminal_lifting.LiftLists
import Submission.Obl.k4_scalar_true_terminal_lifting.LiftMeasure

/-!
# The lifted chart is a true terminal chart of `p`

Assembly of the clauses: if every q-world used by `Q` is good at loss `δ`, the lifted chart
is a true terminal chart of `p` at `K`, with time exponent `h₁ + h₂`, loss `ε₃` and integer
budget `2 * B₂ + 2 * B₁ + 9`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

namespace RefStep

variable {p q : Code} {r b : ℝ} {k K : ℕ} (S : RefStep p q r b k K)
variable {B₂ : ℕ} {h₂ ε₂ : ℝ} (Q : ChartW q B₂ (L q) (L q) h₂ ε₂ true k)

theorem lift_chartData (hN2 : 2 ≤ N p K) (hω : ∀ a, 0 ≤ ω p K a)
    (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (hr : 0 ≤ r) (hLq : L q = L p - r)
    (hbL : b ≤ L p) (hε₁1 : S.ε₁ ≤ 1) (hε₂ : 0 ≤ ε₂) {δ ε₃ : ℝ}
    (hgood : ∀ d, ENNReal.ofReal (N p K ^ (f q (L q) - f p (L p) - δ) * S.J₁ (Q.γ d)) ≤
      ν p K (S.γ₁ (Q.γ d)) (S.A₁ (Q.γ d)))
    (hε₃ : S.ε₁ + ε₂ + δ ≤ ε₃) (hδ : 0 ≤ δ) (hε₁0 : 0 ≤ S.ε₁)
    (hε₃' : 4 * N p K ^ (S.ε₁ + ε₂) ≤ N p K ^ ε₃) :
    ChartData p (2 * B₂ + 2 * S.B₁ + 9) (L p) (L p) (S.h₁ + h₂) ε₃ true K (S.T₁ + Q.T) Q.n
      (S.γ₃ Q) (S.j₃ Q) (S.A₃ Q) (S.C₃ Q) (S.u₃ Q) (S.v₃ Q) (S.J₃ Q) (S.P₃ Q) (S.Λ₃ Q) := by
  have hN0 : 0 < N p K := by linarith
  have hN1 : 1 ≤ N p K := by linarith
  unfold ChartData
  refine ⟨S.lift_time Q hN0, S.lift_count Q hN1, S.lift_meas Q, S.lift_disj Q, S.lift_sub Q,
    fun d => ⟨S.lift_pos Q hν d, S.lift_J_pos Q d, S.lift_J_inv Q hN1 d,
      S.lift_J_le Q hN1 (by linarith) d, S.lift_uv Q hN1 hε₂ hε₃' d, S.lift_deg Q d,
      S.lift_coeff Q hN2 hr hε₁1 d, S.lift_A_bound Q hN1 (by linarith) d,
      S.lift_format5 Q hN2 d, S.lift_format6 Q hN2 d, S.lift_fit Q hN1 hLq (by linarith) d,
      fun _ => S.lift_floor Q hν hN0 (by linarith) d (hgood d)⟩,
    S.lift_card Q hN1 hε₃', S.lift_Λmeas Q, S.lift_null Q hν hN0 hLq hbL,
    S.lift_mass Q hν hω hN1 (by linarith)⟩

theorem lift_chart (hN2 : 2 ≤ N p K) (hω : ∀ a, 0 ≤ ω p K a)
    (hν : ∀ a, IsProbabilityMeasure (ν p K a)) (hr : 0 ≤ r) (hLq : L q = L p - r)
    (hbL : b ≤ L p) (hε₁1 : S.ε₁ ≤ 1) (hε₂ : 0 ≤ ε₂) {δ ε₃ : ℝ}
    (hgood : ∀ d, ENNReal.ofReal (N p K ^ (f q (L q) - f p (L p) - δ) * S.J₁ (Q.γ d)) ≤
      ν p K (S.γ₁ (Q.γ d)) (S.A₁ (Q.γ d)))
    (hε₃ : S.ε₁ + ε₂ + δ ≤ ε₃) (hδ : 0 ≤ δ) (hε₁0 : 0 ≤ S.ε₁)
    (hε₃' : 4 * N p K ^ (S.ε₁ + ε₂) ≤ N p K ^ ε₃) :
    Chart p (2 * B₂ + 2 * S.B₁ + 9) (L p) (L p) (S.h₁ + h₂) ε₃ true K :=
  ⟨S.T₁ + Q.T, Q.n, S.γ₃ Q, S.j₃ Q, S.A₃ Q, S.C₃ Q, S.u₃ Q, S.v₃ Q, S.J₃ Q, S.P₃ Q, S.Λ₃ Q,
    S.lift_chartData Q hN2 hω hν hr hLq hbL hε₁1 hε₂ hgood hε₃ hδ hε₁0 hε₃'⟩

end RefStep

end Submission.Obl.k4_scalar_true_terminal_lifting
