import Submission.Obl.k4_scalar_true_terminal_lifting.Step

/-!
# The lifted chart

Given one index `S : RefStep p q r b k K` of an actual refinement and a true terminal chart
`Q` of `q` at `k`, the lifted chart of `p` at `K` has one piece per piece `d` of `Q`: with
`i = Q.γ d` the q-world of `d`,

* world `γ₁ i`, dyadic index `jcomp (j₁ i) (Q.j d)` at depth `T₁ + Q.T`;
* assignment `A₁ i ∩ θ i ⁻¹' Q.A d`, incidences `C₁ i ∩ Φ i ⁻¹' Q.C d`;
* width `J₁ i * Q.J d`, affine fit `u₃, v₃`, residual polynomial
  `P₁ i + N ^ (-r) * Q.P d ∘ (affine normalization)`;
* label lists: the two candidate `b`-bins of a terminal bin, then the two candidate
  normalized terminal bins of each listed q-world.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The candidate coarse labels (at resolution `NN ^ (-b)`) of a fine label at resolution
`NN ^ (-L)`. -/
noncomputable def coarseLab (NN L b : ℝ) (s : Fin 2) (z : (Fin 2 → ℝ) × ℤ) :
    (Fin 2 → ℝ) × ℤ :=
  (z.1, ⌊(z.2 : ℝ) * (NN ^ (-L) / NN ^ (-b))⌋ + ((s : ℕ) : ℤ))

namespace RefStep

variable {p q : Code} {r b : ℝ} {k K : ℕ} (S : RefStep p q r b k K)

/-- The affine normalization of times and scalar coordinates of the `i`-th q-world. -/
noncomputable def G (i : Fin (W q k)) : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![C S.dt⁻¹ * (X 0 - C (S.t₀ i)), C (S.J₁ i)⁻¹ * (X 1 - C (S.u₁ i) - C (S.v₁ i) * X 0)]

/-- The candidate normalized terminal labels of the `i`-th q-world for a fine label. -/
noncomputable def qlab (i : Fin (W q k)) (s : Fin 2) (z : (Fin 2 → ℝ) × ℤ) :
    (Fin 2 → ℝ) × ℤ :=
  (![(z.1 0 - S.t₀ i) / S.dt, (z.1 1 - S.u₁ i - z.1 0 * S.v₁ i) / S.J₁ i],
    ⌊(z.2 : ℝ) - MvPolynomial.eval z.1 (S.P₁ i) / N p K ^ (-L p)⌋ + ((s : ℕ) : ℤ))

variable {B₂ : ℕ} {h₂ ε₂ : ℝ} (Q : ChartW q B₂ (L q) (L q) h₂ ε₂ true k)

noncomputable def γ₃ (d : Fin Q.n) : Fin (W p K) := S.γ₁ (Q.γ d)

noncomputable def j₃ (d : Fin Q.n) : Fin (2 ^ (S.T₁ + Q.T)) := jcomp (S.j₁ (Q.γ d)) (Q.j d)

noncomputable def A₃ (d : Fin Q.n) : Set (ℕ × (Fin 5 → ℝ)) :=
  S.A₁ (Q.γ d) ∩ S.θ (Q.γ d) ⁻¹' Q.A d

noncomputable def C₃ (d : Fin Q.n) : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  S.C₁ (Q.γ d) ∩ S.Φ (Q.γ d) ⁻¹' Q.C d

noncomputable def J₃ (d : Fin Q.n) : ℝ := S.J₁ (Q.γ d) * Q.J d

noncomputable def u₃ (d : Fin Q.n) : ℝ :=
  S.u₁ (Q.γ d) + S.J₁ (Q.γ d) * Q.u d - S.J₁ (Q.γ d) * Q.v d * (S.t₀ (Q.γ d) / S.dt)

noncomputable def v₃ (d : Fin Q.n) : ℝ := S.v₁ (Q.γ d) + S.J₁ (Q.γ d) * Q.v d / S.dt

noncomputable def P₃ (d : Fin Q.n) : MvPolynomial (Fin 2) ℝ :=
  S.P₁ (Q.γ d) + C (N p K ^ (-r)) * bind₁ (S.G (Q.γ d)) (Q.P d)

open Classical in
noncomputable def Λ₃ (a : Fin (W p K)) (z : (Fin 2 → ℝ) × ℤ) : Finset (Fin Q.n) :=
  Finset.univ.filter (fun d => ∃ s₁ s₂ : Fin 2,
    Q.γ d ∈ S.Λ₁ a (coarseLab (N p K) (L p) b s₁ z) ∧ d ∈ Q.Λ (Q.γ d) (S.qlab (Q.γ d) s₂ z))

lemma mem_Λ₃ (a : Fin (W p K)) (z : (Fin 2 → ℝ) × ℤ) (d : Fin Q.n) :
    d ∈ S.Λ₃ Q a z ↔ ∃ s₁ s₂ : Fin 2,
      Q.γ d ∈ S.Λ₁ a (coarseLab (N p K) (L p) b s₁ z) ∧
        d ∈ Q.Λ (Q.γ d) (S.qlab (Q.γ d) s₂ z) := by
  classical
  unfold Λ₃
  simp

lemma eval_G (i : Fin (W q k)) (w : Fin 2 → ℝ) :
    (fun e => MvPolynomial.eval w (S.G i e)) =
      ![(w 0 - S.t₀ i) / S.dt, (w 1 - S.u₁ i - w 0 * S.v₁ i) / S.J₁ i] := by
  funext e
  fin_cases e
  · simp [G, div_eq_inv_mul]
  · simp [G, div_eq_inv_mul]
    left
    ring

lemma eval_P₃ (d : Fin Q.n) (w : Fin 2 → ℝ) :
    MvPolynomial.eval w (S.P₃ Q d) = MvPolynomial.eval w (S.P₁ (Q.γ d)) +
      N p K ^ (-r) * MvPolynomial.eval
        ![(w 0 - S.t₀ (Q.γ d)) / S.dt, (w 1 - S.u₁ (Q.γ d) - w 0 * S.v₁ (Q.γ d)) / S.J₁ (Q.γ d)]
        (Q.P d) := by
  rw [P₃, map_add, map_mul, eval_C, eval_bind₁_eq, S.eval_G]

end RefStep

end Submission.Obl.k4_scalar_true_terminal_lifting
