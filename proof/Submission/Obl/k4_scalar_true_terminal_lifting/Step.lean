import Submission.Obl.k4_scalar_true_terminal_lifting.LiftBasic
import Submission.Obl.k4_scalar_true_terminal_lifting.Theta

/-!
# One index of an actual refinement

`RefStep p q r b k K` packages the parent chart at the original index `K` which serves the
`k`-th index of `q`, together with the trajectory maps `θ`, the selected-law transports and the
normalized weights, exactly as one index of `Refinement p q r b h` provides them.

`ChartW p B r b h ε isTrue k` packages the witnesses of `Chart p B r b h ε isTrue k`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The witnesses of a chart. -/
structure ChartW (p : Code) (B : ℕ) (r b h ε : ℝ) (isTrue : Bool) (k : ℕ) where
  T : ℕ
  n : ℕ
  γ : Fin n → Fin (W p k)
  j : Fin n → Fin (2 ^ T)
  A : Fin n → Set (ℕ × (Fin 5 → ℝ))
  C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)
  u : Fin n → ℝ
  v : Fin n → ℝ
  J : Fin n → ℝ
  P : Fin n → MvPolynomial (Fin 2) ℝ
  Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)
  hcd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ

theorem chart_iff_nonempty (p : Code) (B : ℕ) (r b h ε : ℝ) (isTrue : Bool) (k : ℕ) :
    Chart p B r b h ε isTrue k ↔ Nonempty (ChartW p B r b h ε isTrue k) := by
  constructor
  · rintro ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hcd⟩
    exact ⟨⟨T, n, γ, j, A, C, u, v, J, P, Λ, hcd⟩⟩
  · rintro ⟨⟨T, n, γ, j, A, C, u, v, J, P, Λ, hcd⟩⟩
    exact ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hcd⟩

/-- One index of an actual refinement. -/
structure RefStep (p q : Code) (r b : ℝ) (k K : ℕ) where
  B₁ : ℕ
  T₁ : ℕ
  h₁ : ℝ
  ε₁ : ℝ
  γ₁ : Fin (W q k) → Fin (W p K)
  j₁ : Fin (W q k) → Fin (2 ^ T₁)
  A₁ : Fin (W q k) → Set (ℕ × (Fin 5 → ℝ))
  C₁ : Fin (W q k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)
  u₁ : Fin (W q k) → ℝ
  v₁ : Fin (W q k) → ℝ
  J₁ : Fin (W q k) → ℝ
  P₁ : Fin (W q k) → MvPolynomial (Fin 2) ℝ
  Λ₁ : Fin (W p K) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k))
  θ : Fin (W q k) → (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ))
  hN : N q k = N p K
  hcd : ChartData p B₁ r b h₁ ε₁ false K T₁ (W q k) γ₁ j₁ A₁ C₁ u₁ v₁ J₁ P₁ Λ₁
  hθ : ∀ i, Measurable (θ i) ∧ (∀ l, (θ i l).1 = l.1) ∧
    (∀ l t, y (θ i l) ((t - ((j₁ i : ℕ) : ℝ) * ((2 : ℝ) ^ T₁)⁻¹) / ((2 : ℝ) ^ T₁)⁻¹) =
      (y l t - u₁ i - t * v₁ i) / J₁ i) ∧
    (∀ l t, x (θ i l) ((t - ((j₁ i : ℕ) : ℝ) * ((2 : ℝ) ^ T₁)⁻¹) / ((2 : ℝ) ^ T₁)⁻¹) =
      (x l t - MvPolynomial.eval ![t, y l t] (P₁ i)) / N p K ^ (-r)) ∧
    ν q k i = (ν p K (γ₁ i) (A₁ i))⁻¹ •
      Measure.map (θ i) ((ν p K (γ₁ i)).restrict (A₁ i)) ∧
    mu q k i = (ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹) * ν p K (γ₁ i) (A₁ i))⁻¹ •
      Measure.map (fun z => (θ i z.1, (z.2 - ((j₁ i : ℕ) : ℝ) * ((2 : ℝ) ^ T₁)⁻¹) /
        ((2 : ℝ) ^ T₁)⁻¹)) ((mu p K (γ₁ i)).restrict (C₁ i))
  hZ : 0 < (∑ i : Fin (W q k), ω p K (γ₁ i) * ((2 : ℝ) ^ T₁)⁻¹ *
      (ν p K (γ₁ i) (A₁ i)).toReal) ∧
    ∀ i, ω q k i = (ω p K (γ₁ i) * ((2 : ℝ) ^ T₁)⁻¹ * (ν p K (γ₁ i) (A₁ i)).toReal) /
      (∑ i : Fin (W q k), ω p K (γ₁ i) * ((2 : ℝ) ^ T₁)⁻¹ * (ν p K (γ₁ i) (A₁ i)).toReal)

namespace RefStep

variable {p q : Code} {r b : ℝ} {k K : ℕ} (S : RefStep p q r b k K)

/-- Relative length of the parent cells. -/
noncomputable def dt : ℝ := ((2 : ℝ) ^ S.T₁)⁻¹

/-- Left end of the parent cell of the `i`-th q-world. -/
noncomputable def t₀ (i : Fin (W q k)) : ℝ := ((S.j₁ i : ℕ) : ℝ) * S.dt

/-- The normalizing map of incidences of the `i`-th q-world. -/
noncomputable def Φ (i : Fin (W q k)) : (ℕ × (Fin 5 → ℝ)) × ℝ → (ℕ × (Fin 5 → ℝ)) × ℝ :=
  fun z => (S.θ i z.1, (z.2 - S.t₀ i) / S.dt)

/-- The normalizing constant of the q-weights. -/
noncomputable def Z : ℝ :=
  ∑ i : Fin (W q k), ω p K (S.γ₁ i) * S.dt * (ν p K (S.γ₁ i) (S.A₁ i)).toReal

lemma dt_pos : 0 < S.dt := by
  unfold dt
  positivity

lemma t₀_nonneg (i : Fin (W q k)) : 0 ≤ S.t₀ i := by
  unfold t₀
  exact mul_nonneg (Nat.cast_nonneg _) S.dt_pos.le

lemma t₀_le_one (i : Fin (W q k)) : S.t₀ i ≤ 1 := by
  unfold t₀ dt
  have h1 : ((S.j₁ i : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ S.T₁ := by
    have := (S.j₁ i).isLt
    exact_mod_cast this
  have h2 : (0 : ℝ) < 2 ^ S.T₁ := by positivity
  rw [← div_eq_mul_inv, div_le_one h2]
  linarith

lemma t₀_div_dt (i : Fin (W q k)) : S.t₀ i / S.dt = ((S.j₁ i : ℕ) : ℝ) := by
  unfold t₀
  field_simp [S.dt_pos.ne']

lemma measurable_θ (i : Fin (W q k)) : Measurable (S.θ i) := (S.hθ i).1

lemma θ_fst (i : Fin (W q k)) (l : ℕ × (Fin 5 → ℝ)) : (S.θ i l).1 = l.1 := (S.hθ i).2.1 l

lemma θ_eq (i : Fin (W q k)) (l : ℕ × (Fin 5 → ℝ)) : S.θ i l = (l.1, (S.θ i l).2) :=
  Prod.ext (S.θ_fst i l) rfl

lemma hy (i : Fin (W q k)) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) :
    y (S.θ i l) ((t - S.t₀ i) / S.dt) = (y l t - S.u₁ i - t * S.v₁ i) / S.J₁ i :=
  (S.hθ i).2.2.1 l t

lemma hx (i : Fin (W q k)) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) :
    x (S.θ i l) ((t - S.t₀ i) / S.dt) =
      (x l t - MvPolynomial.eval ![t, y l t] (S.P₁ i)) / N p K ^ (-r) :=
  (S.hθ i).2.2.2.1 l t

lemma measurable_Φ (i : Fin (W q k)) : Measurable (S.Φ i) :=
  ((S.measurable_θ i).comp measurable_fst).prodMk
    ((measurable_snd.sub_const _).div_const _)

lemma mu_q_eq (i : Fin (W q k)) :
    mu q k i = (ENNReal.ofReal S.dt * ν p K (S.γ₁ i) (S.A₁ i))⁻¹ •
      Measure.map (S.Φ i) ((mu p K (S.γ₁ i)).restrict (S.C₁ i)) :=
  (S.hθ i).2.2.2.2.2

lemma Z_pos : 0 < S.Z := S.hZ.1

lemma ω_q_eq (i : Fin (W q k)) :
    ω q k i = ω p K (S.γ₁ i) * S.dt * (ν p K (S.γ₁ i) (S.A₁ i)).toReal / S.Z :=
  S.hZ.2 i

end RefStep

end Submission.Obl.k4_scalar_true_terminal_lifting
