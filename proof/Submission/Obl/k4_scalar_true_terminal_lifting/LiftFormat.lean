import Submission.Obl.k4_scalar_true_terminal_lifting.LiftDefs

/-!
# Lifted chart: sets and formats

Measurability, disjointness, inclusion in incidence sets and cells, and the polynomial sign
formats of the lifted assignments and incidences (pullbacks of the q-chart formats through
the polynomial maps of `theta_poly`, `theta_poly6`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

namespace RefStep

variable {p q : Code} {r b : ℝ} {k K : ℕ} (S : RefStep p q r b k K)
variable {B₂ : ℕ} {h₂ ε₂ : ℝ} (Q : ChartW q B₂ (L q) (L q) h₂ ε₂ true k)

lemma lift_meas (d : Fin Q.n) : MeasurableSet (S.A₃ Q d) ∧ MeasurableSet (S.C₃ Q d) := by
  have h1 := S.hcd
  unfold ChartData at h1
  obtain ⟨-, -, h13, -⟩ := h1
  have h2 := Q.hcd
  unfold ChartData at h2
  obtain ⟨-, -, h23, -⟩ := h2
  exact ⟨(h13 (Q.γ d)).1.inter (S.measurable_θ (Q.γ d) (h23 d).1),
    (h13 (Q.γ d)).2.inter (S.measurable_Φ (Q.γ d) (h23 d).2)⟩

lemma lift_disj : ∀ d d' : Fin Q.n, d ≠ d' → S.γ₃ Q d = S.γ₃ Q d' → S.j₃ Q d = S.j₃ Q d' →
    Disjoint (S.A₃ Q d) (S.A₃ Q d') := by
  intro d d' hdd' hγ hj
  have h1 := S.hcd
  unfold ChartData at h1
  obtain ⟨-, -, -, h14, -⟩ := h1
  have h2 := Q.hcd
  unfold ChartData at h2
  obtain ⟨-, -, -, h24, -⟩ := h2
  have hj' : jcomp (S.j₁ (Q.γ d)) (Q.j d) = jcomp (S.j₁ (Q.γ d')) (Q.j d') := hj
  obtain ⟨hj1, hj2⟩ := jcomp_inj hj'
  by_cases hγq : Q.γ d = Q.γ d'
  · -- same q-world: the q-assignments are disjoint, pull back through `θ`
    have hdisj := h24 d d' hdd' hγq hj2
    rw [Set.disjoint_left]
    intro l hl hl'
    have hA : S.θ (Q.γ d) l ∈ Q.A d := hl.2
    have hA' : S.θ (Q.γ d') l ∈ Q.A d' := hl'.2
    rw [← hγq] at hA'
    exact Set.disjoint_left.1 hdisj hA hA'
  · -- distinct q-worlds in the same parent world and cell: the parent assignments are disjoint
    have hγ' : S.γ₁ (Q.γ d) = S.γ₁ (Q.γ d') := hγ
    exact (h14 (Q.γ d) (Q.γ d') hγq hγ' hj1).mono Set.inter_subset_left Set.inter_subset_left

lemma lift_sub (d : Fin Q.n) :
    S.C₃ Q d ⊆ E p K (S.γ₃ Q d) ∩ (S.A₃ Q d ×ˢ I (S.T₁ + Q.T) (S.j₃ Q d)) := by
  have h1 := S.hcd
  unfold ChartData at h1
  obtain ⟨-, -, -, -, h15, -⟩ := h1
  have h2 := Q.hcd
  unfold ChartData at h2
  obtain ⟨-, -, -, -, h25, -⟩ := h2
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨hE, hA, -⟩ := h15 (Q.γ d) hw1
  obtain ⟨-, hQA, hQI⟩ := h25 d hw2
  refine ⟨hE, ⟨hA, hQA⟩, ?_⟩
  exact (mem_I_jcomp (S.j₁ (Q.γ d)) (Q.j d) w.2).2 hQI

/-- `R ^ m + R ^ n ≤ R ^ (2 n + 2 m + 9)` for `R ≥ 2`. -/
lemma fmt_rpow_add_le {R : ℝ} (hR : 2 ≤ R) (m n : ℕ) :
    R ^ ((m : ℕ) : ℝ) + R ^ ((n : ℕ) : ℝ) ≤ R ^ (((2 * n + 2 * m + 9 : ℕ)) : ℝ) := by
  rw [Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
  have h1 : (1 : ℝ) ≤ R := by linarith
  have hA : R ^ m ≤ R ^ (m + n) := pow_le_pow_right₀ h1 (by omega)
  have hB : R ^ n ≤ R ^ (m + n) := pow_le_pow_right₀ h1 (by omega)
  have hC : R ^ (m + n + 1) ≤ R ^ (2 * n + 2 * m + 9) := pow_le_pow_right₀ h1 (by omega)
  have hD : R ^ (m + n + 1) = R ^ (m + n) * R := pow_succ _ _
  have hE : 0 ≤ R ^ (m + n) := by positivity
  nlinarith

lemma lift_format5 (hN : 2 ≤ N p K) (d : Fin Q.n) (z : ℕ) :
    Format 5 (N p K ^ (((2 * B₂ + 2 * S.B₁ + 9 : ℕ)) : ℝ)) (2 * B₂ + 2 * S.B₁ + 9)
      {a | (z, a) ∈ S.A₃ Q d} := by
  have h1 := S.hcd
  unfold ChartData at h1
  obtain ⟨-, -, -, -, -, h16, -⟩ := h1
  obtain ⟨-, -, -, -, -, c6, -, -, c9, -⟩ := h16 (Q.γ d)
  have h2 := Q.hcd
  unfold ChartData at h2
  obtain ⟨-, -, -, -, -, h26, -⟩ := h2
  obtain ⟨-, -, -, -, -, -, -, -, e9, -⟩ := h26 d
  -- `θ` acts on coefficients by polynomials of degree `≤ 2`
  obtain ⟨Q5, hQdeg, hQ⟩ := theta_poly (S.θ (Q.γ d)) (S.t₀ (Q.γ d)) S.dt (S.u₁ (Q.γ d))
    (S.v₁ (Q.γ d)) (S.J₁ (Q.γ d)) (N p K ^ (-r)) (S.P₁ (Q.γ d)) S.dt_pos.ne' c6
    (S.hy (Q.γ d)) (S.hx (Q.γ d))
  have hNq : N q k = N p K := S.hN
  have hR1 : (1 : ℝ) ≤ N q k ^ (B₂ : ℝ) := by
    rw [hNq]; exact Real.one_le_rpow (by linarith) (Nat.cast_nonneg _)
  have F1 := Format.mono (c9 z) le_rfl (show S.B₁ ≤ 2 * B₂ + 2 * S.B₁ + 9 by omega)
  have F2 := Format.mono (Format.preimage (e9 z) hR1 Q5 hQdeg) le_rfl
    (show B₂ * 2 ≤ 2 * B₂ + 2 * S.B₁ + 9 by omega)
  have F3 := Format.inter F1 F2
  rw [hNq] at F3
  have F4 := Format.mono F3 (fmt_rpow_add_le hN S.B₁ B₂) le_rfl
  refine Format.congr F4 ?_
  ext a
  have hθa : S.θ (Q.γ d) (z, a) = (z, fun e => eval a (Q5 e)) :=
    Prod.ext (S.θ_fst (Q.γ d) (z, a)) (funext fun e => hQ (z, a) e)
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, A₃, Set.mem_preimage, hθa]

lemma lift_format6 (hN : 2 ≤ N p K) (d : Fin Q.n) (z : ℕ) :
    Format 6 (N p K ^ (((2 * B₂ + 2 * S.B₁ + 9 : ℕ)) : ℝ)) (2 * B₂ + 2 * S.B₁ + 9)
      {a | ((z, fun e : Fin 5 => a e.castSucc), a 5) ∈ S.C₃ Q d} := by
  have h1 := S.hcd
  unfold ChartData at h1
  obtain ⟨-, -, -, -, -, h16, -⟩ := h1
  obtain ⟨-, -, -, -, -, c6, -, -, -, c10, -⟩ := h16 (Q.γ d)
  have h2 := Q.hcd
  unfold ChartData at h2
  obtain ⟨-, -, -, -, -, h26, -⟩ := h2
  obtain ⟨-, -, -, -, -, -, -, -, -, e10, -⟩ := h26 d
  -- `Φ` acts on (coefficients, time) by polynomials of degree `≤ 2`
  obtain ⟨Ψ, hΨdeg, hΨ⟩ := theta_poly6 (S.θ (Q.γ d)) (S.t₀ (Q.γ d)) S.dt (S.u₁ (Q.γ d))
    (S.v₁ (Q.γ d)) (S.J₁ (Q.γ d)) (N p K ^ (-r)) (S.P₁ (Q.γ d)) S.dt_pos.ne' c6
    (S.hy (Q.γ d)) (S.hx (Q.γ d))
  have hNq : N q k = N p K := S.hN
  have hR1 : (1 : ℝ) ≤ N q k ^ (B₂ : ℝ) := by
    rw [hNq]; exact Real.one_le_rpow (by linarith) (Nat.cast_nonneg _)
  have F1 := Format.mono (c10 z) le_rfl (show S.B₁ ≤ 2 * B₂ + 2 * S.B₁ + 9 by omega)
  have F2 := Format.mono (Format.preimage (e10 z) hR1 Ψ hΨdeg) le_rfl
    (show B₂ * 2 ≤ 2 * B₂ + 2 * S.B₁ + 9 by omega)
  have F3 := Format.inter F1 F2
  rw [hNq] at F3
  have F4 := Format.mono F3 (fmt_rpow_add_le hN S.B₁ B₂) le_rfl
  refine Format.congr F4 ?_
  ext a
  obtain ⟨hΨ1, hΨ2⟩ := hΨ z a
  have hθa : S.θ (Q.γ d) (z, fun e : Fin 5 => a e.castSucc) =
      (z, fun e : Fin 5 => eval a (Ψ e.castSucc)) :=
    Prod.ext (S.θ_fst (Q.γ d) _) hΨ1.symm
  have hΦa : S.Φ (Q.γ d) ((z, fun e : Fin 5 => a e.castSucc), a 5) =
      ((z, fun e : Fin 5 => eval a (Ψ e.castSucc)), eval a (Ψ 5)) := by
    rw [hΨ2, ← hθa]
    rfl
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, C₃, Set.mem_preimage, hΦa]

end RefStep

end Submission.Obl.k4_scalar_true_terminal_lifting
