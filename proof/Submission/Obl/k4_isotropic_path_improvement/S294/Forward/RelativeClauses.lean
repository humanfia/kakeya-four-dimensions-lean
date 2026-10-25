-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.RelativeClauses, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.DenseChoice
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.NonPotentialPacket

/-!
# The pointwise clauses of the relative row packet

The relative row packet at a packet `b` below an ancestor `a` (signal: the test `R_a` of `a`)
asks, at every event `p` of its event set, for: a bounded packet base of `b`, a bounded
velocity, the jets of `R_a` along the line of `p` over the WHOLE block of `a`
(`|R_a| ≤ K δ_a`, `|∂₃R_a| ≤ K B`, `|∂₃²R_a| ≤ K B²/δ_a`), the floor `B/K ≤ |∂₃R_a|` at `p`,
and that `p` lies in the assignment and block of `b` and in the block of `a`.

`relative_pointwise`: all of these hold at every event of `b` in the prepared base, with `κ`
(the jets and the floor, from the chart of `a`), `1 + 2(κ² + (K_d + 2κ²))` (the base, as in
`NonPotentialPacket.unsheared_base_norm_le`) and `2 K_d` (the velocity, from the prepared base),
provided `a` contains the lines and events of `b`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294

namespace Forward

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open scoped ENNReal

noncomputable section

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ}

/-- The velocity of an event of the prepared base is bounded by `2 K_d`. -/
theorem norm_v_le_of_base (Q : PreparedAngularPath d k p m H u τ) {w : Fin (d.W k)}
    {q : (ℕ × (Fin 6 → ℝ)) × ℝ} (hq : q ∈ Q.base w) : ‖v q.1‖ ≤ 2 * d.K k := by
  have h0 := Q.velocity_bound w q hq 0
  have h1 := Q.velocity_bound w q hq 1
  calc ‖v q.1‖ ≤ |v q.1 0| + |v q.1 1| := Submission.Lib.K4ChartLifting.plane_norm_le _
    _ ≤ d.K k + d.K k := add_le_add h0 h1
    _ = 2 * d.K k := by ring

/-- **The pointwise clauses of the relative row packet** at an event of `b` in the prepared
base, for an ancestor `a` containing the lines and events of `b`. -/
theorem relative_pointwise {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ} (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (Q : PreparedAngularPath d k p m H u τ) (a b : Fin p.C) (hγ : p.γ a = p.γ b)
    (hFab : p.F b ⊆ p.F a) (hAab : p.A b ⊆ p.A a)
    {q : (ℕ × (Fin 6 → ℝ)) × ℝ} (hqb : q ∈ p.F b) (hqbase : q ∈ Q.base (p.γ b)) :
    q.1 ∈ p.A b ∧
      q.2 ∈ Icc ((p.j b : ℝ) * ((2 : ℝ) ^ p.T (p.lev b))⁻¹)
        (((p.j b : ℝ) + 1) * ((2 : ℝ) ^ p.T (p.lev b))⁻¹) ∧
      q.2 ∈ Icc ((p.j a : ℝ) * ((2 : ℝ) ^ p.T (p.lev a))⁻¹)
        ((p.j a : ℝ) * ((2 : ℝ) ^ p.T (p.lev a))⁻¹ + ((2 : ℝ) ^ p.T (p.lev a))⁻¹) ∧
      ‖Parent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) q‖ ≤
        1 + 2 * (p.κ ^ 2 + (d.K k + 2 * p.κ ^ 2)) ∧
      ‖v q.1‖ ≤ 2 * d.K k ∧
      (∀ t ∈ Icc ((p.j a : ℝ) * ((2 : ℝ) ^ p.T (p.lev a))⁻¹)
          ((p.j a : ℝ) * ((2 : ℝ) ^ p.T (p.lev a))⁻¹ + ((2 : ℝ) ^ p.T (p.lev a))⁻¹),
        |MvPolynomial.eval (x q.1 t) (p.R a)| ≤ p.κ * δ (d.N k) (p.r (p.lev a)) ∧
        |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv 3 (p.R a))| ≤ p.κ * d.B k (p.γ b) ∧
        |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.R a)))| ≤
          p.κ * d.B k (p.γ b) ^ 2 / δ (d.N k) (p.r (p.lev a))) ∧
      d.B k (p.γ b) / p.κ ≤ |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv 3 (p.R a))| := by
  rcases hp.2.2.2.2.2.2.2 b with
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, hFb, -⟩
  rcases hp.2.2.2.2.2.2.2 a with
    ⟨-, -, -, -, -, -, -, -, -, -, -, hfita, hFa, -⟩
  obtain ⟨-, hqA, hqt, -⟩ := hFb q hqb
  obtain ⟨-, hqAa, hqta, hfloor⟩ := hFa q (hFab hqb)
  have hblock : ∀ (jj : ℕ) (TT : ℕ), Icc ((jj : ℝ) / (2 : ℝ) ^ TT) (((jj : ℝ) + 1) / (2 : ℝ) ^ TT) =
      Icc ((jj : ℝ) * ((2 : ℝ) ^ TT)⁻¹) ((jj : ℝ) * ((2 : ℝ) ^ TT)⁻¹ + ((2 : ℝ) ^ TT)⁻¹) := by
    intro jj TT
    rw [div_eq_mul_inv, div_eq_mul_inv, add_mul, one_mul]
  have hblock' : ∀ (jj : ℕ) (TT : ℕ), Icc ((jj : ℝ) / (2 : ℝ) ^ TT) (((jj : ℝ) + 1) / (2 : ℝ) ^ TT) =
      Icc ((jj : ℝ) * ((2 : ℝ) ^ TT)⁻¹) (((jj : ℝ) + 1) * ((2 : ℝ) ^ TT)⁻¹) := by
    intro jj TT
    rw [div_eq_mul_inv, div_eq_mul_inv]
  refine ⟨hqA, ?_, ?_, Parent.NonPotentialPacket.unsheared_base_norm_le hd hp b hqb,
    norm_v_le_of_base Q hqbase, ?_, ?_⟩
  · have := hqt
    rwa [hblock'] at this
  · have := hqta
    rwa [hblock] at this
  · intro t ht
    have ht' : t ∈ Icc ((p.j a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
        (((p.j a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a)) := by rwa [hblock]
    obtain ⟨-, h1, h2, h3⟩ := (hfita q.1 (hAab hqA)).2.2 t ht'
    rw [← hγ]
    exact ⟨h1, h2, h3⟩
  · rw [← hγ]
    exact hfloor

end

end Forward

end Submission.Obl.k4_isotropic_path_improvement.S294
