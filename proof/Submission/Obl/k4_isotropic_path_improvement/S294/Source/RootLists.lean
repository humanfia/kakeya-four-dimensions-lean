-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RootLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PostStateAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRowLists

/-!
# The base-only row lists of the post-state assembly (session x1082)

`post_state_assembly` asks, at every child `b` of an active ancestor `a = par^[c] b`, for the
base-only lists of the scaled ancestor rows `(aA/q) row_a(code_a x)` over `Src_a ∩ F_b`, where
`Src_a` is the regularity source of `a`. `lists_of_lipschitz` derives them from rows Lipschitz on
`Src_a` in the ancestor's clock coordinates (the regularity stage's output) by
`Forward/AncestorRowLists.ancestor_row_lists`, with the middle packet `b0 = par^[lev b - mid] b`
at a registered depth `mid` of the core source.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath)
open scoped ENNReal

noncomputable section

section Lists

variable {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ}
    {K : ℝ} {e R : ℕ}

/-- **Lists from Lipschitz rows.** -/
theorem lists_of_lipschitz (C : BroadMultiscaleCoreSource d k p original n depth K e R)
    {Tt : Type*} {m : ℕ} {H₀ : Fin (d.W k) → Set Event} {u : Tt → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H₀ u τ) (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, original w ⊆ d.E k w) (hHbase : ∀ w, original w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K) (hpower : d.N k ^ (τ + ε) ≤ K)
    (hκK : 3 * p.κ ≤ K) {D J : ℕ} (hD : 5186 ≤ D) (hjets : Analytic.DenseJetBound D J)
    (c : ℕ) (b : Fin p.C) (hc : c ≤ p.lev b) (j : Fin n) (hmidb : depth j ≤ p.lev b)
    (hmida : p.lev b - c ≤ depth j)
    (hr : 0 ≤ p.r (depth j)) (hrL : p.r (depth j) ≤ d.L)
    (hwidth : δ (d.N k) (p.r (depth j)) ≤ δ (d.N k) (p.r (p.lev (p.par^[c] b))))
    (Src : Set Event) (hSrc : Src ⊆ C.current (p.γ (p.par^[c] b)) ∩ p.F (p.par^[c] b))
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (graphMesh : ℝ) {Krows Lp ρ θ aA q : ℝ}
    (hLp : 0 ≤ Lp) (hθ : 0 < θ) (haA : 0 < aA) (hq : 0 < q)
    (hreg : ∀ x ∈ Src, ∀ y ∈ Src,
      ‖row (ancCode (d.N k) p (p.par^[c] b) graphMesh x) -
        row (ancCode (d.N k) p (p.par^[c] b) graphMesh y)‖ ≤
      Lp * (‖clockParentCoordinates p (p.par^[c] b)
          (Parent.SignalGraph.ancestorSignal (d.N k) p (p.par^[c] b)) x -
        clockParentCoordinates p (p.par^[c] b)
          (Parent.SignalGraph.ancestorSignal (d.N k) p (p.par^[c] b)) y‖ + ρ))
    (hsmall : ((aA / q) * Lp) * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
          ((2 : ℝ) ^ p.T (p.lev (p.par^[c] b)))⁻¹) * (2 * θ) +
        (2 * (K ^ 14 * (K ^ 6)⁻¹ * (δ (d.N k) (p.r (depth j)) /
          δ (d.N k) (p.r (p.lev (p.par^[c] b))))) +
          ((K ^ (3 * R + 58 + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
            (K ^ R * ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
              ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
                ((2 : ℝ) ^ p.T (p.lev (p.par^[p.lev b - depth j] b)))⁻¹) * (6 * θ))))) +
        ρ) ≤ (aA / q) * θ)
    (hcount : (K ^ 10 * (2 * K ^ (3 * R + 18))) * 9 ^ 3 ≤ Krows) :
    ∀ c' : Fin 3 → ℝ, ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ Krows ∧
      ∀ x ∈ Src ∩ p.F b, (∀ i : Fin 3, |unshearedPacketBase p b x i - c' i| ≤ θ) →
        (fun i : Fin 3 => ⌊(aA / q) * row (ancCode (d.N k) p (p.par^[c] b) graphMesh x) i /
          ((aA / q) * θ)⌋) ∈ Fc := by
  have hscale : 0 < aA / q := div_pos haA hq
  -- the middle packet and its ancestry
  set a := p.par^[c] b with ha
  set b0 := p.par^[p.lev b - depth j] b with hb0def
  obtain ⟨hlb0, hγb0, hFb0⟩ := Broad.iterate_par_spec hp.toOriginal (p.lev b - depth j) b
    (show p.lev b - depth j ≤ p.lev b by omega)
  change p.lev b0 = p.lev b - (p.lev b - depth j) at hlb0
  change p.γ b0 = p.γ b at hγb0
  change p.F b ⊆ p.F b0 at hFb0
  have hlev0 : p.lev b0 = depth j := by omega
  -- a is the ancestor of b0 at the remaining distance
  have hcomp : a = p.par^[depth j - (p.lev b - c)] b0 := by
    rw [ha, hb0def, ← Function.iterate_add_apply]
    congr 1
    omega
  obtain ⟨hla, hγa, hFa⟩ := Broad.iterate_par_spec hp.toOriginal (depth j - (p.lev b - c)) b0
    (show depth j - (p.lev b - c) ≤ p.lev b0 by omega)
  rw [← hcomp] at hla hγa hFa
  change p.γ a = p.γ b0 at hγa
  change p.F b0 ⊆ p.F a at hFa
  intro c'
  obtain ⟨Fc, hFc, hmem⟩ := Parent.SignalGraph.ancestor_row_lists C Q hpure hd hp hHE hHbase hK hmax
    hpower hκK hD hjets a b j hr hrL b0 hlev0 hγa.symm hwidth hFa hFb0 (Src ∩ p.F b)
    (fun x hx => ⟨(hSrc hx.1).1, hx.2⟩) (ancCode (d.N k) p a graphMesh)
    (fun cd => (aA / q) • row cd) (mul_nonneg hscale.le hLp) hθ.le (mul_pos hscale hθ)
    (fun x hx y hy => by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hscale, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hreg x hx.1 y hy.1) hscale.le)
    hsmall c'
  refine ⟨Fc, hFc.trans hcount, fun x hx hbox => ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul] using hmem x hx hbox

/-- **The list budget from four quarter budgets.** -/
theorem lists_hsmall_of_quarters {Lp ρ θ aA q hba twoK8ratio Bterm hbm : ℝ}
    (hscale : 0 ≤ aA / q)
    (h1 : Lp * (hba * (2 * θ)) ≤ θ / 4) (h2 : Lp * twoK8ratio ≤ θ / 4)
    (h3 : Lp * (Bterm * (hbm * (6 * θ))) ≤ θ / 4) (h4 : Lp * ρ ≤ θ / 4) :
    ((aA / q) * Lp) * (hba * (2 * θ) + (twoK8ratio + Bterm * (hbm * (6 * θ))) + ρ) ≤
      (aA / q) * θ := by
  have hsum : Lp * (hba * (2 * θ) + (twoK8ratio + Bterm * (hbm * (6 * θ))) + ρ) ≤ θ := by
    have := add_le_add (add_le_add h1 (add_le_add h2 h3)) h4
    nlinarith [this]
  calc ((aA / q) * Lp) * (hba * (2 * θ) + (twoK8ratio + Bterm * (hbm * (6 * θ))) + ρ)
      = (aA / q) * (Lp * (hba * (2 * θ) + (twoK8ratio + Bterm * (hbm * (6 * θ))) + ρ)) := by ring
    _ ≤ (aA / q) * θ := mul_le_mul_of_nonneg_left hsum hscale

end Lists

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
