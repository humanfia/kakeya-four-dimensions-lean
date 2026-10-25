-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.CoreOrchestration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1080,
-- branch x1080, commit 5a0a478a0, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/CoreOrchestration.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- o265 from the core relative source certificate, budgets discharged (x1078, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Budgets

/-!
# The core certificate of the relative source

`RelCore` is `RelPPP` without its size budgets: a packet `b` with room `r_b + L/4 ≤ L`, an
ancestor block `(jA, TA)` of it, a depth `rA ∈ [0, r_b]`, a frame centre `cA` with
`‖cA‖ ≤ N^Mr`, a parent quadratic `P0` (degree `≤ 2`, coefficients `≤ N^Mr`), and o288's
`PhysicalPotentialPacket` for the one-packet unscaled virtual instance. The budgets of `RelPPP`
follow from the path (`rel_budgets`) at `M' = 2⌈2L⌉ + Mp + 2Mr + 2Mb + 16`, `Mb` the exponent
of the sequence's family bounds.

`relSource_of_core`: `RelCoreSourceAssertion → RelSourceAssertion`;
`staged_of_rel_core_source`: with o288, o265's frozen statement.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The core certificate a relative source returns at one late sample. -/
def RelCore (q : ℕ) (precision loss : ℝ) (N L d₁ gain : ℝ) (Mr : ℕ) (κ : ℝ) (W : ℕ)
    (ν : Fin W → Measure Ln) (B : Fin W → ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ) (c u : Fin C → P2)
    (A : Fin C → Set Ln) (F : Fin C → Set Ev) (H : Fin W → Set Ev) : Prop :=
  ∃ (b : Fin C) (rA : ℝ) (jA TA : ℕ) (cA : P2) (A_A : Set Ln) (H₀ : Set Ev) (P0 : Po),
    0 ≤ rA ∧ rA ≤ r (lev b) ∧ r (lev b) + L/4 ≤ L ∧
    TA ≤ T (lev b) ∧ jA * 2 ^ (T (lev b) - TA) ≤ j b ∧
    j b < (jA + 1) * 2 ^ (T (lev b) - TA) ∧
    A b ⊆ A_A ∧ ν (γ b) A_A ≠ 0 ∧ MeasurableSet H₀ ∧ H₀ ⊆ H (γ b) ∧
    P0.totalDegree ≤ 2 ∧ (∀ e, |P0.coeff e| ≤ N ^ Mr) ∧ ‖cA‖ ≤ N ^ Mr ∧
    Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket q precision loss
      N L d₁ gain (2 * κ)
      (tanPrior (rFrame N rA jA TA cA (B (γ b))) 0 (ν (γ b)) A_A) 1
      (r (lev b) - rA) (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA))
      (((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)) (u b) P0
      (tanLine (rFrame N rA jA TA cA (B (γ b))) 0 '' A b)
      (tanEvent (rFrame N rA jA TA cA (B (γ b))) 0 '' F b)
      (tanEvent (rFrame N rA jA TA cA (B (γ b))) 0 '' H₀)

/-- The per-grid contract of the core relative source. -/
def RelCoreSourceDs (q : ℕ) (precision loss : ℝ) (cc J D : ℕ) (d₁ κ₁ S η ρ : ℝ) (m : ℕ)
    (s : ℕ → ℝ) (gain δ₀ u0 : ℝ) : Prop :=
  ∀ N K L d W ω ν E P B f g G, pb N K L d S η W ω ν E P B f g G →
    (∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - d₁*r| ≤ δ₀*L) →
    ∀ Mp Dp : ℕ, ∃ Mr M₀ D₀ : ℕ,
    ∀ Mi Di : ℕ, M₀ ≤ Mi → D₀ ≤ Di → ∀ τ : ℝ, 0 < τ → ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    ∀ r T nw κ C lev par γ j c u Q R A F lst,
      path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ
        r T nw κ C lev par γ j c u Q R A F lst →
      ∀ H : Fin (W k) → Set Ev,
        (∀ w, MeasurableSet (H w) ∧ H w ⊆ {p | ∃ b : Fin C, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b}) →
        ENNReal.ofReal (κ⁻¹/2) ≤
          ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) →
        ((wi (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mi Di τ ∨
            cd cc J D (N k) L (W k) (ν k) (B k) Mi d₁ ρ gain τ r T C lev γ j A H) ∨
          narrow (N k) L (W k) (ω k) (ν k) (E k) (B k) m s r T nw gain u0 κ M₀ D₀ α
            C lev γ j A F H) ∨
        RelCore q precision loss (N k) L d₁ gain Mr κ (W k) (ν k) (B k) r T C lev γ j
          c u A F H

/-- The contract of the core relative source, in the order of `RelSourceAssertion`. -/
def RelCoreSourceAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ q : ℕ, 2 ≤ q ∧ ∀ precision : ℝ, 1 ≤ precision → ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
    ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 →
      ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
        grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
          RelCoreSourceDs q precision loss cc J D d₁ κ₁ S η ρ m s gain δ₀ u0

/-- The core certificate with the packet charts and plain size bounds gives `RelPPP`. -/
theorem relPPP_of_core (q : ℕ) (precision loss N L d₁ gain : ℝ) (Mp Dp Mr Mb E : ℕ) (κ : ℝ)
    (W : ℕ) (ν : Fin W → Measure Ln) (B : Fin W → ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ) (c u : Fin C → P2)
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → Po) (A : Fin C → Set Ln)
    (F : Fin C → Set Ev) (H : Fin W → Set Ev) (hN : 2 ≤ N) (hLE : L ≤ E)
    (hch : ∀ b, j b < 2 ^ T (lev b) ∧ ∃ (Ev' : Set Ev) (ex : Prop),
      Split.ch N Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) Ev' (c b) (u b) (Q b)
        (R b) (A b) (F b) ex)
    (hTE : ∀ b, (2:ℝ) ^ T (lev b) ≤ N ^ E)
    (hBb : ∀ w, 0 < B w ∧ B w ≤ N ^ Mb ∧ (B w)⁻¹ ≤ N ^ Mb)
    (hcore : RelCore q precision loss N L d₁ gain Mr κ W ν B r T C lev γ j c u A F H) :
    RelPPP q precision loss N L d₁ gain Mp (2*E + Mp + 2*Mr + 2*Mb + 16) κ W ν B r T C lev γ j
      c u R A F H := by
  obtain ⟨b, rA, jA, TA, cA, A_A, H₀, P0, hrA, hrArb, hroom, hTT, hj, hjup, hAbA, hA0, hH₀m,
    hH₀H, hP0deg, hP0c, hcA, hpp⟩ := hcore
  obtain ⟨hjb, Ev', ex, hchb⟩ := hch b
  obtain ⟨hB0, hBle, hBinv⟩ := hBb (γ b)
  have hjA : jA < 2 ^ TA := by
    have h2 : 2 ^ T (lev b) = 2 ^ TA * 2 ^ (T (lev b) - TA) := by
      rw [← pow_add, Nat.add_sub_cancel' hTT]
    have hlt : jA * 2 ^ (T (lev b) - TA) < 2 ^ TA * 2 ^ (T (lev b) - TA) :=
      lt_of_le_of_lt hj (h2 ▸ hjb)
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hrAE : rA ≤ (E:ℝ) := by linarith
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := rel_budgets N hN Mp Dp Mr Mb E κ (T (lev b)) (j b)
    (r (lev b)) (B (γ b)) Ev' (c b) (u b) (Q b) (R b) (A b) (F b) ex hchb hB0 hBle hBinv (hTE b)
    rA hrA hrAE jA TA hTT hjA cA hcA
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hP0c' : ∀ e, |P0.coeff e| ≤ N ^ (2*E + Mp + 2*Mr + 2*Mb + 16) := fun e =>
    (hP0c e).trans (pow_le_pow_right₀ hN1 (by omega))
  exact ⟨b, rA, jA, TA, cA, A_A, H₀, P0, hrA, hrArb, hroom, hTT, hj, hjup, hAbA, hA0, hH₀m, hH₀H,
    hP0deg, hP0c', h1, h2, h3, h4, h5, h6, h7, hpp⟩

/-- The core relative source gives the relative source contract. -/
theorem relSource_of_core (h : RelCoreSourceAssertion) : RelSourceAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨q, hq2, h⟩ := h hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  refine ⟨q, hq2, fun precision hprec D₀ => ?_⟩
  obtain ⟨D, hD, h⟩ := h precision hprec D₀
  refine ⟨D, hD, fun J hJ hjet loss hloss hloss1 e0 he0 => ?_⟩
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgain, hds⟩ := h J hJ hjet loss hloss hloss1 e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgain, ?_⟩
  obtain ⟨-, -, hgain8, hδ₀0, -, -, -, hs, -, hδ₀g, -, -, -, -⟩ := hgrid
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  obtain ⟨Mr, M₀, D₀', hds⟩ := hds N K L d W ω ν E P B f g G hpb hprof Mp Dp
  have hpb' := hpb
  obtain ⟨hN2, -, -, hL, -, -, -, -, hfam, -⟩ := hpb'
  beta_reduce at hfam
  obtain ⟨Mpb, Dpb, hMD⟩ := hfam
  refine ⟨2 * ⌈2 * L⌉₊ + Mp + 2 * Mr + 2 * Mpb + 16, M₀, D₀', ?_⟩
  intro Mi Di hMi hDi τ hτ α hα hα1
  obtain ⟨σ, hσ, k₀, hds⟩ := hds Mi Di hMi hDi τ hτ α hα hα1
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass
  rcases hds k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with hex | hcore
  · exact Or.inl hex
  · right
    obtain ⟨-, -, -, -, hlev, -, -, hpk⟩ := hpath
    have hN1 : (1:ℝ) ≤ N k := le_trans (by norm_num) (hN2 k)
    have hLE : L ≤ (⌈2 * L⌉₊ : ℝ) := by
      have := Nat.le_ceil (2 * L); linarith
    have hTE : ∀ b, (2:ℝ) ^ T (lev b) ≤ N k ^ ⌈2 * L⌉₊ := by
      intro b
      have hb := (hpk b).1
      obtain ⟨-, -, -, hT2, -⟩ := hlev (lev b) hb
      refine hT2.trans ?_
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have hsb : s (lev b) ≤ 1 := by
        rw [hs]
        have hm : (0:ℝ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hb)
        rw [div_le_one hm]
        exact_mod_cast hb
      have hs0 : 0 ≤ s (lev b) := by rw [hs]; positivity
      have hκs : κ₁ * s (lev b) ≤ 1 := by nlinarith
      have hδ1 : δ₀ ≤ 1 := by linarith
      have := Nat.le_ceil (2 * L)
      nlinarith
    exact relPPP_of_core q precision loss (N k) L d₁ gain Mp Dp Mr Mpb ⌈2 * L⌉₊ κ (W k) (ν k)
      (B k) r T C lev γ j c u Q R A F H (hN2 k) hLE
      (fun b => ⟨(hpk b).2.1, _, _, (hpk b).2.2⟩) hTE
      (fun w => ⟨((hMD k).2.2.2.1 w).2.1, ((hMD k).2.2.2.1 w).2.2.1,
        ((hMD k).2.2.2.1 w).2.2.2.1⟩) hcore

/-- The core relative source and the accepted o288 prove o265's frozen statement. -/
theorem staged_of_rel_core_source (h : RelCoreSourceAssertion)
    (hcomp : Submission.Obl.k4_physical_parent_potential_candidates.CompletionAssertion) :
    StagedWeakAssertion :=
  staged_of_rel_source (relSource_of_core h) hcomp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
