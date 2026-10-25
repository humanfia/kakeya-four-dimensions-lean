-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.RowCore, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1080,
-- branch x1080, commit 5a0a478a0, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/RowCore.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- The relative row core contract: o295 and x1078's `RelCore` (x1080, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.RelativeSource
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.CoreOrchestration

/-!
# The relative row core

`RelRowCore` is x1078's `RelCore` with o288's potential packet replaced by o295's row clauses in
ORIGINAL units (`RelativeRowPacket`, signal = the ancestor's own test `RA`), and with the
coefficient bound asked of `RA` itself (original units) instead of its normalized test.
`relCore_of_rowCore`: one late sample, through `relRowPacket_of_relative`, o295 and
`budget_normTest`. `relCoreSource_of_rowCore : RelRowCoreSourceAssertion → RelCoreSourceAssertion`
(row degree `M` first, then every `Ep`: o294's order) and `staged_of_rel_row_core_source` (with the
accepted o288: o265's frozen statement).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The core certificate of a broad relative ROW source at one late sample. -/
def RelRowCore (M Ep : ℕ) (precision loss : ℝ) (N L d₁ gain : ℝ) (Mr : ℕ) (κ : ℝ) (W : ℕ)
    (ν : Fin W → Measure Ln) (B : Fin W → ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ) (c u : Fin C → P2)
    (A : Fin C → Set Ln) (F : Fin C → Set Ev) (H : Fin W → Set Ev) : Prop :=
  ∃ (b : Fin C) (rA : ℝ) (jA TA : ℕ) (cA : P2) (A_A : Set Ln) (H₀ : Set Ev) (RA : Po),
    0 ≤ rA ∧ rA ≤ r (lev b) ∧ r (lev b) + L/4 ≤ L ∧
    TA ≤ T (lev b) ∧ jA * 2 ^ (T (lev b) - TA) ≤ j b ∧
    j b < (jA + 1) * 2 ^ (T (lev b) - TA) ∧
    MeasurableSet A_A ∧ A b ⊆ A_A ∧ ν (γ b) A_A ≠ 0 ∧ MeasurableSet H₀ ∧ H₀ ⊆ H (γ b) ∧
    RA.totalDegree ≤ 2 ∧ (∀ e, |RA.coeff e| ≤ N ^ Mr) ∧ ‖cA‖ ≤ N ^ Mr ∧
    RelativeRowPacket M Ep precision loss N L d₁ gain (2 * κ) (ν (γ b)) (B (γ b)) TA jA
      (Split.δ N rA) RA (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA)) (c b) (u b)
      (Split.δ N rA * Split.δ N (r (lev b) - rA)) (Split.δ N (r (lev b) - rA)) (A b) (F b) H₀

/-- One late sample: with o295 at row degree `M` (its `Ep`), a relative row core certificate at
exponent `Mr` gives x1078's `RelCore` at `15 + E + 3 Mr + 2 Mb`, where `2^T ≤ N^E` bounds the
packet clocks, `L ≤ E`, and `B^{±1} ≤ N^Mb`. -/
theorem relCore_of_rowCore (M Ep : ℕ) (d₁ : ℝ)
    (hEp : ∀ q : ℕ, 3 * M + 1 ≤ q →
      ∀ (precision loss Nk L gain κ : ℝ) (ν : MeasureTheory.Measure Ln) (B r : ℝ) (T j : ℕ)
        (c u : P2) (P : Po) (A : Set Ln) (F H : Set Ev),
        RowPacket M Ep precision loss Nk L d₁ gain κ ν B r T j c u P A F H →
        Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket q precision
          loss Nk L d₁ gain κ ν B r T j c u P A F H)
    (precision loss N L gain : ℝ) (Mr Mb E : ℕ) (κ : ℝ) (W : ℕ)
    (ν : Fin W → Measure Ln) [∀ w, IsProbabilityMeasure (ν w)] (B : Fin W → ℝ) (r : ℕ → ℝ)
    (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (c u : Fin C → P2) (A : Fin C → Set Ln) (F : Fin C → Set Ev) (H : Fin W → Set Ev)
    (hN : 2 ≤ N) (hLE : L ≤ E)
    (hjT : ∀ b, j b < 2 ^ T (lev b)) (hAm : ∀ b, MeasurableSet (A b))
    (hBb : ∀ w, 0 < B w ∧ B w ≤ N ^ Mb ∧ (B w)⁻¹ ≤ N ^ Mb)
    (hcore : RelRowCore M Ep precision loss N L d₁ gain Mr κ W ν B r T C lev γ j c u A F H) :
    RelCore (3 * M + 1) precision loss N L d₁ gain (15 + E + 3 * Mr + 2 * Mb) κ W ν B r T C lev
      γ j c u A F H := by
  obtain ⟨b, rA, jA, TA, cA, A_A, H₀, RA, hrA, hrArb, hroom, hTT, hj, hjup, hAAm, hAbA, hA0,
    hH₀m, hH₀H, hRAdeg, hRAc, hcA, hrr⟩ := hcore
  have hN1 : (1:ℝ) ≤ N := by linarith
  obtain ⟨hB0, -, hBinv⟩ := hBb (γ b)
  have hjA : jA < 2 ^ TA := by
    have h2 : 2 ^ T (lev b) = 2 ^ TA * 2 ^ (T (lev b) - TA) := by
      rw [← pow_add, Nat.add_sub_cancel' hTT]
    have hlt : jA * 2 ^ (T (lev b) - TA) < 2 ^ TA * 2 ^ (T (lev b) - TA) :=
      lt_of_le_of_lt hj (h2 ▸ hjT b)
    exact Nat.lt_of_mul_lt_mul_right hlt
  have h2TA1 : (1:ℝ) ≤ (2:ℝ) ^ TA := one_le_pow₀ (by norm_num)
  have ht₀ : (0:ℝ) ≤ (jA:ℝ) / (2:ℝ) ^ TA := by positivity
  have ht₁ : (jA:ℝ) / (2:ℝ) ^ TA ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hjA.le
  have hq0 : (0:ℝ) < ((2:ℝ) ^ TA)⁻¹ := by positivity
  have hq1 : ((2:ℝ) ^ TA)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2TA1
  have hδ0 := δ_pos N rA
  have hrAE : rA ≤ (E:ℝ) := by linarith
  have hδinv : (Split.δ N rA)⁻¹ ≤ N ^ E := (δ_inv_le N rA hN1).trans (by
    calc N ^ rA ≤ N ^ (E:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hrAE
      _ = N ^ E := Real.rpow_natCast N E)
  have hscinv : |(B (γ b) / Split.δ N rA)⁻¹| ≤ N ^ Mb := by
    rw [abs_of_pos (inv_pos.mpr (div_pos hB0 hδ0)), inv_div]
    calc Split.δ N rA / B (γ b) ≤ 1 / B (γ b) := by
          gcongr; exact δ_le_one N rA hN1 hrA
      _ = (B (γ b))⁻¹ := one_div _
      _ ≤ N ^ Mb := hBinv
  have hU := virtualFrame_unsubstBudget_le ((jA:ℝ) / (2:ℝ) ^ TA) ((2:ℝ) ^ TA)⁻¹ cA
    (B (γ b) / Split.δ N rA) ht₀ ht₁ hq0.le hq1
  have hP0c : ∀ e, |((rFrame N rA jA TA cA (B (γ b))).normTest (Split.δ N rA) RA).coeff e| ≤
      N ^ (15 + E + 3 * Mr + 2 * Mb) := fun e =>
    budget_normTest N hN _ _ hδ0 RA hRAdeg E Mr Mr Mb _ hRAc hδinv
      (hU.trans (arith_unsubst _ _ _ (one_le_pow₀ hN1) (one_le_pow₀ hN1) hcA _ hscinv))
      (by omega) e
  have hcA' : ‖cA‖ ≤ N ^ (15 + E + 3 * Mr + 2 * Mb) :=
    hcA.trans (pow_le_pow_right₀ hN1 (by omega))
  have hT : ν (γ b) A_A ≠ ⊤ := measure_ne_top _ _
  refine ⟨b, rA, jA, TA, cA, A_A, H₀,
    (rFrame N rA jA TA cA (B (γ b))).normTest (Split.δ N rA) RA,
    hrA, hrArb, hroom, hTT, hj, hjup, hAbA, hA0, hH₀m, hH₀H,
    ((rFrame N rA jA TA cA (B (γ b))).totalDegree_normTest_le _ RA).trans hRAdeg,
    hP0c, hcA', ?_⟩
  exact hEp (3 * M + 1) le_rfl precision loss N L gain (2 * κ) _ 1 (r (lev b) - rA)
    (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA)) _ (u b) _ _ _ _
    (relRowPacket_of_relative M Ep precision loss N L d₁ gain κ (ν (γ b))
      (B (γ b)) hB0 rA TA jA cA A_A hAAm hA0 hT RA hRAdeg (r (lev b))
      (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA)) (c b) (u b) (A b) (hAm b) hAbA (F b)
      H₀ hrr)

/-- The per-grid contract of the relative row core source. -/
def RelRowCoreSourceDs (M Ep : ℕ) (precision loss : ℝ) (cc J D : ℕ) (d₁ κ₁ S η ρ : ℝ) (m : ℕ)
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
        RelRowCore M Ep precision loss (N k) L d₁ gain Mr κ (W k) (ν k) (B k) r T C lev γ j
          c u A F H

/-- The relative row core contract: row degree `M` first, then every `Ep` (o294's order), then
`RelCoreSourceAssertion`'s order. -/
def RelRowCoreSourceAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ M : ℕ, 1 ≤ M ∧ ∀ Ep : ℕ, ∀ precision : ℝ, 1 ≤ precision → ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
    ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 →
      ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
        grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
          RelRowCoreSourceDs M Ep precision loss cc J D d₁ κ₁ S η ρ m s gain δ₀ u0

/-- The relative row core contract and the accepted o295 give x1078's core contract. -/
theorem relCoreSource_of_rowCore (hR : RelRowCoreSourceAssertion) : RelCoreSourceAssertion := by
  have h295 : O295Statement := Submission.k4_physical_row_packet_potential
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨M, hM, hR⟩ := hR hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨Ep, hEp⟩ := h295 M d₁ hd₁ hd₁1
  refine ⟨3 * M + 1, by omega, fun precision hprec D₀ => ?_⟩
  obtain ⟨D, hD₀, hR⟩ := hR Ep precision hprec D₀
  refine ⟨D, hD₀, fun J hJ hjet loss hloss hloss1 e0 he0 => ?_⟩
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgain, hds⟩ := hR J hJ hjet loss hloss hloss1 e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgain, ?_⟩
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  obtain ⟨Mr, M₀, D₀', hds⟩ := hds N K L d W ω ν E P B f g G hpb hprof Mp Dp
  have hpb' := hpb
  obtain ⟨hN2, -, -, -, -, -, -, -, hfam, -⟩ := hpb'
  beta_reduce at hfam
  obtain ⟨Mpb, Dpb, hMD⟩ := hfam
  refine ⟨15 + ⌈2 * L⌉₊ + 3 * Mr + 2 * Mpb, M₀, D₀', ?_⟩
  intro Mi Di hMi hDi τ hτ α hα hα1
  obtain ⟨σ, hσ, k₀, hds⟩ := hds Mi Di hMi hDi τ hτ α hα hα1
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass
  rcases hds k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with hex | hcore
  · exact Or.inl hex
  · right
    obtain ⟨-, -, -, -, -, -, -, hpk⟩ := hpath
    have hLE : L ≤ (⌈2 * L⌉₊ : ℝ) := by
      have := Nat.le_ceil (2 * L); linarith
    have : ∀ w, IsProbabilityMeasure (ν k w) := fun w => ((hMD k).2.2.2.1 w).1
    have hAm : ∀ b, MeasurableSet (A b) := by
      intro b
      obtain ⟨-, -, hch⟩ := hpk b
      obtain ⟨-, -, -, -, -, -, hAbm, -⟩ := hch
      exact hAbm
    exact relCore_of_rowCore M Ep d₁ hEp precision loss (N k) L gain Mr Mpb ⌈2 * L⌉₊ κ (W k)
      (ν k) (B k) r T C lev γ j c u A F H (hN2 k) hLE (fun b => (hpk b).2.1) hAm
      (fun w => ⟨((hMD k).2.2.2.1 w).2.1, ((hMD k).2.2.2.1 w).2.2.1,
        ((hMD k).2.2.2.1 w).2.2.2.1⟩) hcore

/-- The relative row core source and the accepted o288 (o295 enters through its accepted
theorem) prove o265's frozen statement. -/
theorem staged_of_rel_row_core_source (hR : RelRowCoreSourceAssertion)
    (hcomp : Submission.Obl.k4_physical_parent_potential_candidates.CompletionAssertion) :
    StagedWeakAssertion :=
  staged_of_rel_core_source (relCoreSource_of_rowCore hR) hcomp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
