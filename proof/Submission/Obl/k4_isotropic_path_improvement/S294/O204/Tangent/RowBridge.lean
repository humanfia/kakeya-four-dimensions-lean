-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.RowBridge, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Row-packet form of x1078's virtual source contract (session x1088).

x1078's `VirtualSourceAssertion` (o204, `Tangent.Orchestration`, ported here) asks a broad
source for o288's `PhysicalPotentialPacket` on the one-packet virtual instance below an ancestor.
`VirtualRowSourceAssertion` asks for the qualified `RowPacket M Ep` on exactly the same virtual
instance, with the qualification degree `M` chosen first and then any precision exponent `Ep`,
as in o294; o295 (`RowPotentialAssertion`) converts it, at the potential degree `q = 3M + 1`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Orchestration
import Submission.Obl.k4_isotropic_path_improvement.S294.Route265.Interface

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- `VirtualPPP` with the qualified row packet of degree `M` and precision exponent `Ep` in
place of the physical potential packet. -/
def VirtualRow (M Ep : ℕ) (precision loss : ℝ) (N L d₁ gain : ℝ) (m : ℕ) (s : ℕ → ℝ)
    (Mp Mr : ℕ) (κ : ℝ) (W : ℕ) (ν : Fin W → Measure Ln) (B : Fin W → ℝ) (r : ℕ → ℝ)
    (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (c u : Fin C → P2) (R : Fin C → Po) (A : Fin C → Set Ln) (F : Fin C → Set Ev)
    (H : Fin W → Set Ev) : Prop :=
  ∃ (b : Fin C) (iA jA TA : ℕ) (cA : P2) (A_A : Set Ln) (H₀ : Set Ev) (P0 : Po),
    iA < m ∧ 0 ≤ s iA ∧ s iA * L ≤ r (lev b) ∧ 8 * gain * L ≤ L - s iA * L ∧
    r (lev b) + 2 * gain * L ≤ L ∧
    TA ≤ T (lev b) ∧ jA * 2 ^ (T (lev b) - TA) ≤ j b ∧
    j b < (jA + 1) * 2 ^ (T (lev b) - TA) ∧
    MeasurableSet A_A ∧ A b ⊆ A_A ∧ ν (γ b) A_A ≠ 0 ∧ MeasurableSet H₀ ∧ H₀ ⊆ H (γ b) ∧
    P0.totalDegree ≤ 2 ∧ (∀ e, |P0.coeff e| ≤ N ^ Mr) ∧
    (2:ℝ) ^ (T (lev b) - TA) ≤ N ^ Mr ∧ Mp ≤ Mr ∧ (2:ℝ)^TA * N^Mp ≤ N^Mr ∧
    ‖((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)‖ + ‖u b‖ ≤ N ^ Mr ∧
    (∀ e, |((vFrame N L (s iA) jA TA cA (B (γ b))).normTest
      (Split.δ N (s iA * L)) (R b)).coeff e| ≤ N^Mr) ∧
    (∀ l ∈ A b, ∀ e, |(tanLine (vFrame N L (s iA) jA TA cA (B (γ b))) 0 l).2 e| ≤ N^Mr) ∧
    81 * |Split.δ N (s iA * L)| * residualBudget 0 1 ^ 2 *
      (vFrame N L (s iA) jA TA cA (B (γ b))).substBudget ^ 2 ≤ N ^ Mr ∧
    Submission.Obl.k4_isotropic_path_improvement.S294.RowPacket M Ep precision loss
      N (L - s iA * L) d₁ (gain * L / (L - s iA * L)) (2 * κ)
      (tanPrior (vFrame N L (s iA) jA TA cA (B (γ b))) 0 (ν (γ b)) A_A) 1
      (r (lev b) - s iA * L) (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA))
      (((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)) (u b) P0
      (tanLine (vFrame N L (s iA) jA TA cA (B (γ b))) 0 '' A b)
      (tanEvent (vFrame N L (s iA) jA TA cA (B (γ b))) 0 '' F b)
      (tanEvent (vFrame N L (s iA) jA TA cA (B (γ b))) 0 '' H₀)

/-- `VirtualSourceDs` with `VirtualRow` in place of `VirtualPPP`. -/
def VirtualRowSourceDs (M Ep : ℕ) (precision loss : ℝ) (cc J D : ℕ) (d₁ κ₁ S η ρ : ℝ)
    (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ) : Prop :=
  ∀ N K L d W ω ν E P B f g G, pb N K L d S η W ω ν E P B f g G →
    (∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - d₁*r| ≤ δ₀*L) →
    ∀ Mp Dp : ℕ, ∃ Mr : ℕ, ∀ Mlow : ℕ, ∃ M₀ D₀ : ℕ, Mlow ≤ M₀ ∧
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
        VirtualRow M Ep precision loss (N k) L d₁ gain m s Mp Mr κ (W k) (ν k) (B k) r T C lev
          γ j c u R A F H

/-- **The row-packet source contract**, in o294's quantifier order: the qualification degree
`M` first, then any precision exponent `Ep`, then the relation degree (large enough for
o288 at `q = 3M + 1`), the jet exponent, any precision and loss, and the grid. -/
def VirtualRowSourceAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ M : ℕ, 1 ≤ M ∧ ∀ Ep : ℕ, ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
      max 5186 (864 * (2 * ((3 * M + 1) + 2)) + 2) ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
    ∀ precision : ℝ, 1 ≤ precision → ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 →
      ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
        grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
          VirtualRowSourceDs M Ep precision loss cc J D d₁ κ₁ S η ρ m s gain δ₀ u0

/-- **Bridge**: o295 turns a row-packet source into x1078's potential source. -/
theorem virtual_source_of_rows
    (hrows : Submission.Obl.k4_isotropic_path_improvement.S294.Route265.RowPotentialAssertion)
    (hVR : VirtualRowSourceAssertion) : VirtualSourceAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨M, hM, hVR⟩ := hVR hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨Ep, hrowsM⟩ := hrows M d₁ hd₁ hd₁1
  refine ⟨3 * M + 1, by omega, ?_⟩
  intro D₀
  obtain ⟨D, hD₀, hDmin, hVR⟩ := hVR Ep D₀
  refine ⟨D, hD₀, hDmin, ?_⟩
  intro J hJ hjet precision hprec loss hloss hloss1 e0 he0
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgain, hds⟩ :=
    hVR J hJ hjet precision hprec loss hloss hloss1 e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgain, ?_⟩
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  obtain ⟨Mr, hds⟩ := hds N K L d W ω ν E P B f g G hpb hprof Mp Dp
  refine ⟨Mr, ?_⟩
  intro Mlow
  obtain ⟨M₀, D₀', hM₀, hds⟩ := hds Mlow
  refine ⟨M₀, D₀', hM₀, ?_⟩
  intro Mi Di hMi hDi τ hτ α hα hα1
  obtain ⟨σ, hσ, k₀, hds⟩ := hds Mi Di hMi hDi τ hτ α hα hα1
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass
  rcases hds k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with hexit | hrow
  · exact Or.inl hexit
  · right
    obtain ⟨b, iA, jA, TA, cA, A_A, H₀, P0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, hRow⟩ := hrow
    exact ⟨b, iA, jA, TA, cA, A_A, H₀, P0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      hrowsM (3 * M + 1) le_rfl precision loss _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRow⟩

/-- **o265 from o295, a row-packet source and the accepted o288** (through x1078's
orchestration). -/
theorem staged_of_rows_and_virtual_row_source
    (hrows : Submission.Obl.k4_isotropic_path_improvement.S294.Route265.RowPotentialAssertion)
    (hVR : VirtualRowSourceAssertion)
    (hcomp : Submission.Obl.k4_physical_parent_potential_candidates.CompletionAssertion) :
    StagedWeakAssertion :=
  staged_of_virtual_source (virtual_source_of_rows hrows hVR) hcomp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
