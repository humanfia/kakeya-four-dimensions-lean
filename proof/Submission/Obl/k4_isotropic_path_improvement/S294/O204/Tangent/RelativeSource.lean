-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.RelativeSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1080,
-- branch x1080, commit 5a0a478a0, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/RelativeSource.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- The relative source contract and o295 give x1078's virtual source contract (x1080, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.VirtualRowPacket
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.RelativeOrchestration
import Submission.Obl.k4_physical_row_packet_potential

/-!
# From a relative row-packet source to the virtual source contract

x1078's `VirtualSourceAssertion` (`Tangent.Orchestration`) asks the broad source for o288's
`PhysicalPotentialPacket` on a one-packet virtual instance below an ancestor. Here the source is
asked instead for o295's row clauses in ORIGINAL units with precisions relative to the ancestor
(`RelativeRowPacket`, signal = the ancestor's own test `RA`), in o294's quantifier order (row
degree `M` first, then every precision exponent `Ep`). `virtual_source_of_relative`: with o295's
frozen statement (`O295Statement`, `exact`-compatible with o295's theorem), the relative contract
gives the virtual one, through `virtualRowPacket_of_relative`. Together with
`staged_of_virtual_source` and the accepted o288 this proves o265's frozen statement.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- o295's frozen statement with its bindings named; `Submission.k4_physical_row_packet_potential`
has exactly this type up to definitional unfolding. -/
def O295Statement : Prop :=
  ∀ M : ℕ, ∀ d₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → ∃ Ep : ℕ, ∀ q : ℕ, 3 * M + 1 ≤ q →
    ∀ (precision loss Nk L gain κ : ℝ) (ν : MeasureTheory.Measure Ln) (B r : ℝ) (T j : ℕ)
      (c u : P2) (P : Po) (A : Set Ln) (F H : Set Ev),
      RowPacket M Ep precision loss Nk L d₁ gain κ ν B r T j c u P A F H →
      Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket q precision
        loss Nk L d₁ gain κ ν B r T j c u P A F H

/-- The certificate a broad RELATIVE source returns at one late sample: `VirtualPPP`'s data with
the potential packet replaced by `RelativeRowPacket` for the ancestor test `RA`. -/
def VirtualRel (M Ep : ℕ) (precision loss : ℝ) (N L d₁ gain : ℝ) (m : ℕ) (s : ℕ → ℝ)
    (Mp Mr : ℕ) (κ : ℝ) (W : ℕ) (ν : Fin W → Measure Ln) (B : Fin W → ℝ) (r : ℕ → ℝ)
    (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (c u : Fin C → P2) (R : Fin C → Po) (A : Fin C → Set Ln) (F : Fin C → Set Ev)
    (H : Fin W → Set Ev) : Prop :=
  ∃ (b : Fin C) (iA jA TA : ℕ) (cA : P2) (A_A : Set Ln) (H₀ : Set Ev) (RA : Po),
    iA < m ∧ 0 ≤ s iA ∧ s iA * L ≤ r (lev b) ∧ 8 * gain * L ≤ L - s iA * L ∧
    r (lev b) + 2 * gain * L ≤ L ∧
    TA ≤ T (lev b) ∧ jA * 2 ^ (T (lev b) - TA) ≤ j b ∧
    j b < (jA + 1) * 2 ^ (T (lev b) - TA) ∧
    MeasurableSet A_A ∧ A b ⊆ A_A ∧ ν (γ b) A_A ≠ 0 ∧ MeasurableSet H₀ ∧ H₀ ⊆ H (γ b) ∧
    RA.totalDegree ≤ 2 ∧ (∀ e, |((vFrame N L (s iA) jA TA cA (B (γ b))).normTest (Split.δ N (s iA * L)) RA).coeff e| ≤ N ^ Mr) ∧
    (2:ℝ) ^ (T (lev b) - TA) ≤ N ^ Mr ∧ Mp ≤ Mr ∧ (2:ℝ)^TA * N^Mp ≤ N^Mr ∧
    ‖((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)‖ + ‖u b‖ ≤ N ^ Mr ∧
    (∀ e, |((vFrame N L (s iA) jA TA cA (B (γ b))).normTest
      (Split.δ N (s iA * L)) (R b)).coeff e| ≤ N^Mr) ∧
    (∀ l ∈ A b, ∀ e, |(tanLine (vFrame N L (s iA) jA TA cA (B (γ b))) 0 l).2 e| ≤ N^Mr) ∧
    81 * |Split.δ N (s iA * L)| * residualBudget 0 1 ^ 2 *
      (vFrame N L (s iA) jA TA cA (B (γ b))).substBudget ^ 2 ≤ N ^ Mr ∧
    RelativeRowPacket M Ep precision loss N (L - s iA * L) d₁ (gain * L / (L - s iA * L)) (2 * κ)
      (ν (γ b)) (B (γ b)) TA jA (Split.δ N (s iA * L)) RA (T (lev b) - TA)
      (j b - jA * 2 ^ (T (lev b) - TA)) (c b) (u b)
      (Split.δ N (s iA * L) * Split.δ N (r (lev b) - s iA * L)) (Split.δ N (r (lev b) - s iA * L))
      (A b) (F b) H₀

/-- The per-grid relative contract. -/
def RelativeSourceDs (M Ep : ℕ) (precision loss : ℝ) (cc J D : ℕ) (d₁ κ₁ S η ρ : ℝ) (m : ℕ)
    (s : ℕ → ℝ) (gain δ₀ u0 : ℝ) : Prop :=
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
        VirtualRel M Ep precision loss (N k) L d₁ gain m s Mp Mr κ (W k) (ν k) (B k) r T C lev γ j
          c u R A F H

/-- The relative contract, in o294's quantifier order. -/
def RelativeSourceAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ M : ℕ, 1 ≤ M ∧ ∀ Ep : ℕ, ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
      max 5186 (864 * (2 * ((3 * M + 1) + 2)) + 2) ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
    ∀ precision : ℝ, 1 ≤ precision → ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 →
      ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
        grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
          RelativeSourceDs M Ep precision loss cc J D d₁ κ₁ S η ρ m s gain δ₀ u0




/-- The relative source contract and o295 give the virtual source contract. -/
theorem virtual_source_of_relative (hR : RelativeSourceAssertion) (h295 : O295Statement) :
    VirtualSourceAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨M, hM, hR⟩ := hR hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨Ep, hEp⟩ := h295 M d₁ hd₁ hd₁1
  refine ⟨3 * M + 1, by omega, fun D₀ => ?_⟩
  obtain ⟨D, hD₀, hDmin, hR⟩ := hR Ep D₀
  refine ⟨D, hD₀, hDmin, ?_⟩
  intro J hJ hjet precision hprec loss hloss hloss1 e0 he0
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgain, hds⟩ :=
    hR J hJ hjet precision hprec loss hloss hloss1 e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgain, ?_⟩
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  have hpb' := hpb
  obtain ⟨Mr, hds⟩ := hds N K L d W ω ν E P B f g G hpb hprof Mp Dp
  refine ⟨Mr, fun Mlow => ?_⟩
  obtain ⟨M₀, D₀', hM₀, hds⟩ := hds Mlow
  refine ⟨M₀, D₀', hM₀, fun Mi Di hMi hDi τ hτ α hα hα1 => ?_⟩
  obtain ⟨σ, hσ, k₀, hds⟩ := hds Mi Di hMi hDi τ hτ α hα hα1
  refine ⟨σ, hσ, k₀, fun k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass => ?_⟩
  rcases hds k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with hexit | hrel
  · exact Or.inl hexit
  · right
    obtain ⟨b, iA, jA, TA, cA, A_A, H₀, RA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, hRAdeg, hP0c, h16, h17, h18, h19, h20, h21, h22, hrr⟩ := hrel
    -- facts from the problem and the path
    obtain ⟨-, -, -, -, -, -, -, -, hfam, -⟩ := hpb'
    beta_reduce at hfam
    obtain ⟨Mpb, Dpb, hMD⟩ := hfam
    have hνprob : IsProbabilityMeasure (ν k (γ b)) := ((hMD k).2.2.2.1 (γ b)).1
    have hBpos : 0 < B k (γ b) := ((hMD k).2.2.2.1 (γ b)).2.1
    obtain ⟨-, -, -, -, -, -, -, hpb⟩ := hpath
    obtain ⟨-, -, hch⟩ := hpb b
    obtain ⟨-, -, -, -, -, -, hAbm, -⟩ := hch
    have hT : ν k (γ b) A_A ≠ ⊤ := measure_ne_top _ _
    refine ⟨b, iA, jA, TA, cA, A_A, H₀,
      (vFrame (N k) L (s iA) jA TA cA (B k (γ b))).normTest (Split.δ (N k) (s iA * L)) RA,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      ((vFrame (N k) L (s iA) jA TA cA (B k (γ b))).totalDegree_normTest_le _ RA).trans hRAdeg,
      hP0c, h16, h17, h18, h19, h20, h21, h22, ?_⟩
    exact hEp (3 * M + 1) le_rfl precision loss (N k) (L - s iA * L) (gain * L / (L - s iA * L))
      (2 * κ) _ 1 (r (lev b) - s iA * L) (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA))
      _ (u b) _ _ _ _
      (virtualRowPacket_of_relative M Ep precision loss (N k) L d₁ gain κ (ν k (γ b))
        (B k (γ b)) hBpos (s iA) TA jA cA A_A h9 h11 hT RA hRAdeg (r (lev b))
        (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA)) (c b) (u b) (A b) hAbm h10 (F b) H₀ hrr)

/-- The whole relative route: a relative row-packet source, o295 and the accepted o288 prove
o265's frozen statement (`StagedWeakAssertion`). -/
theorem staged_of_relative (hR : RelativeSourceAssertion) (h295 : O295Statement)
    (hcomp : Submission.Obl.k4_physical_parent_potential_candidates.CompletionAssertion) :
    StagedWeakAssertion :=
  staged_of_virtual_source (virtual_source_of_relative hR h295) hcomp


/-! ## The unscaled form (x1078's `RelPPP`, recommended target) -/

lemma rFrame_eq (N rA : ℝ) (jA TA : ℕ) (cA : P2) (B : ℝ) :
    rFrame N rA jA TA cA B =
      isoPFrame ((jA : ℝ) * ((2 : ℝ) ^ TA)⁻¹) ((2 : ℝ) ^ TA)⁻¹ cA (B / Split.δ N rA) := by
  simp only [rFrame, virtualFrame, isoPFrame, isoFrame, div_eq_mul_inv]

/-- The forward transport at the literal data of `RelPPP` (unscaled `L`, `gain`; ancestor depth
`rA`; slack `2κ`). -/
theorem relRowPacket_of_relative (M Ep : ℕ) (precision loss N L d₁ gain κ : ℝ)
    (ν : Measure Ln) [SFinite ν] (B : ℝ) (hB : 0 < B) (rA : ℝ)
    (TA jA : ℕ) (cA : P2) (A_A : Set Ln) (hAA : MeasurableSet A_A) (hAA0 : ν A_A ≠ 0)
    (hAAT : ν A_A ≠ ⊤) (RA : Po) (hRA : RA.totalDegree ≤ 2)
    (rb : ℝ) (T' j' : ℕ) (cb ub : P2) (Ab : Set Ln) (hAb : MeasurableSet Ab) (hAbA : Ab ⊆ A_A)
    (Fb H₀ : Set Ev)
    (h : RelativeRowPacket M Ep precision loss N L d₁ gain (2 * κ) ν B TA jA (Split.δ N rA) RA T' j'
      cb ub (Split.δ N rA * Split.δ N (rb - rA)) (Split.δ N (rb - rA)) Ab Fb H₀) :
    RowPacket M Ep precision loss N L d₁ gain (2 * κ)
      (tanPrior (rFrame N rA jA TA cA B) 0 ν A_A) 1 (rb - rA) T' j'
      (((2:ℝ)^TA) • (cb + ((jA:ℝ)/(2:ℝ)^TA) • ub - cA)) ub
      ((rFrame N rA jA TA cA B).normTest (Split.δ N rA) RA)
      (tanLine (rFrame N rA jA TA cA B) 0 '' Ab)
      (tanEvent (rFrame N rA jA TA cA B) 0 '' Fb)
      (tanEvent (rFrame N rA jA TA cA B) 0 '' H₀) := by
  have haA : 0 < Split.δ N rA := by unfold Split.δ; positivity
  have haB : 0 < Split.δ N rA * Split.δ N (rb - rA) := by
    have : 0 < Split.δ N (rb - rA) := by unfold Split.δ; positivity
    positivity
  have hq : ((2 : ℝ) ^ TA)⁻¹ ≠ 0 := by positivity
  have hsc : B / Split.δ N rA ≠ 0 := (div_pos hB haA).ne'
  have key := rowPacket_of_relative M Ep precision loss N L d₁ gain (2 * κ) ν B hB TA jA cA A_A
    hAA hAA0 hAAT (Split.δ N rA) haA RA hRA T' j' cb ub (Split.δ N rA * Split.δ N (rb - rA))
    (rb - rA) haB rfl Ab hAb hAbA Fb H₀ h
  simp only at key
  rw [rFrame_eq, image_tanLine_eq _ _ _ _ hq hsc, image_tanEvent_eq _ _ _ _ hq hsc,
    image_tanEvent_eq _ _ _ _ hq hsc, ← relCenter_eq TA T' jA j' cA cb ub]
  exact key

/-- The certificate of a broad relative ROW source (unscaled form): `RelPPP`'s data with the
potential packet replaced by `RelativeRowPacket` for the ancestor's test `RA`. -/
def RelRowCert (M Ep : ℕ) (precision loss : ℝ) (N L d₁ gain : ℝ) (Mp Mr : ℕ) (κ : ℝ) (W : ℕ)
    (ν : Fin W → Measure Ln) (B : Fin W → ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ) (c u : Fin C → P2)
    (R : Fin C → Po) (A : Fin C → Set Ln) (F : Fin C → Set Ev) (H : Fin W → Set Ev) : Prop :=
  ∃ (b : Fin C) (rA : ℝ) (jA TA : ℕ) (cA : P2) (A_A : Set Ln) (H₀ : Set Ev) (RA : Po),
    0 ≤ rA ∧ rA ≤ r (lev b) ∧ r (lev b) + L/4 ≤ L ∧
    TA ≤ T (lev b) ∧ jA * 2 ^ (T (lev b) - TA) ≤ j b ∧
    j b < (jA + 1) * 2 ^ (T (lev b) - TA) ∧
    A b ⊆ A_A ∧ ν (γ b) A_A ≠ 0 ∧ MeasurableSet H₀ ∧ H₀ ⊆ H (γ b) ∧
    MeasurableSet A_A ∧ RA.totalDegree ≤ 2 ∧ (∀ e, |((rFrame N rA jA TA cA (B (γ b))).normTest (Split.δ N rA) RA).coeff e| ≤ N ^ Mr) ∧
    (2:ℝ) ^ (T (lev b) - TA) ≤ N ^ Mr ∧ Mp ≤ Mr ∧ (2:ℝ)^TA * N^Mp ≤ N^Mr ∧
    ‖((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)‖ + ‖u b‖ ≤ N ^ Mr ∧
    (∀ e, |((rFrame N rA jA TA cA (B (γ b))).normTest (Split.δ N rA) (R b)).coeff e| ≤
      N^Mr) ∧
    (∀ l ∈ A b, ∀ e, |(tanLine (rFrame N rA jA TA cA (B (γ b))) 0 l).2 e| ≤ N^Mr) ∧
    81 * |Split.δ N rA| * residualBudget 0 1 ^ 2 *
      (rFrame N rA jA TA cA (B (γ b))).substBudget ^ 2 ≤ N ^ Mr ∧
    RelativeRowPacket M Ep precision loss N L d₁ gain (2 * κ) (ν (γ b)) (B (γ b)) TA jA
      (Split.δ N rA) RA (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA)) (c b) (u b)
      (Split.δ N rA * Split.δ N (r (lev b) - rA)) (Split.δ N (r (lev b) - rA)) (A b) (F b) H₀

/-- The per-grid relative row contract (unscaled form). -/
def RelRowSourceDs (M Ep : ℕ) (precision loss : ℝ) (cc J D : ℕ) (d₁ κ₁ S η ρ : ℝ) (m : ℕ)
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
        RelRowCert M Ep precision loss (N k) L d₁ gain Mp Mr κ (W k) (ν k) (B k) r T C lev γ j
          c u R A F H

/-- The relative row contract: row degree `M` first, then every `Ep` (o294's order). -/
def RelRowSourceAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ M : ℕ, 1 ≤ M ∧ ∀ Ep : ℕ, ∀ precision : ℝ, 1 ≤ precision → ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
    ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 →
      ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
        grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
          RelRowSourceDs M Ep precision loss cc J D d₁ κ₁ S η ρ m s gain δ₀ u0

/-- The relative row contract and the accepted o295 give x1078's `RelSourceAssertion`. -/
theorem rel_source_of_rel_row (hR : RelRowSourceAssertion) : RelSourceAssertion := by
  have h295 : O295Statement := Submission.k4_physical_row_packet_potential
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨M, hM, hR⟩ := hR hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨Ep, hEp⟩ := h295 M d₁ hd₁ hd₁1
  refine ⟨3 * M + 1, by omega, fun precision hprec D₀ => ?_⟩
  obtain ⟨D, hD₀, hR⟩ := hR Ep precision hprec D₀
  refine ⟨D, hD₀, ?_⟩
  intro J hJ hjet loss hloss hloss1 e0 he0
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgain, hds⟩ := hR J hJ hjet loss hloss hloss1 e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgain, ?_⟩
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  have hpb' := hpb
  obtain ⟨Mr, M₀, D₀', hds⟩ := hds N K L d W ω ν E P B f g G hpb hprof Mp Dp
  refine ⟨Mr, M₀, D₀', fun Mi Di hMi hDi τ hτ α hα hα1 => ?_⟩
  obtain ⟨σ, hσ, k₀, hds⟩ := hds Mi Di hMi hDi τ hτ α hα hα1
  refine ⟨σ, hσ, k₀, fun k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass => ?_⟩
  rcases hds k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with hexit | hrel
  · exact Or.inl hexit
  · right
    obtain ⟨b, rA, jA, TA, cA, A_A, H₀, RA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hAAm,
      hRAdeg, hP0c, h13, h14, h15, h16, h17, h18, h19, hrr⟩ := hrel
    obtain ⟨-, -, -, -, -, -, -, -, hfam, -⟩ := hpb'
    beta_reduce at hfam
    obtain ⟨Mpb, Dpb, hMD⟩ := hfam
    have hνprob : IsProbabilityMeasure (ν k (γ b)) := ((hMD k).2.2.2.1 (γ b)).1
    have hBpos : 0 < B k (γ b) := ((hMD k).2.2.2.1 (γ b)).2.1
    obtain ⟨-, -, -, -, -, -, -, hpb⟩ := hpath
    obtain ⟨-, -, hch⟩ := hpb b
    obtain ⟨-, -, -, -, -, -, hAbm, -⟩ := hch
    have hT : ν k (γ b) A_A ≠ ⊤ := measure_ne_top _ _
    refine ⟨b, rA, jA, TA, cA, A_A, H₀,
      (rFrame (N k) rA jA TA cA (B k (γ b))).normTest (Split.δ (N k) rA) RA,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      ((rFrame (N k) rA jA TA cA (B k (γ b))).totalDegree_normTest_le _ RA).trans hRAdeg,
      hP0c, h13, h14, h15, h16, h17, h18, h19, ?_⟩
    exact hEp (3 * M + 1) le_rfl precision loss (N k) L gain (2 * κ) _ 1 (r (lev b) - rA)
      (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA)) _ (u b) _ _ _ _
      (relRowPacket_of_relative M Ep precision loss (N k) L d₁ gain κ (ν k (γ b))
        (B k (γ b)) hBpos rA TA jA cA A_A hAAm h8 hT RA hRAdeg (r (lev b))
        (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA)) (c b) (u b) (A b) hAbm h7 (F b) H₀ hrr)

/-- The whole relative route (unscaled form): a relative row source and the accepted o288 prove
o265's frozen statement; o295 is used through its accepted theorem. -/
theorem staged_of_rel_row_source (hR : RelRowSourceAssertion)
    (hcomp : Submission.Obl.k4_physical_parent_potential_candidates.CompletionAssertion) :
    StagedWeakAssertion :=
  staged_of_rel_source (rel_source_of_rel_row hR) hcomp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
