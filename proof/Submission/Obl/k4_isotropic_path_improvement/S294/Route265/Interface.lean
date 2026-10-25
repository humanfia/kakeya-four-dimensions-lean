-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Route265.Interface, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The o265-direct route (x1080's plan, post on o265 at 2026-10-22 07:36Z), named statements.
Session x1088.

o265 (`k4_staged_weak_breadth_discovery`) is, as the accepted o288 records in its
`StagedInterface.StagedAssertion`, the staged weak breadth discovery: after a uniform grid,
either the width exit, a candidate `cd` at some old packet, or the narrow exit.  The route
produces, at an actual old packet `b`, a VIRTUAL instance (time, base and signal rescaled to an
ancestor window `a`, signal the ancestor test `R_a / δ_a`), on which

* o295 (`k4_physical_row_packet_potential`, statement `RowPotentialAssertion` below) turns the
  virtual qualified row packet into the virtual physical potential packet, and
* the accepted o288 (`CompletionAssertion`) turns that packet into a virtual candidate,

which the instance returns to an actual candidate at `b`.  `RelativeSourceAssertion` is what
remains to be produced: the original exits, or such an instance.  Its quantifier order is
the one the two black boxes impose (o288's relation degree, precision and loss come first;
the virtual format exponents precede o288's coefficient exponent `Mc`, which precedes `M₀`;
the virtual coefficient exponent `Mi'` precedes o288's threshold `Nk₀`). -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Interface
import Submission.Obl.k4_physical_parent_potential_candidates.Statement

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294

noncomputable section

namespace Route265

open Submission.Obl.k4_physical_parent_potential_candidates (cd)

/-- The frozen statement of o295 `k4_physical_row_packet_potential` (x1070's split of o287). -/
def RowPotentialAssertion : Prop :=
  ∀ M : ℕ, ∀ d₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → ∃ Ep : ℕ, ∀ q : ℕ, 3 * M + 1 ≤ q →
    ∀ (precision loss Nk L gain κ : ℝ) (ν : MeasureTheory.Measure Ln) (B r : ℝ) (T j : ℕ)
      (c u : P2) (P : Po) (A : Set Ln) (F H : Set Ev),
      RowPacket M Ep precision loss Nk L d₁ gain κ ν B r T j c u P A F H →
        PhysicalPotentialPacket q precision loss Nk L d₁ gain κ ν B r T j c u P A F H

/-- One virtual instance: a qualified row packet for some virtual data, the hypotheses the
accepted o288 needs for that single virtual packet, and the return of the virtual candidate to
the actual `target`. The virtual family has one world and one packet. -/
def VirtualInstance (M Ep : ℕ) (precision loss : ℝ) (cc J D : ℕ) (Nk L d₁ ρ gain τ : ℝ)
    (Mp' Dp' Mr' Mi' : ℕ) (target : Prop) : Prop :=
  ∃ (κ' : ℝ) (ν' : MeasureTheory.Measure Ln) (B' r' : ℝ) (T' j' : ℕ) (c' u' : P2)
    (Q' : Matrix (Fin 2) (Fin 2) ℝ) (R' P0' : Po) (A' : Set Ln) (F' H' : Set Ev) (ex' : Prop),
    RowPacket M Ep precision loss Nk L d₁ gain κ' ν' B' r' T' j' c' u' P0' A' F' H' ∧
    1 ≤ κ' ∧ (2 : ℝ) ^ T' ≤ Nk ^ Mr' ∧ MeasureTheory.IsProbabilityMeasure ν' ∧
    0 < B' ∧ B' ≤ Nk ^ Mr' ∧ B'⁻¹ ≤ Nk ^ Mr' ∧
    P0'.totalDegree ≤ 2 ∧ (∀ e, |P0'.coeff e| ≤ Nk ^ Mr') ∧
    ch Nk Mp' Dp' κ' T' (j' : ℝ) r' B' Set.univ c' u' Q' R' A' F' ex' ∧
    j' < 2 ^ T' ∧ 0 ≤ r' ∧ r' + 2 * gain * L ≤ L ∧
    (cd cc J D Nk L 1 (fun _ => ν') (fun _ => B') Mi' d₁ ρ gain τ (fun _ => r') (fun _ => T') 1
        (fun _ => 0) (fun _ => 0) (fun _ => j') (fun _ => A') (fun _ => H') → target)

/-- **What the relative-scale source must produce.** The same frozen hypotheses as o265,
with the qualification degree `M` chosen first, then any precision exponent `Ep`, precision and
loss (supplied by o295 and o288), then the uniform grid; for every admissible sequence, the
virtual format exponents, then (after o288's `Mc'`) the narrow-exit format, then a virtual
coefficient exponent `Mi' ≥ Mc'`; eventually, for every path and final set `H`, the original
width or narrow exit, or a virtual instance whose candidate returns to an actual `cd`. -/
def RelativeSourceAssertion : Prop :=
  ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
  ∃ M : ℕ, 1 ≤ M ∧ ∀ Ep : ℕ, ∀ precision : ℝ, 1 ≤ precision → ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
  ∀ J : ℕ, 1 ≤ J → JointJetBound D J → ∀ loss : ℝ, 0 < loss → loss ≤ 1 →
  ∀ e0 : ℝ, 0 < e0 → ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
    grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
  ∀ N K L d W ω ν E P B f g G, pb N K L d S η W ω ν E P B f g G →
    (∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - d₁ * r| ≤ δ₀ * L) →
  ∀ Mp Dp : ℕ, ∃ Mp' Dp' Mr' : ℕ, ∀ Mc' : ℕ, ∃ M₀ D₀' : ℕ, ∀ Mi Di : ℕ, M₀ ≤ Mi → D₀' ≤ Di →
  ∀ τ : ℝ, 0 < τ → ∀ α : ℝ, 0 < α → α ≤ 1 →
  ∃ Mi' : ℕ, Mc' ≤ Mi' ∧ ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
  ∀ r T nw κ C lev par γ j c u Q R A F lst,
    path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u
      Q R A F lst →
    ∀ H : Fin (W k) → Set Ev,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ {p | ∃ b : Fin C, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b}) →
      ENNReal.ofReal (κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) →
      (wi (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mi Di τ ∨
        narrow (N k) L (W k) (ω k) (ν k) (E k) (B k) m s r T nw gain u0 κ M₀ D₀' α C lev γ j
          A F H) ∨
      VirtualInstance M Ep precision loss cc J D (N k) L d₁ ρ gain τ Mp' Dp' Mr' Mi'
        (cd cc J D (N k) L (W k) (ν k) (B k) Mi d₁ ρ gain τ r T C lev γ j A H)

end Route265

end

end Submission.Obl.k4_isotropic_path_improvement.S294
