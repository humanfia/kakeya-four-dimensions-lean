-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.NaturalCore, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1080,
-- branch x1080, commit 5a0a478a0, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/NaturalCore.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- The relative row core in natural units: ancestor width δ_A, signal R_A/δ_b (x1080, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.RowCore

/-!
# The relative row core in natural units

With the ancestor depth snapped to the dyadic grid, `rA = ⌊r_A c⌋ / c` (`c = log N / log 2`),
`δ(N, rA) = δ(N, r_A)` and `δ(N, rA) * δ(N, r_b - rA) = δ(N, r_b)` hold EXACTLY
(`δ_snap`, `δ_snap_mul`). So the source may state `RelativeRowPacket` in its natural units:
thickness `δ_A = δ(N, r_A)` of the actual ancestor, physical signal `R_A / δ_b` with
`δ_b = δ(N, r_b)`, and relative thickness `a' = δ_b / δ_A`, with no factor-two bookkeeping
(`RelRowCoreNat`). `relRowCore_of_nat`, `relRowCoreSource_of_nat`, and with o288
`staged_of_rel_row_core_nat_source`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The depth `r` snapped down to the dyadic grid of `N`. -/
def snap (N r : ℝ) : ℝ := (⌊r * (Real.log N / Real.log 2)⌋ : ℝ) / (Real.log N / Real.log 2)

lemma snap_spec (N : ℝ) (hN : 2 ≤ N) (r : ℝ) :
    snap N r * Real.log N / Real.log 2 = (⌊r * Real.log N / Real.log 2⌋ : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  unfold snap
  rw [mul_div_assoc]
  field_simp

lemma δ_snap (N : ℝ) (hN : 2 ≤ N) (r : ℝ) : Split.δ N (snap N r) = Split.δ N r := by
  rw [δ_eq, δ_eq, snap_spec N hN r, Int.floor_intCast]

lemma δ_snap_mul (N : ℝ) (hN : 2 ≤ N) (r rb : ℝ) :
    Split.δ N (snap N r) * Split.δ N (rb - snap N r) = Split.δ N rb := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : (rb - snap N r) * Real.log N / Real.log 2 =
      rb * Real.log N / Real.log 2 - (⌊r * Real.log N / Real.log 2⌋ : ℝ) := by
    rw [← snap_spec N hN r]; ring
  rw [δ_eq, δ_eq, δ_eq, snap_spec N hN r, Int.floor_intCast, hsub, Int.floor_sub_intCast,
    ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  congr 1
  ring

lemma snap_nonneg (N : ℝ) (hN : 2 ≤ N) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ snap N r := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  unfold snap
  apply div_nonneg _ (div_pos hlN hl2).le
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hr (div_pos hlN hl2).le)

lemma snap_le (N : ℝ) (hN : 2 ≤ N) (r : ℝ) : snap N r ≤ r := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  unfold snap
  rw [div_le_iff₀ (div_pos hlN hl2)]
  exact Int.floor_le _

/-- The relative row core in natural units: `RelRowCore` with the ACTUAL ancestor depth `rA`
(any real in `[0, r_b]`), ancestor thickness `δ(N, rA)`, physical signal `RA / δ(N, r_b)` and
relative thickness `δ(N, r_b) / δ(N, rA)`. -/
def RelRowCoreNat (M Ep : ℕ) (precision loss : ℝ) (N L d₁ gain : ℝ) (Mr : ℕ) (κ : ℝ) (W : ℕ)
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
      (Split.δ N (r (lev b))) (Split.δ N (r (lev b)) / Split.δ N rA) (A b) (F b) H₀

/-- One late sample: the natural-unit certificate is a `RelRowCore` at the snapped depth. -/
theorem relRowCore_of_nat (M Ep : ℕ) (precision loss N L d₁ gain : ℝ) (Mr : ℕ) (κ : ℝ) (W : ℕ)
    (ν : Fin W → Measure Ln) (B : Fin W → ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ) (c u : Fin C → P2)
    (A : Fin C → Set Ln) (F : Fin C → Set Ev) (H : Fin W → Set Ev) (hN : 2 ≤ N)
    (h : RelRowCoreNat M Ep precision loss N L d₁ gain Mr κ W ν B r T C lev γ j c u A F H) :
    RelRowCore M Ep precision loss N L d₁ gain Mr κ W ν B r T C lev γ j c u A F H := by
  obtain ⟨b, rA, jA, TA, cA, A_A, H₀, RA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, hrr⟩ := h
  have hmul := δ_snap_mul N hN rA (r (lev b))
  have hA := δ_snap N hN rA
  have hA0 : Split.δ N rA ≠ 0 := (δ_pos N rA).ne'
  have hrel : Split.δ N (r (lev b) - snap N rA) = Split.δ N (r (lev b)) / Split.δ N rA := by
    rw [← hmul, hA]; field_simp
  refine ⟨b, snap N rA, jA, TA, cA, A_A, H₀, RA, snap_nonneg N hN rA h0,
    (snap_le N hN rA).trans h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ?_⟩
  rw [hmul, hA, hrel]
  exact hrr

/-- The per-grid contract of the natural-unit relative row core source. -/
def RelRowCoreNatSourceDs (M Ep : ℕ) (precision loss : ℝ) (cc J D : ℕ) (d₁ κ₁ S η ρ : ℝ)
    (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ) : Prop :=
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
        RelRowCoreNat M Ep precision loss (N k) L d₁ gain Mr κ (W k) (ν k) (B k) r T C lev γ j
          c u A F H

/-- The natural-unit relative row core contract (order of `RelRowCoreSourceAssertion`). -/
def RelRowCoreNatSourceAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ M : ℕ, 1 ≤ M ∧ ∀ Ep : ℕ, ∀ precision : ℝ, 1 ≤ precision → ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
    ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 →
      ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
        grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
          RelRowCoreNatSourceDs M Ep precision loss cc J D d₁ κ₁ S η ρ m s gain δ₀ u0

theorem relRowCoreSource_of_nat (hR : RelRowCoreNatSourceAssertion) :
    RelRowCoreSourceAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨M, hM, hR⟩ := hR hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  refine ⟨M, hM, fun Ep precision hprec D₀ => ?_⟩
  obtain ⟨D, hD₀, hR⟩ := hR Ep precision hprec D₀
  refine ⟨D, hD₀, fun J hJ hjet loss hloss hloss1 e0 he0 => ?_⟩
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgain, hds⟩ := hR J hJ hjet loss hloss hloss1 e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgain, ?_⟩
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  have hN2 : ∀ k, 2 ≤ N k := hpb.1
  obtain ⟨Mr, M₀, D₀', hds⟩ := hds N K L d W ω ν E P B f g G hpb hprof Mp Dp
  refine ⟨Mr, M₀, D₀', fun Mi Di hMi hDi τ hτ α hα hα1 => ?_⟩
  obtain ⟨σ, hσ, k₀, hds⟩ := hds Mi Di hMi hDi τ hτ α hα hα1
  refine ⟨σ, hσ, k₀, fun k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass => ?_⟩
  rcases hds k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with hex | hnat
  · exact Or.inl hex
  · exact Or.inr (relRowCore_of_nat M Ep precision loss (N k) L d₁ gain Mr κ (W k) (ν k) (B k) r
      T C lev γ j c u A F H (hN2 k) hnat)

/-- The natural-unit relative row core source and the accepted o288 prove o265's frozen
statement. -/
theorem staged_of_rel_row_core_nat_source (hR : RelRowCoreNatSourceAssertion)
    (hcomp : Submission.Obl.k4_physical_parent_potential_candidates.CompletionAssertion) :
    StagedWeakAssertion :=
  staged_of_rel_row_core_source (relRowCoreSource_of_nat hR) hcomp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
