-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.RelativeOrchestration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit 29e0a82c5, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/RelativeOrchestration.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- o265 from an unscaled virtual source and o288 (x1078, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Relative

/-!
# o265 from a relative (unscaled) virtual source and o288

`RelSourceAssertion` is the contract for the broad source in the unscaled form: the virtual
instance below an ancestor keeps `N`, `L` and `gain`; the ancestor depth `rA ∈ [0, r_b]` is
arbitrary (an actual path depth may be used), and the packet has room `r_b + L/4 ≤ L`.
In o294's quantifier order, with the precision of o288 before the relation degree, every late
sample returns the original width/candidate exits, the narrow atlas (at the source's own
exponents), or a `RelPPP` certificate: a packet `b`, an ancestor block `(jA, TA)` with frame
centre `cA`, and o288's `PhysicalPotentialPacket` for the one-packet virtual instance, with the
size budgets at one exponent `Mr` chosen after `Mp, Dp`.

`staged_of_rel_source`: this contract and the accepted o288 prove o265's frozen
`StagedWeakAssertion`. o288's exponent `Mc` is chosen once, for `(L, gain)`; the narrow exit is
moved to the larger exponent `max M₀ (Mc + Mr)` by `narrow_mono`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- Charts are monotone in the polynomial exponent and the format degree. -/
theorem ch_mono_MD {Nk : ℝ} {M M' D D' : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {E : Set Ev} {c u : P2} {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : Po} {A : Set Ln} {F : Set Ev}
    {ex : Prop} (h : Split.ch Nk M D κ T j r Bv E c u Q R A F ex) (hNk : 1 ≤ Nk)
    (hM : M ≤ M') (hD : D ≤ D') : Split.ch Nk M' D' κ T j r Bv E c u Q R A F ex := by
  obtain ⟨hQ, hcu, hQQ, hQs, hdeg, hcoef, hA, hF, hfmt, hAl, hFp, hx⟩ := h
  have hpow : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hNk hM
  refine ⟨hQ, hcu.trans hpow, hQQ.trans hpow, hQs, hdeg, fun e => (hcoef e).trans hpow, hA, hF,
    fun i => ⟨Submission.Lib.K4RepresentativeAssembly.fmt_mono (hfmt i).1 hpow hD,
      Submission.Lib.K4RepresentativeAssembly.fmt_mono (hfmt i).2 hpow hD⟩, ?_, hFp, hx⟩
  intro l hl
  obtain ⟨h1, h2, h3⟩ := hAl l hl
  exact ⟨h1.trans hpow, fun e => (h2 e).trans hpow, h3⟩

/-- The narrow exit is monotone in its atlas exponents. -/
theorem narrow_mono {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
    {E : Fin W → Set Ev} {B : Fin W → ℝ} {m : ℕ} {s r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {gain u0 κ : ℝ} {Mw Dw Mw' Dw' : ℕ} {α : ℝ} {C : ℕ} {lev : Fin C → ℕ} {γ : Fin C → Fin W}
    {j : Fin C → ℕ} {A : Fin C → Set Ln} {F : Fin C → Set Ev} {H : Fin W → Set Ev}
    (h : narrow Nk L W ω ν E B m s r T nw gain u0 κ Mw Dw α C lev γ j A F H) (hNk : 1 ≤ Nk)
    (hM : Mw ≤ Mw') (hD : Dw ≤ Dw') :
    narrow Nk L W ω ν E B m s r T nw gain u0 κ Mw' Dw' α C lev γ j A F H := by
  obtain ⟨i, β, hi, hs1, hs2, hu, hβ, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂, hC, hdisj, hcard,
    hch, hmass⟩ := h
  exact ⟨i, β, hi, hs1, hs2, hu, hβ, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hC.trans (pow_le_pow_right₀ hNk hM), hdisj, hcard,
    fun b => ⟨ch_mono_MD (hch b).1 hNk hM hD, (hch b).2⟩, hmass⟩

/-- The unscaled virtual frame of an ancestor block `(jA, TA)` at depth `rA`. -/
abbrev rFrame (N rA : ℝ) (jA TA : ℕ) (cA : P2) (B : ℝ) : PFrame :=
  virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA (B / Split.δ N rA)

/-- The certificate a broad source returns at one late sample (unscaled form). -/
def RelPPP (q : ℕ) (precision loss : ℝ) (N L d₁ gain : ℝ) (Mp Mr : ℕ) (κ : ℝ) (W : ℕ)
    (ν : Fin W → Measure Ln) (B : Fin W → ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ) (c u : Fin C → P2)
    (R : Fin C → Po) (A : Fin C → Set Ln) (F : Fin C → Set Ev) (H : Fin W → Set Ev) : Prop :=
  ∃ (b : Fin C) (rA : ℝ) (jA TA : ℕ) (cA : P2) (A_A : Set Ln) (H₀ : Set Ev) (P0 : Po),
    0 ≤ rA ∧ rA ≤ r (lev b) ∧ r (lev b) + L/4 ≤ L ∧
    TA ≤ T (lev b) ∧ jA * 2 ^ (T (lev b) - TA) ≤ j b ∧
    j b < (jA + 1) * 2 ^ (T (lev b) - TA) ∧
    A b ⊆ A_A ∧ ν (γ b) A_A ≠ 0 ∧ MeasurableSet H₀ ∧ H₀ ⊆ H (γ b) ∧
    P0.totalDegree ≤ 2 ∧ (∀ e, |P0.coeff e| ≤ N ^ Mr) ∧
    (2:ℝ) ^ (T (lev b) - TA) ≤ N ^ Mr ∧ Mp ≤ Mr ∧ (2:ℝ)^TA * N^Mp ≤ N^Mr ∧
    ‖((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)‖ + ‖u b‖ ≤ N ^ Mr ∧
    (∀ e, |((rFrame N rA jA TA cA (B (γ b))).normTest (Split.δ N rA) (R b)).coeff e| ≤
      N^Mr) ∧
    (∀ l ∈ A b, ∀ e, |(tanLine (rFrame N rA jA TA cA (B (γ b))) 0 l).2 e| ≤ N^Mr) ∧
    81 * |Split.δ N rA| * residualBudget 0 1 ^ 2 *
      (rFrame N rA jA TA cA (B (γ b))).substBudget ^ 2 ≤ N ^ Mr ∧
    Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket q precision loss
      N L d₁ gain (2 * κ)
      (tanPrior (rFrame N rA jA TA cA (B (γ b))) 0 (ν (γ b)) A_A) 1
      (r (lev b) - rA) (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA))
      (((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)) (u b) P0
      (tanLine (rFrame N rA jA TA cA (B (γ b))) 0 '' A b)
      (tanEvent (rFrame N rA jA TA cA (B (γ b))) 0 '' F b)
      (tanEvent (rFrame N rA jA TA cA (B (γ b))) 0 '' H₀)

/-- The per-grid contract of the broad source (unscaled form). -/
def RelSourceDs (q : ℕ) (precision loss : ℝ) (cc J D : ℕ) (d₁ κ₁ S η ρ : ℝ) (m : ℕ)
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
        RelPPP q precision loss (N k) L d₁ gain Mp Mr κ (W k) (ν k) (B k) r T C lev γ j
          c u R A F H

/-- The contract of the broad source (unscaled form), precision before the degree. -/
def RelSourceAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ q : ℕ, 2 ≤ q ∧ ∀ precision : ℝ, 1 ≤ precision → ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
    ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 →
      ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
        grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
          RelSourceDs q precision loss cc J D d₁ κ₁ S η ρ m s gain δ₀ u0

/-- The relative source contract and the accepted o288 prove o265's frozen statement. -/
theorem staged_of_rel_source (hRS : RelSourceAssertion)
    (hcomp : Submission.Obl.k4_physical_parent_potential_candidates.CompletionAssertion) :
    StagedWeakAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ D₀
  obtain ⟨ccr, hccr, hrestore⟩ := restoration_exponent
  obtain ⟨q, hq2, hRS⟩ := hRS hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨precision, hprec, h288⟩ := hcomp hmk q hq2 ccr hccr d₁ ρ hd₁ hd₁1 hρ hdρ
  obtain ⟨D, hD₀, hRS⟩ := hRS precision hprec (max D₀ (max 5186 (864 * (2 * (q + 2)) + 2)))
  refine ⟨D, le_trans (le_max_left _ _) hD₀, ?_⟩
  have hDmin : max 5186 (864 * (2 * (q + 2)) + 2) ≤ D := le_trans (le_max_right _ _) hD₀
  intro J hJ hjet e0 he0
  obtain ⟨loss, hloss, hloss1, h288⟩ := h288 D hDmin J hJ hjet
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgain, hds⟩ := hRS J hJ hjet loss hloss hloss1 e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgain, ?_⟩
  have hgain0 : 0 < gain := hgrid.2.1
  have hgain8 : gain ≤ 1/8 := hgrid.2.2.1
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  obtain ⟨Mr, M₀, D₀', hds⟩ := hds N K L d W ω ν E P B f g G hpb hprof Mp Dp
  obtain ⟨hN2, hNtend, -, hL, -, -, -, -, hfam, -⟩ := hpb
  beta_reduce at hfam
  obtain ⟨Mpb, Dpb, hMD⟩ := hfam
  have hνprob : ∀ k γ, IsProbabilityMeasure (ν k γ) := fun k γ => ((hMD k).2.2.2.1 γ).1
  have hBpos : ∀ k γ, 0 < B k γ := fun k γ => ((hMD k).2.2.2.1 γ).2.1
  -- o288's exponent, once for `(L, gain)`
  obtain ⟨Mc, hMc⟩ := h288 L gain hL hgain0 hgain8 Mr Dp Mr
  refine ⟨max M₀ (Mc + Mr), D₀', ?_⟩
  intro Mi Di hMi hDi τ hτ α hα hα1
  obtain ⟨σ, hσ, k₀, hds⟩ := hds Mi Di (le_trans (le_max_left _ _) hMi) hDi τ hτ α hα hα1
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨Nk₀, -, hNk₀⟩ := hMc Mc le_rfl (τ/2) (by positivity)
  have hev : ∀ᶠ k in Filter.atTop, Nk₀ ≤ N k ∧ (2:ℝ) ≤ N k ^ (τ/2) := by
    refine (hNtend.eventually_ge_atTop Nk₀).and ?_
    filter_upwards [hNtend.eventually_ge_atTop ((2:ℝ) ^ (2/τ))] with k hk
    calc (2:ℝ) = ((2:ℝ) ^ (2/τ)) ^ (τ/2) := by
          rw [← Real.rpow_mul (by norm_num)]
          have : 2 / τ * (τ / 2) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ N k ^ (τ/2) := Real.rpow_le_rpow (by positivity) hk (by positivity)
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max k₀ k₁, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass
  have hk₀ : k₀ ≤ k := le_of_max_le_left hk
  have hk₁' := hk₁ k (le_of_max_le_right hk)
  have hN1 : (1:ℝ) ≤ N k := le_trans (by norm_num) (hN2 k)
  rcases hds k hk₀ r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with
    (hexit | hnar) | hppp
  · exact Or.inl hexit
  · exact Or.inr (narrow_mono hnar hN1 (le_max_left _ _) le_rfl)
  · left; right
    obtain ⟨b, rA, jA, TA, cA, A_A, H₀, P0, hrA, hrArb, hroomL, hTT, hj, hjup,
      hAbA, hA0, hH₀m, hH₀H, hP0deg, hP0c, h2T, hMpr, hframe, hcenter, hcoeffR, hline, hcoeff,
      hpp⟩ := hppp
    obtain ⟨hκ1, -, -, -, -, -, -, hpb⟩ := hpath
    obtain ⟨-, -, hch⟩ := hpb b
    have hch' := hch
    obtain ⟨-, -, -, -, -, -, hAbm, -⟩ := hch'
    have hroom : r (lev b) + 2 * gain * L ≤ L := by
      have := mul_le_mul_of_nonneg_right hgain8 hL.le
      linarith
    have hT : ν k (γ b) A_A ≠ ⊤ := by
      have := hνprob k (γ b); exact measure_ne_top _ _
    obtain ⟨hprob, hjv, hrv, hroomv⟩ := virtual_instance_facts_rel (ν k (γ b)) A_A hA0 hT
      (rFrame (N k) rA jA TA cA (B k (γ b))) 0 L gain rA (r (lev b))
      (T (lev b)) TA jA (j b) hj hjup hrA hrArb hroom
    have hchv := ch_virtual (N k) Mp Dp Mr κ (T (lev b)) (j b) TA jA (r (lev b)) rA
      (B k (γ b)) (E k (γ b)) (c b) (u b) cA (Q b) (R b) (A b) (F b) _ hN1 hMpr (hBpos k (γ b))
      (by linarith) hTT hj hch hcenter hframe hcoeffR hline
    have hcdv := hNk₀ (N k) hk₁'.1 1
      (fun _ => tanPrior (rFrame (N k) rA jA TA cA (B k (γ b))) 0 (ν k (γ b)) A_A)
      (fun _ => 1) (2 * κ) (fun _ => r (lev b) - rA) (fun _ => T (lev b) - TA) 1
      (fun _ => 0) (fun _ => 0) (fun _ => j b - jA * 2 ^ (T (lev b) - TA))
      (fun _ => ((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)) (fun _ => u b)
      (fun _ => ((2:ℝ)^TA) • Q b)
      (fun _ => (rFrame (N k) rA jA TA cA (B k (γ b))).normTest (Split.δ (N k) rA) (R b))
      (fun _ => tanLine (rFrame (N k) rA jA TA cA (B k (γ b))) 0 '' A b)
      (fun _ => tanEvent (rFrame (N k) rA jA TA cA (B k (γ b))) 0 '' F b)
      (fun _ => tanEvent (rFrame (N k) rA jA TA cA (B k (γ b))) 0 '' H₀) _ 0 P0
      (by linarith) h2T hprob one_pos (one_le_pow₀ hN1) (by simpa using one_le_pow₀ hN1)
      hP0deg hP0c hchv hjv hrv hroomv hpp
    have hcoeff' : 81 * |Split.δ (N k) rA| * (N k) ^ Mc * residualBudget 0 1 ^ 2 *
        (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
          (B k (γ b) / Split.δ (N k) rA)).substBudget ^ 2 ≤ (N k) ^ Mi := by
      have hpos : 0 ≤ (N k) ^ Mc := by positivity
      calc 81 * |Split.δ (N k) rA| * (N k) ^ Mc * residualBudget 0 1 ^ 2 *
            (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
              (B k (γ b) / Split.δ (N k) rA)).substBudget ^ 2
          = (N k) ^ Mc * (81 * |Split.δ (N k) rA| * residualBudget 0 1 ^ 2 *
            (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
              (B k (γ b) / Split.δ (N k) rA)).substBudget ^ 2) := by ring
        _ ≤ (N k) ^ Mc * (N k) ^ Mr := mul_le_mul_of_nonneg_left hcoeff hpos
        _ = (N k) ^ (Mc + Mr) := by rw [pow_add]
        _ ≤ (N k) ^ Mi := pow_le_pow_right₀ hN1 (le_trans (le_max_right _ _) hMi)
    have htwo : (2:ℝ) ≤ N k ^ (τ - τ/2) := by
      have : τ - τ/2 = τ/2 := by ring
      rw [this]; exact hk₁'.2
    have hsf : ∀ w, SFinite (ν k w) := fun w => by have := hνprob k w; infer_instance
    exact cd_original_of_virtual_cd_rel ccr hrestore cc J D hjet (W k) (ν k) (B k) r T C lev γ j
      A H b A_A H₀ hAbm hAbA hA0 hT hH₀m hH₀H cA 0 jA TA hTT hj (N k) L d₁ ρ gain τ (τ/2)
      rA Mi Mc (hBpos k (γ b)) (hN2 k) hL.le hroomL (by linarith) htwo hcoeff' hcdv

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
