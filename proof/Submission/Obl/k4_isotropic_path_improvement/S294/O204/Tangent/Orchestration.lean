-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Orchestration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit c3fccb87c, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/Orchestration.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- The top-level orchestration of the virtual route to o265 (x1078, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Assembly

/-!
# o265 from a virtual source and o288

`VirtualSourceAssertion` is the contract for the broad source of the isotropic route: in the
quantifier order of o294 (potential degree first, then the relation degree, the jet exponent,
any precision and loss, and the grid), every late sample of every admissible original-law
problem returns the original width/candidate exits, the narrow atlas, or a `VirtualPPP`
certificate: a packet `b`, an ancestor at a grid level `iA`, and a physical potential packet
(o288's `PhysicalPotentialPacket`) for the one-packet virtual instance below that ancestor, with
all size budgets at one exponent `Mr` chosen before the output format.

`staged_of_virtual_source`: this contract and the accepted o288 prove o265's frozen
`StagedWeakAssertion`. The virtual candidate of o288 is taken at the restoration exponent
(`restoration_exponent`) and returned by `cd_original_of_virtual_cd`; the chart hypothesis of
o288 at the virtual packet is `ch_virtual`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The isotropic frame of an ancestor at grid depth `sA * L`. -/
abbrev vFrame (N L sA : ℝ) (jA TA : ℕ) (cA : P2) (B : ℝ) : PFrame :=
  virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA (B / Split.δ N (sA * L))

/-- The certificate a broad source returns at one late sample. -/
def VirtualPPP (q : ℕ) (precision loss : ℝ) (N L d₁ gain : ℝ) (m : ℕ) (s : ℕ → ℝ)
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
    Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket q precision loss
      N (L - s iA * L) d₁ (gain * L / (L - s iA * L)) (2 * κ)
      (tanPrior (vFrame N L (s iA) jA TA cA (B (γ b))) 0 (ν (γ b)) A_A) 1
      (r (lev b) - s iA * L) (T (lev b) - TA) (j b - jA * 2 ^ (T (lev b) - TA))
      (((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)) (u b) P0
      (tanLine (vFrame N L (s iA) jA TA cA (B (γ b))) 0 '' A b)
      (tanEvent (vFrame N L (s iA) jA TA cA (B (γ b))) 0 '' F b)
      (tanEvent (vFrame N L (s iA) jA TA cA (B (γ b))) 0 '' H₀)

/-- The per-grid contract of the broad source. -/
def VirtualSourceDs (q : ℕ) (precision loss : ℝ) (cc J D : ℕ) (d₁ κ₁ S η ρ : ℝ) (m : ℕ)
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
        VirtualPPP q precision loss (N k) L d₁ gain m s Mp Mr κ (W k) (ν k) (B k) r T C lev γ j
          c u R A F H

/-- The contract of the broad source, in o294's quantifier order. -/
def VirtualSourceAssertion : Prop :=
  mk → ∀ cc : ℕ, 1 ≤ cc → ∀ d₁ κ₁ S η ρ : ℝ,
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ q : ℕ, 2 ≤ q ∧ ∀ D₀ : ℕ, ∃ D : ℕ, D₀ ≤ D ∧ max 5186 (864 * (2 * (q + 2)) + 2) ≤ D ∧
    ∀ J : ℕ, 1 ≤ J → JointJetBound D J →
    ∀ precision : ℝ, 1 ≤ precision → ∀ loss : ℝ, 0 < loss → loss ≤ 1 → ∀ e0 : ℝ, 0 < e0 →
      ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ u0 : ℝ),
        grid κ₁ ρ m s gain δ₀ u0 ∧ gain ≤ e0 ∧
          VirtualSourceDs q precision loss cc J D d₁ κ₁ S η ρ m s gain δ₀ u0



/-- o288's conclusion at one value of `Nk`, for all data. -/
def O288At (q ccr J D : ℕ) (precision loss : ℝ) (d₁ ρ L gain : ℝ) (Mp Dp Mr Mi : ℕ)
    (τ Nk : ℝ) : Prop :=
  ∀ W : ℕ,
  ∀ (ν : Fin W → MeasureTheory.Measure Ln) (B : Fin W → ℝ) (κ : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (c u : Fin C → P2) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → Po) (A : Fin C → Set Ln) (F : Fin C → Set Ev)
    (H : Fin W → Set Ev) (ex : Prop) (b : Fin C) (P0 : Po),
    1 ≤ κ →
    (2 : ℝ) ^ T (lev b) ≤ Nk ^ Mr →
    MeasureTheory.IsProbabilityMeasure (ν (γ b)) →
    0 < B (γ b) → B (γ b) ≤ Nk ^ Mr → (B (γ b))⁻¹ ≤ Nk ^ Mr →
    P0.totalDegree ≤ 2 → (∀ e, |P0.coeff e| ≤ Nk ^ Mr) →
    Submission.Obl.k4_physical_parent_potential_candidates.ch Nk Mp Dp κ (T (lev b)) (j b : ℝ)
      (r (lev b)) (B (γ b)) Set.univ (c b) (u b) (Q b) (R b) (A b) (F b) ex →
    j b < 2 ^ T (lev b) → 0 ≤ r (lev b) → r (lev b) + 2 * gain * L ≤ L →
    Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket q precision loss
      Nk L d₁ gain κ (ν (γ b)) (B (γ b))
      (r (lev b)) (T (lev b)) (j b) (c b) (u b) P0 (A b) (F b) (H (γ b)) →
    Submission.Obl.k4_physical_parent_potential_candidates.cd ccr J D Nk L W ν B Mi d₁ ρ gain τ
      r T C lev γ j A H

/-- The virtual source contract and the accepted o288 prove o265's frozen statement. -/
theorem staged_of_virtual_source (hVS : VirtualSourceAssertion)
    (hcomp : Submission.Obl.k4_physical_parent_potential_candidates.CompletionAssertion) :
    StagedWeakAssertion := by
  intro hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ D₀
  obtain ⟨ccr, hccr, hrestore⟩ := restoration_exponent
  obtain ⟨q, hq2, hVS⟩ := hVS hmk cc hcc d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨precision, hprec, h288⟩ := hcomp hmk q hq2 ccr hccr d₁ ρ hd₁ hd₁1 hρ hdρ
  obtain ⟨D, hD₀, hDmin, hVS⟩ := hVS D₀
  refine ⟨D, hD₀, ?_⟩
  intro J hJ hjet e0 he0
  obtain ⟨loss, hloss, hloss1, h288⟩ := h288 D hDmin J hJ hjet
  obtain ⟨m, s, gain, δ₀, u0, hgrid, hgain, hds⟩ :=
    hVS J hJ hjet precision hprec loss hloss hloss1 e0 he0
  refine ⟨m, s, gain, δ₀, u0, hgrid, hgain, ?_⟩
  have hgain0 : 0 < gain := hgrid.2.1
  intro N K L d W ω ν E P B f g G hpb hprof Mp Dp
  obtain ⟨Mr, hds⟩ := hds N K L d W ω ν E P B f g G hpb hprof Mp Dp
  obtain ⟨hN2, hNtend, -, hL, -, -, -, -, hfam, -⟩ := hpb
  beta_reduce at hfam
  obtain ⟨Mpb, Dpb, hMD⟩ := hfam
  have hνprob : ∀ k γ, IsProbabilityMeasure (ν k γ) := fun k γ => ((hMD k).2.2.2.1 γ).1
  have hBpos : ∀ k γ, 0 < B k γ := fun k γ => ((hMD k).2.2.2.1 γ).2.1
  -- o288's exponent `Mc`, one for each grid level of the ancestor
  have hMc : ∀ i : Fin m, ∃ Mc : ℕ,
      (0 < L - s i * L ∧ 0 < gain * L / (L - s i * L) ∧ gain * L / (L - s i * L) ≤ 1/8) →
      ∀ Mi : ℕ, Mc ≤ Mi → ∀ τ : ℝ, 0 < τ → ∃ Nk₀ : ℝ, 2 ≤ Nk₀ ∧ ∀ Nk : ℝ, Nk₀ ≤ Nk →
        O288At q ccr J D precision loss d₁ ρ (L - s i * L) (gain * L / (L - s i * L))
          Mr Dp Mr Mi τ Nk := by
    intro i
    by_cases hv : 0 < L - s i * L ∧ 0 < gain * L / (L - s i * L) ∧
        gain * L / (L - s i * L) ≤ 1/8
    · obtain ⟨Mc, hMc⟩ := h288 (L - s i * L) (gain * L / (L - s i * L)) hv.1 hv.2.1 hv.2.2
        Mr Dp Mr
      exact ⟨Mc, fun _ => hMc⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose Mc hMc using hMc
  have hMcle : ∀ i, Mc i ≤ ∑ i, Mc i := fun i =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  obtain ⟨M₀, D₀', hM₀, hds⟩ := hds ((∑ i, Mc i) + Mr)
  refine ⟨M₀, D₀', ?_⟩
  intro Mi Di hMi hDi τ hτ α hα hα1
  obtain ⟨σ, hσ, k₀, hds⟩ := hds Mi Di hMi hDi τ hτ α hα hα1
  refine ⟨σ, hσ, ?_⟩
  -- o288's threshold `Nk₀`, one for each grid level, at the virtual exponent `∑ Mc` and `τ/2`
  have hNk : ∀ i : Fin m, ∃ Nk₀ : ℝ,
      (0 < L - s i * L ∧ 0 < gain * L / (L - s i * L) ∧ gain * L / (L - s i * L) ≤ 1/8) →
      ∀ Nk : ℝ, Nk₀ ≤ Nk →
        O288At q ccr J D precision loss d₁ ρ (L - s i * L) (gain * L / (L - s i * L))
          Mr Dp Mr (∑ i, Mc i) (τ/2) Nk := by
    intro i
    by_cases hv : 0 < L - s i * L ∧ 0 < gain * L / (L - s i * L) ∧
        gain * L / (L - s i * L) ≤ 1/8
    · obtain ⟨Nk₀, -, h⟩ := hMc i hv (∑ i, Mc i) (hMcle i) (τ/2) (by positivity)
      exact ⟨Nk₀, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose Nk₀ hNk₀ using hNk
  have hev : ∀ᶠ k in Filter.atTop, (∀ i : Fin m, Nk₀ i ≤ N k) ∧ (2:ℝ) ≤ N k ^ (τ/2) := by
    refine (Filter.eventually_all.mpr fun i => hNtend.eventually_ge_atTop (Nk₀ i)).and ?_
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
  rcases hds k hk₀ r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with hexit | hppp
  · exact hexit
  · left; right
    obtain ⟨b, iA, jA, TA, cA, A_A, H₀, P0, hiA, hs0, hsr, hroomv, hroom, hTT, hj, hjup, -,
      hAbA, hA0, hH₀m, hH₀H, hP0deg, hP0c, h2T, hMpr, hframe, hcenter, hcoeffR, hline, hcoeff,
      hpp⟩ := hppp
    have hN1 : (1:ℝ) ≤ N k := le_trans (by norm_num) (hN2 k)
    obtain ⟨hκ1, -, -, -, -, -, -, hpb⟩ := hpath
    obtain ⟨-, -, hch⟩ := hpb b
    have hch' := hch
    obtain ⟨-, -, -, -, -, -, hAbm, -⟩ := hch'
    have hgL : 0 < gain * L := mul_pos hgain0 hL
    have hrAL : s iA * L < L := by linarith
    have hLv : 0 < L - s iA * L := by linarith
    have hv : 0 < L - s iA * L ∧ 0 < gain * L / (L - s iA * L) ∧
        gain * L / (L - s iA * L) ≤ 1/8 := by
      refine ⟨hLv, div_pos hgL hLv, ?_⟩
      rw [div_le_iff₀ hLv]; linarith
    have hT : ν k (γ b) A_A ≠ ⊤ := by
      have := hνprob k (γ b); exact measure_ne_top _ _
    obtain ⟨hprob, hjv, hrv, hroomv'⟩ := virtual_instance_facts (ν k (γ b)) A_A hA0 hT
      (vFrame (N k) L (s iA) jA TA cA (B k (γ b))) 0 L gain (s iA * L) (r (lev b))
      (T (lev b)) TA jA (j b) hj hjup hrAL hsr hroom
    have hchv := ch_virtual (N k) Mp Dp Mr κ (T (lev b)) (j b) TA jA (r (lev b)) (s iA * L)
      (B k (γ b)) (E k (γ b)) (c b) (u b) cA (Q b) (R b) (A b) (F b) _ hN1 hMpr (hBpos k (γ b))
      (by linarith) hTT hj hch hcenter hframe hcoeffR hline
    have hcdv := hNk₀ ⟨iA, hiA⟩ hv (N k) (hk₁'.1 ⟨iA, hiA⟩) 1
      (fun _ => tanPrior (vFrame (N k) L (s iA) jA TA cA (B k (γ b))) 0 (ν k (γ b)) A_A)
      (fun _ => 1) (2 * κ) (fun _ => r (lev b) - s iA * L) (fun _ => T (lev b) - TA) 1
      (fun _ => 0) (fun _ => 0) (fun _ => j b - jA * 2 ^ (T (lev b) - TA))
      (fun _ => ((2:ℝ)^TA) • (c b + ((jA:ℝ)/(2:ℝ)^TA) • u b - cA)) (fun _ => u b)
      (fun _ => ((2:ℝ)^TA) • Q b)
      (fun _ => (vFrame (N k) L (s iA) jA TA cA (B k (γ b))).normTest
        (Split.δ (N k) (s iA * L)) (R b))
      (fun _ => tanLine (vFrame (N k) L (s iA) jA TA cA (B k (γ b))) 0 '' A b)
      (fun _ => tanEvent (vFrame (N k) L (s iA) jA TA cA (B k (γ b))) 0 '' F b)
      (fun _ => tanEvent (vFrame (N k) L (s iA) jA TA cA (B k (γ b))) 0 '' H₀) _ 0 P0
      (by linarith) h2T hprob one_pos (one_le_pow₀ hN1) (by simpa using one_le_pow₀ hN1)
      hP0deg hP0c hchv hjv hrv hroomv' hpp
    have hcoeff' : 81 * |Split.δ (N k) (s iA * L)| * (N k) ^ (∑ i, Mc i) *
        residualBudget 0 1 ^ 2 *
        (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
          (B k (γ b) / Split.δ (N k) (s iA * L))).substBudget ^ 2 ≤ (N k) ^ Mi := by
      have hpos : 0 ≤ (N k) ^ (∑ i, Mc i) := by positivity
      calc 81 * |Split.δ (N k) (s iA * L)| * (N k) ^ (∑ i, Mc i) *
            residualBudget 0 1 ^ 2 *
            (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
              (B k (γ b) / Split.δ (N k) (s iA * L))).substBudget ^ 2
          = (N k) ^ (∑ i, Mc i) * (81 * |Split.δ (N k) (s iA * L)| *
            residualBudget 0 1 ^ 2 *
            (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
              (B k (γ b) / Split.δ (N k) (s iA * L))).substBudget ^ 2) := by ring
        _ ≤ (N k) ^ (∑ i, Mc i) * (N k) ^ Mr := mul_le_mul_of_nonneg_left hcoeff hpos
        _ = (N k) ^ ((∑ i, Mc i) + Mr) := by rw [pow_add]
        _ ≤ (N k) ^ Mi := pow_le_pow_right₀ hN1 (le_trans hM₀ hMi)
    have htwo : (2:ℝ) ≤ N k ^ (τ - τ/2) := by
      have : τ - τ/2 = τ/2 := by ring
      rw [this]; exact hk₁'.2
    have hsf : ∀ w, SFinite (ν k w) := fun w => by have := hνprob k w; infer_instance
    exact cd_original_of_virtual_cd ccr hrestore cc J D hjet (W k) (ν k) (B k) r T C lev γ j A H
      b A_A H₀ hAbm hAbA hA0 hT hH₀m hH₀H cA 0 jA TA hTT hj (N k) L d₁ ρ gain τ (τ/2)
      (s iA * L) Mi (∑ i, Mc i) (hBpos k (γ b)) (hN2 k) hgain0.le (mul_nonneg hs0 hL.le) hrAL
      (by linarith) htwo hcoeff' hcdv

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
