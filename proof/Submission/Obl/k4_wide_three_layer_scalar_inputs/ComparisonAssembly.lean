import Submission.Obl.k4_wide_three_layer_scalar_inputs.WitnessCounts
import Submission.Obl.k4_wide_three_layer_scalar_inputs.WitnessPrediction

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context

open Set MeasureTheory Filter
open Inherited.Native Inherited.Core

noncomputable section

open scoped Classical

variable {α : Type} [MeasurableSpace α] (W : Context α)

/-- The concrete original coarse/fine witnesses provide all fields of
the compared block, with one common law and the original block prefix. -/
theorem comparedBlock_of_witnesses {Rcap H C chartError : ℝ}
    (P : Support.BlockPrefix W.cfg W.k W.s H) (hi : P.i = W.i)
    (hB : BlocksAt W.cfg.comparisonData W.k W.s Rcap)
    (hb : Measurable (W.cfg.b W.k)) (hK : 1 ≤ W.cfg.K W.k) (hN : 0 < W.cfg.N W.k)
    (hχ : 0 < W.χ) (hχm : W.χ ≤ W.m)
    (hle : P.lam ≤ W.layers.ρs) (hpos : 0 < P.lam univ)
    (hhor : ∀ᵐ p ∂P.lam, |W.cfg.b W.k p.1 4 + W.cfg.b W.k p.1 0| ≤ W.ζ)
    (hkeys : ∀ᵐ p ∂P.lam, slotKey (W.cfg.b W.k) W.χ W.m W.t₀ p.1 ∈ W.KB)
    (hgood : ∀ᵐ p ∂P.lam, p ∉ shortBad W.cfg.comparisonData W.k W.s W.datum
      W.m W.K₁ W.Mst W.KB)
    (hpc : ∀ γ e, |W.predictionPC P.L γ e| ≤ H)
    (htc : ∀ γ e, |W.predictionTC P.L γ e| ≤ H)
    (hfit : W.PredictionFits P.L chartError)
    (hfit1 : (W.cfg.N W.k ^ W.ε * W.cfg.N W.k ^ (-(W.s + W.u)) + W.freezingError) /
      W.a + chartError ≤ H * W.cfg.N W.k ^ (-W.u))
    (hfit2 : (W.cfg.N W.k ^ W.ε * W.cfg.N W.k ^ (-(W.s + W.v)) + W.freezingError) /
      W.a + chartError ≤ H * W.cfg.N W.k ^ (-W.v))
    (hC : 0 ≤ C) (hCbudget : 14 * W.cfg.K W.k * C ≤ H)
    (hcount : ∀ key ∈ W.KB, ((W.coarseCandidates key).card : ℝ) ≤ C)
    (hfine1 : ∀ γ, ((W.offsetBins γ 1 W.u).card : ℝ) ≤ H * W.cfg.N W.k ^ (W.cfg.d * W.u))
    (hfine2 : ∀ γ, ((W.offsetBins γ 2 W.v).card : ℝ) ≤ H * W.cfg.N W.k ^ (W.cfg.d * W.v)) :
    Nonempty (Support.ComparedBlock W.cfg W.k W.s W.u W.v W.χ H) := by
  have hsupp : ∀ᵐ p ∂P.lam,
      p.1 ∈ W.cfg.B W.k W.s W.i ∧ p.2 ∈ Icc W.t₀ (W.t₀ + W.q) := by
    filter_upwards [P.lam_supp] with p hp
    simpa only [hi, t₀, q, slotStart, slotLen] using hp
  have hcover := W.occurrence_cover P.lam hle hsupp hhor hkeys hgood
  have hne : P.lam ≠ 0 := by intro hz; simpa [hz] using hpos
  letI : NeZero P.lam := ⟨hne⟩
  obtain ⟨p₀, fallback, -⟩ := hcover.exists
  have hframe := W.predictionFrame_eq_prefix P hi
  apply P.of_partition W.u W.v W.χ W.Coarse W.Label W.occurrence
    (W.occurrence_measurable hB hb) W.occurrence_disjoint fallback hcover
    (fun x => x.1.1) W.chart (W.predictionTC P.L) (W.predictionPC P.L)
    (fun x => W.physicalOffset x.1.1 1 x.1.2.1 / W.a)
    (fun x => W.physicalOffset x.1.1 2 x.1.2.2 / W.a) htc hpc
  · intro x
    exact Filter.Eventually.of_forall fun p hp =>
      Prod.ext (congrFun hp.2.2.2.2 0) (congrFun hp.2.2.2.2 1)
  · intro x
    filter_upwards [hhor, hsupp] with p hh hs hp
    have hf := hfit x.1.1 1 x.1.2.1 x.2.1 p.1 p.2 hp.2.2.1 hp.2.2.2.2 hh hs.2
    rw [hframe] at hf
    exact hf.trans hfit1
  · intro x
    filter_upwards [hhor, hsupp] with p hh hs hp
    have hf := hfit x.1.1 2 x.1.2.2 x.2.2 p.1 p.2 hp.2.2.2.1 hp.2.2.2.2 hh hs.2
    rw [hframe] at hf
    exact hf.trans hfit2
  · intro z3 z0
    obtain ⟨G, hcard, hG⟩ := W.coarse_menu_of_key_counts hB hK hN hχ hχm hC hcount z3 z0
    refine ⟨G, hcard.trans hCbudget, ?_⟩
    intro x
    exact Filter.Eventually.of_forall fun p hp h3 h0 => hG x.1.1
      (Prod.ext ((congrFun hp.2.2.2.2 0).symm.trans h3)
        ((congrFun hp.2.2.2.2 1).symm.trans h0))
  · intro z3 z0 γ
    refine ⟨W.offsetBins γ 1 W.u, hfine1 γ, ?_⟩
    intro x
    exact Filter.Eventually.of_forall fun p hp h3 h0 hcrs => by
      have hm := W.mem_offsetBins x.1.1 1 W.u x.1.2.1 x.2.1
      simpa only [hcrs] using hm
  · intro z3 z0 γ
    refine ⟨W.offsetBins γ 2 W.v, hfine2 γ, ?_⟩
    intro x
    exact Filter.Eventually.of_forall fun p hp h3 h0 hcrs => by
      have hm := W.mem_offsetBins x.1.1 2 W.v x.1.2.2 x.2.2
      simpa only [hcrs] using hm

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context
