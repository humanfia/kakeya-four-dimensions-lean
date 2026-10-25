-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.StagesFinal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The outer assembly (session x1088).

`stagesProducer_of_lanes`: `StagesProducer tune` from the lanes holding eventually
(`Source.FinalTune.LanesEventually`), for any tuning paying the fixed core/jet and census powers
whose depth covers `NativeDesign.graphLowerCoeff`. At every pre-sample choice it takes
`σS = min` of the lanes' exponent and of the exponents of every eventual lemma
(`eventually_geom_le`, `eventually_brow_le`, `eventually_hcount_native`, the source factor of
the problem, and the fixed tails), and at every late sample applies `Source.SampleAt.sample_at`
with the fits of `Source.SampleFitsAt` and the window inequalities of `Source.SampleWindow`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.FinalTune
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFitsAt
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.BrowNumerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.CorePowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Route

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

/-- The doubled prepared tolerance pays the count of the core envelope. -/
theorem tau_le_count (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    {κ₁ d₁ precision loss gain δ₀ L budget : ℝ} {Ep : ℕ} (hL : 0 < L) (hloss : 0 < loss)
    (hgain : 0 < gain) (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) :
    2 * tauOf tune δ₀ L budget ≤
      2 * (loss * gain * L / ((Ep : ℝ) + 1) / 10000) / FixedSourcePowers.slack := by
  have hS0 : 0 < FixedSourcePowers.slack := FixedSourcePowers.slack_positive
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hE : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  have h1 : tolOf tune κ₁ d₁ Ep precision loss gain ≤
      loss * gain / (10000 * ((Ep : ℝ) + 1) * FixedSourcePowers.slack) := by
    unfold tolOf
    apply div_le_div₀ (by positivity) _ (by positivity) _
    · have : tune.budget κ₁ d₁ Ep precision loss * (loss * gain) ≤ 1 * (loss * gain) :=
        mul_le_mul_of_nonneg_right hB1 (by positivity)
      linarith [show tune.budget κ₁ d₁ Ep precision loss * loss * gain =
        tune.budget κ₁ d₁ Ep precision loss * (loss * gain) by ring]
    · apply mul_le_mul_of_nonneg_left hslack (by positivity)
  have h2 : tauOf tune δ₀ L budget ≤ δ₀ * L := min_le_left _ _
  have h3 : δ₀ * L ≤ loss * gain / (10000 * ((Ep : ℝ) + 1) * FixedSourcePowers.slack) * L :=
    mul_le_mul_of_nonneg_right (hδ.trans h1) hL.le
  have e : 2 * (loss * gain * L / ((Ep : ℝ) + 1) / 10000) / FixedSourcePowers.slack =
      2 * (loss * gain / (10000 * ((Ep : ℝ) + 1) * FixedSourcePowers.slack) * L) := by
    field_simp
  rw [e]
  linarith

/-- **`StagesProducer` from the eventual lanes.** -/
theorem stagesProducer_of_lanes (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    (hslackC : censusSlack ≤ tune.slack)
    (hdepth : ∀ κ₁ d₁ Ep precision loss, NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision ≤
      tune.depth κ₁ d₁ Ep precision loss)
    (hlanes : LanesEventually tune) : StagesProducer tune := by
  apply stagesProducer_of_stageAt
  intro hmk d₁ κ₁ ρ Ep precision loss e0 hd₁ hd₁1 hκ₁ hκ₁1 hρ hdρ hprec hloss hloss1 he0
    m s δ₀ C target indices hgrid hδtol hδm hm8 hgm htarget hstarget hm2 hC1 hCge hCle hCt hind
    d hd hprof Mp Dp budget hbud hbud1
  obtain ⟨σL, hσL, evL⟩ := hlanes hmk d₁ κ₁ ρ Ep precision loss e0 hd₁ hd₁1 hκ₁ hκ₁1 hρ hdρ hprec
    hloss hloss1 he0 m s δ₀ C target indices hgrid hδtol hδm hm8 hgm htarget hstarget hm2 hC1 hCge
    hCle hCt hind d hd hprof Mp Dp budget hbud hbud1
  -- the pre-sample facts
  have hL : 0 < d.L := hd.2.2.2.1
  have hNt : Tendsto d.N atTop atTop := hd.2.1
  have hgain : 0 < gainOf tune κ₁ d₁ Ep precision loss e0 := gainOf_pos hκ₁ hd₁1 hprec hloss he0
  have hδ₀ : 0 < δ₀ := hgrid.2.2.2.1
  have hm : 0 < m := by omega
  have hδg : δ₀ ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / 100 := hgrid.2.2.2.2.2.2.2.2.2.1
  have hmg : 1 / (m : ℝ) ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁ :=
    hgrid.2.2.2.2.2.2.2.2.1
  have hE1 : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  have hkexp : 0 < (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) := by positivity
  have hub0 : 0 ≤ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) := by
    unfold ubOf
    have := tune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  have hF0 : 0 ≤ (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) := Nat.cast_nonneg _
  have hρc0 : 0 ≤ (3 * δ₀ * (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) + 1 / (m : ℝ)) := by positivity
  have hD : 0 < loss * gainOf tune κ₁ d₁ Ep precision loss e0 / ((Ep : ℝ) + 1) := by positivity
  have hτpos : 0 < (tauOf tune δ₀ d.L budget) := by
    unfold tauOf
    have := zero_lt_one.trans_le tune.one_le_slack
    exact lt_min (by positivity) (by positivity)
  -- the eventual lemmas
  obtain ⟨σ1, hσ1, -, ev1⟩ := eventually_geom_le d.N hNt hδ₀ hL
  obtain ⟨σ2, hσ2, -, ev2⟩ := eventually_brow_le d.N hNt hL hδ₀.le hub0 hρc0 hD hd₁1.le
    (brow_rate tune hκ₁ hκ₁1 hloss hgain hδ₀.le hslackC hδtol hgm)
  obtain ⟨σ3, hσ3, -, ev3⟩ := eventually_hcount_native d.N hNt (budget := (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) / 10000)
    (f := (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1))) (by positivity) (by linarith)
  have evtail : ∀ᶠ k in atTop, (2 : ℝ) ^ 12 ≤ d.N k ^ ((loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) / 8) ∧
      4 ≤ d.N k ^ (gainOf tune κ₁ d₁ Ep precision loss e0 * d.L) ∧
      512 ≤ d.N k ^ (gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / 2) ∧
      mk4MeshFloorConstant ≤ d.N k ^ (gainOf tune κ₁ d₁ Ep precision loss e0 * d.L) ∧
      (m : ℝ) ≤ d.N k ^ (2 * (tauOf tune δ₀ d.L budget)) := by
    refine (((tendsto_rpow_atTop (by positivity : 0 < (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) / 8)).comp hNt).eventually
      (eventually_ge_atTop _)).and ((((tendsto_rpow_atTop (by positivity :
        0 < gainOf tune κ₁ d₁ Ep precision loss e0 * d.L)).comp hNt).eventually
      (eventually_ge_atTop _)).and ((((tendsto_rpow_atTop (by positivity :
        0 < gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / 2)).comp hNt).eventually
      (eventually_ge_atTop _)).and ((((tendsto_rpow_atTop (by positivity :
        0 < gainOf tune κ₁ d₁ Ep precision loss e0 * d.L)).comp hNt).eventually
      (eventually_ge_atTop _)).and (((tendsto_rpow_atTop (by positivity : 0 < 2 * (tauOf tune δ₀ d.L budget))).comp
        hNt).eventually (eventually_ge_atTop _)))))
  -- the exponent of the paths
  obtain ⟨σS, hσSdef⟩ : ∃ x, x = min (min σL σ1) (min σ2 (min σ3 (min ((loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) / 8)
      (gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / 2)))) := ⟨_, rfl⟩
  have hσS : 0 < σS := by
    rw [hσSdef]
    exact lt_min (lt_min hσL hσ1) (lt_min hσ2 (lt_min hσ3 (lt_min (by positivity)
      (by positivity))))
  have hσSL : σS ≤ σL := by rw [hσSdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hσS1 : σS ≤ σ1 := by rw [hσSdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hσS2 : σS ≤ σ2 := by rw [hσSdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hσS3 : σS ≤ σ3 := by
    rw [hσSdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσSK : σS ≤ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) / 8 := by
    rw [hσSdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hσSa : σS ≤ gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / 2 := by
    rw [hσSdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  have evK : ∀ᶠ k in atTop, d.K k ≤ d.N k ^ σS := hd.2.2.1.2 σS hσS
  refine ⟨σS, hσS, ?_⟩
  filter_upwards [evL, ev1, ev2, ev3, evtail, evK] with k hLk h1 h2 h3 htail hKk
  obtain ⟨h12, h4, h512, hconst, hmN⟩ := htail
  have hN1 : 1 < d.N k := by linarith [hd.1 k]
  have hw : ∀ {σ x : ℝ}, σS ≤ σ → x ≤ d.N k ^ σS → x ≤ d.N k ^ σ := fun hσ hx =>
    hx.trans (Real.rpow_le_rpow_of_exponent_le hN1.le hσ)
  have hτδ : (tauOf tune δ₀ d.L budget) ≤ δ₀ * d.L := min_le_left _ _
  -- the geometry envelope at this sample
  have hgeom : ∀ κ Kd τ : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σS → Kd ≤ d.N k ^ σS → 0 ≤ τ → τ ≤ δ₀ * d.L →
      KgeomAt κ Kd (d.N k) δ₀ d.L τ ≤ d.N k ^ (3 * δ₀ * d.L) := by
    intro κ Kd τ hκ hκN hKdN hτ0 hτ
    have h := h1 κ Kd τ hκ (hw hσS1 hκN) (hw hσS1 hKdN) hτ0 hτ
    unfold KgeomAt
    rwa [← two_mul]
  -- the row bound at this sample
  have hrow : ∀ κ Kd τ : ℝ, 1 ≤ κ → κ ≤ d.N k ^ σS → 1 ≤ Kd → Kd ≤ d.N k ^ σS → 0 ≤ τ →
      τ ≤ δ₀ * d.L →
      28 * KgAt κ Kd (d.N k) δ₀ d.L τ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) d₁ m ^ 6 ≤ d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) := by
    intro κ Kd τ hκ hκN hKd hKdN hτ0 hτ
    obtain ⟨hK24, hκK, hNK⟩ := KgeomAt_facts (Kd := Kd) (δ₀ := δ₀) (L := d.L) hκ hN1.le hτ0
    have hKc1 : 1 ≤ KcenAt κ Kd (d.N k) δ₀ d.L τ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m := by
      unfold KcenAt; exact (censusK_ge (by linarith) _ _ _ _ _).1
    have hKc : KcenAt κ Kd (d.N k) δ₀ d.L τ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m ≤ d.N k ^ ((3 * δ₀ * (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) + 1 / (m : ℝ)) * d.L) := by
      unfold KcenAt
      exact censusK_le_rpow hK24 hκ hκK hN1.le hNK (by positivity) hL.le (by positivity)
        (hgeom κ Kd τ hκ hκN hKdN hτ0 hτ)
    have h := h2 κ Kd (KcenAt κ Kd (d.N k) δ₀ d.L τ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0)) m) τ hκ (hw hσS2 hκN) hKd
      (hw hσS2 hKdN) hKc1 hKc hτ0 hτ
    have e : loss * gainOf tune κ₁ d₁ Ep precision loss e0 / ((Ep : ℝ) + 1) * d.L = (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) := by
      ring
    rw [e] at h
    unfold KgAt CbandAt
    exact h
  -- the doubled tolerance pays the core envelope's count
  have htauB : 2 * (tauOf tune δ₀ d.L budget) ≤ 2 * ((loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) / 10000) / FixedSourcePowers.slack :=
    tau_le_count tune hslack hL hloss hgain hδtol
  have hτ0 : 0 ≤ (tauOf tune δ₀ d.L budget) := hτpos.le
  have hX₀ : (0 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by
    have : (0 : ℝ) ≤ precision := by linarith
    positivity
  have hwinA := listA_window tune (C := C) hκ₁ hκ₁1 hd₁ hd₁1 hprec hloss hloss1 he0 hδ₀.le hm hslackC
    hδtol hδg hgm hmg (hdepth κ₁ d₁ Ep precision loss) hCge
  have hwinB := listB_window tune (C := C) hκ₁ hκ₁1 hd₁ hd₁1 hprec hloss hloss1 he0 hδ₀.le hm hslackC
    hδtol hδg hmg hCge
  have hband_rate := band_rate tune hκ₁ hκ₁1 hd₁ hd₁1 hprec hloss hloss1 he0
    (hdepth κ₁ d₁ Ep precision loss)
  exact sample_at tune hslack hslackC hd₁ hd₁1 hκ₁ hκ₁1 hρ hdρ hprec hloss hloss1 he0 hgrid hδtol
    hδm hm8 hgm htarget hstarget hm2 hC1 hCge hCle hCt hind hd hprof hbud hbud1 hσS hKk
    (fun κ source τ hκ hκN hsN hτ0' hτ => h1 κ source τ hκ (hw hσS1 hκN) (hw hσS1 hsN) hτ0' hτ)
    hmN hσSK h12 (by linarith)
    (fun κ Kd Kc τ hκ hκN hKd hKdN hKc hKcN hτ0' hτ => by
      have h := h2 κ Kd Kc τ hκ (hw hσS2 hκN) hKd (hw hσS2 hKdN) hKc hKcN hτ0' hτ
      have e : loss * gainOf tune κ₁ d₁ Ep precision loss e0 / ((Ep : ℝ) + 1) * d.L = (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)) := by
        ring
      rwa [e] at h)
    (fun κ source tolerance hκ hκN hsN htol0 htol =>
      h3 κ source tolerance hκ (hw hσS3 hκN) (hw hσS3 hsN) htol0 (htol.trans htauB))
    (fun κ Kd hκ hκN hKd hKdN => listA_at (Ep := Ep) hN1 hL hκ (by linarith) hκ₁ hd₁ hd₁1 hprec
      hloss1 hgain hτ0 hδ₀.le hub0 (hgeom κ Kd _ hκ hκN hKdN hτ0 hτδ)
      (hrow κ Kd _ hκ hκN hKd hKdN hτ0 hτδ) (hw hσSa hκN) h512 hconst h4 hwinA)
    (fun κ Kd εv hκ hκN hKd hKdN hεv => listB_at hN1 hL hκ hκ₁ hX₀ hgain hτ0 hδ₀.le hub0
      (hgeom κ Kd _ hκ hκN hKdN hτ0 hτδ) hεv h4 hwinB)
    (fun κ Kd hκ hκN hKd hKdN => band_at (Ep := Ep) hN1 hL hκ (by linarith) hκ₁ hd₁ hd₁1 hprec
      hloss1 hgain (hrow κ Kd _ hκ hκN hKd hKdN hτ0 hτδ) (hw hσSa hκN) h512 hconst hband_rate)
    (hLk σS hσS hσSL)

/-- **`StagesProducer` at the final tuning**, from the eventual lanes. -/
theorem stagesProducer_final (hlanes : LanesEventually finalTune) : StagesProducer finalTune :=
  stagesProducer_of_lanes finalTune finalTune_slack finalTune_censusSlack
    (fun κ₁ d₁ Ep precision loss => depth_ge_graphLower κ₁ d₁ Ep precision loss) hlanes

/-- **The staged weak assertion (o265's statement)** from the eventual lanes. -/
theorem staged_of_lanes (hlanes : LanesEventually finalTune) : O204.Split.StagedWeakAssertion :=
  staged_of_stagesProducer finalTune (stagesProducer_final hlanes)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
