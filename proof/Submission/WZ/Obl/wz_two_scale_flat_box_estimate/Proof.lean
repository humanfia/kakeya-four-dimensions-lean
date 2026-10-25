-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Proof.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Assembly
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.ScaleParameters
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Reduction
import Submission.WZ.Obl.wz_flat_factored_improvement.PacketNumerics

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric

set_option maxHeartbeats 800000 in
lemma flat_small_scale_from_estimate {σ ω : ℝ} (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : Estimate σ ω) : FlatSmallScaleConclusion σ ω := by
  have hBody := WangZahlLot.Obl.wz_flat_factored_improvement.body_estimate_of_tube_estimate
    hσ.le hσhalf hω hE
  intro ε hε
  obtain ⟨Af, ηf, df, hAf, hηf, hdf, _, Hf⟩ := fineBoxBound_of_body_estimate hBody
    (by positivity : 0 < ε / 4)
  obtain ⟨Ac, ηc, dc, hAc, hηc, hdc, _, Hc⟩ := coarseBoxBound_of_body_estimate hBody
    (by positivity : 0 < ε / 4)
  obtain ⟨dn, hdn, _, Hn⟩ := WangZahlLot.Obl.wz_flat_factored_improvement.tube_number_power_bound
  obtain ⟨s, d, hs, hd, HP⟩ := choose_assembly_parameters hε hω1 hηf hηc hdf hdc hdn
  refine ⟨Af * Ac, s, d, mul_pos hAf hAc, hs, hd, ?_⟩
  intro δ hδ hδ100 hδd n x v Y hA ρ hδρ hρ1 N y w f hC a b c hρa hab hbc hc hc8 hflat L z e g hB
  obtain ⟨K, Kc, hP⟩ := HP δ hδ hδ100 hδd
  have ha : 0 < a := hδ.trans_le (hδρ.trans hρa)
  have hδ1 : δ ≤ 1 := by linarith
  have haSmall := hP.smallBox a b ha hab (hbc.trans hc8) hflat
  have hnmax : (n : ℝ) ≤ δ ^ (-100 : ℝ) :=
    (Hn δ hδ hP.numberScale n x v (fun i => (hA.2.1 i).1)
      (fun i => (hA.2.1 i).2.1) hA.2.2.1).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num))
  exact two_scale_assembly hσ.le hσhalf hAf hAc Hf Hc hδ hδ1 hP.fineScale hP.coarseScale
    rfl hP.largeBudget hδρ hρa hab hbc hc hc8 haSmall K Kc hP.regularizationDepth
    hP.regularizationBudget hP.logarithmicBudget hP.bottomScale
    (hP.regularizationCut a b ha hab (hbc.trans hc8)) hP.fineDensity hP.coarseDensity hP.finalError
    x v Y y w f z e g hA hC hB hnmax

lemma conclusion_from_estimate {σ ω : ℝ} (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : Estimate σ ω) : Conclusion σ ω :=
  conclusion_of_flat_small_scale hσ.le hω.le hE
    (flat_small_scale_from_estimate hσ hσhalf hω hω1 hE)

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
