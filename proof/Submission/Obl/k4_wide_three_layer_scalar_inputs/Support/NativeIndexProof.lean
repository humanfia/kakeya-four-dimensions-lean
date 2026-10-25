import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.NativeIndex

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

namespace ComparedBlock

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v M H θ : ℝ}

/-- The original consensus law supplies the common field, its corrected
fine fit, and the complete residual support on one original block. -/
theorem native_index_after_consensus (hv : cfg.Valid)
    (CB : ComparedBlock cfg k s u v (cfg.N k ^ (-M)) H)
    (E : NativeIndexScales)
    (num : NativeIndexBudget (cfg.N k) (cfg.K k) cfg.d cfg.S cfg.κ
      s u v M H CB.frame.q θ E)
    (hF : Field.FieldAt cfg.S E.C₀ E.A (nativeTau cfg.d u) E.εF E.η (cfg.N k))
    (hcap : CapsAt cfg k E.R) (hB : BlocksAt cfg k s E.R)
    (hBe : BlocksAt cfg k E.se E.R)
    (hnest : ∀ j : Fin (cfg.n k E.se), ∃ h : Fin (cfg.n k s),
      cfg.A k E.se j ⊆ cfg.A k s h ∧
        Data.I (cfg.T k E.se) (cfg.j k E.se j) ⊆ Data.I (cfg.T k s) (cfg.j k s h))
    (F : NativeConsensusData CB E) :
    Submission.Obl.k4_wide_three_layer_scalar_inputs.Data.ExtractionAt
      cfg k θ s v E.m E.J := by
  classical
  have hN : 1 ≤ cfg.N k := by linarith [hv.scale k]
  have hN₀ : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hN₁ : 1 < cfg.N k := by linarith [hv.scale k]
  have hK : 1 ≤ cfg.K k := hv.subpower.1 k
  have hK₀ : 0 < cfg.K k := zero_lt_one.trans_le hK
  obtain ⟨hb, hν, hπ, hμ, hρμ, -⟩ := hv.basic k
  let : IsProbabilityMeasure (cfg.ν k) := hν
  let : IsProbabilityMeasure (cfg.π k) := hπ
  have hχ : 0 < cfg.N k ^ (-M) := Real.rpow_pos_of_pos hN₀ _
  have hδ : 0 < cfg.N k ^ (-E.B) := Real.rpow_pos_of_pos hN₀ _
  have hχ₁ : cfg.N k ^ (-M) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr num.M_nonneg)
  have hδ₁ : cfg.N k ^ (-E.B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN
      (neg_nonpos.mpr (num.M_nonneg.trans num.M_B))
  have hq : 0 < CB.frame.q := by dsimp [frame, blockFrame]; positivity
  have hq₁ : CB.frame.q ≤ 1 := by
    dsimp [frame, blockFrame]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hR₁ : E.R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ num.R_one
  have hdom : F.lam ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume :=
    F.le.trans (CB.lam_le.trans (hρμ.trans hμ))
  have hvel : ∀ᵐ p ∂F.lam, |cfg.b k p.1 3| ≤ cfg.K k :=
    ae_mono (F.le.trans (CB.lam_le.trans hρμ)) (ae_original_velocity_bound hv k)
  have hagree : ∀ᵐ p ∂F.lam,
      let Q := sigmaState CB.frame (cfg.N k ^ (-E.B)) (cfg.N k ^ (-2 * u))
        (cfg.N k ^ (-2 * u)) (cfg.b k p.1) p.2
      |lin1 (CB.tc (CB.crs (CB.lab p.1))) (stateCenter (cfg.N k ^ (-E.B)) Q 0)
          (stateCenter (cfg.N k ^ (-E.B)) Q 1) -
        lin1 (CB.tc (F.center Q)) (stateCenter (cfg.N k ^ (-E.B)) Q 0)
          (stateCenter (cfg.N k ^ (-E.B)) Q 1)| +
        |CB.tc (CB.crs (CB.lab p.1)) 3 - CB.tc (F.center Q) 3| <
          cfg.N k ^ (-nativeTau cfg.d u) := F.agree
  have hcell := CB.field_base_cell_cap hcap hB hN₀ hK hb hπ hρμ F.lam F.le
    hδ num.field_base_width num.r_lo num.r_hi num.cell_lo num.cell_hi hR₁ num.R_one
    CB.L_bd num.cell_hidden_width num.cell_mesh num.cell_lip num.cell_budget
  have hfrost := field_frostman_from_caps hcap hN₁ hK₀.le hv.palette_pos
    num.frost_v₀_pos num.frost_v₀_B num.frost_dimension num.frost_K
    num.frost_lo num.B_hi hR₁ num.R_one
  have hχq : cfg.N k ^ (-M) / CB.frame.q ≤ 1 :=
    (div_le_one hq).mpr num.chart_length
  have hAχ : cfg.N k ^ (-E.A) ≤ cfg.N k ^ (-M) :=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg num.M_A)
  have hAχq : cfg.N k ^ (-E.A) ≤ cfg.N k ^ (-M) / CB.frame.q :=
    hAχ.trans (le_div_self hχ.le hq hq₁)
  have hδdef : cfg.N k ^ (-E.B) = cfg.N k ^ (-(E.C₀ * (E.A + nativeTau cfg.d u))) := by
    rw [num.field_mesh]
  obtain ⟨C, hC, hmass⟩ := CB.field_step hF hN₀ hδdef hδ₁ hχ hχ₁ hχq hAχ hAχq
    hK num.field_K num.field_H num.field_fit hb hB (true_assignment_ne_zero hB hN₀ hK₀ CB.i)
    F.lam F.le hdom hvel F.mass F.center hagree F.state hcell hfrost
  let lam := CB.fieldLaw F.center (cfg.N k ^ (-E.B)) (cfg.N k ^ (-2 * u))
    (cfg.N k ^ (-2 * u)) C (cfg.N k ^ E.εF * cfg.N k ^ (-nativeTau cfg.d u)) F.lam
  have hlam : lam ≤ CB.lam := (CB.fieldLaw_le _ _ _ _ _ _ _).trans F.le
  have hmass' : ENNReal.ofReal (cfg.N k ^ (-E.εF)) *
      (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)) ≤ lam univ := by
    rw [show lam univ = F.lam (CB.fieldCapture F.center (cfg.N k ^ (-E.B))
      (cfg.N k ^ (-2 * u)) (cfg.N k ^ (-2 * u)) C
      (cfg.N k ^ E.εF * cfg.N k ^ (-nativeTau cfg.d u))) from
        CB.fieldLaw_mass _ _ _ _ _ _ _]
    exact hmass
  have hU : ∀ᵐ p ∂F.lam, |CB.frame.tr (cfg.b k p.1) p.2| ≤ cfg.K k := by
    filter_upwards [ae_mono F.le CB.ae_good] with p hp
    exact (CB.good_bounds hB hN₀ hK CB.hL hp).2.2.1
  have hfit := CB.fieldLaw_corrected_fit F.center
    (E := cfg.N k ^ E.εF * cfg.N k ^ (-nativeTau cfg.d u)) hδ C hb F.lam F.le hU
    (hagree.mono fun p hp => hp.le)
  have hfit' : ∀ᵐ p ∂lam,
      |CB.frame.resid (cfg.b k p.1) p.2 - transv C (CB.frame.zt p.2)
          (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2) -
        quadZ (CB.pc (CB.crs (CB.lab p.1))) (CB.frame.zt p.2)
          (CB.frame.zZ (cfg.b k p.1) p.2) - CB.D2 (CB.lab p.1)| ≤
        (8 * H * (cfg.K k) ^ 2) * cfg.N k ^ (-v) :=
    hfit.mono fun p hp => hp.trans num.recovery
  have hdeep_m : 100 * (cfg.K k) ^ 7 * cfg.N k ^ (2 * s - cfg.κ * E.se) ≤
      cfg.N k ^ (-E.m) := num.deep_coordinates.trans
        (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg num.m_B))
  have hvar : ∀ j : Fin (cfg.n k E.se),
      ∀ p ∈ (cfg.B k E.se j ×ˢ Data.I (cfg.T k E.se) (cfg.j k E.se j)) ∩
        (cfg.B k s CB.i ×ˢ Data.I (cfg.T k s) (cfg.j k s CB.i)),
      ∀ p' ∈ (cfg.B k E.se j ×ˢ Data.I (cfg.T k E.se) (cfg.j k E.se j)) ∩
        (cfg.B k s CB.i ×ˢ Data.I (cfg.T k s) (cfg.j k s CB.i)),
      |CB.frame.zt p.2 - CB.frame.zt p'.2| ≤ cfg.N k ^ (-E.m) ∧
      |CB.frame.zZ (cfg.b k p.1) p.2 - CB.frame.zZ (cfg.b k p'.1) p'.2| ≤
        cfg.N k ^ (-E.m) ∧
      |(CB.frame.resid (cfg.b k p.1) p.2 - transv C (CB.frame.zt p.2)
          (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2)) -
        (CB.frame.resid (cfg.b k p'.1) p'.2 - transv C (CB.frame.zt p'.2)
          (CB.frame.zZ (cfg.b k p'.1) p'.2) (CB.frame.tr (cfg.b k p'.1) p'.2))| ≤
        cfg.N k ^ (-v) := by
    intro j p hp p' hp'
    have hd := deep_coord_variation_bound hv num.s_nonneg num.se_nonneg hB hBe
      CB.i CB.L CB.hL j hp hp'
    have hc := deep_corrected_variation_bound hv num.s_nonneg num.se_nonneg hB hBe
      CB.i CB.L CB.hL C (Real.one_le_rpow hN num.εF_nonneg) hC j hp hp'
    refine ⟨?_, ?_, hc.trans num.deep_corrected⟩
    · simpa [coords, frame] using (hd 0).trans hdeep_m
    · simpa [coords, frame] using (hd 1).trans hdeep_m
  have hHH : H ≤ 8 * H * (cfg.K k) ^ 2 := by
    have hKsq : 1 ≤ (cfg.K k) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hKsq (zero_le_one.trans CB.H_one)
    nlinarith [CB.H_one]
  exact CB.extractionAt_of_corrected_fit hv hB hBe num.B_lo num.B_hi num.M_nonneg
    num.M_m num.M_B num.m_nonneg hHH num.output_loss num.output_large lam hlam C hmass'
    hfit' hnest hvar num.output_small num.output_count num.output_L
    (fun e => (hC e).trans (Real.rpow_le_rpow_of_exponent_le hN num.output_C)) num.output_K

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
