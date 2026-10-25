import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.GeometricOutput
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualSupport
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualCharts
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualBudgets

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original product domination transfers the original label-parameter bound
to every incidence law dominated by `μ`. -/
theorem ae_original_velocity_bound (hv : cfg.Valid) (k : ℕ) :
    ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 3| ≤ cfg.K k := by
  obtain ⟨-, -, -, hμ, -, -, -, -, hb, -⟩ := hv.basic k
  have hh := (Measure.quasiMeasurePreserving_fst (μ := cfg.ν k) (ν := (volume : Measure ℝ))).ae hb
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hμ).ae_le hh] with p hp
  linarith only [hp, abs_nonneg (cfg.b k p.1 0), abs_nonneg (cfg.b k p.1 1),
    abs_nonneg (cfg.b k p.1 4)]

namespace ComparedBlock

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable {k : ℕ} {s u v M H : ℝ}
    (CB : ComparedBlock cfg k s u v (cfg.N k ^ (-M)) H)

/-- The captured original law, corrected fit, and explicit geometric/numerical
budgets give the complete frozen output after one final support pruning. -/
theorem extractionAt_of_corrected_fit (hv : cfg.Valid) {se R v' Hout m η θ J : ℝ}
    (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k se R)
    (hv'1 : R⁻¹ ≤ v') (hv'2 : v' ≤ R)
    (hM : 0 ≤ M) (hmM : M ≤ m) (hv'M : M ≤ v') (hm : 0 ≤ m)
    (hHH : H ≤ Hout) (hηθ : 2 * η ≤ θ) (hlarge : 54 ≤ cfg.N k ^ η)
    (lam : Measure (α × ℝ)) (hlam : lam ≤ CB.lam) (C : Fin 4 → ℝ)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-η)) *
      (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s CB.i)) ≤ lam univ)
    (hfit : ∀ᵐ p ∂lam,
      let F := blockFrame cfg k s CB.i CB.L
      |F.resid (cfg.b k p.1) p.2 - transv C (F.zt p.2) (F.zZ (cfg.b k p.1) p.2)
          (F.tr (cfg.b k p.1) p.2) -
        quadZ (CB.pc (CB.crs (CB.lab p.1))) (F.zt p.2) (F.zZ (cfg.b k p.1) p.2) -
          CB.D2 (CB.lab p.1)| ≤ Hout * cfg.N k ^ (-v))
    (hnest : ∀ j : Fin (cfg.n k se), ∃ h : Fin (cfg.n k s), cfg.A k se j ⊆ cfg.A k s h ∧
      Data.I (cfg.T k se) (cfg.j k se j) ⊆ Data.I (cfg.T k s) (cfg.j k s h))
    (hvar : ∀ j : Fin (cfg.n k se),
      ∀ p ∈ (cfg.B k se j ×ˢ Data.I (cfg.T k se) (cfg.j k se j)) ∩
        (cfg.B k s CB.i ×ˢ Data.I (cfg.T k s) (cfg.j k s CB.i)),
      ∀ p' ∈ (cfg.B k se j ×ˢ Data.I (cfg.T k se) (cfg.j k se j)) ∩
        (cfg.B k s CB.i ×ˢ Data.I (cfg.T k s) (cfg.j k s CB.i)),
      let F := blockFrame cfg k s CB.i CB.L
      |F.zt p.2 - F.zt p'.2| ≤ cfg.N k ^ (-m) ∧
      |F.zZ (cfg.b k p.1) p.2 - F.zZ (cfg.b k p'.1) p'.2| ≤ cfg.N k ^ (-m) ∧
      |(F.resid (cfg.b k p.1) p.2 - transv C (F.zt p.2) (F.zZ (cfg.b k p.1) p.2)
          (F.tr (cfg.b k p.1) p.2)) -
        (F.resid (cfg.b k p'.1) p'.2 - transv C (F.zt p'.2) (F.zZ (cfg.b k p'.1) p'.2)
          (F.tr (cfg.b k p'.1) p'.2))| ≤ cfg.N k ^ (-v))
    (hsmall : Hout * (5 + 3 * cfg.K k) * cfg.N k ^ (-m) ≤ cfg.N k ^ (-v))
    (hcount : 84 * cfg.K k *
      ((ENNReal.ofReal (cfg.K k) / ENNReal.ofReal (cfg.N k ^ (-2 * η))).toReal *
        (48 * cfg.K k) * Hout ^ 3) ≤ cfg.N k ^ θ)
    (hL : H * cfg.N k ^ (2 * s) ≤ cfg.N k ^ J)
    (hC : ∀ e, |C e| ≤ cfg.N k ^ θ) (hKθ : cfg.K k ≤ cfg.N k ^ θ) :
    Submission.Obl.k4_wide_three_layer_scalar_inputs.Data.ExtractionAt cfg k θ s v m J := by
  have hN : 1 ≤ cfg.N k := by linarith [hv.scale k]
  have hN₀ : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hK : 1 ≤ cfg.K k := hv.subpower.1 k
  have hK₀ : 0 ≤ cfg.K k := zero_le_one.trans hK
  obtain ⟨hb, hν, hπ, hμ, hρμ, hunit, -⟩ := hv.basic k
  letI : IsProbabilityMeasure (cfg.ν k) := hν
  have hlamμ : lam ≤ cfg.μ k := hlam.trans (CB.lam_le.trans hρμ)
  have hsupp : ∀ᵐ p ∂lam, p.1 ∈ cfg.B k s CB.i ∧
      p.2 ∈ Data.I (cfg.T k s) (cfg.j k s CB.i) := by
    filter_upwards [ae_mono hlam CB.lam_supp] with p hp
    exact ⟨hp.1, by rw [← blockFrame_interval CB.i CB.L]; exact hp.2⟩
  have hZ : ∀ᵐ p ∂lam, |(blockFrame cfg k s CB.i CB.L).zZ (cfg.b k p.1) p.2| ≤ cfg.K k := by
    filter_upwards [ae_mono hlam CB.lam_supp] with p hp
    exact (whole_block_bounds hB hN₀ CB.i CB.L CB.hL hp.1 hp.2).1
  have htimeμ : ∀ᵐ p ∂cfg.μ k, p ∈ univ ×ˢ Icc (0 : ℝ) 1 := by
    exact (ae_iff.mpr hunit)
  have htime : ∀ᵐ p ∂lam, p.2 ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [ae_mono hlamμ htimeμ] with p hp
    exact hp.2
  have hvel := ae_mono hlamμ (ae_original_velocity_bound hv k)
  have hq : 0 < (blockFrame cfg k s CB.i CB.L).q := by dsimp [blockFrame]; positivity
  have hq₁ : (blockFrame cfg k s CB.i CB.L).q ≤ 1 := by
    dsimp [blockFrame]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hcharts := residual_chart_menus_at (blockFrame cfg k s CB.i CB.L) (cfg.b k) lam
    hN hK hq hq₁ hM hmM hv'M (hB.c_bd CB.i 1) htime hvel
  have hcoarse : ∀ ch : ℤ × ℤ, ∃ G : Finset CB.Γ, (G.card : ℝ) ≤ Hout ∧
      ∀ᵐ p ∂lam, (⌊cfg.b k p.1 3 / cfg.N k ^ (-M)⌋, ⌊cfg.b k p.1 0 / cfg.N k ^ (-M)⌋) = ch →
        CB.crs (CB.lab p.1) ∈ G := by
    intro ch
    obtain ⟨G, hcard, hmem⟩ := CB.coarse_list ch.1 ch.2
    refine ⟨G, hcard.trans hHH, ?_⟩
    filter_upwards [ae_mono hlam hmem] with p hp hc
    exact hp (congrArg Prod.fst hc) (congrArg Prod.snd hc)
  have hoffset : ∀ (ch : ℤ × ℤ) (γ : CB.Γ), ∃ Fo : Finset ℤ,
      (Fo.card : ℝ) ≤ Hout * cfg.N k ^ (cfg.d * v) ∧
      ∀ᵐ p ∂lam, (⌊cfg.b k p.1 3 / cfg.N k ^ (-M)⌋, ⌊cfg.b k p.1 0 / cfg.N k ^ (-M)⌋) = ch →
        CB.crs (CB.lab p.1) = γ → ⌊CB.D2 (CB.lab p.1) / cfg.N k ^ (-v)⌋ ∈ Fo := by
    intro ch γ
    obtain ⟨Fo, hcard, hmem⟩ := CB.offset2_list ch.1 ch.2 γ
    refine ⟨Fo, hcard.trans (mul_le_mul_of_nonneg_right hHH (Real.rpow_nonneg hN₀.le _)), ?_⟩
    filter_upwards [ae_mono hlam hmem] with p hp hc hγ
    exact hp (congrArg Prod.fst hc) (congrArg Prod.snd hc) hγ
  let δp := ENNReal.ofReal (cfg.N k ^ (-2 * η))
  have hδ0 : δp ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hN₀ _))
  have hδtop : δp ≠ ⊤ := ENNReal.ofReal_ne_top
  have hr := residual_support_at hN₀ hK hν hπ hb hμ hB hBe hv'1 hv'2
    CB.i CB.L lam C CB.Γ CB.Λ CB.lab CB.crs CB.chartOf CB.pc CB.D2 (cfg.N k ^ (-M))
    Hout m v (cfg.K k) (48 * cfg.K k) δp (CB.H_one.trans hHH) hK₀
  obtain ⟨lam', hle, hloss, Fs, hcard, hsupport⟩ := hr CB.lab_meas hlamμ hsupp hZ
    (fun γ e => (CB.pc_bd γ e).trans hHH) (ae_mono hlam CB.chart_ae) hfit
    hcoarse hoffset hnest hvar hcharts hsmall hδ0 hδtop
  have hW : ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s CB.i) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hmass' := residual_pruning_mass_floor hN₀ hlarge hW hmass hloss
  have hmassθ : ENNReal.ofReal (cfg.N k ^ (-θ)) *
      (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s CB.i)) ≤ lam' univ := by
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith))) le_rfl).trans hmass'
  have hsize := residual_table_normalized_bound Fs hN hm hK
    (show 0 ≤ (ENNReal.ofReal (cfg.K k) / δp).toReal * (48 * cfg.K k) * Hout ^ 3 by
      have hh := CB.H_one.trans hHH
      positivity) hcard
  have hsizeθ : (Fs.card : ℝ) * (cfg.N k ^ (-m)) ^ 2 ≤
      cfg.N k ^ θ * (cfg.N k ^ (-v)) ^ (-cfg.d) := by
    have hp : (cfg.N k ^ (-v)) ^ (-cfg.d) = cfg.N k ^ (cfg.d * v) := by
      rw [← Real.rpow_mul hN₀.le]
      congr 1
      ring
    rw [hp]
    exact hsize.trans (mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hN₀.le _))
  exact CB.extractionAt_of_residual_table hB hN₀ lam' (hle.trans hlam) C hmassθ hL hC hKθ
    Fs hsizeθ hsupport

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
