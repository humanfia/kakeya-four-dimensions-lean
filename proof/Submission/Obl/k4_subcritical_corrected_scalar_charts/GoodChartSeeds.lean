/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/GoodChartSeeds.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.CorrectionEvents
import Submission.Obl.k4_subcritical_corrected_scalar_charts.CorrectedFamily

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory

noncomputable section

namespace Data.ChosenPairedSample

variable {α : Type} [MeasurableSpace α] {cfg : Data α}
variable {k : ℕ} {M s₀ ε : ℝ} (sample : cfg.ChosenPairedSample k M s₀ ε)

def seedCharts : ChartFamily α where
  n := sample.coarse.charts.n
  G := sample.originalGoodChart
  q := sample.coarse.charts.q
  g := sample.coarse.charts.g

theorem originalGoodChart_disjoint :
    Pairwise (fun c c' => Disjoint (sample.originalGoodChart c) (sample.originalGoodChart c')) := by
  intro c c' hne
  exact (sample.coarse.disjoint c c' hne).mono inter_subset_left inter_subset_left

/-- The original residual floor is exactly unchanged by the static good-line
cut, before any current-law correction-time restriction. -/
theorem originalGoodChart_mass_eq (h : cfg.Prepared) (parent : cfg.NativeLevel k s₀)
    (hM : M ≤ cfg.e₀) (c : Fin sample.coarse.charts.n) :
    cfg.ρ k (sample.originalGoodChart c ×ˢ Icc (0 : ℝ) 1) =
      cfg.ρ k (sample.coarse.charts.G c ×ˢ Icc (0 : ℝ) 1) := by
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  apply original_good_line_cut_mass (cfg.μ k) (cfg.ρ k) (h.basic k).2.2.2.2.1
    (goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)))
  filter_upwards [parent.original_good_ae h] with p hp
  exact ⟨hp.1, hp.2.trans (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hM))⟩

theorem seed_prepared (h : cfg.Prepared) (parent : cfg.NativeLevel k s₀)
    {ξ : ℝ} (hM : M ≤ cfg.e₀) (hεξ : ε ≤ ξ) (hK : 2 * cfg.K k ≤ cfg.N k ^ ξ) :
    sample.seedCharts.SeedPrepared cfg k (cfg.N k ^ (-M))
      (cfg.N k ^ (-(2 * cfg.κ * s₀))) (cfg.N k ^ (-s₀)) ξ (cfg.N k ^ ε) := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hA : 0 < cfg.N k ^ (-s₀) := Real.rpow_pos_of_pos hN _
  refine ⟨sample.measurableSet_originalGoodChart h, sample.originalGoodChart_disjoint,
    ?_, sample.coarse.box, ?_, ?_⟩
  · intro c l hl
    have hlab := sample.coarse.labels c l hl.1
    exact ⟨hlab.1, hlab.2.1, hlab.2.2, fun e => (hl.2.1 e).trans hK, hl.2.2⟩
  · intro c l hl t ht
    unfold chartSignal
    rw [abs_div, abs_of_pos hA]
    exact (div_le_iff₀ hA).mpr (sample.coarse.fit c l hl.1 t ht)
  · intro c
    dsimp only [seedCharts] at c ⊢
    rw [sample.originalGoodChart_mass_eq h parent hM]
    apply le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) (sample.coarse.floor c)
    exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hN ε)
      (Real.rpow_le_rpow_of_exponent_le hN1 hεξ)

/-- A nonempty full good chart has bounded centers at the scales used by the
native contact and scalar variation estimates. -/
theorem originalGoodChart_center_bounds (h : cfg.Prepared) (hM : 0 < M) (hs₀ : 0 < s₀)
    {c : Fin sample.coarse.charts.n} (hc : (sample.originalGoodChart c).Nonempty) :
    |(sample.coarse.charts.q c 1 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀))| ≤ 3 * cfg.K k ∧
      |(sample.coarse.charts.q c 0 : ℝ) * cfg.N k ^ (-M)| ≤ 3 * cfg.K k := by
  obtain ⟨l, hl⟩ := hc
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hD : 0 < cfg.N k ^ (-(2 * cfg.κ * s₀)) := Real.rpow_pos_of_pos hN _
  have hχ : 0 < cfg.N k ^ (-M) := Real.rpow_pos_of_pos hN _
  have hD1 : cfg.N k ^ (-(2 * cfg.κ * s₀)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith [h.rate_pos])
  have hχ1 : cfg.N k ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hp := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hD (cfg.b k l 0)
  have hv := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hχ (cfg.b k l 3)
  rw [(sample.coarse.labels c l hl.1).2.1] at hp
  rw [(sample.coarse.labels c l hl.1).1] at hv
  have hpp := abs_sub_le ((sample.coarse.charts.q c 1 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀)))
    (cfg.b k l 0) 0
  have hvv := abs_sub_le ((sample.coarse.charts.q c 0 : ℝ) * cfg.N k ^ (-M)) (cfg.b k l 3) 0
  simp only [sub_zero, abs_sub_comm] at hpp hvv
  have hp' : |(sample.coarse.charts.q c 1 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀)) -
      cfg.b k l 0| ≤ cfg.N k ^ (-(2 * cfg.κ * s₀)) := by
    simpa only [mul_comm, abs_sub_comm] using hp
  have hv' : |(sample.coarse.charts.q c 0 : ℝ) * cfg.N k ^ (-M) - cfg.b k l 3| ≤
      cfg.N k ^ (-M) := by simpa only [mul_comm, abs_sub_comm] using hv
  constructor <;> linarith [hl.2.1 0, hl.2.1 3, h.subpower.1 k]

end Data.ChosenPairedSample

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
