/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/HeavyChartPruning.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/HeavyChartPruning.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.TruePruning
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open scoped Classical ENNReal

noncomputable section

def Atlas.chartMassCeiling {p : Data} {k : ℕ} (a : Atlas p k) (θ : ℝ) (b : Fin a.C) : ENNReal :=
  ENNReal.ofReal (θ * crossingFactor a.κ * |Matrix.det (a.Q b)| / (2 : ℝ) ^ a.T)

def Atlas.densityBoundedLabels {p : Data} {k : ℕ} (a : Atlas p k) (θ : ℝ) : Finset (Fin a.C) :=
  Finset.univ.filter (fun b => ((p.ν k (a.γ b)).prod volume) (a.F b) ≤
    2 * a.chartMassCeiling θ b)

theorem Atlas.mass_below_density_ceiling {p : Data} {k M D : ℕ} {r θ : ℝ}
    (a : Atlas p k) (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ) (hθ : 0 ≤ θ)
    (hB : ∀ γ, 0 < p.B k γ) (m : ℕ) (hmesh : 4 * a.κ ^ 2 ≤ (m : ℝ))
    (hg : ∀ γ, Measurable (p.g k γ r))
    (hmap : ∀ γ, Measure.map (obs (p.B k γ) (δ (p.N k) r))
      (((p.ν k γ).prod volume).restrict (p.E k γ)) =
        (volume.prod Measure.count).withDensity (p.g k γ r))
    (b : Fin a.C) :
    ((p.ν k (a.γ b)).prod volume)
      (a.F b \ {q | ENNReal.ofReal θ < p.g k (a.γ b) r
        (obs (p.B k (a.γ b)) (δ (p.N k) r) q)}) ≤ a.chartMassCeiling θ b := by
  let S : Set Observation := {o | ChartCrosses a.κ a.T (a.j b : ℝ) (δ (p.N k) r)
    (p.B k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) m o}
  have hS : MeasurableSet S := measurableSet_chartCrosses _ _ _ _ _ _ _ _ _ _
  have hsub : a.F b ⊆ obs (p.B k (a.γ b)) (δ (p.N k) r) ⁻¹' S :=
    fun q hq => (ha.2.2.1 b).crosses_of_mem (hB _) hκ hmesh hq
  have h := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.mass_le_of_density_le
    (measurable_obs _ _) (hg _) (hmap _) hS (ENNReal.ofReal θ) hsub
  have hZ : MeasurableSet {q | ENNReal.ofReal θ < p.g k (a.γ b) r
      (obs (p.B k (a.γ b)) (δ (p.N k) r) q)} :=
    measurableSet_lt measurable_const ((hg _).comp (measurable_obs _ _))
  obtain ⟨hQ, _, _, _, hR, _, _, hF, _, _, hsel, _⟩ := ha.2.2.1 b
  rw [Measure.restrict_apply (hF.diff hZ), inter_eq_left.mpr
    (fun q hq => (hsel q hq.1).1)] at h
  calc
    _ ≤ ENNReal.ofReal θ * (volume.prod Measure.count) S := h
    _ ≤ ENNReal.ofReal θ * ENNReal.ofReal
        (crossingFactor a.κ * |Matrix.det (a.Q b)| / (2 : ℝ) ^ a.T) :=
      mul_le_mul' le_rfl (volume_chartCrosses hR (by unfold δ; positivity)
        (hB _) (by linarith) hQ)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hθ]
      congr 1
      ring

/-- Charts with mass above the geometric ceiling are mostly in the original
density exception. Their deletion costs at most twice that exceptional mass. -/
theorem Atlas.heavy_chart_loss_le {p : Data} {k M D : ℕ} {r θ : ℝ}
    (a : Atlas p k) (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ) (hθ : 0 ≤ θ)
    (hB : ∀ γ, 0 < p.B k γ) (m : ℕ) (hmesh : 4 * a.κ ^ 2 ≤ (m : ℝ))
    (hg : ∀ γ, Measurable (p.g k γ r))
    (hmap : ∀ γ, Measure.map (obs (p.B k γ) (δ (p.N k) r))
      (((p.ν k γ).prod volume).restrict (p.E k γ)) =
        (volume.prod Measure.count).withDensity (p.g k γ r)) :
    a.deletedMass (a.densityBoundedLabels θ) ≤
      2 * (∑ γ, ENNReal.ofReal (p.ω k γ) *
        (((p.ν k γ).prod volume).restrict (p.E k γ))
          {q | ENNReal.ofReal θ < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}) := by
  let Z : Fin (p.W k) → Set Incidence := fun γ =>
    {q | ENNReal.ofReal θ < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}
  have hZ (γ : Fin (p.W k)) : MeasurableSet (Z γ) :=
    measurableSet_lt measurable_const ((hg γ).comp (measurable_obs _ _))
  have hsingle (b : Fin a.C) (hb : b ∉ a.densityBoundedLabels θ) :
      ((p.ν k (a.γ b)).prod volume) (a.F b) ≤
        2 * ((p.ν k (a.γ b)).prod volume) (a.F b ∩ Z (a.γ b)) := by
    apply Submission.Obl.k4_scalar_terminal_chart_packet_extraction.le_two_mul_inter_of_diff_le
      ((p.ν k (a.γ b)).prod volume) (c := a.chartMassCeiling θ b) ENNReal.ofReal_ne_top
      (a.mass_below_density_ceiling ha hκ hθ hB m hmesh hg hmap b)
    exact (lt_of_not_ge (by
      simpa only [densityBoundedLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hb)).le
  calc
    _ ≤ ∑ b ∈ Finset.univ \ a.densityBoundedLabels θ, ENNReal.ofReal (p.ω k (a.γ b)) *
        (2 * ((p.ν k (a.γ b)).prod volume) (a.F b ∩ Z (a.γ b))) :=
      Finset.sum_le_sum (fun b hb => mul_le_mul' le_rfl (hsingle b (Finset.mem_sdiff.mp hb).2))
    _ ≤ ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) *
        (2 * ((p.ν k (a.γ b)).prod volume) (a.F b ∩ Z (a.γ b))) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 2 * ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) *
        ((p.ν k (a.γ b)).prod volume) (a.F b ∩ Z (a.γ b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ _ := mul_le_mul' le_rfl
      (a.selected_weighted_budget ha.2.1 _ ha.2.2.1 Z hZ)

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
