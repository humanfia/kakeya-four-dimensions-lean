/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/LightChartPruning.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/LightChartPruning.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.AtlasBudget
import Submission.Obl.k4_balanced_native_packet_transport.CPF.TruePruning

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory
open scoped Classical ENNReal

noncomputable section

def Atlas.priorEfficientLabels {p : Data} {k : ℕ} (a : Atlas p k) (H : ℝ) : Finset (Fin a.C) :=
  Finset.univ.filter (fun b => ((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b) ≤
    ENNReal.ofReal H * ((p.ν k (a.γ b)).prod volume) (a.F b))

/-- A chart with very little selected mass relative to its full assigned prior
can be dropped at inverse-threshold cost, using the original assignment budget. -/
theorem Atlas.light_chart_loss_le {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r H : ℝ} (a : Atlas p k) (ha : a.TrueAt M D r) (hH : 0 < H) :
    a.deletedMass (a.priorEfficientLabels H) ≤ ENNReal.ofReal H⁻¹ := by
  have hH0 : ENNReal.ofReal H ≠ 0 := (ENNReal.ofReal_pos.mpr hH).ne'
  have hsingle (b : Fin a.C) (hb : b ∉ a.priorEfficientLabels H) :
      ((p.ν k (a.γ b)).prod volume) (a.F b) ≤ ENNReal.ofReal H⁻¹ *
        (((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b)) := by
    have hn : ¬ ((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b) ≤
        ENNReal.ofReal H * ((p.ν k (a.γ b)).prod volume) (a.F b) := by
      simpa only [priorEfficientLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    apply (ENNReal.mul_le_mul_iff_right hH0 ENNReal.ofReal_ne_top).mp
    calc
      _ ≤ ((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b) := (lt_of_not_ge hn).le
      _ = _ := by
        rw [ENNReal.ofReal_inv_of_pos hH, ← mul_assoc, ENNReal.mul_inv_cancel hH0
          ENNReal.ofReal_ne_top, one_mul]
  calc
    _ ≤ ∑ b ∈ Finset.univ \ a.priorEfficientLabels H, ENNReal.ofReal (p.ω k (a.γ b)) *
        (ENNReal.ofReal H⁻¹ * (((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b))) :=
      Finset.sum_le_sum (fun b hb => mul_le_mul' le_rfl (hsingle b (Finset.mem_sdiff.mp hb).2))
    _ ≤ ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) *
        (ENNReal.ofReal H⁻¹ * (((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b))) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ENNReal.ofReal H⁻¹ * a.budget := by
      unfold Atlas.budget
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      unfold Atlas.assignedWeight
      ring
    _ ≤ ENNReal.ofReal H⁻¹ * 1 := mul_le_mul' le_rfl (ha.budget_le_one hp)
    _ = _ := mul_one _

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
