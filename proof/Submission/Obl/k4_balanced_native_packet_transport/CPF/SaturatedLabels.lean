/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/SaturatedLabels.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/SaturatedLabels.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.LightChartPruning
import Submission.Obl.k4_balanced_native_packet_transport.CPF.HeavyChartPruning

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory
open scoped Classical ENNReal

noncomputable section

theorem Atlas.deletedMass_inter_le {p : Data} {k : ℕ} (a : Atlas p k)
    (s t : Finset (Fin a.C)) : a.deletedMass (s ∩ t) ≤ a.deletedMass s + a.deletedMass t := by
  have heq (s : Finset (Fin a.C)) : a.deletedMass s =
      ∑ b, if b ∈ s then 0 else ENNReal.ofReal (p.ω k (a.γ b)) *
        ((p.ν k (a.γ b)).prod volume) (a.F b) := by
    unfold deletedMass
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b ∈ s <;> simp [hb]
  rw [heq, heq, heq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  by_cases hs : b ∈ s <;> by_cases ht : b ∈ t <;> simp [hs, ht, le_add_self]

def Atlas.saturatedLabels {p : Data} {k : ℕ} (a : Atlas p k) (H θ : ℝ) : Finset (Fin a.C) :=
  a.priorEfficientLabels H ∩ a.densityBoundedLabels θ

theorem Atlas.saturated_prior_bound {p : Data} {k : ℕ} {H θ : ℝ} (a : Atlas p k)
    (hH : 0 ≤ H) (b : Fin a.C) (hb : b ∈ a.saturatedLabels H θ) :
    p.ν k (a.γ b) (a.A b) ≤
      ENNReal.ofReal (2 * H * θ * crossingFactor a.κ * |Matrix.det (a.Q b)|) := by
  obtain ⟨hl, hh⟩ := Finset.mem_inter.mp hb
  have hlight := (Finset.mem_filter.mp hl).2
  have hheavy := (Finset.mem_filter.mp hh).2
  have hq0 : (2 : ENNReal) ^ a.T ≠ 0 := by positivity
  have hqtop : (2 : ENNReal) ^ a.T ≠ ⊤ := by finiteness
  have hqeq : (2 : ENNReal) ^ a.T = ENNReal.ofReal ((2 : ℝ) ^ a.T) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hbound : ((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b) ≤
      ENNReal.ofReal (2 * H * θ * crossingFactor a.κ * |Matrix.det (a.Q b)| /
        (2 : ℝ) ^ a.T) := by
    calc
      _ ≤ ENNReal.ofReal H * ((p.ν k (a.γ b)).prod volume) (a.F b) := hlight
      _ ≤ ENNReal.ofReal H * (2 * a.chartMassCeiling θ b) := mul_le_mul' le_rfl hheavy
      _ = _ := by
        unfold chartMassCeiling
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul hH]
        congr 1
        ring
  calc
    _ = (2 : ENNReal) ^ a.T *
        (((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b)) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hq0 hqtop, one_mul]
    _ ≤ (2 : ENNReal) ^ a.T * ENNReal.ofReal
        (2 * H * θ * crossingFactor a.κ * |Matrix.det (a.Q b)| / (2 : ℝ) ^ a.T) :=
      mul_le_mul' le_rfl hbound
    _ = _ := by
      rw [hqeq, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

theorem Atlas.saturated_label_loss_le {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r H θ : ℝ} (a : Atlas p k) (ha : a.TrueAt M D r)
    (hκ : 1 ≤ a.κ) (hH : 0 < H) (hθ : 0 ≤ θ)
    (hB : ∀ γ, 0 < p.B k γ) (m : ℕ) (hmesh : 4 * a.κ ^ 2 ≤ (m : ℝ))
    (hg : ∀ γ, Measurable (p.g k γ r))
    (hmap : ∀ γ, Measure.map (obs (p.B k γ) (δ (p.N k) r))
      (((p.ν k γ).prod volume).restrict (p.E k γ)) =
        (volume.prod Measure.count).withDensity (p.g k γ r)) :
    a.deletedMass (a.saturatedLabels H θ) ≤ ENNReal.ofReal H⁻¹ +
      2 * (∑ γ, ENNReal.ofReal (p.ω k γ) *
        (((p.ν k γ).prod volume).restrict (p.E k γ))
          {q | ENNReal.ofReal θ < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}) := by
  exact (a.deletedMass_inter_le _ _).trans (add_le_add (a.light_chart_loss_le hp ha hH)
    (a.heavy_chart_loss_le ha hκ hθ hB m hmesh hg hmap))

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
