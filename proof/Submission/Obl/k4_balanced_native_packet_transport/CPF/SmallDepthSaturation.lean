/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/SmallDepthSaturation.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SmallDepthPackets
import Submission.Obl.k4_balanced_native_packet_transport.CPF.PriorCalibration

/-! Saturated small-depth packets with two-sided bounds on their full actual
assigned prior masses. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace SmallDepthSaturation

open MeasureTheory Set Filter

theorem prior_power_band {p : Data} (hp : p.Valid) {k M D : ℕ} {r ε : ℝ}
    {a : Atlas p k} (ha : a.SaturatedAt M D r) (hκ : 1 ≤ a.κ)
    (hκN : a.κ ≤ p.N k ^ ε) (b : Fin a.C) :
    0 < (p.ν k (a.γ b) (a.A b)).toReal ∧
      p.N k ^ (-p.f r - ε) ≤
        (p.ν k (a.γ b) (a.A b)).toReal / |(a.Q b).det| ∧
      (p.ν k (a.γ b) (a.A b)).toReal / |(a.Q b).det| ≤
        p.N k ^ (-p.f r + ε) := by
  obtain ⟨hpos, hlo, hhi⟩ := ha.assigned_prior_calibration hp hκ b
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hJ : 0 < |(a.Q b).det| := abs_pos.mpr (ha.1.2.2.1 b).1
  have hbase : 0 < p.N k ^ (-p.f r) := Real.rpow_pos_of_pos hN _
  have heq : (p.ν k (a.γ b) (a.A b)).toReal / |(a.Q b).det| =
      ((p.ν k (a.γ b) (a.A b)).toReal /
        (p.N k ^ (-p.f r) * |(a.Q b).det|)) * p.N k ^ (-p.f r) := by
    field_simp
  have hinv : p.N k ^ (-ε) ≤ a.κ⁻¹ := by
    rw [Real.rpow_neg hN.le]
    exact inv_anti₀ (by linarith) hκN
  refine ⟨hpos, ?_, ?_⟩
  · calc
      p.N k ^ (-p.f r - ε) = p.N k ^ (-ε) * p.N k ^ (-p.f r) := by
        rw [← Real.rpow_add hN]
        congr 1
        ring
      _ ≤ _ := by rw [heq]; exact mul_le_mul_of_nonneg_right (hinv.trans hlo) hbase.le
  · calc
      _ ≤ p.N k ^ ε * p.N k ^ (-p.f r) := by
        rw [heq]
        exact mul_le_mul_of_nonneg_right (hhi.trans hκN) hbase.le
      _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring

/-- Actual saturated true systems at a small positive depth, with full assigned
prior mass bounds uniform in every retained chart. -/
theorem exists_small_saturated_systems (hi : InitialHorizon) {p : Data} (hp : p.Valid)
    {b d D err : ℝ} (hb : 0 < b) (hbL : 2 * b ≤ p.L)
    (hD : 0 < D) (hD₁ : D < 1) (hdD : d < D)
    (hclose : ∀ t ∈ Icc (0 : ℝ) (2 * b), |p.f t - p.f 0 - d * t| ≤ err)
    (hsmall : 2 * err ≤ (D - d) * b) :
    ∃ r ∈ Icc b (2 * b), ∀ h : ℝ, 2 * b < h →
      ∃ M₁ D₁ : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
        ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
          (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.SaturatedAt M₁ D₁ r ∧
          ∀ c, 0 < (p.ν k (a.γ c) (a.A c)).toReal ∧
            p.N k ^ (-p.f r - ε) ≤
              (p.ν k (a.γ c) (a.A c)).toReal / |(a.Q c).det| ∧
            (p.ν k (a.γ c) (a.A c)).toReal / |(a.Q c).det| ≤
              p.N k ^ (-p.f r + ε) := by
  obtain ⟨r, hr, htrue⟩ := SmallDepthPackets.exists_small_true_systems hi hp
    hb hbL hD hD₁ hdD hclose hsmall
  refine ⟨r, hr, fun h hh => ?_⟩
  have hinput : ∃ M₁ D₁ : ℕ, ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
      ∃ a : Atlas p k, 1 ≤ a.κ ∧ a.κ ≤ p.N k ^ σ ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M₁ D₁ r := by
    obtain ⟨M₁, D₁, hs⟩ := htrue h hh
    refine ⟨M₁, D₁, fun σ hσ => (hs σ hσ).mono ?_⟩
    rintro k ⟨a, hκ, _, hκN, hT, ha⟩
    exact ⟨a, hκ, hκN, hT, ha⟩
  obtain ⟨M₁, D₁, hs⟩ := saturated_atlases_of_true_at_depth hp
    (hb.trans_le hr.1).le (hr.2.trans hbL) hinput
  refine ⟨M₁, D₁, fun ε hε => (hs ε hε).mono ?_⟩
  rintro k ⟨a, hκ, hK, hκN, hT, ha⟩
  exact ⟨a, hκ, hK, hκN, hT, ha, fun c => prior_power_band hp ha hκ hκN c⟩

end SmallDepthSaturation
end Submission.Obl.k4_balanced_native_packet_transport.CPF
