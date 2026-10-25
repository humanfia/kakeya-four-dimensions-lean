/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/SampleBand.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SampleSheets
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingVolume
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DyadicMatching

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep.TestedSample

open MeasureTheory Set Metric

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

theorem matching_band_pow_bound (hω : ∀ γ, 0 ≤ ωk γ) (hNk : 0 < Nk)
    {r M₀ : ℝ} (hr : 0 < r) (hM₀ : 0 < M₀) (hδM : δ Nk L ≤ 2 * M₀)
    (hpos : ∀ p : s.Active,
      DiscPosOn (s.P (s.src p)) (gridCenter (r / 2) (gridLabel (r / 2) (s.sourceBase p))) r ∧
      DiscPosOn (s.P (s.wit p)) (gridCenter (r / 2) (gridLabel (r / 2) (s.sourceBase p))) r)
    (i : Fin s.m × ↥(gridBox (r / 2) (1 / 8)) × Bool) (k : ℕ) :
    (s.toPairTests hω hNk (by positivity : 0 < r / 2) (by linarith) hpos).toDiscSetup.Pm
      {p | (s.toPairTests hω hNk (by positivity : 0 < r / 2) (by linarith) hpos).toDiscSetup.lab
          ((s.toPairTests hω hNk (by positivity : 0 < r / 2) (by linarith) hpos).toDiscSetup.src p) =
          (s.toPairTests hω hNk (by positivity : 0 < r / 2) (by linarith) hpos).toDiscSetup.lab i ∧
        ‖(s.toPairTests hω hNk (by positivity : 0 < r / 2) (by linarith) hpos).toDiscSetup.φ i
          (emb ((s.toPairTests hω hNk (by positivity : 0 < r / 2) (by linarith) hpos).toDiscSetup.x p)) -
          ((s.toPairTests hω hNk (by positivity : 0 < r / 2) (by linarith) hpos).toDiscSetup.w p : ℂ)‖
            ≤ 2 * (M₀ * 2 ^ k)} ≤
      ENNReal.ofReal (matchingVolumeConstant *
        (s.sourceCeiling (s.frame i.1) * (2 * r) ^ 3) *
          (2 * M₀ / δ Nk L) ^ dc * ((2 : ℝ) ^ dc) ^ k) := by
  let T := s.toPairTests hω hNk (by positivity : 0 < r / 2) (by linarith) hpos
  have hδ : 0 < δ Nk L := by unfold δ; positivity
  have hwidth : 0 < 2 * (M₀ * 2 ^ k) := by positivity
  have hmax : max (2 * (M₀ * 2 ^ k)) (δ Nk L) = 2 * (M₀ * 2 ^ k) := by
    apply max_eq_left
    calc δ Nk L ≤ 2 * M₀ := hδM
      _ ≤ 2 * (M₀ * 2 ^ k) := by
        have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
        nlinarith
  let cap := fun b ρ => s.sourceCeiling b * (max ρ (δ Nk L) / δ Nk L) ^ dc
  have hb := T.matching_band_bound cap (s.band_density hω) i hwidth
  have hpow : (max (2 * (M₀ * 2 ^ k)) (δ Nk L) / δ Nk L) ^ dc =
      (2 * M₀ / δ Nk L) ^ dc * ((2 : ℝ) ^ dc) ^ k := by
    rw [hmax]
    have hh := dyadic_ratio_rpow (mul_pos (by norm_num : (0 : ℝ) < 2) hM₀)
      (half_pos hδ) k dc
    convert hh using 1 <;> congr 1 <;> ring
  have hcap : 0 ≤ cap (s.frame i.1) (2 * (M₀ * 2 ^ k)) :=
    mul_nonneg (s.sourceCeiling_nonneg hω hNk.le _) (Real.rpow_nonneg (by positivity) _)
  refine hb.trans ?_
  calc _ ≤ ENNReal.ofReal (cap (s.frame i.1) (2 * (M₀ * 2 ^ k))) *
        ENNReal.ofReal (matchingVolumeConstant * (2 * r) ^ 3) :=
      mul_le_mul' le_rfl (matching_grid_ball_volume hr _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hcap]
      dsimp [cap]
      rw [hpow]
      congr 1
      ring

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep.TestedSample
