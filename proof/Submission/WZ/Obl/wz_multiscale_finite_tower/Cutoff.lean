-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Cutoff.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The endpoint expression at the input error constants is a single scale power. -/
theorem endpoint_power_identity {d : ℝ} (hd : 0 < d) (a ω t η σ N : ℝ) (hN : 0 ≤ N) :
    a * d ^ (ω + t) * (d ^ (-η))⁻¹ * (N * d ^ 2) *
      ((d ^ (-η)) ^ (-(3 / 2 : ℝ)) * d ^ (-η) * (N * d)) ^ (-σ) =
    a * d ^ (ω + t + η * (1 - σ / 2)) * (N * d ^ 2) * (N * d) ^ (-σ) := by
  rw [Real.mul_rpow (by positivity : 0 ≤ (d ^ (-η)) ^ (-(3 / 2 : ℝ)) * d ^ (-η))
    (mul_nonneg hN hd.le)]
  rw [← Real.rpow_mul hd.le, ← Real.rpow_add hd, ← Real.rpow_mul hd.le]
  rw [← Real.rpow_neg hd.le, neg_neg]
  have hp : d ^ (ω + t) * d ^ η * d ^ ((-η * -(3 / 2 : ℝ) + -η) * -σ) =
      d ^ (ω + t + η * (1 - σ / 2)) := by
    rw [← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    ring
  calc
    _ = a * (d ^ (ω + t) * d ^ η * d ^ ((-η * -(3 / 2 : ℝ) + -η) * -σ)) *
        (N * d ^ 2) * (N * d) ^ (-σ) := by ring
    _ = _ := by rw [hp]

/-- Above a fixed positive cutoff the endpoint estimate pays for any fixed exponent gain. -/
theorem Endpoint.away_from_zero {σ ω : ℝ} (hE : Endpoint σ ω)
    (hσ : σ ≤ 1 / 2) {α D : ℝ} (hα : 0 < α) (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → D ≤ d → ∀ n x v Y,
      Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y → VolumeBound σ ω κ α d n Y := by
  obtain ⟨a, ha, η, hη, hbound⟩ := hE 1 zero_lt_one
  let p : ℝ := α + 1 + η * (1 - σ / 2)
  have hp : 0 ≤ p := by
    dsimp [p]
    have : 0 ≤ η * (1 - σ / 2) := mul_nonneg hη.le (by linarith)
    linarith
  refine ⟨a * (min D 1) ^ p, mul_pos ha (Real.rpow_pos_of_pos (lt_min hD zero_lt_one) _),
    η, hη, ?_⟩
  intro d hd hd100 hDd n x v Y hA
  have hd1 : d ≤ 1 := by linarith
  have herror : 1 ≤ d ^ (-η) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_nonpos.mpr hη.le)
  have h := hbound d hd hd100 (d ^ (-η)) (d ^ (-η)) herror herror n x v Y hA
  rw [endpoint_power_identity hd a ω 1 η σ n (Nat.cast_nonneg n)] at h
  apply le_trans (ENNReal.ofReal_le_ofReal _) h
  have hpow : (min D 1) ^ p ≤ d ^ p :=
    Real.rpow_le_rpow (le_min hD.le zero_le_one) ((min_le_left D 1).trans hDd) hp
  have hscale : (a * (min D 1) ^ p) * d ^ (ω - α) ≤
      a * d ^ (ω + 1 + η * (1 - σ / 2)) := by
    calc
      _ ≤ (a * d ^ p) * d ^ (ω - α) := by gcongr
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hd]
        congr 2
        dsimp [p]
        ring
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hscale (by positivity)) (Real.rpow_nonneg (by positivity) _)

end WangZahlLot.Obl.wz_multiscale_finite_tower
