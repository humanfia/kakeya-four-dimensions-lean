-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Slack.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Scales

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

/-- A finite-depth mesh with a strictly positive margin for every insertion. -/
noncomputable def meshExponent (ω : ℝ) (q : ℕ) : ℝ :=
  (2 - (1 / 2 : ℝ) ^ q) * (1 - ω / 100) ^ q

lemma meshExponent_zero (ω : ℝ) : meshExponent ω 0 = 1 := by
  norm_num [meshExponent]

lemma meshExponent_pos {ω : ℝ} (hω : ω ≤ 1) (q : ℕ) : 0 < meshExponent ω q := by
  have hh : (1 / 2 : ℝ) ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact mul_pos (by linarith) (pow_pos (by linarith : 0 < 1 - ω / 100) q)

lemma meshExponent_le {ω : ℝ} (hω : ω ≤ 1) (q : ℕ) :
    meshExponent ω q ≤ 2 * (1 - ω / 100) ^ q := by
  dsimp [meshExponent]
  exact mul_le_mul_of_nonneg_right (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) q])
    (pow_nonneg (by linarith) q)

lemma meshExponent_succ (ω : ℝ) (q : ℕ) :
    meshExponent ω (q + 1) = meshExponent ω q * (1 - ω / 100) +
      (1 / 2 : ℝ) ^ (q + 1) * (1 - ω / 100) ^ (q + 1) := by
  dsimp [meshExponent]
  rw [pow_succ, pow_succ]
  ring

/-- The positive increment in the mesh exponent absorbs an arbitrary fixed insertion loss. -/
lemma exists_mesh_slack_cutoff {ω c D : ℝ} (hω : ω ≤ 1) (hc : 0 < c) (hD : 0 < D)
    (q : ℕ) : ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      d ^ (meshExponent ω (q + 1)) ≤ c * (d ^ (meshExponent ω q)) ^ (1 - ω / 100) := by
  have ha : 0 < 1 - ω / 100 := by linarith
  let gap : ℝ := (1 / 2 : ℝ) ^ (q + 1) * (1 - ω / 100) ^ (q + 1)
  have hgap : 0 < gap := mul_pos (pow_pos (by norm_num) _) (pow_pos ha _)
  obtain ⟨d₀, hd₀, hd₀D, hsmall⟩ := exists_scale_cutoff c gap D hc hgap hD
  refine ⟨d₀, hd₀, hd₀D, ?_⟩
  intro d hd hdd
  rw [meshExponent_succ, Real.rpow_add hd, Real.rpow_mul hd.le]
  exact (mul_le_mul_of_nonneg_left (hsmall d hd hdd) (by positivity)).trans_eq (mul_comm _ _)

/-- Both subdivided intervals meet the new mesh once the fixed geometric losses are absorbed. -/
lemma inserted_gaps_with_slack {ω d c u v z : ℝ} {q : ℕ}
    (hd : 0 < d) (hω : ω ≤ 1) (hc : 0 ≤ c)
    (hslack : d ^ (meshExponent ω (q + 1)) ≤
      c * (d ^ (meshExponent ω q)) ^ (1 - ω / 100))
    (hold : d ^ (meshExponent ω q) ≤ z)
    (hu : c * z ^ (1 - ω / 100) ≤ u) (hv : c * z ^ (1 - ω / 100) ≤ v) :
    d ^ (meshExponent ω (q + 1)) ≤ u ∧ d ^ (meshExponent ω (q + 1)) ≤ v := by
  have hp : (d ^ (meshExponent ω q)) ^ (1 - ω / 100) ≤ z ^ (1 - ω / 100) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hd.le _) hold (by linarith)
  have h := hslack.trans (mul_le_mul_of_nonneg_left hp hc)
  exact ⟨h.trans hu, h.trans hv⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
