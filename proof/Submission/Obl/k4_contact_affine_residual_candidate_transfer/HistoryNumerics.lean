/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/HistoryNumerics.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Filter
open scoped ENNReal

noncomputable section

/-- A common floor fraction pays for all entry histories at all grid depths. -/
def historyFloorFraction (K : ℝ) (M m : ℕ) : ℝ :=
  (8 * K * ((m : ℝ) + 1) * (M : ℝ) ^ (m + 1))⁻¹

theorem historyFloorFraction_pos {K : ℝ} {M m : ℕ} (hK : 0 < K) (hM : 1 ≤ M) :
    0 < historyFloorFraction K M m := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  unfold historyFloorFraction
  positivity

theorem historyFloorFraction_le_one {K : ℝ} {M m : ℕ} (hK : 1 ≤ K) (hM : 1 ≤ M) :
    historyFloorFraction K M m ≤ 1 := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpow : (1 : ℝ) ≤ (M : ℝ) ^ (m + 1) := one_le_pow₀ hMr
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  apply inv_le_one_of_one_le₀
  change 1 ≤ 8 * K * ((m : ℝ) + 1) * (M : ℝ) ^ (m + 1)
  nlinarith [mul_le_mul hK (show 1 ≤ (m : ℝ) + 1 by linarith) (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ K)]

theorem historyFloorFraction_inv {K : ℝ} {M m : ℕ} :
    (historyFloorFraction K M m)⁻¹ = 8 * K * ((m : ℝ) + 1) * (M : ℝ) ^ (m + 1) := by
  rw [historyFloorFraction, inv_inv]

/-- The complete forest costs exactly one eighth of the original inverse-K
mass reserve, independently of its entry count. -/
theorem historyFloorFraction_cost {K : ℝ} {M m : ℕ} (hK : 0 < K) (hM : 1 ≤ M) :
    ENNReal.ofReal (historyFloorFraction K M m) *
      (((m + 1 : ℕ) : ℝ≥0∞) * (M : ℝ≥0∞) ^ (m + 1)) = ENNReal.ofReal (K⁻¹ / 8) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hθ := historyFloorFraction_pos (m := m) hK hM
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hθ.le]
  congr 1
  push_cast
  unfold historyFloorFraction
  field_simp

theorem historyFloorFraction_cost_lt_reserve {K : ℝ} {M m : ℕ}
    (hK : 0 < K) (hM : 1 ≤ M) :
    ENNReal.ofReal (historyFloorFraction K M m) *
      (((m + 1 : ℕ) : ℝ≥0∞) * (M : ℝ≥0∞) ^ (m + 1)) < ENNReal.ofReal (K⁻¹ / 2) := by
  rw [historyFloorFraction_cost hK hM]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  have := inv_pos.mpr hK
  linarith

/-- For a fixed grid resolution the reciprocal history fraction has only a
fixed polynomial dependence on the original subpower bounds. -/
theorem inverse_history_fraction_bound {K H : ℝ} {M m : ℕ}
    (hK : 0 ≤ K) (_hH : 0 ≤ H) (hM : (M : ℝ) ≤ 2 * H) :
    (historyFloorFraction K M m)⁻¹ ≤
      (8 * ((m : ℝ) + 1) * 2 ^ (m + 1)) * K * H ^ (m + 1) := by
  rw [historyFloorFraction_inv]
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg M) hM (m + 1)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 8 * K * ((m : ℝ) + 1) by positivity)
  rw [mul_pow] at hh
  nlinarith only [hh]


/-- At a fixed number of grid steps, all palette and pruning costs fit into
any prescribed power. The centering term uses only half that power. -/
theorem eventually_history_packet_cost
    (N K H : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hH : ∀ k, 1 ≤ H k)
    (hKsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ M : ℕ, (M : ℝ) ≤ 2 * H k →
      1 + H k + (historyFloorFraction (K k) M m)⁻¹ + N k ^ (ε / 2) + ((m : ℝ) + 1) ≤
        N k ^ ε := by
  let C : ℝ := 8 * ((m : ℝ) + 1) * 2 ^ (m + 1)
  let e : ℝ := ε / (8 * ((m : ℝ) + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have hC : ∀ᶠ k in atTop, C ≤ N k ^ (ε / 4) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 4)).comp hNt).eventually_ge_atTop C
  have hfour : ∀ᶠ k in atTop, 4 ≤ N k ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hNt).eventually_ge_atTop 4
  have hsteps : ∀ᶠ k in atTop, (m : ℝ) + 2 ≤ N k ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hNt).eventually_ge_atTop _
  filter_upwards [hKsub (ε / 8) (by positivity), hHsub e he,
    hHsub (ε / 2) (by positivity), hC, hfour, hsteps] with k hk hhe hh hc hf hs
  intro M hM
  have hNpos : 0 < N k := lt_of_lt_of_le zero_lt_one (hN k)
  have hK0 : 0 ≤ K k := zero_le_one.trans (hK k)
  have hH0 : 0 ≤ H k := zero_le_one.trans (hH k)
  have hpow : H k ^ (m + 1) ≤ N k ^ (ε / 8) := by
    calc
      _ ≤ (N k ^ e) ^ (m + 1) := pow_le_pow_left₀ hH0 hhe _
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        congr 1
        dsimp [e]
        push_cast
        field_simp
  have hinv : (historyFloorFraction (K k) M m)⁻¹ ≤ N k ^ (ε / 2) := by
    calc
      _ ≤ C * K k * H k ^ (m + 1) := inverse_history_fraction_bound hK0 hH0 hM
      _ ≤ N k ^ (ε / 4) * N k ^ (ε / 8) * N k ^ (ε / 8) := by
        apply mul_le_mul (mul_le_mul hc hk hK0 (by positivity)) hpow
          (pow_nonneg hH0 _) (by positivity)
      _ = _ := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        congr 1
        ring
  calc
    _ ≤ 4 * N k ^ (ε / 2) := by linarith
    _ ≤ N k ^ (ε / 2) * N k ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
