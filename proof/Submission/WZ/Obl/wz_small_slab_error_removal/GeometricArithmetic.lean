-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_slab_error_removal.GeometricArithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_slab_error_removal.Arithmetic

namespace WangZahlLot.Obl.wz_small_slab_error_removal

set_option maxHeartbeats 800000

theorem coefficient_pos {s w ε a δ m l N : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hm : 0 < m) (hl : 0 < l) (hN : 0 < N) :
    0 < coefficient s w ε a δ m l N := by
  unfold coefficient
  positivity

theorem log_coefficient {s w ε a δ m l N : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hm : 0 < m) (hl : 0 < l) (hN : 0 < N) :
    Real.log (coefficient s w ε a δ m l N) = Real.log a +
      (w + ε + 2 - s) * Real.log δ + (-1 + (3 / 2 : ℝ) * s) * Real.log m +
      (-s) * Real.log l + (1 - s) * Real.log N := by
  rw [coefficient_factorization hδ hm hl hN]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hδ, Real.log_rpow hm, Real.log_rpow hl, Real.log_rpow hN]

/-- Exponent bookkeeping for the balanced convex-container reduction. -/
theorem coefficient_geometric_transfer {s w ε a δ m l n k N ρ t M ζ : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ (1 / 2 : ℝ)) (hw : 0 ≤ w)
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) (hl : 0 < l) (hn : 0 < n) (hk : 0 < k) (hN : 0 < N)
    (hρ : 0 < ρ) (ht : 0 < t) (hM : 0 < M)
    (hζ : 0 ≤ ζ) (hζε : ζ * (w + 3) ≤ ε / 2)
    (hscale : δ ^ (1 + ζ) ≤ ρ)
    (hconvex : M ≤ δ ^ (-ζ) * m * (k * t * N * ρ ^ 2) / (n * δ ^ 2))
    (hslab : δ ^ ζ ≤ l * k * t ^ (1 / 2 : ℝ))
    (hpacking : δ ^ 2 * (n / (k * N)) ^ (1 / 2 : ℝ) ≤ δ ^ (-ζ) * t * ρ ^ 2) :
    coefficient s w ε a δ m l n ≤
      δ ^ ζ * t * k * coefficient s w 0 (a * δ ^ (ε / 2)) ρ M 1 N := by
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hα : -1 + (3 / 2 : ℝ) * s ≤ 0 := by linarith
  have hK := Real.log_le_log hM hconvex
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_rpow hδ] at hK
  have hS := Real.log_le_log (Real.rpow_pos_of_pos hδ ζ) hslab
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hδ, Real.log_rpow ht] at hS
  have hB := Real.log_le_log (by positivity : 0 < δ ^ 2 * (n / (k * N)) ^ (1 / 2 : ℝ)) hpacking
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity : 0 < n / (k * N)),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_rpow hδ] at hB
  have hR := Real.log_le_log (Real.rpow_pos_of_pos hδ (1 + ζ)) hscale
  rw [Real.log_rpow hδ] at hR
  have h₁ := mul_le_mul_of_nonpos_left hK hα
  have h₂ := mul_le_mul_of_nonneg_left hS hs
  have h₃ := mul_le_mul_of_nonneg_left hB hs
  have h₄ := mul_le_mul_of_nonneg_left hR hw
  have hmarg : ε / 2 + ζ * (w + 2 + s / 2) ≤ ε := by
    have hsζ : ζ * (w + 2 + s / 2) ≤ ζ * (w + 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hζ
    linarith
  have h₅ := mul_le_mul_of_nonpos_right hmarg hlogδ
  have hcp : 0 < coefficient s w 0 (a * δ ^ (ε / 2)) ρ M 1 N :=
    coefficient_pos (by positivity) hρ hM zero_lt_one hN
  apply (Real.log_le_log_iff (coefficient_pos ha hδ hm hl hn)
    (by positivity : 0 < δ ^ ζ * t * k * coefficient s w 0 (a * δ ^ (ε / 2)) ρ M 1 N)).mp
  rw [log_coefficient ha hδ hm hl hn,
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    log_coefficient (by positivity) hρ hM zero_lt_one hN,
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hδ, Real.log_rpow hδ, Real.log_one]
  push_cast at h₁ h₂ h₃ h₄ h₅ ⊢
  nlinarith only [h₁, h₂, h₃, h₄, h₅]

end WangZahlLot.Obl.wz_small_slab_error_removal
