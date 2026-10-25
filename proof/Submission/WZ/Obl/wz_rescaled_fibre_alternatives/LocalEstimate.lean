-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.LocalEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.PowerLoss

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (exists_rotation)

lemma selected_estimate_lower {d σ ω ε θ a n M : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hσ : 0 ≤ σ) (hθ : 0 ≤ θ)
    (hθε : 2 * θ ≤ ε / 2) (ha : 0 ≤ a) (hn : 0 < n) (hM : 0 < M)
    (hMn : M ≤ n) (hcard : d ^ θ * n ≤ M) :
    a * d ^ (ω + ε) * (n * d ^ 2) * (n * d) ^ (-σ) ≤
      a * d ^ (ω + ε / 2) * (d ^ (-θ))⁻¹ * (M * d ^ 2) *
        ((d ^ (-θ)) ^ (-(3 / 2 : ℝ)) * d ^ (-θ) * (M * d)) ^ (-σ) := by
  have hm : 0 < d ^ (-θ) := Real.rpow_pos_of_pos hd _
  have hm1 : 1 ≤ d ^ (-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr hθ)
  have hmhalf : (d ^ (-θ)) ^ (-(3 / 2 : ℝ)) * d ^ (-θ) ≤ 1 := by
    have he : (d ^ (-θ)) ^ (-(3 / 2 : ℝ)) * d ^ (-θ) = (d ^ (-θ)) ^ (-(1 / 2 : ℝ)) := by
      rw [show (-(1 / 2 : ℝ)) = -(3 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hm, Real.rpow_one]
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  have hi : (d ^ (-θ)) ^ (-(3 / 2 : ℝ)) * d ^ (-θ) * (M * d) ≤ n * d := by
    calc
      _ ≤ 1 * (M * d) := mul_le_mul_of_nonneg_right hmhalf (by positivity)
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hMn hd.le
  have hip : (n * d) ^ (-σ) ≤
      ((d ^ (-θ)) ^ (-(3 / 2 : ℝ)) * d ^ (-θ) * (M * d)) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hi (neg_nonpos.mpr hσ)
  calc
    _ ≤ a * d ^ (ω + ε / 2 + 2 * θ) * (n * d ^ 2) * (n * d) ^ (-σ) := by
      have hpow : d ^ (ω + ε) ≤ d ^ (ω + ε / 2 + 2 * θ) :=
        Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow ha) (by positivity)) (by positivity)
    _ = a * d ^ (ω + ε / 2) * (d ^ (-θ))⁻¹ * ((d ^ θ * n) * d ^ 2) * (n * d) ^ (-σ) := by
      rw [Real.rpow_neg hd.le, inv_inv,
        show ω + ε / 2 + 2 * θ = (ω + ε / 2) + (θ + θ) by ring,
        Real.rpow_add hd (ω + ε / 2) (θ + θ), Real.rpow_add hd θ θ]
      ring
    _ ≤ a * d ^ (ω + ε / 2) * (d ^ (-θ))⁻¹ * (M * d ^ 2) * (n * d) ^ (-σ) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hip (by positivity)

lemma normalized_volume_identity {r s n : ℝ} (hr : 0 < r) (hs : 0 < s) (hn : 0 ≤ n)
    (a β σ : ℝ) :
    a * (normalizedRadius r s) ^ β * (n * (normalizedRadius r s) ^ 2) *
      (n * normalizedRadius r s) ^ (-σ) =
    jacobian r * ((a * (4 * contraction) ^ β * (16 / contraction) * (4 * contraction) ^ (-σ)) *
      (s / r) ^ β * (n * s ^ 2) * (n * (s / r)) ^ (-σ)) := by
  have he : n * normalizedRadius r s = (4 * contraction) * (n * (s / r)) := by
    rw [radius_eq_ratio]
    ring
  have hnpow : (n * normalizedRadius r s) ^ (-σ) =
      (4 * contraction) ^ (-σ) * (n * (s / r)) ^ (-σ) := by
    rw [he, Real.mul_rpow (by norm_num) (by positivity)]
  have hpow : (normalizedRadius r s) ^ β = (4 * contraction) ^ β * (s / r) ^ β := by
    rw [radius_eq_ratio, Real.mul_rpow (by norm_num) (by positivity)]
  rw [hnpow, hpow, radius_eq_ratio]
  dsimp [jacobian]
  field_simp
  ring

/-- The affine normalization gives the fibre version of `E`, including repeated tubes. -/
lemma local_estimate {σ ω : ℝ} (hσ : 0 ≤ σ)
    (hE : WangZahlLot.Obl.wz_nonflat_factored_improvement.EstimateE σ ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a η₀ c : ℝ, 0 < a ∧ 0 < η₀ ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ η r s : ℝ, 0 < η → η ≤ η₀ → 0 < s → s ≤ c * r → r ≤ 1 →
      ∀ y w : Space, ‖w‖ = 1 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Fibre r s η y w x v Y →
      ENNReal.ofReal (a * (s / r) ^ (ω + ε) * (n * s ^ 2) * (n * (s / r)) ^ (-σ)) ≤
        volume (⋃ i, Y i) := by
  obtain ⟨a₀, ha₀, ηE, hηE, HE⟩ := hE (ε / 2) (by positivity)
  let θ := min ηE (ε / 8)
  have hθ : 0 < θ := lt_min hηE (by positivity)
  obtain ⟨η₀, c, hη₀, hc, hc1, HN⟩ := normalize_with_power_loss hθ
  let a := a₀ * (4 * contraction) ^ (ω + ε) * (16 / contraction) * (4 * contraction) ^ (-σ)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, η₀, c, ha, hη₀, hc, hc1, ?_⟩
  intro η r s hη hη0 hs hsr hr1 y w hw n x v Y hF
  obtain ⟨e, hew⟩ := exists_rotation hw
  obtain ⟨hr, M, j, z, u, hj, hA, hcover, hmid, hcard, hmass⟩ :=
    HN η r s hη hη0 hs hsr hr1 y w e hw hew n x v Y hF
  have hR : 0 < normalizedRadius r s := normalizedRadius_pos hr hs
  have hsr' : s ≤ r := hsr.trans (mul_le_of_le_one_left hr.le hc1)
  have hR100 : normalizedRadius r s ≤ 1 / 100 := (normalizedRadius_le hr hsr').trans (by norm_num)
  have hR1 : normalizedRadius r s ≤ 1 := by linarith
  have hM : 0 < M := hA.1
  have hMn : (M : ℝ) ≤ n := by
    exact_mod_cast (show M ≤ n by simpa using Fintype.card_le_of_injective j hj)
  have hm : 1 ≤ (normalizedRadius r s) ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hR hR1 (neg_nonpos.mpr hθ.le)
  have hAE := admissible_mono hR hR1 (min_le_left ηE (ε / 8)) le_rfl le_rfl hA
  have hEst := HE (normalizedRadius r s) hR hR100 _ _ hm hm M z u
    (fun i => normalize e y w r hr '' Y (j i)) hM
    (fun i => (hAE.2.1 i).1) (fun i => (hAE.2.1 i).2.1) hAE.2.2.1
    (fun i => (hAE.2.1 i).2.2.1) (fun i => (hAE.2.1 i).2.2.2) hAE.2.2.2.1
    (by simpa only [ConvexCount, true_and] using hAE.2.2.2.2.1) hAE.2.2.2.2.2
  have hscalar := selected_estimate_lower (ω := ω) (ε := ε) hR hR1 hσ hθ.le
    (by have := min_le_right ηE (ε / 8); dsimp [θ]; linarith)
    ha₀.le (Nat.cast_pos.mpr hF.1) (Nat.cast_pos.mpr hM) hMn hcard
  have hlower : ENNReal.ofReal (a₀ * (normalizedRadius r s) ^ (ω + ε) *
      (n * (normalizedRadius r s) ^ 2) * (n * normalizedRadius r s) ^ (-σ)) ≤
      ENNReal.ofReal (jacobian r) * volume (⋃ i, Y i) := by
    calc
      _ ≤ volume (⋃ i, normalize e y w r hr '' Y (j i)) :=
        (ENNReal.ofReal_le_ofReal hscalar).trans hEst
      _ ≤ volume (normalize e y w r hr '' (⋃ i, Y i)) := by
        apply measure_mono
        rintro p hp
        obtain ⟨i, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
        exact ⟨q, Set.mem_iUnion.mpr ⟨j i, hq⟩, rfl⟩
      _ = _ := normalize_volume e y w hr _
  rw [normalized_volume_identity hr hs (Nat.cast_nonneg n) a₀ (ω + ε) σ] at hlower
  exact WangZahlLot.Obl.wz_nonflat_factored_improvement.ofReal_cancel_factor
    (by positivity : 0 < jacobian r) hlower

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
