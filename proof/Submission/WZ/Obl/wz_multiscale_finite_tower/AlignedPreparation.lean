-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.AlignedPreparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedInitialization
import Submission.WZ.Obl.wz_multiscale_finite_tower.PowerErrors

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

set_option maxHeartbeats 800000

/-- Initial alignment, with every fixed geometric loss absorbed into an
arbitrarily small bottom-scale power. -/
theorem prepare_aligned_family {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∃ η d₀ : ℝ, 0 < η ∧ 0 < d₀ ∧ d₀ ≤ D ∧ d₀ ≤ 1 / 100000 ∧
    ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ n x v Y,
      Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
    ∃ (m : ℕ) (X V : Fin m → Space) (Z : Fin m → Set Space) (u : Space) (h : ℝ),
      AlignedFamily d (d ^ ε) (d ^ (-ε)) (d ^ (-ε)) u h m X V Z ∧ m ≤ n ∧
      (⋃ i, Z i) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) := by
  obtain ⟨C, hC, hinit⟩ := aligned_refinement_at_width
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let η := min (ε / 40) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : 40 * η ≤ ε := by have := min_le_left (ε / 40) (1 / 4); dsimp [η]; linarith
  have hη1 : η ≤ 1 / 4 := min_le_right _ _
  let B : ℝ := 1000000000000000 * C
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨d₀, hd₀, hd₀D, hcut⟩ := exists_scale_cutoff (1 / B) η (min D (1 / 100000))
    (by positivity) hη (lt_min hD (by norm_num))
  refine ⟨η, d₀, hη, hd₀, hd₀D.trans (min_le_left _ _),
    hd₀D.trans (min_le_right _ _), ?_⟩
  intro d hd hdd n x v Y hA
  have hd1 : d ≤ 1 := (hdd.trans (hd₀D.trans (min_le_right _ _))).trans (by norm_num)
  have hbase : B * d ^ η ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hcut d hd hdd) hB.le
    simpa only [mul_one_div_cancel hB.ne'] using hh
  have hcoef (c a : ℝ) (hc : 0 ≤ c) (hcB : c ≤ B) (ha : η ≤ a) : c * d ^ a ≤ 1 :=
    power_coefficient_bound hd hd1 hc hcB ha hbase
  let b := d ^ (2 * η)
  have hb : 0 < b := Real.rpow_pos_of_pos hd _
  have hdb : d ≤ b := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hd hd1
      (show 2 * η ≤ 1 by linarith)
  have hbhalf : b ≤ 1 / 2 := by
    have hh := hcoef 2 (2 * η) (by norm_num) (by dsimp [B]; nlinarith) (by linarith)
    dsimp [b]
    linarith
  have hsmall : 3072 * b ≤ d ^ η := by
    have hh := hcoef 3072 η (by norm_num) (by dsimp [B]; nlinarith) le_rfl
    have hh' := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hd.le η)
    dsimp [b]
    rw [mul_assoc, ← Real.rpow_add hd, one_mul] at hh'
    convert hh' using 1 <;> congr 2 <;> ring
  obtain ⟨m, X, V, Z, u, h, hF, hmn, hsub, hmass⟩ := hinit hd hdb hbhalf hsmall
    (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hd.le _) hA
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hF.nonempty
  have hcard : d ^ (3 * η) / (896 * C) * n ≤ m := by
    have hh := ((mul_le_mul' (a := ENNReal.ofReal (b / (16 * C))) le_rfl hA.2.2.2.1).trans hmass).trans
      (hF.mass_le hd.le hd1)
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ b / (16 * C))] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 56 * (m : ℝ) * d ^ 2)).mp hh
    have hc : (b / (16 * C)) * (d ^ η * n) ≤ 56 * m := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
      convert hh' using 1 <;> ring
    have he : d ^ (3 * η) / (896 * C) * n =
        (1 / 56 : ℝ) * ((b / (16 * C)) * (d ^ η * n)) := by
      dsimp [b]
      rw [show 3 * η = 2 * η + η by ring, Real.rpow_add hd]
      ring
    rw [he]
    linarith
  have hden : d ^ ε ≤ d ^ η / 4 := density_power_bound hd (by norm_num)
    (hcoef 4 (ε - η) (by norm_num) (by dsimp [B]; nlinarith) (by linarith))
  have hcount : d ^ (-η) * WangZahlLot.Obl.wz_rescaled_fibre_alternatives.convexExpansionLoss 2 ≤ d ^ (-ε) := by
    have hh := inverse_power_error_bound hd (hcoef 512000 (ε - η) (by norm_num)
      (by dsimp [B]; nlinarith) (by linarith))
    norm_num [WangZahlLot.Obl.wz_rescaled_fibre_alternatives.convexExpansionLoss] at ⊢
    simpa only [mul_comm] using hh
  let A : ℝ := 512000000 * (896 * C)
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hroot : 512000000 * d ^ (-η) * n / m ≤ d ^ (-ε) := by
    have hbound : A * d ^ (-(4 * η)) ≤ d ^ (-ε) := inverse_power_error_bound hd
      (hcoef A (ε - 4 * η) hA0.le (by dsimp [A, B]; nlinarith) (by linarith))
    apply (div_le_iff₀ hm).mpr
    calc
      _ = (A * d ^ (-(4 * η))) * (d ^ (3 * η) / (896 * C) * n) := by
        have he : d ^ (-(4 * η)) * d ^ (3 * η) = d ^ (-η) := by
          rw [← Real.rpow_add hd]
          congr 1
          ring
        dsimp [A]
        calc
          _ = (512000000 * (896 * C)) * (d ^ (-(4 * η)) * d ^ (3 * η)) * n / (896 * C) := by
            rw [he]
            field_simp
          _ = _ := by ring
      _ ≤ (A * d ^ (-(4 * η))) * m := mul_le_mul_of_nonneg_left hcard (by positivity)
      _ ≤ d ^ (-ε) * m := mul_le_mul_of_nonneg_right hbound hm.le
  have hret : d ^ ε ≤ b / (16 * C) := density_power_bound hd (by positivity)
    (hcoef (16 * C) (ε - 2 * η) (by positivity) (by dsimp [B]; nlinarith) (by linarith))
  refine ⟨m, X, V, Z, u, h, hF.mono hden hcount hroot, hmn, hsub, ?_⟩
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hret) le_rfl).trans hmass

end WangZahlLot.Obl.wz_multiscale_finite_tower
