-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GridRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GridCapacity
import Submission.WZ.Obl.wz_multiscale_finite_tower.Scales

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridCell gridUnion gridUnion_measurable)
open WangZahlLot.Obl.wz_flat_factored_improvement (gridHull)

/-- A single spatial density regularization costs any prescribed positive power
of the bottom scale, uniformly over all mesh widths at most one. -/
theorem regularize_grid_relative {ζ D : ℝ} (hζ : 0 < ζ) (hD : 0 < D) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧
      ∀ d θ a : ℝ, 0 < d → d ≤ d₀ → θ ≤ 1 → 0 < a → a ≤ 1 →
      ∀ (n : ℕ) (Y : Fin n → Set Space),
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ ball 0 1) →
      ∀ E : Set Space, MeasurableSet E → (∀ i, Y i ⊆ E) →
      ENNReal.ofReal (d ^ θ * n * d ^ 2) ≤ ∑ i, volume (Y i) →
      ∃ (S : Finset (Fin 3 → ℤ)) (t : ℝ), 0 < t ∧
        (∀ i, MeasurableSet (Y i ∩ gridUnion a S)) ∧
        ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤
          ∑ i, volume (Y i ∩ gridUnion a S) ∧
        (∀ z ∈ S, t * a ^ 3 ≤ volume.real (E ∩ gridCell a z) ∧
          d ^ ζ * volume.real (E ∩ gridCell a z) ≤ t * a ^ 3) ∧
        ∀ (N : ℕ) (U : Fin N → Set Space),
          ENNReal.ofReal t * volume (⋃ k, gridHull a S (U k)) ≤ volume E := by
  obtain ⟨K, hKbig⟩ := exists_nat_gt (4 / ζ)
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := (div_pos (by norm_num) hζ).trans hKbig
    exact_mod_cast this
  have hKpow : 4 ≤ ζ * (K : ℝ) := by
    have hh := (div_lt_iff₀ hζ).mp hKbig
    linarith
  obtain ⟨d₀, hd₀, hd₀D, hcut⟩ := exists_scale_cutoff (1 / (2 * K)) ζ (min D (1 / 288))
    (by positivity) hζ (lt_min hD (by norm_num))
  refine ⟨d₀, hd₀, hd₀D.trans (min_le_left _ _), ?_⟩
  intro d θ a hd hdd hθ ha ha1 n Y hYm hYB E hE hYE hmass
  have hd288 : d ≤ 1 / 288 := hdd.trans (hd₀D.trans (min_le_right _ _))
  have hd1 : d ≤ 1 := by linarith
  have hρ : 0 < d ^ ζ := Real.rpow_pos_of_pos hd _
  have hpower : (d ^ ζ) ^ K ≤ d ^ 4 := by
    rw [← Real.rpow_mul_natCast hd.le]
    simpa only [Real.rpow_ofNat] using
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 hKpow)
  have hθpow : d ^ 3 ≤ d ^ θ * d ^ 2 := by
    rw [← Real.rpow_natCast d 2, ← Real.rpow_add hd]
    simpa only [Real.rpow_ofNat, Nat.cast_ofNat] using
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (show θ + 2 ≤ 3 by linarith))
  have hsmall : (d ^ ζ) ^ K * 144 ≤ d ^ θ * d ^ 2 / 2 := by
    calc
      _ ≤ d ^ 4 * 144 := mul_le_mul_of_nonneg_right hpower (by norm_num)
      _ = (144 * d) * d ^ 3 := by ring
      _ ≤ (1 / 2 : ℝ) * d ^ 3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (1 / 2 : ℝ) * (d ^ θ * d ^ 2) := mul_le_mul_of_nonneg_left hθpow (by norm_num)
      _ = _ := by ring
  have hYfin (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (hYB i))
  have hsumfin : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hYfin i)
  let H : ℝ := ∑ i, volume.real (Y i)
  have hH : d ^ θ * n * d ^ 2 ≤ H := by
    have hh := (ENNReal.ofReal_le_iff_le_toReal hsumfin).mp hmass
    simpa only [H, ENNReal.toReal_sum (fun i _ => hYfin i), measureReal_def] using hh
  obtain ⟨S₀, hcover, hcap⟩ := unitBall_grid_cover ha ha1
  obtain ⟨S, t, hS, ht, hm, hclass⟩ := grid_density_class_relative ha hρ hKpos S₀ Y hYm hYE
    (fun i => (hYB i).trans hcover) hcap (le_refl H) (by
      have hn := Nat.cast_nonneg (α := ℝ) n
      nlinarith [mul_le_mul_of_nonneg_left hsmall hn])
  refine ⟨S, t, ht, fun i => (hYm i).inter (gridUnion_measurable a S), ?_, hclass, ?_⟩
  · have hZfin (i : Fin n) : volume (Y i ∩ gridUnion a S) ≠ ⊤ :=
      ne_top_of_le_ne_top (hYfin i) (measure_mono inter_subset_left)
    have hZsum : (∑ i, volume (Y i ∩ gridUnion a S)) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun i _ => hZfin i)
    rw [← ENNReal.ofReal_toReal hsumfin, ← ENNReal.ofReal_mul hρ.le]
    apply (ENNReal.ofReal_le_iff_le_toReal hZsum).mpr
    rw [ENNReal.toReal_sum (fun i _ => hYfin i), ENNReal.toReal_sum (fun i _ => hZfin i)]
    change d ^ ζ * H ≤ ∑ i, volume.real (Y i ∩ gridUnion a S)
    calc
      _ ≤ (1 / (2 * K)) * H := mul_le_mul_of_nonneg_right (hcut d hd hdd) (by dsimp [H]; positivity)
      _ = H / (2 * K) := by ring
      _ ≤ _ := hm
  · intro N U
    exact fibre_gridHull_union_transfer ha ht.le S hE
      (fun z hz => (hclass z hz).1) U

theorem regularize_grid {ζ D : ℝ} (hζ : 0 < ζ) (hD : 0 < D) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧
      ∀ d θ a : ℝ, 0 < d → d ≤ d₀ → θ ≤ 1 → 0 < a → a ≤ 1 →
      ∀ (n : ℕ) (Y : Fin n → Set Space),
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ ball 0 1) →
      ENNReal.ofReal (d ^ θ * n * d ^ 2) ≤ ∑ i, volume (Y i) →
      ∃ (S : Finset (Fin 3 → ℤ)) (t : ℝ), 0 < t ∧
        (∀ i, MeasurableSet (Y i ∩ gridUnion a S)) ∧
        ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤
          ∑ i, volume (Y i ∩ gridUnion a S) ∧
        (∀ z ∈ S, t * a ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell a z) ∧
          d ^ ζ * volume.real ((⋃ i, Y i) ∩ gridCell a z) ≤ t * a ^ 3) ∧
        ∀ (N : ℕ) (U : Fin N → Set Space),
          ENNReal.ofReal t * volume (⋃ k, gridHull a S (U k)) ≤ volume (⋃ i, Y i) := by
  obtain ⟨d₀, hd₀, hd₀D, H⟩ := regularize_grid_relative hζ hD
  refine ⟨d₀, hd₀, hd₀D, ?_⟩
  intro d θ a hd hdd hθ ha ha1 n Y hYm hYB hmass
  exact H d θ a hd hdd hθ ha ha1 n Y hYm hYB (⋃ i, Y i) (MeasurableSet.iUnion hYm)
    (fun i => subset_iUnion Y i) hmass

end WangZahlLot.Obl.wz_multiscale_finite_tower
