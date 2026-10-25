-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.DyadicPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicShading
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorRetention

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory Set
open scoped Classical

/-- The number of dyadic count classes costs an arbitrarily small power when
the family size is polynomially bounded in the reciprocal scale. -/
theorem logarithmic_count_power {D ν : ℝ} (hD : 0 < D) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ n : ℕ, (n : ℝ) ≤ δ ^ (-D) → (Nat.log 2 n + 1 : ℝ) ≤ δ ^ (-ν) := by
  let q := ν / (2 * D)
  have hq : 0 < q := by dsimp [q]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := 1 / (q * Real.log 2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨d, hd, hconst⟩ := fixed_constant_power_bound (ν := ν / 2) hC (by positivity)
  refine ⟨min 1 d, lt_min zero_lt_one hd, ?_⟩
  intro δ hδ hδd n hn
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  by_cases hn0 : n = 0
  · subst n
    simpa using Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hν.le)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hnq : 1 ≤ (n : ℝ) ^ q := Real.one_le_rpow hn1 hq.le
  have hlog := Real.natLog_le_logb n 2
  have hlogpow := Real.log_le_rpow_div hnpos.le hq
  have hnat : (Nat.log 2 n + 1 : ℝ) ≤ C * (n : ℝ) ^ q := by
    calc
      _ ≤ Real.log n / Real.log 2 + 1 := by
        simpa only [Real.logb, Nat.cast_ofNat] using add_le_add hlog (le_refl (1 : ℝ))
      _ ≤ ((n : ℝ) ^ q / q) / Real.log 2 + (n : ℝ) ^ q :=
        add_le_add (div_le_div_of_nonneg_right hlogpow hlog2.le) hnq
      _ = _ := by dsimp [C]; field_simp
  have hpow : (n : ℝ) ^ q ≤ δ ^ (-(ν / 2)) := by
    have hh := Real.rpow_le_rpow hnpos.le hn hq.le
    rw [← Real.rpow_mul hδ.le] at hh
    have he : -D * q = -(ν / 2) := by dsimp [q]; field_simp
    simpa only [he] using hh
  refine hnat.trans ?_
  calc
    C * (n : ℝ) ^ q ≤ δ ^ (-(ν / 2)) * δ ^ (-(ν / 2)) :=
      mul_le_mul (hconst δ hδ (hδd.trans (min_le_right _ _))) hpow
        (Real.rpow_nonneg hnpos.le _) (Real.rpow_nonneg hδ.le _)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring

/-- Power-loss version of the common multiplicity-level refinement. -/
theorem dyadic_shading_refinement_power {D ν : ℝ} (hD : 0 < D) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ (n : ℕ), (n : ℝ) ≤ δ ^ (-D) →
      ∀ (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space),
      (∀ i, MeasurableSet (Y i)) →
      ∃ (k : ℕ) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space),
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        ENNReal.ofReal (δ ^ ν) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
        ∀ p ∈ ⋃ i, Z i,
          2 ^ k ≤ (Finset.univ.filter fun i => p ∈ Z i).card ∧
          (Finset.univ.filter fun i => p ∈ Z i).card < 2 ^ (k + 1) := by
  obtain ⟨d, hd, hlog⟩ := logarithmic_count_power hD hν
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd n hn Y hY
  obtain ⟨k, Z, _, hZ, hmass, hlevel⟩ := dyadic_shading_refinement volume Y hY
  refine ⟨k, Z, hZ, ?_, hlevel⟩
  have hlog' : ((Nat.log 2 n + 1 : ℕ) : ENNReal) ≤ ENNReal.ofReal (δ ^ (-ν)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hlog δ hδ hδd n hn)
  have hh : (∑ i, volume (Y i)) ≤ ENNReal.ofReal (δ ^ (-ν)) * ∑ i, volume (Z i) := by
    refine hmass.trans ?_
    simpa only [Fintype.card_fin] using mul_le_mul_left hlog' (∑ i, volume (Z i))
  have he : ENNReal.ofReal (δ ^ ν) * ENNReal.ofReal (δ ^ (-ν)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
    simp
  calc
    _ ≤ ENNReal.ofReal (δ ^ ν) * (ENNReal.ofReal (δ ^ (-ν)) * ∑ i, volume (Z i)) :=
      mul_le_mul_right hh _
    _ = _ := by rw [← mul_assoc, he, one_mul]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
