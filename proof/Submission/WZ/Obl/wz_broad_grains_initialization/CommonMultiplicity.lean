-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.CommonMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.PointwiseRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicPower

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (bodyCount)
open scoped Classical

/-- Dyadic multiplicity selection as a common point cut. The explicit form
of the cut preserves pointwise directional proportions. -/
theorem common_multiplicity_cut {n : ℕ} (Y : Fin n → Set Space)
    (hY : ∀ i, MeasurableSet (Y i)) :
    ∃ (G : Set Space) (m : ℝ), MeasurableSet G ∧ 0 < m ∧
      (∑ i, volume (Y i)) ≤ ENNReal.ofReal (Nat.log 2 n + 1 : ℝ) *
        ∑ i, volume (Y i ∩ G) ∧
      ∀ p ∈ ⋃ i, Y i ∩ G, bodyCount (fun i => Y i ∩ G) p ∈ Set.Icc m (2 * m) := by
  classical
  let K := Nat.log 2 n + 1
  let pattern : Space → Finset (Fin n) := fun p => Finset.univ.filter (fun i => p ∈ Y i)
  have hpat (p : Space) (i : Fin n) : i ∈ pattern p ↔ p ∈ Y i := by simp [pattern]
  let G : Fin K → Set Space := fun k => {p | Nat.log 2 (pattern p).card = (k : ℕ)}
  have hG (k : Fin K) : MeasurableSet (G k) :=
    wz_measurable_angular_selection.measurableSet_pattern hY pattern hpat
      (fun S => Nat.log 2 S.card = (k : ℕ))
  have hcover (i : Fin n) : Y i ⊆ ⋃ k, Y i ∩ G k := by
    intro p hp
    have hk : Nat.log 2 (pattern p).card < K := by
      have hh := Nat.log_mono_right (pattern p).card_le_univ (b := 2)
      simpa only [Fintype.card_fin, K] using Nat.lt_succ_of_le hh
    exact Set.mem_iUnion.mpr ⟨⟨Nat.log 2 (pattern p).card, hk⟩, hp, rfl⟩
  have hsum : (∑ i, volume (Y i)) ≤ ∑ k, ∑ i, volume (Y i ∩ G k) := by
    calc
      _ ≤ ∑ i, ∑ k, volume (Y i ∩ G k) := Finset.sum_le_sum fun i _ =>
        (measure_mono (hcover i)).trans (by simpa only [tsum_fintype] using measure_iUnion_le (fun k => Y i ∩ G k))
      _ = _ := Finset.sum_comm
  letI : Nonempty (Fin K) := ⟨⟨0, Nat.succ_pos _⟩⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
    (fun k => ∑ i, volume (Y i ∩ G k)) Finset.univ_nonempty
  refine ⟨G k, (2 : ℝ) ^ (k : ℕ), hG k, by positivity, ?_, ?_⟩
  · apply hsum.trans
    calc
      _ ≤ ∑ _l : Fin K, ∑ i, volume (Y i ∩ G k) := Finset.sum_le_sum fun l hl => hk l hl
      _ = _ := by simp [K, nsmul_eq_mul, ENNReal.ofReal_add]
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    have hne : (pattern p).card ≠ 0 := Finset.card_ne_zero.mpr ⟨i, (hpat p i).mpr hi.1⟩
    have hlog : Nat.log 2 (pattern p).card = (k : ℕ) := hi.2
    have hcount : bodyCount Y p = ((pattern p).card : ℝ) := by
      simp [bodyCount, pattern, Set.ncard_eq_toFinset_card']
    rw [body_count_cut, if_pos hi.2, hcount]
    have hlo := Nat.pow_log_le_self 2 hne
    have hhi := (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (pattern p).card).le
    rw [hlog] at hlo hhi
    constructor
    · exact_mod_cast hlo
    · rw [pow_succ, mul_comm] at hhi
      exact_mod_cast hhi

/-- Polynomially many fine tubes make the common multiplicity cut cost an
arbitrarily small power of the fine radius. -/
theorem common_multiplicity_cut_power {D ν : ℝ} (hD : 0 < D) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ (n : ℕ), (n : ℝ) ≤ δ ^ (-D) → ∀ Y : Fin n → Set Space,
      (∀ i, MeasurableSet (Y i)) →
      ∃ (G : Set Space) (m : ℝ), MeasurableSet G ∧ 0 < m ∧
        ENNReal.ofReal (δ ^ ν) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Y i ∩ G) ∧
        ∀ p ∈ ⋃ i, Y i ∩ G, bodyCount (fun i => Y i ∩ G) p ∈ Set.Icc m (2 * m) := by
  obtain ⟨d, hd, hlog⟩ := wz_clustered_cover_volume_gain.Parent.logarithmic_count_power hD hν
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd n hn Y hY
  obtain ⟨G, m, hG, hm, hmass, hlevel⟩ := common_multiplicity_cut Y hY
  refine ⟨G, m, hG, hm, ?_, hlevel⟩
  have hbound := hmass.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hlog δ hδ hδd n hn)) le_rfl)
  calc
    _ ≤ ENNReal.ofReal (δ ^ ν) *
        (ENNReal.ofReal (δ ^ (-ν)) * ∑ i, volume (Y i ∩ G)) := mul_le_mul' le_rfl hbound
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
      simp

end WangZahlLot.Obl.wz_broad_grains_initialization
