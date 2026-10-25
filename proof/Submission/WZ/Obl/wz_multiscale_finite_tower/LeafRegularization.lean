-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.LeafRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyRestriction
import Submission.WZ.Obl.wz_multiscale_finite_tower.DenseRestriction
import Submission.WZ.Obl.wz_multiscale_finite_tower.MultipleGrids

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced)

/-- After a small mass restriction, make every surviving leaf dense and balance
all ancestor partitions, at a controlled additional mass cost. -/
theorem regularize_dense_leaves {d θ τ K L h : ℝ} {J : ℕ} (T : TubeHierarchy J)
    {Y Z : Fin (T.layer J).card → Set Space} {u : Space}
    (F : AlignedFamily d (d ^ θ) K L u h (T.layer J).card
      (T.layer J).position (T.layer J).direction Y)
    (hd : 0 < d) (hd1 : d < 1) (hτ : 0 < τ) (hθ : θ ≤ τ)
    (hZ : ∀ i, Z i ⊆ Y i)
    (hret : ENNReal.ofReal (d ^ τ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i))
    (q : ℕ) (hq : 0 < q) (hcard : ((T.layer J).card : ℝ) < (d ^ (-τ)) ^ q)
    (hsmall : 2 * (q : ℝ) ^ (J + 1) * d ^ τ ≤ 1) (hsmall56 : 56 * d ^ τ ≤ 1) :
    ∃ S : Finset (Fin (T.layer J).card), S.Nonempty ∧
      ENNReal.ofReal (d ^ (2 * τ)) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i) ∧
      (∀ i ∈ S, ENNReal.ofReal (d ^ (θ + τ) / 2 * d ^ 2) ≤ volume (Z i)) ∧
      (∀ j, j ≤ J → Balanced S (T.ancestor j) (d ^ (-τ))) ∧
      d ^ (4 * τ) * (T.layer J).card ≤ S.card := by
  classical
  have hZfin (i) : volume (Z i) ≠ ⊤ := ne_top_of_le_ne_top measure_ball_ne_top
    (measure_mono ((hZ i).trans ((F.shading i).trans (F.ball i))))
  have hden := shading_density_of_mass_retention hd F.mass_lower hret
  obtain ⟨U, hU, hUmass, hUdense⟩ := heavy_shadings hd (Real.rpow_pos_of_pos hd _)
    F.nonempty Z hZfin hden
  have hR : 1 < d ^ (-τ) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hd hd1 (by linarith)
  obtain ⟨color, hcolor⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.exists_size_color
    (T.layer J).card q (d ^ (-τ)) hq hR hcard
  obtain ⟨S, hSU, hmass, hbal⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.regularize_nested
    T.ancestor (J + 1) q (T.layer J).card hq (d ^ (-τ)) color hcolor
    (fun j k hjk hk i i' he => T.nested hjk (by omega) he) U
    ((Finset.card_le_card (Finset.subset_univ U)).trans_eq (by simp)) (fun i => volume (Z i))
  have htwo : (∑ i, volume (Z i)) ≤ (2 : ℝ≥0∞) * ∑ i ∈ U, volume (Z i) := by
    calc
      _ = (2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * ∑ i, volume (Z i)) := by
        rw [one_div, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ _ := mul_le_mul' le_rfl hUmass
  have hchain : ENNReal.ofReal (d ^ τ) * (∑ i, volume (Y i)) ≤
      ENNReal.ofReal (2 * (q : ℝ) ^ (J + 1)) * ∑ i ∈ S, volume (Z i) := by
    apply (hret.trans htwo).trans
    have hh := mul_le_mul' (le_refl (2 : ℝ≥0∞)) hmass
    simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_pow (Nat.cast_nonneg q), mul_assoc] using hh
  have hretain : ENNReal.ofReal (d ^ (2 * τ)) * (∑ i, volume (Y i)) ≤
      ∑ i ∈ S, volume (Z i) := by
    have he : d ^ (2 * τ) = d ^ τ * d ^ τ := by rw [← Real.rpow_add hd]; congr 1; ring
    rw [he, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), mul_assoc]
    apply (mul_le_mul' le_rfl hchain).trans
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
    have hc : ENNReal.ofReal (d ^ τ * (2 * (q : ℝ) ^ (J + 1))) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith only [hsmall])
    simpa only [one_mul] using mul_le_mul' hc (le_refl (∑ i ∈ S, volume (Z i)))
  have hS : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hnR : (0 : ℝ) < (T.layer J).card := Nat.cast_pos.mpr F.nonempty
    have hpos : 0 < ∑ i, volume (Y i) :=
      (ENNReal.ofReal_pos.mpr (by positivity)).trans_le F.mass_lower
    rw [he, Finset.sum_empty] at hretain
    exact (not_lt_of_ge hretain) (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hd _)).ne' hpos.ne')
  refine ⟨S, hS, hretain, fun i hi => hUdense i (hSU hi), fun j hj => hbal j (by omega), ?_⟩
  have hc := retained_subset_cardinality hd (Real.rpow_nonneg hd.le (2 * τ)) S F.mass_lower
    (fun i hi => (measure_mono ((hZ i).trans (F.shading i))).trans
      (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hd.le hd1.le _ _ (F.unit i))) hretain
  have hp : d ^ (4 * τ) ≤ d ^ (2 * τ + θ) / 56 := density_power_bound hd (by norm_num)
    (power_coefficient_bound hd hd1.le (by norm_num) le_rfl (by linarith) hsmall56)
  rw [Real.rpow_add hd] at hp
  exact (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)).trans hc

end WangZahlLot.Obl.wz_multiscale_finite_tower
