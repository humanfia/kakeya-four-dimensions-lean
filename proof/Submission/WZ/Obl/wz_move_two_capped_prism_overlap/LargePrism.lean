-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.LargePrism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_move_two_fibre_multiplicity_gain.SharpMultiplicity
import Submission.WZ.Obl.wz_multiscale_finite_tower.Elementary

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, LargePrism.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O A P)

theorem admissible_volume_factor_upper {δ h σ : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y) :
    (n * δ ^ 2) * (n * δ) ^ (-σ) ≤ 128 * δ ^ (-(2 * h)) := by
  have hA' : WangZahlLot.Obl.wz_multiscale_finite_tower.FrameAdmissible δ δ h n x v Y := hA
  have hcard := hA'.card_bound hδ
  have hpow := WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain.slab_power_lower
    hδ hδ1 hh hσ hσ1 hA
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
  have hinv : (n * δ) ^ (-σ) ≤ 8 * δ ^ (-h) := by
    rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) * δ), Real.rpow_neg hδ.le]
    rw [inv_le_iff_one_le_mul₀ (by positivity : 0 < ((n : ℝ) * δ) ^ σ)]
    have he : (8 * (δ ^ h)⁻¹) * ((n : ℝ) * δ) ^ σ =
        (8 * ((n : ℝ) * δ) ^ σ) / δ ^ h := by ring
    rw [he, le_div_iff₀ (Real.rpow_pos_of_pos hδ h)]
    simpa only [one_mul] using hpow
  calc
    _ ≤ (16 * δ ^ (-h)) * (8 * δ ^ (-h)) :=
      mul_le_mul hcard hinv (by positivity) (by positivity)
    _ = 128 * δ ^ (-(2 * h)) := by
      calc
        _ = 128 * (δ ^ (-h) * δ ^ (-h)) := by ring
        _ = _ := by rw [← Real.rpow_add hδ]; congr 2; ring

theorem valid_prism_count_pos {ω ζ δ h ρ c : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V} {o : ℕ}
    (hδ : 0 < δ) (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (H : D.Valid ω ζ δ h ρ c x v Y o) : 0 < D.L := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
  have hmassY : 0 < ∑ i, volume (Y i) :=
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < δ ^ h * n * δ ^ 2)).trans_le hA.2.2.2.1
  have hmass : 0 < ∑ i, ∑ j, volume (D.W i j) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h)).ne' hmassY.ne' ).trans_le H.2.2.2.2.2.1
  by_contra hnot
  have he : D.L = 0 := by omega
  have : IsEmpty (Fin D.L) := Fin.isEmpty_iff.mpr he
  simp at hmass

/-- A single prism whose shortest side is a sufficiently large power of
the fine radius already gives the desired gain by its shading density. -/
theorem gain_of_large_short_side {σ ω ζ δ h ρ c : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V} {o : ℕ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (_hω : 0 < ω)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hhω : h ≤ ω / 8)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (H : D.Valid ω ζ δ h ρ c x v Y o) (hlarge : δ ^ (ω / 8) ≤ D.a) :
    O ((1 / 128 : ℝ) * δ ^ (ω - ω / 4) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
      volume (⋃ i, Y i) := by
  have hfac := admissible_volume_factor_upper hδ hδ1 hh hσ hσ1 hA
  have hL := valid_prism_count_pos D hδ hA H
  let j : Fin D.L := ⟨0, hL⟩
  rcases H with ⟨ha, hab, hbc, hc, hW, _, hdense, _⟩
  have ha0 : 0 < D.a := hδ.trans_le ha
  have hc0 : 0 < c := ha0.trans_le (hab.trans hbc)
  have hb0 : 0 < ρ * c := ha0.trans_le hab
  have hvol : O (δ ^ h * D.a ^ 3) ≤ volume (⋃ i, Y i) := by
    apply le_trans _ ((hdense j).trans (measure_mono ?_))
    · change O (δ ^ h * D.a ^ 3) ≤ O (δ ^ h) * volume (P D.a (ρ * c) c (D.z j) (D.e j))
      rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume
        ha0.le hb0.le hc0.le]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le h)]
      apply ENNReal.ofReal_le_ofReal
      gcongr
      calc D.a ^ 3 = D.a * D.a * D.a := by ring
        _ ≤ D.a * (ρ * c) * c := by gcongr; exact hab.trans hbc
    · exact iUnion_mono fun i => (hW i j).2.1.trans inter_subset_left
  apply le_trans (ENNReal.ofReal_le_ofReal _) hvol
  calc
    (1 / 128 : ℝ) * δ ^ (ω - ω / 4) * (n * δ ^ 2) * (n * δ) ^ (-σ) =
        (1 / 128 : ℝ) * δ ^ (ω - ω / 4) * ((n * δ ^ 2) * (n * δ) ^ (-σ)) := by ring
    _ ≤ (1 / 128 : ℝ) * δ ^ (ω - ω / 4) * (128 * δ ^ (-(2 * h))) := by gcongr
    _ = δ ^ (ω - ω / 4 - 2 * h) := by
      rw [show (1 / 128 : ℝ) * δ ^ (ω - ω / 4) * (128 * δ ^ (-(2 * h))) =
        δ ^ (ω - ω / 4) * δ ^ (-(2 * h)) by ring, ← Real.rpow_add hδ]
      congr 1
    _ ≤ δ ^ (h + 3 * (ω / 8)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    _ = δ ^ h * (δ ^ (ω / 8)) ^ 3 := by
      rw [Real.rpow_add hδ, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 2
      ring
    _ ≤ δ ^ h * D.a ^ 3 := by gcongr

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
