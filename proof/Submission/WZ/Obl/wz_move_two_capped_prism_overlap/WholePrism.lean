-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.WholePrism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.NeighborhoodGain
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Budgets
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, WholePrism.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O A E P)

/-- The whole shading of any prism containing `p` fits into the `4c`-ball
around `p`. Thus this density estimate does not need regularity of its pieces. -/
theorem whole_prism_ball_density {ω ζ δ h ρ c : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (H : D.Valid ω ζ δ h ρ c x v Y o)
    (i : Fin n) (p : V) (hp : p ∈ ⋃ j, D.W i j) :
    O (δ ^ h * D.a * ρ * c ^ 2) ≤ volume ((⋃ k, Y k) ∩ ball p (4 * c)) := by
  obtain ⟨j, hpj⟩ := mem_iUnion.mp hp
  rcases H with ⟨ha, hab, hbc, _, hW, _, hdense, _⟩
  have ha0 := hδ.trans_le ha
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have hpU := (hW i j).2.1 hpj |>.2
  have hball := WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_subset_closedBall
    hab hbc hc0.le (D.z j) (D.e j)
  have hsub : (⋃ k, D.W k j) ⊆ (⋃ k, Y k) ∩ ball p (4 * c) := by
    intro q hq
    obtain ⟨k, hqk⟩ := mem_iUnion.mp hq
    have hqY := (hW k j).2.1 hqk
    refine ⟨mem_iUnion.mpr ⟨k, hqY.1⟩, ?_⟩
    have hqz : dist q (D.z j) ≤ c := hball hqY.2
    have hpz : dist p (D.z j) ≤ c := hball hpU
    apply mem_ball.mpr
    calc
      dist q p ≤ dist q (D.z j) + dist (D.z j) p := dist_triangle _ _ _
      _ ≤ 2 * c := by rw [dist_comm (D.z j) p]; linarith
      _ < 4 * c := by linarith
  calc
    _ = O (δ ^ h) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) := by
      rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume ha0.le hb0.le hc0.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le h)]
      congr 1
      ring
    _ ≤ volume (⋃ k, D.W k j) := hdense j
    _ ≤ _ := measure_mono hsub

/-- Moderately round prisms at a radius separated from `δ` already give the
volume gain. This branch uses all original incidences, including points where
their local density inside an individual prism is poor. -/
theorem gain_of_nonthin_prisms {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ κ η τ d₀ : ℝ, 0 < κ ∧ 0 < η ∧ 0 < τ ∧ η ≤ τ ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → h ≤ η →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y → ∀ ω' ζ ρ c (D : PrismData n),
      D.Valid ω' ζ δ h ρ c x v Y 1 → δ ^ (1 - b) ≤ 8 * c → c ≤ 1 / 8 →
      δ ^ τ ≤ D.a * ρ / c →
      O (κ * δ ^ (ω - b * ω / 2) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        volume (⋃ i, Y i) := by
  obtain ⟨κ, η, ν, dN, hκ, hη, hν, hην, _, hdN, hdN100, HN⟩ :=
    gain_of_dense_neighborhoods hσ hσ2 hω hω1 hE hb hb1
  obtain ⟨dP, hdP, HP⟩ := WangZahlLot.Obl.wz_normalized_projection_coarse_fine.exists_power_absorption
    (C := 64) (p := 5 * ν) (r := 0) (by norm_num) (by linarith)
  refine ⟨κ, η, 6 * ν, min dN dP, hκ, hη, by positivity, by linarith,
    lt_min hdN hdP, (min_le_left _ _).trans hdN100, ?_⟩
  intro δ h hδ hδcut hhη n x v Y hA ω' ζ ρ c D H hclo hchi hround
  have hδN := hδcut.trans (min_le_left _ _)
  have hδP := hδcut.trans (min_le_right _ _)
  have hδlt : δ < 1 := (hδN.trans hdN100).trans_lt (by norm_num)
  have hδ1 := hδlt.le
  have hhν := hhη.trans hην
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, _, hW, hmass, _⟩
  have hc : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
  let B : ℝ := 1 - Real.logb δ (8 * c)
  have hpow : δ ^ (1 - B) = 8 * c := by
    rw [show 1 - B = Real.logb δ (8 * c) by dsimp [B]; ring]
    exact Real.rpow_logb hδ hδlt.ne (by positivity)
  have hbB : b ≤ B := by
    have hh : δ ^ (1 - b) ≤ δ ^ (1 - B) := by rwa [hpow]
    have hh' := (Real.rpow_le_rpow_left_iff_of_base_lt_one hδ hδlt).mp hh
    linarith
  have hB1 : B ≤ 1 := by
    have hh : δ ^ (1 - B) ≤ δ ^ (0 : ℝ) := by rw [hpow, Real.rpow_zero]; linarith
    have hh' := (Real.rpow_le_rpow_left_iff_of_base_lt_one hδ hδlt).mp hh
    linarith
  have hrad : δ ^ (1 - B) / 2 = 4 * c := by rw [hpow]; ring
  let W (i : Fin n) : Set V := ⋃ j, D.W i j
  have hWm (i : Fin n) : MeasurableSet (W i) := MeasurableSet.iUnion fun j => (hW i j).1
  have hWY (i : Fin n) : W i ⊆ Y i :=
    iUnion_subset fun j => (hW i j).2.1.trans inter_subset_left
  have hWvol (i : Fin n) : volume (W i) = ∑ j, volume (D.W i j) := by
    change volume (⋃ j, D.W i j) = _
    rw [measure_iUnion, tsum_fintype]
    · intro j j' hne
      exact (hW i j).2.2 j' hne
    · exact fun j => (hW i j).1
  apply HN δ B hδ hδN hbB hB1 n x v Y W
    (WangZahlLot.Obl.wz_multiscale_finite_tower.Admissible.mono_error hA hδ hδ1 hhη)
    (fun i => ⟨hWm i, hWY i⟩) ?_ ?_
  · calc
      _ ≤ O (δ ^ h) * ∑ i, volume (Y i) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhν)) le_rfl
      _ ≤ ∑ i, ∑ j, volume (D.W i j) := hmass
      _ = _ := by simp_rw [hWvol]
  · intro i p hp
    rw [hrad]
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) (whole_prism_ball_density D hδ H i p hp)
    have hsmall : 64 * δ ^ (5 * ν) ≤ 1 := by simpa using HP δ hδ hδP
    have hcoef : 64 * δ ^ (12 * ν) ≤ δ ^ h * δ ^ (6 * ν) := by
      calc
        _ = (64 * δ ^ (5 * ν)) * δ ^ (7 * ν) := by
          rw [mul_assoc, ← Real.rpow_add hδ]
          congr 2
          ring
        _ ≤ δ ^ (7 * ν) := by nlinarith [Real.rpow_pos_of_pos hδ (7 * ν)]
        _ ≤ δ ^ (h + 6 * ν) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        _ = _ := Real.rpow_add hδ _ _
    have hshape : δ ^ (6 * ν) * c ≤ D.a * ρ := (le_div_iff₀ hc).mp hround
    calc
      _ = (64 * δ ^ (12 * ν)) * c ^ 3 := by ring
      _ ≤ (δ ^ h * δ ^ (6 * ν)) * c ^ 3 := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (δ ^ h * c ^ 2) * (δ ^ (6 * ν) * c) := by ring
      _ ≤ (δ ^ h * c ^ 2) * (D.a * ρ) := mul_le_mul_of_nonneg_left hshape (by positivity)
      _ = _ := by ring

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
