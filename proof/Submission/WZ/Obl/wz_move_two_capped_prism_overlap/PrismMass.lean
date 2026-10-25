-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.PrismMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_move_two_long_grains_gain.CrossBox
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyLevel
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_normalized_projection_iteration.Expansion

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, PrismMass.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P T K q)

/-- A prism's total fine incidence mass is bounded by convex counting and
the amount of one unit tube inside its containing ball. No common
multiplicity or cross-prism avoidance is needed. -/
theorem prism_mass_upper {ω ζ δ h ρ c m : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hm : 0 ≤ m) (h4 : 4 * δ ≤ c)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hK : K δ m n x v) (H : D.Valid ω ζ δ h ρ c x v Y o) (j : Fin D.L) :
    ∑ i, volume (D.W i j) ≤ O (1492992 * m * D.a * ρ) := by
  classical
  rcases H with ⟨ha, hab, hbc, hc, hW, _, _, hcross, _⟩
  have ha0 := hδ.trans_le ha
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have hρ0 : 0 < ρ := (mul_pos_iff.mp hb0).resolve_right
    (by intro h; linarith [h.2]) |>.1
  let B := P (18 * D.a / c) (18 * (ρ * c) / c) 4 (D.z j) (D.e j)
  let S := Finset.univ.filter (fun i => (D.W i j).Nonempty)
  have hSB (i : Fin n) (hi : i ∈ S) : T δ (x i) (v i) ⊆ B := by
    have hi' := (Finset.mem_filter.mp hi).2
    have hends := (hcross i j hi').2.2
    exact WangZahlLot.Obl.wz_move_two_long_grains_gain.tube_subset_enlarged_box
      (hv i) hδ ha hab hbc hc h4 (hends (-c / 2) (by simp)) (hends (c / 2) (by simp))
  have hcard : (S.card : ℝ) ≤ q n {i | T δ (x i) (v i) ⊆ B} := by
    have hh := Set.ncard_le_ncard (s := (↑S : Set (Fin n))) (t := {i | T δ (x i) (v i) ⊆ B})
      (fun i hi => hSB i hi)
    rw [Set.ncard_coe_finset] at hh
    exact Nat.cast_le.mpr hh
  have hcount : (S.card : ℝ) * δ ^ 2 ≤ m * (1296 * D.a * ρ / c) := by
    have hKT := hK B (WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_convex _ _ _ _ _)
    have hvol : volume B = O (1296 * D.a * ρ / c) := by
      dsimp only [B]
      rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume
        (by positivity) (by positivity) (by norm_num)]
      congr 1
      field_simp
      ring
    change O (q n {i | T δ (x i) (v i) ⊆ B} * δ ^ 2) ≤ O m * volume B at hKT
    rw [hvol, ← ENNReal.ofReal_mul hm] at hKT
    apply (mul_le_mul_of_nonneg_right hcard (sq_nonneg δ)).trans
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hKT
  have hpiece (i : Fin n) : volume (D.W i j) ≤ O (1152 * c * δ ^ 2) := by
    have hp : D.W i j ⊆ T δ (x i) (v i) ∩ closedBall (D.z j) c := by
      intro p hp
      have hh := (hW i j).2.1 hp
      exact ⟨hY i hh.1,
        WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_subset_closedBall hab hbc hc0.le _ _ hh.2⟩
    exact (measure_mono hp).trans
      (WangZahlLot.Obl.wz_normalized_projection_iteration.tube_inter_ball_volume_le
        hδ (ha.trans (hab.trans hbc)) (x i) (v i) (D.z j) (hv i))
  have hsum : ∑ i, volume (D.W i j) ≤ O ((S.card : ℝ) * (1152 * c * δ ^ 2)) := by
    calc
      _ = ∑ i ∈ S, volume (D.W i j) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        have he : D.W i j = ∅ := Set.not_nonempty_iff_eq_empty.mp
          (by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
        simp only [he, measure_empty]
      _ ≤ ∑ _i ∈ S, O (1152 * c * δ ^ 2) := Finset.sum_le_sum (fun i _ => hpiece i)
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [O, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  apply hsum.trans (ENNReal.ofReal_le_ofReal ?_)
  have hh := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ 1152 * c)
  have he : 1152 * c * (m * (1296 * D.a * ρ / c)) = 1492992 * m * D.a * ρ := by
    field_simp
    ring
  rw [he] at hh
  nlinarith

/-- Pointwise broadness supplies a minimum fine multiplicity in every
nonempty prism shading. -/
theorem prism_broad_min_count {ω ζ δ h ρ c : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hv : ∀ i, ‖v i‖ = 1)
    (H : D.Valid ω ζ δ h ρ c x v Y o) (j : Fin D.L) (p : V)
    (hp : p ∈ ⋃ i, D.W i j) :
    δ ^ h * (ρ / δ) ^ (ω * ζ / 100) ≤ q n {i | p ∈ D.W i j} := by
  rcases H with ⟨ha, hab, hbc, hc, _, _, _, _, hbroad, _⟩
  have hc0 := hδ.trans_le (ha.trans (hab.trans hbc))
  have hρ0 : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hδρ : δ ≤ ρ := (ha.trans hab).trans (by nlinarith)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have hcap : (1 : ℝ) ≤ q n {k | p ∈ D.W k j ∧ min ‖v k - v i‖ ‖v k + v i‖ ≤ δ} := by
    have hn : 1 ≤ ({k | p ∈ D.W k j ∧ min ‖v k - v i‖ ‖v k + v i‖ ≤ δ} : Set (Fin n)).ncard := by
      apply Nat.one_le_iff_ne_zero.mpr
      have hmem : i ∈ ({k | p ∈ D.W k j ∧ min ‖v k - v i‖ ‖v k + v i‖ ≤ δ} : Set (Fin n)) :=
        ⟨hi, by simp [hδ.le]⟩
      exact Set.ncard_ne_zero_of_mem hmem
    exact_mod_cast hn
  have hb := hcap.trans (hbroad j p (v i) δ (hv i) le_rfl hδρ)
  have hcoef : 0 < δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100) := by positivity
  have he : (δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100))⁻¹ =
      δ ^ h * (ρ / δ) ^ (ω * ζ / 100) := by
    rw [mul_inv, ← Real.rpow_neg hδ.le, neg_neg, ← Real.inv_rpow (div_nonneg hδ.le hρ0.le), inv_div]
  rw [← he]
  exact (inv_le_iff_one_le_mul₀ hcoef).mpr (by simpa only [mul_comm] using hb)

/-- Broadness, prism density and convex counting force short grains as
soon as the angular scale is separated from the fine radius. -/
theorem prism_length_budget {ω ζ δ h ρ c m : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hm : 0 ≤ m) (h4 : 4 * δ ≤ c)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hK : K δ m n x v) (H : D.Valid ω ζ δ h ρ c x v Y o) (j : Fin D.L) :
    δ ^ (2 * h) * (ρ / δ) ^ (ω * ζ / 100) * c ^ 2 ≤ 1492992 * m := by
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, _, hW, _, hdense, _⟩
  have ha0 := hδ.trans_le ha
  have hb0 := ha0.trans_le hab
  have hc0 := hb0.trans_le hbc
  have hρ0 : 0 < ρ := (mul_pos_iff.mp hb0).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hcount := WangZahlLot.Obl.wz_clustered_cover_volume_gain.body_level_mul_volume_le_mass
    (fun i => (hW i j).1) (prism_broad_min_count D hδ hv H j)
  have hupper := prism_mass_upper D hδ hm h4 hv hY hK H j
  have hchain := (mul_le_mul' le_rfl (hdense j)).trans (hcount.trans hupper)
  change O (δ ^ h * (ρ / δ) ^ (ω * ζ / 100)) *
    (O (δ ^ h) * volume (P D.a (ρ * c) c (D.z j) (D.e j))) ≤ _ at hchain
  rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume ha0.le hb0.le hc0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _),
    ← ENNReal.ofReal_mul (by positivity)] at hchain
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ 1492992 * m * D.a * ρ)).mp hchain
  have hpow : δ ^ (2 * h) = δ ^ h * δ ^ h := by
    rw [show 2 * h = h + h by ring, Real.rpow_add hδ]
  apply le_of_mul_le_mul_right (a := D.a * ρ) _ (mul_pos ha0 hρ0)
  rw [hpow]
  nlinarith [hr]

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
