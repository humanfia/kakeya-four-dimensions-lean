-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.BallPrismSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PrismSelection
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover

/-! Direction selection when the old grain fits in a thickness-sized ball. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory

/-- The radius-sized exceptional old grains allow a three-dimensional angular
grid, at a cost polynomial only in the length enlargement. -/
theorem ball_prism_selection {d a b c L : ℝ} {n : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hca : c ≤ 100*a) (hL : 100000000*c ≤ L)
    (x v : Fin n → V) (z : V) (e : V ≃ₗᵢ[ℝ] V) (hv : ∀ i, ‖v i‖ = 1)
    (hmeet : ∀ i, ∃ p ∈ T d (x i) (v i) ∩ P a b c z e,
      4*L ≤ dist p (x i) ∧ 4*L ≤ dist p (x i+v i))
    (weight : Fin n → ℝ) (hw : ∀ i, 0 ≤ weight i) (hsum : 0 < ∑ i, weight i) :
    ∃ (S : Finset (Fin n)) (g : V ≃ₗᵢ[ℝ] V), S.Nonempty ∧
      (∑ i, weight i) ≤ 1000000000*(L/c)^3 * ∑ i ∈ S, weight i ∧
      d ≤ 10000*a ∧ 10000*a ≤ 10000*enlargedSlope b c*L ∧
      10000*enlargedSlope b c*L ≤ L ∧
      P a b c z e ⊆ P (10000*a/10) (10000*enlargedSlope b c*L/10) (L/10) z g ∧
      ∀ i ∈ S, Crosses d (10000*a) (10000*enlargedSlope b c*L) L (x i) (v i) z g ∧
        T d (x i) (v i) ∩ ball z (L/2) ⊆ P (10000*a) (10000*enlargedSlope b c*L) L z g := by
  classical
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hLp : 0 < L := by linarith
  have hcL : c ≤ L := by linarith
  have hR : 0 < enlargedSlope b c := enlargedSlope_pos hb hc
  have hRa := enlargedSlope_large_length hb.le hc hbc hL
  have hAB : 10000*a ≤ 10000*enlargedSlope b c*L := by nlinarith
  have hBL : 10000*enlargedSlope b c*L ≤ L := by
    have hh : enlargedSlope b c ≤ 1/1000000 := min_le_right _ _
    nlinarith
  let s := a/(3*L)
  have hs : 0 < s := by dsimp [s]; positivity
  let M : ℕ := ⌈s⁻¹⌉₊
  have hM : 1 ≤ (M : ℝ)*s := (rectangle_grid_size hs).1
  have hvb : ∀ i j, |v i j| ≤ M*s := by
    intro i j
    have hh := wz_move_two_long_grains_gain.abs_coord_le_norm (v i) j
    exact hh.trans ((hv i) ▸ hM)
  obtain ⟨K, hK, ref, href⟩ := wz_clustered_cover_volume_gain.finite_grid_representatives
    hn (fun i j => v i j) hs hvb
  have hKp : 0 < K := by rw [hK]; positivity
  have hKsize : (K : ℝ) ≤ 1000000000*(L/c)^3 := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ s⁻¹ by positivity)
    have hMbound : (M : ℝ) ≤ 3*L/a+1 := by
      dsimp [M, s]
      dsimp [s] at hceil
      simpa only [inv_div] using hceil.le
    have hLa : 1 ≤ L/c := (one_le_div hc).mpr hcL
    have hscale : L/a ≤ 100*(L/c) := by
      apply (div_le_iff₀ ha).mpr
      have hh := mul_le_mul_of_nonneg_left hca (show 0 ≤ L/c by positivity)
      have he : (L/c)*c = L := div_mul_cancel₀ L hc.ne'
      nlinarith
    have hm3 : (M : ℝ) ≤ 3*(L/a)+1 := by convert hMbound using 1 <;> ring
    have hbase : (2*M+1 : ℝ) ≤ 1000*(L/c) := by linarith
    rw [hK]
    push_cast
    calc
      _ ≤ (1000*(L/c))^3 := pow_le_pow_left₀ (by positivity) hbase 3
      _ = _ := by ring
  choose label hlabel using href
  obtain ⟨k, hk⟩ := weighted_scale_selection hKp Finset.univ label weight
  let S := Finset.univ.filter (fun i => label i = k)
  have hSne : S.Nonempty := by
    by_contra hh
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    change (∑ i, weight i) ≤ K * ∑ i ∈ S, weight i at hk
    rw [he] at hk
    simp only [Finset.sum_empty, mul_zero] at hk
    linarith
  obtain ⟨g, hg⟩ := wz_broad_grains_initialization.frame_last_of_unit (hv (ref k))
  have hcore : P a b c z e ⊆
      P (10000*a/10) (10000*enlargedSlope b c*L/10) (L/10) z g := by
    intro p hp
    have hpn := wz_clustered_cover_volume_gain.frozen_prism_norm ha.le hab hbc z e hp
    have hcj (j : Fin 3) : |g (p-z) j| ≤ c :=
      (wz_move_two_long_grains_gain.abs_coord_le_norm _ _).trans (by simpa only [g.norm_map] using hpn)
    exact ⟨by linarith [hcj 0], by linarith [hcj 1], by linarith [hcj 2]⟩
  refine ⟨S, g, hSne, hk.trans (mul_le_mul_of_nonneg_right hKsize
    (Finset.sum_nonneg (fun i _ => hw i))), by linarith, hAB, hBL, hcore, ?_⟩
  intro i hi
  have hik : label i = k := (Finset.mem_filter.mp hi).2
  have hcoord := hlabel i
  rw [hik] at hcoord
  have hclose : ‖v i-v (ref k)‖ ≤ a/L := by
    have hh := wz_clustered_cover_volume_gain.norm_le_coord_sum (v i-v (ref k))
    change ‖v i-v (ref k)‖ ≤ |v i 0-v (ref k) 0|+|v i 1-v (ref k) 1|+|v i 2-v (ref k) 2| at hh
    have he : 3*s = a/L := by dsimp [s]; ring
    linarith [hcoord 0, hcoord 1, hcoord 2]
  have htrans (j : Fin 3) (hj : j ≠ 2) : |g (v i) j| ≤ a/L := by
    have hh := wz_move_two_long_grains_gain.abs_coord_le_norm (g (v i-v (ref k))) j
    have hj0 : g (v (ref k)) j = 0 := by rw [hg]; simp [hj]
    simpa only [map_sub, PiLp.sub_apply, hj0, sub_zero, g.norm_map] using hh.trans
      (by simpa only [g.norm_map] using hclose)
  have hlong : 1/2 ≤ |g (v i) 2| := abs_long_of_transverse_small g (hv i)
    ((htrans 0 (by decide)).trans (by apply (div_le_iff₀ hLp).mpr; linarith))
    ((htrans 1 (by decide)).trans (by apply (div_le_iff₀ hLp).mpr; linarith))
  obtain ⟨p, hp, hpleft, hpright⟩ := hmeet i
  have hcros : Crosses d (10000*a) (10000*enlargedSlope b c*L) L (x i) (v i) z g := by
    refine prism_crosses_of_core_abs hd (by positivity) hAB hBL (by linarith) g (hv i) hlong
      ?_ ?_ hp.1 (hcore hp.2) hpleft hpright
    · have hh := (le_div_iff₀ hLp).mp (htrans 0 (by decide)); nlinarith
    · have hh := (le_div_iff₀ hLp).mp (htrans 1 (by decide)); nlinarith
  exact ⟨hcros, hcros.ball_subset hLp⟩

/-- A common enlarged-prism selector valid for every old grain length. -/
theorem enlarged_prism_selection_all {d a b c L : ℝ} {n : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc1 : c ≤ 1) (hL : 100000000*c ≤ L)
    (x v : Fin n → V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hv : ∀ i, ‖v i‖ = 1) (hcross : ∀ i, Crosses d a b c (x i) (v i) z e)
    (hmeet : ∀ i, ∃ p ∈ T d (x i) (v i) ∩ P a b c z e,
      4*L ≤ dist p (x i) ∧ 4*L ≤ dist p (x i+v i))
    (weight : Fin n → ℝ) (hw : ∀ i, 0 ≤ weight i) (hsum : 0 < ∑ i, weight i) :
    ∃ (S : Finset (Fin n)) (g : V ≃ₗᵢ[ℝ] V), S.Nonempty ∧
      (∑ i, weight i) ≤ 1000000000*(L/c)^3 * ∑ i ∈ S, weight i ∧
      d ≤ 10000*a ∧ 10000*a ≤ 10000*enlargedSlope b c*L ∧
      10000*enlargedSlope b c*L ≤ L ∧
      P a b c z e ⊆ P (10000*a/10) (10000*enlargedSlope b c*L/10) (L/10) z g ∧
      ∀ i ∈ S, Crosses d (10000*a) (10000*enlargedSlope b c*L) L (x i) (v i) z g ∧
        T d (x i) (v i) ∩ ball z (L/2) ⊆ P (10000*a) (10000*enlargedSlope b c*L) L z g := by
  by_cases hdc : d ≤ c/100
  · obtain ⟨S, g, hS, hret, hrest⟩ := enlarged_prism_selection hn hd hda hab hbc hc1 hdc hL
      x v z e hv hcross hmeet weight hw hsum
    refine ⟨S, g, hS, hret.trans (mul_le_mul_of_nonneg_right ?_
      (Finset.sum_nonneg (fun i _ => hw i))), hrest⟩
    have hc : 0 < c := hd.trans_le (hda.trans (hab.trans hbc))
    have hD : 1 ≤ L/c := (one_le_div hc).mpr (by linarith)
    nlinarith [sq_nonneg (L/c), mul_le_mul_of_nonneg_left hD (sq_nonneg (L/c))]
  · exact ball_prism_selection hn hd hda hab hbc (by linarith) hL x v z e hv hmeet weight hw hsum

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
