-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Containment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Lines
import Submission.WZ.Obl.wz_normalized_projection_iteration.Interior
import Submission.WZ.Obl.wz_normalized_projection_iteration.Convex

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric MeasureTheory
open scoped ENNReal Pointwise

/-- Axial contraction commutes with the height parametrization of a line. -/
theorem linePoint_homothety {z w : Space} (hw2 : w 2 ≠ 0) (p : Space) (R : ℝ) :
    linePoint z w ((AffineMap.homothety (z + (1 / 2 : ℝ) • w) R p) 2) =
      AffineMap.homothety (z + (1 / 2 : ℝ) • w) R (linePoint z w (p 2)) := by
  have hm := linePoint_at_segment (x := z) hw2 (1 / 2 : ℝ)
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  unfold linePoint at hm ⊢
  rw [add_smul, mul_smul, sub_smul]
  have hbase : (lineBase z w) + (z + (1 / 2 : ℝ) • w) 2 • lineSlope w =
      z + (1 / 2 : ℝ) • w := hm
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hbase
  rw [← hbase]
  module

/-- A point near the supporting line and in the unit ball lies in a fixed axial dilation. -/
theorem mem_homothetic_tube {r R : ℝ} (hr : 0 < r) (hR : 10 ≤ R)
    {z w p : Space} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ = 1)
    (hw2 : (1 / 2 : ℝ) ≤ w 2) (hp : ‖p‖ ≤ 1)
    (hnear : dist p (linePoint z w (p 2)) < R * r) :
    p ∈ AffineMap.homothety (z + (1 / 2 : ℝ) • w) R '' Tube r z w := by
  have hRp : 0 < R := by linarith
  have hRi : 0 < R⁻¹ := inv_pos.mpr hRp
  have hRi1 : R⁻¹ ≤ 1 / 10 := by
    rw [← one_div, div_le_iff₀ hRp]
    linarith
  let m : Space := z + (1 / 2 : ℝ) • w
  let q : Space := AffineMap.homothety m R⁻¹ p
  have hp2 := abs_le.mp ((coordinate_abs_le p 2).trans hp)
  have hz2 := abs_le.mp ((coordinate_abs_le z 2).trans hz)
  have hw2' : w 2 ≤ 1 := (le_abs_self _).trans ((coordinate_abs_le w 2).trans_eq hw)
  have hq2 : q 2 = z 2 + w 2 / 2 + R⁻¹ * (p 2 - (z 2 + w 2 / 2)) := by
    simp only [q, m, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
      PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  have hqI : q 2 ∈ Icc (z 2) (z 2 + w 2) := by
    have habs : |p 2 - (z 2 + w 2 / 2)| ≤ 5 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hp2.1, hp2.2, hz2.1, hz2.2]
    have hh : |R⁻¹ * (p 2 - (z 2 + w 2 / 2))| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_pos hRi]
      have := mul_le_mul hRi1 habs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 10)
      norm_num at this
      exact this
    rw [abs_le] at hh
    rw [hq2]
    constructor <;> linarith [hh.1, hh.2]
  have hqnear : dist q (linePoint z w (q 2)) < r := by
    rw [show linePoint z w (q 2) =
      AffineMap.homothety m R⁻¹ (linePoint z w (p 2)) from
        linePoint_homothety (by linarith) p R⁻¹]
    change dist (AffineMap.homothety m R⁻¹ p)
      (AffineMap.homothety m R⁻¹ (linePoint z w (p 2))) < r
    rw [dist_homothety, Real.norm_eq_abs, abs_of_pos hRi]
    calc
      _ < R⁻¹ * (R * r) := mul_lt_mul_of_pos_left hnear hRi
      _ = r := by rw [← mul_assoc, inv_mul_cancel₀ hRp.ne', one_mul]
  refine ⟨q, mem_thickening_iff.mpr
    ⟨linePoint z w (q 2), linePoint_mem_segment (by linarith) hqI, hqnear⟩, ?_⟩
  change AffineMap.homothety m R (AffineMap.homothety m R⁻¹ p) = p
  rw [← AffineMap.homothety_mul_apply, mul_inv_cancel₀ hRp.ne', AffineMap.homothety_one]
  rfl

/-- Nearby line parameters put every fine tube inside a fixed dilation of its coarse tube. -/
theorem fine_tube_subset_dilation {δ r : ℝ} (hr : 0 < r) (hδr : δ ≤ r)
    {x v z w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ v 2) (hw2 : (1 / 2 : ℝ) ≤ w 2)
    (hz : ‖z‖ ≤ 1) (hball : Tube δ x v ⊆ ball 0 1)
    (hbase : ‖lineBase x v - lineBase z w‖ ≤ 20 * r)
    (hdir : ‖v - w‖ ≤ r) :
    Tube δ x v ⊆ AffineMap.homothety (z + (1 / 2 : ℝ) • w) (100 : ℝ) '' Tube r z w := by
  intro p hp
  have hp1 : ‖p‖ ≤ 1 := (by simpa using hball hp : ‖p‖ < 1).le
  apply mem_homothetic_tube hr (by norm_num) hz hw hw2 hp1
  have hnear := linePoint_near_tube hv hv2 hp
  rw [dist_comm] at hnear
  have hparams := linePoint_dist_le (x := x) (y := z) hv hw hv2 hw2
    ((coordinate_abs_le p 2).trans hp1)
  have htri := dist_triangle p (linePoint x v (p 2)) (linePoint z w (p 2))
  linarith

/-- One convex enlargement simultaneously contains the fixed axial dilates of all its tubes. -/
theorem exists_convex_tube_dilation_container {r : ℝ} (hr : 0 < r)
    {W : Set Space} (hW : Convex ℝ W) :
    ∃ U : Set Space, Convex ℝ U ∧
      volume U ≤ ENNReal.ofReal ((4800 : ℝ) ^ 3) * volume W ∧
      ∀ z w : Space, Tube r z w ⊆ W → Tube r z w ⊆ ball 0 1 →
        AffineMap.homothety (z + (1 / 2 : ℝ) • w) (100 : ℝ) '' Tube r z w ⊆ U := by
  let W₀ : Set Space := W ∩ ball 0 1
  have hW₀ : Convex ℝ W₀ := hW.inter (convex_ball _ _)
  have hW₀b : Bornology.IsBounded W₀ := isBounded_ball.subset inter_subset_right
  have hinter (z w : Space) (hsub : Tube r z w ⊆ W₀) : (interior W₀).Nonempty := by
    have hT : IsOpen (Tube r z w) := isOpen_thickening
    have hzT : z ∈ Tube r z w := (self_subset_thickening hr _) (left_mem_segment ℝ z (z + w))
    exact ⟨z, (hT.subset_interior_iff.mpr hsub) hzT⟩
  by_cases hi : (interior W₀).Nonempty
  · obtain ⟨U, hU, hvol, hcover⟩ := exists_convex_difference_container hW₀ hW₀b hi
      (show (1 : ℝ) ≤ 100 by norm_num)
    refine ⟨U, hU, ?_, ?_⟩
    · rw [hvol]
      norm_num only [show (48 : ℝ) * 100 = 4800 by norm_num]
      exact mul_le_mul_right (measure_mono inter_subset_left) _
    · intro z w hTW hTB p hp
      obtain ⟨q, hq, rfl⟩ := hp
      let m : Space := z + (1 / 2 : ℝ) • w
      have hmT : m ∈ Tube r z w := by
        apply self_subset_thickening hr
        rw [segment_eq_image']
        exact ⟨1 / 2, by norm_num, by simp [m]⟩
      have hmW : m ∈ W₀ := ⟨hTW hmT, hTB hmT⟩
      have hqW : q ∈ W₀ := ⟨hTW hq, hTB hq⟩
      simpa only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm] using
        hcover m hmW q hqW m hmW
  · refine ⟨∅, convex_empty, by simp, ?_⟩
    intro z w hTW hTB
    exact (hi (hinter z w (fun p hp => ⟨hTW hp, hTB hp⟩))).elim

/-- Equal-size disjoint groups transfer the Frostman count to their coarse representatives. -/
theorem frostman_grouped_dilations {η δ r : ℝ} (hr : 0 < r)
    {n m M : ℕ} {x v : Fin n → Space} {z w : Fin m → Space}
    (A : Fin m → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hM : ∀ j, M ≤ (A j).card)
    (hcover : ∀ j, ∀ i ∈ A j, Tube δ (x i) (v i) ⊆
      AffineMap.homothety (z j + (1 / 2 : ℝ) • w j) (100 : ℝ) '' Tube r (z j) (w j))
    (hball : ∀ j, Tube r (z j) (w j) ⊆ ball 0 1)
    (hF : Frostman η δ n x v) :
    ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((M : ℝ) * (Set.ncard {j | Tube r (z j) (w j) ⊆ W} : ℝ)) ≤
      ENNReal.ofReal ((4800 : ℝ) ^ 3 * (δ ^ (-η) * (n : ℝ))) * volume W := by
  classical
  intro W hW
  obtain ⟨U, hU, hvol, hbig⟩ := exists_convex_tube_dilation_container hr hW
  let J : Finset (Fin m) := Finset.univ.filter fun j => Tube r (z j) (w j) ⊆ W
  let Q : Finset (Fin n) := J.biUnion A
  let B : Finset (Fin n) := Finset.univ.filter fun i => Tube δ (x i) (v i) ⊆ U
  have hQB : Q ⊆ B := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (hcover j i hij).trans
      (hbig (z j) (w j) (Finset.mem_filter.mp hj).2 (hball j))
  have hcard : M * J.card ≤ B.card := by
    have heq : Q.card = ∑ j ∈ J, (A j).card :=
      Finset.card_biUnion (fun i _ j _ hij => hA hij)
    have hh : M * J.card ≤ Q.card := by
      rw [heq]
      calc
        _ = ∑ _j ∈ J, M := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun j _ => hM j)
    exact hh.trans (Finset.card_le_card hQB)
  have hJ : J.card = Set.ncard {j | Tube r (z j) (w j) ⊆ W} := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [J]
  have hB : B.card = Set.ncard {i | Tube δ (x i) (v i) ⊆ U} := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [B]
  have hc : ENNReal.ofReal ((M : ℝ) * (Set.ncard {j | Tube r (z j) (w j) ⊆ W} : ℝ)) ≤
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ U} : ℝ) := by
    apply ENNReal.ofReal_le_ofReal
    rw [← hJ, ← hB]
    exact_mod_cast hcard
  calc
    _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume U := hc.trans (hF U hU)
    _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) *
        (ENNReal.ofReal ((4800 : ℝ) ^ 3) * volume W) := mul_le_mul_right hvol _
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4800 ^ 3)]
      ring

end WangZahlLot.Obl.wz_normalized_projection_iteration
