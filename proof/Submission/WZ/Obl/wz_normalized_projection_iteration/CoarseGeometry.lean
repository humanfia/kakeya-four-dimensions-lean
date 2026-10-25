-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.CoarseGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Grid
import Submission.WZ.Obl.wz_normalized_projection_iteration.Containment
import Submission.WZ.Obl.wz_normalized_projection_iteration.Shading
import Submission.WZ.Obl.wz_normalized_projection_iteration.Partition

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric MeasureTheory
open scoped ENNReal

/-- Uniform, separated cells with sufficient retained mass give the required coarse family. -/
theorem family_of_cells {η β δ r D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hδr : δ ≤ r) (hr1 : r ≤ 1 / 4) (hD : 0 < D)
    (hdensity : 147456 * r ^ β ≤ D)
    (hcountConst : 768 * (4800 : ℝ) ^ 3 * δ ^ (-η) ≤ D * r ^ (-β))
    {n m M : ℕ} (hm : 0 < m) (hM : 0 < M)
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hH : Family η δ n x v Y) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ v i 2)
    (hF : Frostman η δ n x v)
    (A : Fin m → Finset (Fin n)) (a : Fin m → Fin n)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcard : ∀ j, M ≤ (A j).card ∧ (A j).card ≤ 2 * M)
    (hmax : ∀ j, ∀ i ∈ A j, (volume (Y i)).toReal ≤ (volume (Y (a j))).toReal)
    (hcell : ∀ j, ∀ i ∈ A j, lineCell r (x i) (v i) = lineCell r (x (a j)) (v (a j)))
    (hsep : ∀ i j, i ≠ j →
      volume (Tube r (inwardStart r (x (a i)) (v (a i))) (v (a i)) ∩
        Tube r (inwardStart r (x (a j)) (v (a j))) (v (a j))) ≤
      (1 / 2 : ENNReal) * volume (Tube r (inwardStart r (x (a i)) (v (a i))) (v (a i))))
    (hmass : D * (n : ℝ) * δ ^ 2 ≤ ∑ j, ∑ i ∈ A j, (volume (Y i)).toReal)
    {f : ℝ → ℝ} (hf : Slope f) (hf0 : |f 0| ≤ 1) :
    ∃ Z : Fin m → Set Space,
      Family β r m (fun j => inwardStart r (x (a j)) (v (a j))) (fun j => v (a j)) Z ∧
      Frostman β r m (fun j => inwardStart r (x (a j)) (v (a j))) (fun j => v (a j)) ∧
      volume (Projection f (⋃ j, Z j)) ≤
        ENNReal.ofReal 7396 * volume (thickening r (Projection f (⋃ i, Y i))) := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  let z : Fin m → Space := fun j => inwardStart r (x (a j)) (v (a j))
  let w : Fin m → Space := fun j => v (a j)
  have hx (i : Fin n) : ‖x i‖ ≤ 1 := by
    have hh := hH.2.2.1 i ((self_subset_thickening hδ _) (left_mem_segment ℝ (x i) (x i + v i)))
    exact (by simpa using hh : ‖x i‖ < 1).le
  have hxv (i : Fin n) : ‖x i + v i‖ ≤ 1 := by
    have hh := hH.2.2.1 i ((self_subset_thickening hδ _) (right_mem_segment ℝ (x i) (x i + v i)))
    exact (by simpa using hh : ‖x i + v i‖ < 1).le
  have hcoarse (j : Fin m) : Tube r (z j) (w j) ⊆ ball 0 1 :=
    inward_tube_subset_ball hr hr1 (hx _) (hxv _) (hH.2.1 _)
  have hYupper (i : Fin n) : volume (Y i) ≤ ENNReal.ofReal (384 * δ ^ 2) :=
    (measure_mono (hH.2.2.2.2.2.1 i)).trans
      (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ (by linarith) _ _ (hH.2.1 i))
  have hYr (i : Fin n) : (volume (Y i)).toReal ≤ 384 * δ ^ 2 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hYupper i)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 384 * δ ^ 2)] using hh
  have hMn : (M : ℝ) * m ≤ n := by
    exact_mod_cast disjoint_groups_count_le A hA (fun j => (hcard j).1)
  have hex (j : Fin m) := exists_expanded_shading hδ hδr hr1 (hH.2.1 (a j))
    (hH.2.2.1 (a j)) (hH.2.2.2.2.1 (a j)) (hH.2.2.2.2.2.1 (a j))
  choose Z hZm hZT hZgrowth hZnear using hex
  have hZupper (j : Fin m) : volume (Z j) ≤ ENNReal.ofReal (384 * r ^ 2) :=
    (measure_mono (hZT j)).trans
      (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hr (by linarith) _ _ (hH.2.1 (a j)))
  have hZfinite (j : Fin m) : volume (Z j) ≠ ⊤ :=
    (lt_of_le_of_lt (hZupper j) ENNReal.ofReal_lt_top).ne
  have hZgrowReal (j : Fin m) : r ^ 2 * (volume (Y (a j))).toReal ≤
      (73728 * δ ^ 2) * (volume (Z j)).toReal := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hZfinite j)) (hZgrowth j)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 73728 * δ ^ 2)] using hh
  let SY : ℝ := ∑ j, (volume (Y (a j))).toReal
  let SZ : ℝ := ∑ j, (volume (Z j)).toReal
  have hS : D * (n : ℝ) * δ ^ 2 ≤ 2 * M * SY := by
    apply hmass.trans
    calc
      _ ≤ ∑ j, (2 * (M : ℝ)) * (volume (Y (a j))).toReal := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ ∑ _i ∈ A j, (volume (Y (a j))).toReal := Finset.sum_le_sum (fun i hi => hmax j i hi)
          _ = ((A j).card : ℝ) * (volume (Y (a j))).toReal := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (hcard j).2) ENNReal.toReal_nonneg
      _ = _ := by rw [← Finset.mul_sum]
  have hG : r ^ 2 * SY ≤ (73728 * δ ^ 2) * SZ := by
    dsimp [SY, SZ]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hZgrowReal j)
  have hLower : D * n * r ^ 2 ≤ 147456 * M * SZ := by
    apply (mul_le_mul_iff_right₀ hδsq).mp
    calc
      δ ^ 2 * (D * n * r ^ 2) = r ^ 2 * (D * n * δ ^ 2) := by ring
      _ ≤ r ^ 2 * (2 * M * SY) := mul_le_mul_of_nonneg_left hS (sq_nonneg r)
      _ = (2 * M) * (r ^ 2 * SY) := by ring
      _ ≤ (2 * M) * ((73728 * δ ^ 2) * SZ) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = δ ^ 2 * (147456 * M * SZ) := by ring
  have hZmassReal : r ^ β * m * r ^ 2 ≤ SZ := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 147456 * M by positivity)).mp
    calc
      (147456 * M) * (r ^ β * m * r ^ 2) = (147456 * r ^ β) * (M * m) * r ^ 2 := by ring
      _ ≤ D * (M * m) * r ^ 2 := by gcongr
      _ ≤ D * n * r ^ 2 := by gcongr
      _ ≤ 147456 * M * SZ := hLower
  have hUpperMass : D * (n : ℝ) * δ ^ 2 ≤ (m : ℝ) * (2 * M * (384 * δ ^ 2)) := by
    apply hmass.trans
    calc
      _ ≤ ∑ _j : Fin m, 2 * (M : ℝ) * (384 * δ ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ ∑ _i ∈ A j, 384 * δ ^ 2 := Finset.sum_le_sum (fun i _ => hYr i)
          _ = ((A j).card : ℝ) * (384 * δ ^ 2) := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (hcard j).2) (by positivity)
      _ = _ := by simp
  have hDn : D * (n : ℝ) ≤ 768 * M * m := by
    apply (mul_le_mul_iff_right₀ hδsq).mp
    convert hUpperMass using 1 <;> ring
  have hCoeff : (4800 : ℝ) ^ 3 * (δ ^ (-η) * n) ≤ M * (r ^ (-β) * m) := by
    apply (mul_le_mul_iff_right₀ hD).mp
    calc
      D * (4800 ^ 3 * (δ ^ (-η) * n)) = (4800 ^ 3 * δ ^ (-η)) * (D * n) := by ring
      _ ≤ (4800 ^ 3 * δ ^ (-η)) * (768 * M * m) :=
        mul_le_mul_of_nonneg_left hDn (by positivity)
      _ = (768 * 4800 ^ 3 * δ ^ (-η)) * (M * m) := by ring
      _ ≤ (D * r ^ (-β)) * (M * m) := mul_le_mul_of_nonneg_right hcountConst (by positivity)
      _ = D * (M * (r ^ (-β) * m)) := by ring
  have hDilation : ∀ j, ∀ i ∈ A j, Tube δ (x i) (v i) ⊆
      AffineMap.homothety (z j + (1 / 2 : ℝ) • w j) (100 : ℝ) '' Tube r (z j) (w j) := by
    intro j i hi
    have hclose := lineCell_close hr (hcell j i hi)
    have hz : ‖z j‖ ≤ 1 := (inward_start_norm hr.le hr1 (hx (a j)) (hH.2.1 (a j))).trans (by linarith)
    apply fine_tube_subset_dilation hr hδr (hH.2.1 i) (hH.2.1 (a j))
      (hv2 i) (hv2 (a j)) hz (hH.2.2.1 i) _ hclose.1
    have hs := lineBase_dist_start (x := inwardStart r (x (a j)) (v (a j)))
      (y := x (a j)) (hH.2.1 (a j)) (hv2 (a j))
    have hd := inward_start_dist hr.le (hx (a j)) (hH.2.1 (a j))
    rw [dist_eq_norm] at hd
    have ht := norm_sub_le_norm_sub_add_norm_sub (lineBase (x i) (v i))
      (lineBase (x (a j)) (v (a j))) (lineBase (z j) (w j))
    rw [norm_sub_rev] at hs
    change ‖lineBase (x (a j)) (v (a j)) - lineBase (z j) (w j)‖ ≤ _ at hs
    linarith [hclose.2]
  have hFcoarse : Frostman β r m z w := by
    intro W hW
    have hh := frostman_grouped_dilations hr A hA (fun j => (hcard j).1)
      hDilation hcoarse hF W hW
    have hc := ENNReal.ofReal_le_ofReal hCoeff
    have hh' := hh.trans (mul_le_mul_left hc (volume W))
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ M),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ M), mul_assoc] at hh'
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hMr).ne' ENNReal.ofReal_ne_top).mp hh'
  refine ⟨Z, ⟨hm, fun j => hH.2.1 (a j), hcoarse, hsep, hZm, hZT, ?_⟩, hFcoarse, ?_⟩
  · have hvolsum : (∑ j, volume (Z j)) = ENNReal.ofReal SZ := by
      dsimp only [SZ]
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
      apply Finset.sum_congr rfl
      intro j _
      exact (ENNReal.ofReal_toReal (hZfinite j)).symm
    rw [hvolsum]
    exact ENNReal.ofReal_le_ofReal hZmassReal
  · apply projected_area_of_nearby hr hf hf0
    · intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact ball_subset_closedBall (hH.2.2.1 i (hH.2.2.2.2.2.1 i hi))
    · intro p hp
      obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      exact ball_subset_closedBall (hcoarse j (hZT j hj))
    · intro p hp
      obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      obtain ⟨q, hq, hpq⟩ := hZnear j p hj
      exact ⟨q, mem_iUnion.mpr ⟨a j, hq⟩, hpq⟩

end WangZahlLot.Obl.wz_normalized_projection_iteration
