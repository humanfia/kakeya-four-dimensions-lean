-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_brush_selection.Energy
import Submission.WZ.Obl.wz_off_stem_brush_overlap.Geometry
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Basic

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped Classical

/-- A broad incidence graph has a vertex with many geometric neighbours.
The relation is arbitrary; its two inputs are a pointwise broadness bound and
an upper bound for the volume of every related pair. -/
theorem broad_subset_neighbor_count {n : ℕ} (hn : 0 < n) (Y : Fin n → Set Space)
    (R : Fin n → Fin n → Prop) (D : Finset (Fin n)) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : volume (⋃ i, Y i) ≠ ⊤) (hpos : 0 < (volume (⋃ i, Y i)).toReal)
    {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ i j, R i j → (volume (Y i ∩ Y j)).toReal ≤ B)
    (hbroad : ∀ i p, wz_transverse_brush_selection.multiplicity Y Finset.univ p ≤
      2 * wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p) :
    ∃ (i : Fin n) (F : Finset (Fin n)), F ⊆ D ∧
      (∀ j ∈ F, R j i ∧ (Y j ∩ Y i).Nonempty) ∧
      (∑ j ∈ D, (volume (Y j)).toReal) ^ 2 ≤
        2 * (volume (⋃ j, Y j)).toReal * (n : ℝ) * F.card * B := by
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hfin (measure_mono (subset_iUnion Y i))
  let F : Fin n → Finset (Fin n) := fun i =>
    D.filter fun j => R j i ∧ (Y j ∩ Y i).Nonempty
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => (F i).card)
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
  have hrow : ∀ k, (∑ j ∈ D.filter (fun j => R j k),
      (volume (Y j ∩ Y k)).toReal) ≤ (F i).card * B := by
    intro k
    have heq : (∑ j ∈ D.filter (fun j => R j k),
        (volume (Y j ∩ Y k)).toReal) = ∑ j ∈ F k, (volume (Y j ∩ Y k)).toReal := by
      symm
      apply Finset.sum_subset
      · intro j hj
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2.1⟩
      · intro j hj hjF
        have hempty : Y j ∩ Y k = ∅ := by
          apply Set.not_nonempty_iff_eq_empty.mp
          intro hne
          exact hjF (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2, hne⟩)
        simp [hempty]
    rw [heq]
    calc
      _ ≤ ∑ _j ∈ F k, B := Finset.sum_le_sum fun j hj =>
        hpair j k (Finset.mem_filter.mp hj).2.1
      _ = (F k).card * B := by simp
      _ ≤ (F i).card * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hi k (Finset.mem_univ k)) hB
  have htotal : (∑ k, ∑ j ∈ D.filter (fun j => R j k),
      (volume (Y j ∩ Y k)).toReal) ≤ (n : ℝ) * ((F i).card * B) := by
    simpa using Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hrow k)
  have henergy := wz_transverse_brush_selection.broad_energy Y D R hY hYfin hbroad
  have hcs := wz_transverse_brush_selection.integral_sq_bound (MeasurableSet.iUnion hY) hfin hpos
    (wz_transverse_brush_selection.integrable_multiplicity Y D (fun j _ => hY j)
      (fun j _ => hYfin j))
    (wz_transverse_brush_selection.integrable_multiplicity_sq Y D (fun j _ => hY j)
      (fun j _ => hYfin j))
    (fun p hp => by
      apply Finset.sum_eq_zero
      intro j _
      exact wz_transverse_brush_selection.oneOn_of_notMem
        (fun h => hp (mem_iUnion.mpr ⟨j, h⟩)))
  rw [wz_transverse_brush_selection.integral_multiplicity Y D
    (fun j _ => hY j) (fun j _ => hYfin j)] at hcs
  refine ⟨i, F i, Finset.filter_subset _ _, fun j hj => (Finset.mem_filter.mp hj).2, ?_⟩
  calc
    _ ≤ (volume (⋃ j, Y j)).toReal *
        ∫ p, wz_transverse_brush_selection.multiplicity Y D p ^ 2 := hcs
    _ ≤ (volume (⋃ j, Y j)).toReal * (2 * ((n : ℝ) * ((F i).card * B))) :=
      mul_le_mul_of_nonneg_left
        (henergy.trans (mul_le_mul_of_nonneg_left htotal (by norm_num))) ENNReal.toReal_nonneg
    _ = _ := by ring

/-- The whole-family version of the broad neighbour count. -/
theorem broad_neighbor_count {n : ℕ} (hn : 0 < n) (Y : Fin n → Set Space)
    (R : Fin n → Fin n → Prop) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : volume (⋃ i, Y i) ≠ ⊤) (hpos : 0 < (volume (⋃ i, Y i)).toReal)
    {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ i j, R i j → (volume (Y i ∩ Y j)).toReal ≤ B)
    (hbroad : ∀ i p, wz_transverse_brush_selection.multiplicity Y Finset.univ p ≤
      2 * wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p) :
    ∃ (i : Fin n) (F : Finset (Fin n)),
      (∀ j ∈ F, R j i ∧ (Y j ∩ Y i).Nonempty) ∧
      (∑ j, (volume (Y j)).toReal) ^ 2 ≤
        2 * (volume (⋃ j, Y j)).toReal * (n : ℝ) * F.card * B := by
  obtain ⟨i, F, _, hR, hS⟩ := broad_subset_neighbor_count hn Y R Finset.univ hY hfin hpos hB hpair hbroad
  exact ⟨i, F, hR, hS⟩

/-- An off-stem broad brush has many full tubes in one thin slab. This is a
quantitative planar concentration step that needs no polynomial partition. -/
theorem off_stem_subset_broad_slab {δ r b : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space) (D : Finset (Fin n)) (y w : Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hshade : ∀ i, Y i ⊆ Tube δ (x i) (v i) \ Metric.thickening r (Set.range fun t : ℝ => y + t • w))
    (hfin : volume (⋃ i, Y i) ≠ ⊤) (hpos : 0 < (volume (⋃ i, Y i)).toReal)
    (hstem : ∀ i, (Y i).Nonempty → (Tube δ (x i) (v i) ∩ Tube δ y w).Nonempty)
    (hbroad : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) :
    ∃ (e : Space) (t : ℝ) (F : Finset (Fin n)), F ⊆ D ∧ ‖e‖ = 1 ∧
      (∀ i ∈ F, Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 15 * δ / r}) ∧
      (∑ i ∈ D, (volume (Y i)).toReal) ^ 2 ≤
        8192 * (volume (⋃ i, Y i)).toReal * (n : ℝ) * F.card * δ ^ 3 / b := by
  let R : Fin n → Fin n → Prop := fun i j => b < min ‖v j - v i‖ ‖v j + v i‖
  have hcounts : ∀ i p, wz_transverse_brush_selection.multiplicity Y Finset.univ p ≤
      2 * wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p := by
    intro i p
    have hnear := hbroad p (v i) (hv i)
    rw [wz_transverse_brush_selection.incidence_ncard] at hnear
    have hfull : ({j | p ∈ Y j}.ncard : ℝ) =
        wz_transverse_brush_selection.multiplicity Y Finset.univ p := by
      simpa using wz_transverse_brush_selection.incidence_ncard Y (fun _ => True) p
    rw [hfull] at hnear
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => min ‖v j - v i‖ ‖v j + v i‖ ≤ b)
      (fun j => wz_transverse_brush_selection.oneOn (Y j) p)
    simp only [not_le] at hsplit
    change wz_transverse_brush_selection.multiplicity Y
        (Finset.univ.filter fun j => min ‖v j - v i‖ ‖v j + v i‖ ≤ b) p +
      wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p =
        wz_transverse_brush_selection.multiplicity Y Finset.univ p at hsplit
    linarith
  have hpair : ∀ i j, R i j → (volume (Y i ∩ Y j)).toReal ≤ 4096 * δ ^ 3 / b := by
    intro i j hR
    have hsep : b ≤ min ‖v i - v j‖ ‖v i + v j‖ := by
      dsimp [R] at hR
      rw [norm_sub_rev, add_comm]
      exact hR.le
    have hm := measure_mono (μ := volume) (inter_subset_inter (fun p hp => (hshade i hp).1)
      (fun p hp => (hshade j hp).1))
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (hm.trans (wz_transverse_brush_selection.transverse_intersection_volume
        hδ hb hb1 (hv i) (hv j) hsep))
  obtain ⟨i, F, hFD, hF, hmass⟩ := broad_subset_neighbor_count hn Y R D hY hfin hpos
    (by positivity : 0 ≤ 4096 * δ ^ 3 / b) hpair hcounts
  obtain ⟨basis, _, hi, hw⟩ := wz_off_stem_brush_overlap.adapted_basis (v i) w
  refine ⟨basis 2, inner ℝ (basis 2) (x i), F, hFD, basis.norm_eq_one 2, ?_, ?_⟩
  · intro j hj p hp
    obtain ⟨q, hqj, hqi⟩ := (hF j hj).2
    have hoff : ((Tube δ (x i) (v i) \ Metric.thickening r
        (wz_off_stem_brush_overlap.Stem y w)) ∩ Tube δ (x j) (v j)).Nonempty :=
      ⟨q, hshade i hqi, (hshade j hqj).1⟩
    have hh := wz_off_stem_brush_overlap.normal_coordinate hδ hr hr1
      (basis.norm_eq_one 2) hi hw (hv j) (hstem i ⟨q, hqi⟩) (hstem j ⟨q, hqj⟩) hoff hp
    simpa only [mem_ofPred_eq, inner_sub_right] using hh
  · convert hmass using 1
    ring

/-- The whole-brush form of the slab concentration bound. -/
theorem off_stem_broad_slab {δ r b : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : 0 < b) (hb1 : b ≤ 1) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space) (y w : Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hshade : ∀ i, Y i ⊆ Tube δ (x i) (v i) \ Metric.thickening r (Set.range fun t : ℝ => y + t • w))
    (hfin : volume (⋃ i, Y i) ≠ ⊤) (hpos : 0 < (volume (⋃ i, Y i)).toReal)
    (hstem : ∀ i, (Tube δ (x i) (v i) ∩ Tube δ y w).Nonempty)
    (hbroad : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) :
    ∃ (e : Space) (t : ℝ) (F : Finset (Fin n)), ‖e‖ = 1 ∧
      (∀ i ∈ F, Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 15 * δ / r}) ∧
      (∑ i, (volume (Y i)).toReal) ^ 2 ≤
        8192 * (volume (⋃ i, Y i)).toReal * (n : ℝ) * F.card * δ ^ 3 / b := by
  obtain ⟨e, t, F, _, he, hslab, hmass⟩ := off_stem_subset_broad_slab hδ hr hr1 hb hb1 hn
    x v Y Finset.univ y w hv hY hshade hfin hpos (fun i _ => hstem i) hbroad
  exact ⟨e, t, F, he, hslab, hmass⟩

/-- If each shaded tube of the brush is dense and its union has volume at
most `U * delta`, the planar subfamily retains the explicit fraction
`b * lam^2 / (8192 * U)` of the original shading mass. -/
theorem off_stem_broad_planar_mass {δ r b lam U : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hlam : 0 < lam) (hU : 0 < U) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space) (y w : Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hshade : ∀ i, Y i ⊆ Tube δ (x i) (v i) \ Metric.thickening r (Set.range fun t : ℝ => y + t • w))
    (hdense : ∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i))
    (hvol : volume (⋃ i, Y i) ≤ ENNReal.ofReal (U * δ))
    (hstem : ∀ i, (Tube δ (x i) (v i) ∩ Tube δ y w).Nonempty)
    (hbroad : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) :
    ∃ (e : Space) (t : ℝ) (F : Finset (Fin n)), ‖e‖ = 1 ∧
      (∀ i ∈ F, Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 15 * δ / r}) ∧
      ENNReal.ofReal (b * lam ^ 2 / (8192 * U)) * (∑ i, volume (Y i)) ≤
        ∑ i ∈ F, volume (Y i) := by
  have hfin : volume (⋃ i, Y i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hfin (measure_mono (subset_iUnion Y i))
  have hdenseR : ∀ i, lam * δ ^ 2 ≤ (volume (Y i)).toReal :=
    fun i => (ENNReal.ofReal_le_iff_le_toReal (hYfin i)).mp (hdense i)
  have hpos : 0 < (volume (⋃ i, Y i)).toReal := by
    have hi := (hdenseR ⟨0, hn⟩).trans
      (ENNReal.toReal_mono hfin (measure_mono (subset_iUnion Y ⟨0, hn⟩)))
    exact (mul_pos hlam (sq_pos_of_pos hδ)).trans_le hi
  obtain ⟨e, t, F, he, hslab, hmass⟩ :=
    off_stem_broad_slab hδ hr hr1 hb hb1 hn x v Y y w hv hY hshade hfin hpos hstem hbroad
  let S := ∑ i, (volume (Y i)).toReal
  let W := ∑ i ∈ F, (volume (Y i)).toReal
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hS : lam * (n : ℝ) * δ ^ 2 ≤ S := by
    simpa [S, mul_assoc, mul_comm, mul_left_comm] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hdenseR i)
  have hW : lam * (F.card : ℝ) * δ ^ 2 ≤ W := by
    simpa [W, mul_assoc, mul_comm, mul_left_comm] using
      Finset.sum_le_sum (fun i (_ : i ∈ F) => hdenseR i)
  have hq : (volume (⋃ i, Y i)).toReal ≤ U * δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
  have hmass' : S ^ 2 ≤ 8192 * U * (n : ℝ) * F.card * δ ^ 4 / b := by
    refine hmass.trans ?_
    calc
      _ ≤ 8192 * (U * δ) * (n : ℝ) * F.card * δ ^ 3 / b := by gcongr
      _ = _ := by ring
  have hcancel : lam * S ≤ 8192 * U * (F.card : ℝ) * δ ^ 2 / b := by
    apply (mul_le_mul_iff_left₀ (show 0 < (n : ℝ) * δ ^ 2 by positivity)).mp
    calc
      (lam * S) * ((n : ℝ) * δ ^ 2) = S * (lam * (n : ℝ) * δ ^ 2) := by ring
      _ ≤ S * S := mul_le_mul_of_nonneg_left hS hS0
      _ = S ^ 2 := (pow_two S).symm
      _ ≤ _ := hmass'
      _ = _ := by ring
  have hretain : b * lam ^ 2 / (8192 * U) * S ≤ W := by
    calc
      _ = (b * lam / (8192 * U)) * (lam * S) := by ring
      _ ≤ (b * lam / (8192 * U)) * (8192 * U * (F.card : ℝ) * δ ^ 2 / b) :=
        mul_le_mul_of_nonneg_left hcancel (by positivity)
      _ = lam * (F.card : ℝ) * δ ^ 2 := by field_simp
      _ ≤ _ := hW
  refine ⟨e, t, F, he, hslab, ?_⟩
  have hsum : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  have hsumF : (∑ i ∈ F, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum) hsumF).mp
  simpa only [S, W, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ b * lam ^ 2 / (8192 * U)),
    ENNReal.toReal_sum (fun i _ => hYfin i)] using hretain

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
