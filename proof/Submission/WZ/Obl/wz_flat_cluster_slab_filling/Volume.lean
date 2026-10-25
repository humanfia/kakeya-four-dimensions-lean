-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.Volume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Basic

/-!
Volume estimates for tubes, tube pieces, tube slices and boxes, for the proof of
`WangZahlLot.wz_flat_cluster_slab_filling`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

lemma tube_measurable (δ : ℝ) (x v : Space) : MeasurableSet (Tube δ x v) :=
  isOpen_thickening.measurableSet

lemma tube_convex (δ : ℝ) (x v : Space) : Convex ℝ (Tube δ x v) :=
  (convex_segment x (x + v)).thickening δ

private lemma tube_isBounded (δ : ℝ) (x v : Space) : Bornology.IsBounded (Tube δ x v) := by
  have hs : IsCompact (segment ℝ x (x + v)) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  exact hs.isBounded.thickening

lemma tube_totallyBounded (δ : ℝ) (x v : Space) : TotallyBounded (Tube δ x v) :=
  (tube_isBounded δ x v).isCompact_closure.totallyBounded.subset subset_closure

lemma tube_volume_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x v : Space) (hv : ‖v‖ = 1) :
    volume (Tube δ x v) ≤ ENNReal.ofReal (384 * δ ^ 2) :=
  WangZahlLot.Obl.wz_off_stem_brush_overlap.tube_volume_upper hδ hδ1 x v hv

lemma tube_volume_ne_top (δ : ℝ) (x v : Space) : volume (Tube δ x v) ≠ ⊤ :=
  (tube_isBounded δ x v).measure_lt_top.ne

/-- A point of a unit tube lies within `δ` of a point of its axis. -/
private lemma tube_axis_point {δ : ℝ} {x v p : Space} (hp : p ∈ Tube δ x v) :
    ∃ t ∈ Icc (0 : ℝ) 1, dist p (x + t • v) < δ := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  exact ⟨t, ht, by simpa using hpq⟩

/-- A point within `δ` of a point of the axis lies in the tube. -/
private lemma mem_tube_of_dist {δ : ℝ} {x v p : Space} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : dist p (x + t • v) < δ) : p ∈ Tube δ x v := by
  refine mem_thickening_iff.mpr ⟨x + t • v, ?_, hp⟩
  rw [segment_eq_image']
  exact ⟨t, ht, by simp⟩

/-- The axis of a unit tube is parametrized isometrically. -/
private lemma axis_dist {x v : Space} (hv : ‖v‖ = 1) (s t : ℝ) :
    dist (x + s • v) (x + t • v) = |s - t| := by
  rw [WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.dist_segment_param x v hv,
    Real.dist_eq]

/-- The axial coordinate of a point near the axis is close to its parameter. -/
private lemma inner_near_axis {δ t : ℝ} {x v q : Space} (hv : ‖v‖ = 1)
    (hq : dist q (x + t • v) < δ) : |inner ℝ v (q - x) - t| < δ := by
  have hvv : inner ℝ v v = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hid : inner ℝ v (q - x) - t = inner ℝ v (q - (x + t • v)) := by
    rw [show q - x = (q - (x + t • v)) + t • v by abel, inner_add_right, inner_smul_right, hvv]
    ring
  rw [hid]
  calc
    |inner ℝ v (q - (x + t • v))| ≤ ‖v‖ * ‖q - (x + t • v)‖ := abs_real_inner_le_norm _ _
    _ < δ := by rw [hv, one_mul, ← dist_eq_norm]; exact hq

/-- The part of a unit tube within distance `L` of one of its points has volume `≳ L δ²`. -/
lemma tube_ball_volume_lower {δ L : ℝ} {x w p : Space} (hδ : 0 < δ) (hw : ‖w‖ = 1)
    (hL : 3 * δ ≤ L) (hL2 : L ≤ 2) (hp : p ∈ Tube δ x w) :
    ENNReal.ofReal (L * δ ^ 2 / 8) ≤ volume (Tube δ x w ∩ ball p L) := by
  obtain ⟨t₀, ht₀, hpt₀⟩ := tube_axis_point hp
  set lo : ℝ := max 0 (t₀ - L / 2) with hlo
  set hi : ℝ := min 1 (t₀ + L / 2) with hhi
  have hT : Icc lo hi ⊆ Icc 0 1 := by
    intro t ht
    exact ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
  have hlen : L / 2 ≤ hi - lo := by
    have h1 := ht₀.1
    have h2 := ht₀.2
    rcases le_total 0 (t₀ - L / 2) with h3 | h3 <;>
      rcases le_total 1 (t₀ + L / 2) with h4 | h4
    · rw [hlo, hhi, max_eq_right h3, min_eq_left h4]; linarith
    · rw [hlo, hhi, max_eq_right h3, min_eq_right h4]; linarith
    · rw [hlo, hhi, max_eq_left h3, min_eq_left h4]; linarith
    · rw [hlo, hhi, max_eq_left h3, min_eq_right h4]; linarith
  have hvolT : ENNReal.ofReal (L / 2) ≤ volume (Icc lo hi) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hlen
  have h := WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.segment_shading_volume_lower
    x w hw hT hδ hvolT
  have heq : L / 2 * δ ^ 2 / 4 = L * δ ^ 2 / 8 := by ring
  rw [heq] at h
  refine h.trans (measure_mono ?_)
  intro q hq
  obtain ⟨_, ⟨t, ht, rfl⟩, hqt⟩ := mem_thickening_iff.mp hq
  refine ⟨mem_tube_of_dist (hT ht) (by linarith), ?_⟩
  rw [mem_ball]
  have htt₀ : |t - t₀| ≤ L / 2 := by
    rw [abs_le]
    constructor
    · linarith [ht.1, le_max_right 0 (t₀ - L / 2)]
    · linarith [ht.2, min_le_right 1 (t₀ + L / 2)]
  calc
    dist q p ≤ dist q (x + t • w) + dist (x + t • w) (x + t₀ • w) + dist (x + t₀ • w) p :=
      dist_triangle4 _ _ _ _
    _ < δ / 2 + L / 2 + δ := by
      rw [axis_dist hw, dist_comm (x + t₀ • w)]
      linarith
    _ ≤ L := by linarith

/-- The part of a unit tube within distance `L` of one of its points has volume `≲ L δ²`. -/
lemma tube_ball_volume_upper {δ L : ℝ} {x w p : Space} (hδ : 0 < δ) (hw : ‖w‖ = 1)
    (hL : δ ≤ L) (hp : p ∈ Tube δ x w) :
    volume (Tube δ x w ∩ ball p L) ≤ ENNReal.ofReal (1664 * L * δ ^ 2) := by
  obtain ⟨t₀, ht₀, hpt₀⟩ := tube_axis_point hp
  set T : Set ℝ := Icc 0 1 ∩ Icc (t₀ - (L + 2 * δ)) (t₀ + (L + 2 * δ)) with hTdef
  have hT : T ⊆ Icc 0 1 := inter_subset_left
  have hdiam : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ 2 * L + 4 * δ := by
    intro s hs t ht
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hs.2.1, hs.2.2, ht.2.1, ht.2.2]
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    x w hw hT hδ (by linarith : (0 : ℝ) ≤ 2 * L + 4 * δ) hdiam
  calc
    volume (Tube δ x w ∩ ball p L) ≤
        volume (thickening δ ((fun t : ℝ => x + t • w) '' T)) := by
      apply measure_mono
      intro q ⟨hqT, hqb⟩
      obtain ⟨t, ht, hqt⟩ := tube_axis_point hqT
      refine mem_thickening_iff.mpr ⟨x + t • w, ⟨t, ⟨ht, ?_⟩, rfl⟩, hqt⟩
      have hd : |t - t₀| < L + 2 * δ := by
        rw [← axis_dist hw]
        calc
          dist (x + t • w) (x + t₀ • w) ≤
              dist (x + t • w) q + dist q p + dist p (x + t₀ • w) := dist_triangle4 _ _ _ _
          _ < δ + L + δ := by
            rw [dist_comm (x + t • w)]
            rw [mem_ball] at hqb
            linarith
          _ = L + 2 * δ := by ring
      rw [abs_lt] at hd
      exact ⟨by linarith, by linarith⟩
    _ ≤ ENNReal.ofReal (128 * (2 * (2 * L + 4 * δ) + δ) * δ ^ 2) := h
    _ ≤ ENNReal.ofReal (1664 * L * δ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
      nlinarith

/-- A slice of axial length `D` of a unit tube has volume `≲ (D + δ) δ²`. -/
lemma tube_slice_volume_upper {δ a D : ℝ} {x v : Space} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hD : 0 ≤ D) :
    volume (Tube δ x v ∩ {q | a ≤ inner ℝ v (q - x) ∧ inner ℝ v (q - x) ≤ a + D}) ≤
      ENNReal.ofReal (128 * (2 * (D + 2 * δ) + δ) * δ ^ 2) := by
  set T : Set ℝ := Icc 0 1 ∩ Icc (a - δ) (a + D + δ) with hTdef
  have hT : T ⊆ Icc 0 1 := inter_subset_left
  have hdiam : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ D + 2 * δ := by
    intro s hs t ht
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hs.2.1, hs.2.2, ht.2.1, ht.2.2]
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    x v hv hT hδ (by linarith : (0 : ℝ) ≤ D + 2 * δ) hdiam
  refine (measure_mono ?_).trans h
  intro q ⟨hqT, hqa, hqb⟩
  obtain ⟨t, ht, hqt⟩ := tube_axis_point hqT
  refine mem_thickening_iff.mpr ⟨x + t • v, ⟨t, ⟨ht, ?_⟩, rfl⟩, hqt⟩
  have herr := abs_lt.mp (inner_near_axis hv hqt)
  exact ⟨by linarith, by linarith⟩

lemma box_measurable (a b c : ℝ) (z : Space) (g : Space ≃ₗᵢ[ℝ] Space) :
    MeasurableSet (Box a b c z g) := by
  have hc : ∀ i : Fin 3, Measurable (fun p : Space => |(g (p - z)) i|) := by
    intro i
    apply Continuous.measurable
    fun_prop
  exact (measurableSet_le (hc 0) measurable_const).inter
    ((measurableSet_le (hc 1) measurable_const).inter (measurableSet_le (hc 2) measurable_const))

lemma box_volume {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (z : Space)
    (g : Space ≃ₗᵢ[ℝ] Space) :
    volume (Box a b c z g) = ENNReal.ofReal (a * b * c) := by
  have he : Box a b c z g = (fun p : Space => p + -z) ⁻¹' ((g : Space → Space) ⁻¹'
      WangZahlLot.Obl.wz_regular_transverse_affine_cells.coordinateBox
        ![a / 2, b / 2, c / 2]) := by
    ext p
    simp only [Box, WangZahlLot.Obl.wz_regular_transverse_affine_cells.coordinateBox,
      mem_ofPred_eq, mem_preimage, sub_eq_add_neg]
    constructor
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  rw [he, measure_preimage_add_right, g.measurePreserving.measure_preimage
      (WangZahlLot.Obl.wz_regular_transverse_affine_cells.coordinateBox_measurable
        _).nullMeasurableSet,
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_coordinateBox]
  · congr 1
    simp [Fin.prod_univ_three]
    ring
  · intro i
    fin_cases i <;> simp <;> positivity

/-- The cells of length `D` along the axis of the tube `[x, x+v]`. -/
def cell (δ D : ℝ) (x v : Space) (m : ℕ) : Set Space :=
  {q | (m : ℝ) * D ≤ inner ℝ v (q - x) + δ ∧ inner ℝ v (q - x) + δ ≤ ((m : ℝ) + 1) * D}

/-- The axial coordinate of a point of a unit tube. -/
private lemma tube_inner_bounds {δ : ℝ} {x v q : Space} (hv : ‖v‖ = 1)
    (hq : q ∈ Tube δ x v) : -δ < inner ℝ v (q - x) ∧ inner ℝ v (q - x) < 1 + δ := by
  obtain ⟨t, ht, hqt⟩ := tube_axis_point hq
  have herr := abs_lt.mp (inner_near_axis hv hqt)
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- A set of mass `a` in a unit tube meets many of the axial cells. -/
lemma many_cells {δ D a : ℝ} {x v : Space} (hδ : 0 < δ) (hv : ‖v‖ = 1) (hD : 0 < D)
    (Z : Set Space) (hZm : MeasurableSet Z) (hZ : Z ⊆ Tube δ x v)
    (ha : ENNReal.ofReal a ≤ volume Z) (M : ℕ) (hM : 1 + 2 * δ ≤ (M : ℝ) * D) :
    a ≤ 128 * (2 * (D + 2 * δ) + δ) * δ ^ 2 *
      ((Finset.univ.filter fun m : Fin M => (Z ∩ cell δ D x v m).Nonempty).card : ℝ) := by
  -- measurability of `Z` is not needed
  have _ := hZm
  set G := Finset.univ.filter fun m : Fin M => (Z ∩ cell δ D x v m).Nonempty with hG
  set C : ℝ := 128 * (2 * (D + 2 * δ) + δ) * δ ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hcover : Z ⊆ ⋃ m ∈ G, (Tube δ x v ∩ cell δ D x v m) := by
    intro q hqZ
    have hqT := hZ hqZ
    obtain ⟨h1, h2⟩ := tube_inner_bounds hv hqT
    set s : ℝ := inner ℝ v (q - x) + δ with hs
    have hs0 : 0 ≤ s / D := div_nonneg (by linarith) hD.le
    have hsM : s / D < M := by
      rw [div_lt_iff₀ hD]
      linarith
    have hm : ⌊s / D⌋₊ < M := (Nat.floor_lt hs0).mpr hsM
    let m : Fin M := ⟨⌊s / D⌋₊, hm⟩
    have hqc : q ∈ cell δ D x v m := by
      have hf1 : (⌊s / D⌋₊ : ℝ) ≤ s / D := Nat.floor_le hs0
      have hf2 : s / D < (⌊s / D⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      refine ⟨?_, ?_⟩
      · change (⌊s / D⌋₊ : ℝ) * D ≤ s
        rwa [le_div_iff₀ hD] at hf1
      · change s ≤ ((⌊s / D⌋₊ : ℝ) + 1) * D
        rw [div_lt_iff₀ hD] at hf2
        exact hf2.le
    refine mem_iUnion₂.mpr ⟨m, ?_, hqT, hqc⟩
    rw [hG, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, q, hqZ, hqc⟩
  have hslice : ∀ m ∈ G, volume (Tube δ x v ∩ cell δ D x v m) ≤ ENNReal.ofReal C := by
    intro m _
    refine (measure_mono ?_).trans
      (tube_slice_volume_upper (a := (m : ℝ) * D - δ) (x := x) hδ hv hD.le)
    intro q ⟨hqT, hq1, hq2⟩
    refine ⟨hqT, ?_, ?_⟩
    · linarith
    · linarith
  have hbound : ENNReal.ofReal a ≤ ENNReal.ofReal ((G.card : ℝ) * C) := by
    calc
      ENNReal.ofReal a ≤ volume Z := ha
      _ ≤ volume (⋃ m ∈ G, (Tube δ x v ∩ cell δ D x v m)) := measure_mono hcover
      _ ≤ ∑ m ∈ G, volume (Tube δ x v ∩ cell δ D x v m) := measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ G, ENNReal.ofReal C := Finset.sum_le_sum hslice
      _ = ENNReal.ofReal ((G.card : ℝ) * C) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) hC0)).mp hbound
  linarith [mul_comm C (G.card : ℝ)]

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
