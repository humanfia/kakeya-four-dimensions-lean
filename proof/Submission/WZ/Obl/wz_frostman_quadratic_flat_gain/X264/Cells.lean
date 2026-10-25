-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.Cells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridUnion
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Selection
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file Cells.lean), namespace renamed.

/-!
# Density at scale `s` through blocks of grid cells

Step 1 and the product inequalities (5.26), (5.29) of the proof of Proposition 5.1 in the
supplied paper, with grid cells of side `s` in place of balls of radius `s`.

`block s z` is the union of the `27` cells `gridCell s (z + d)`, `d ∈ {-1,0,1}³`.
* `sum_block_le`: the blocks of a finite set of keys cover each point at most `27` times.
* `block_product`: if every block of `S` is `r`-dense in `E`, then `r |⋃ blocks| ≤ 27 |E|`.
* `thickening_gridUnion_subset`: the `s`-neighbourhood of a union of cells lies in the
  union of their blocks.
* `upper_average`: a subset of `E` inside cells whose blocks are at most `Λ`-dense has
  volume at most `Λ |N_{2s}(V)|` when it lies in `V`.
* `cell_density_pigeonhole`: a dyadic density class of blocks carries a fixed fraction of
  the mass of the shadings.
-/

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

noncomputable section

open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridCell gridKey gridKeys gridUnion)

/-- The offsets `{-1, 0, 1}³`, as an image of `Fin 3 → Fin 3`. -/
def offsets : Finset (Fin 3 → ℤ) :=
  (Finset.univ : Finset (Fin 3 → Fin 3)).image (fun f i => (f i : ℤ) - 1)

lemma card_offsets_le : offsets.card ≤ 27 := by
  calc offsets.card ≤ (Finset.univ : Finset (Fin 3 → Fin 3)).card := Finset.card_image_le
    _ = 27 := by simp

lemma zero_mem_offsets : (0 : Fin 3 → ℤ) ∈ offsets := by
  refine Finset.mem_image.mpr ⟨fun _ => 1, Finset.mem_univ _, ?_⟩
  funext i
  simp

lemma mem_offsets_of_abs_le {d : Fin 3 → ℤ} (h : ∀ i, -1 ≤ d i ∧ d i ≤ 1) : d ∈ offsets := by
  refine Finset.mem_image.mpr ⟨fun i => ⟨(d i + 1).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
  · have := h i
    omega
  · funext i
    have := h i
    simp only
    omega

/-- The block of `27` cells around the cell with key `z`. -/
def block (s : ℝ) (z : Fin 3 → ℤ) : Set Space := ⋃ d ∈ offsets, gridCell s (z + d)

lemma block_measurable (s : ℝ) (z : Fin 3 → ℤ) : MeasurableSet (block s z) :=
  Finset.measurableSet_biUnion _ fun d _ =>
    WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_measurable s (z + d)

lemma gridCell_subset_block (s : ℝ) (z : Fin 3 → ℤ) : gridCell s z ⊆ block s z := by
  intro p hp
  refine Set.mem_biUnion zero_mem_offsets ?_
  simpa using hp

lemma volume_block_le {s : ℝ} (hs : 0 ≤ s) (z : Fin 3 → ℤ) :
    volume (block s z) ≤ ENNReal.ofReal (27 * s ^ 3) := by
  calc
    volume (block s z) ≤ ∑ d ∈ offsets, volume (gridCell s (z + d)) :=
      measure_biUnion_finset_le _ _
    _ = offsets.card * ENNReal.ofReal (s ^ 3) := by
      simp [WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_volume hs]
    _ ≤ 27 * ENNReal.ofReal (s ^ 3) := by
      gcongr
      exact_mod_cast card_offsets_le
    _ = ENNReal.ofReal (27 * s ^ 3) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- Blocks of distinct keys cover each point at most `27` times. -/
lemma sum_block_le {s : ℝ} (hs : 0 < s) {E : Set Space} (hE : MeasurableSet E)
    (S : Finset (Fin 3 → ℤ)) :
    ∑ z ∈ S, volume (E ∩ block s z) ≤ 27 * volume E := by
  classical
  have hcell (d : Fin 3 → ℤ) : ∑ z ∈ S, volume (E ∩ gridCell s (z + d)) ≤ volume E := by
    have hdisj : Set.PairwiseDisjoint (↑S) (fun z => E ∩ gridCell s (z + d)) := by
      intro z _ w _ hzw
      refine ((WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_disjoint hs)
        ?_).mono inter_subset_right inter_subset_right
      intro h
      exact hzw (add_right_cancel h)
    rw [← measure_biUnion_finset hdisj (fun z _ =>
      hE.inter (WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_measurable s _))]
    exact measure_mono (Set.iUnion₂_subset fun _ _ => inter_subset_left)
  calc
    ∑ z ∈ S, volume (E ∩ block s z)
        ≤ ∑ z ∈ S, ∑ d ∈ offsets, volume (E ∩ gridCell s (z + d)) := by
      gcongr with z hz
      rw [block, Set.inter_iUnion₂]
      exact measure_biUnion_finset_le _ _
    _ = ∑ d ∈ offsets, ∑ z ∈ S, volume (E ∩ gridCell s (z + d)) := Finset.sum_comm
    _ ≤ ∑ _d ∈ offsets, volume E := Finset.sum_le_sum fun d _ => hcell d
    _ = offsets.card * volume E := by simp
    _ ≤ 27 * volume E := by
      gcongr
      exact_mod_cast card_offsets_le

/-- Product inequality (5.29): dense blocks see a proportional part of `E`. -/
lemma block_product {s : ℝ} (hs : 0 < s) {E : Set Space} (hE : MeasurableSet E)
    (S : Finset (Fin 3 → ℤ)) (r : ENNReal)
    (hdense : ∀ z ∈ S, r * volume (block s z) ≤ volume (E ∩ block s z)) :
    r * volume (⋃ z ∈ S, block s z) ≤ 27 * volume E := by
  calc
    r * volume (⋃ z ∈ S, block s z) ≤ r * ∑ z ∈ S, volume (block s z) := by
      gcongr
      exact measure_biUnion_finset_le _ _
    _ = ∑ z ∈ S, r * volume (block s z) := Finset.mul_sum _ _ _
    _ ≤ ∑ z ∈ S, volume (E ∩ block s z) := Finset.sum_le_sum hdense
    _ ≤ 27 * volume E := sum_block_le hs hE S

lemma coord_sub_le (p q : Space) (i : Fin 3) : |p i - q i| ≤ ‖p - q‖ := by
  have h := PiLp.norm_apply_le (p - q) i
  simpa [Real.norm_eq_abs] using h

/-- The `s`-neighbourhood of a union of cells lies in the union of their blocks. -/
lemma thickening_gridUnion_subset {s : ℝ} (hs : 0 < s) (S : Finset (Fin 3 → ℤ)) :
    thickening s (gridUnion s S) ⊆ ⋃ z ∈ S, block s z := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  obtain ⟨z, hzS, hqz⟩ := Set.mem_iUnion₂.mp hq
  refine Set.mem_iUnion₂.mpr ⟨z, hzS, ?_⟩
  have hkey : gridKey s p - z ∈ offsets := by
    apply mem_offsets_of_abs_le
    intro i
    have hpi : |p i - q i| < s := (coord_sub_le p q i).trans_lt (by rwa [← dist_eq_norm])
    have hq1 := (hqz i).1
    have hq2 := (hqz i).2
    have hpl : ((z i : ℝ) - 1) * s < p i := by
      have := (abs_lt.mp hpi).1
      nlinarith
    have hpu : p i < ((z i : ℝ) + 2) * s := by
      have := (abs_lt.mp hpi).2
      nlinarith
    have hfl : gridKey s p i = ⌊p i / s⌋ := rfl
    have h1 : (z i : ℝ) - 1 < p i / s := (lt_div_iff₀ hs).mpr hpl
    have h2 : p i / s < (z i : ℝ) + 2 := (div_lt_iff₀ hs).mpr hpu
    have hf1 : (z i : ℤ) - 1 ≤ ⌊p i / s⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith
    have hf2 : ⌊p i / s⌋ ≤ z i + 1 := by
      have := Int.floor_le (p i / s)
      have : (⌊p i / s⌋ : ℝ) < (z i : ℝ) + 2 := lt_of_le_of_lt this h2
      have : ⌊p i / s⌋ < z i + 2 := by exact_mod_cast this
      omega
    simp only [Pi.sub_apply, hfl]
    constructor <;> omega
  refine Set.mem_biUnion hkey ?_
  have : z + (gridKey s p - z) = gridKey s p := by abel
  rw [this]
  exact WangZahlLot.Obl.wz_nonflat_factored_improvement.mem_gridCell_key hs p

/-- Upper averaging (5.26): a part of `E` lying in `V` and in cells whose blocks are at
most `Λ s³`-full has volume at most `Λ |N_{2s}(V)|`. -/
lemma upper_average {s Λ : ℝ} (hs : 0 < s) (hΛ : 0 ≤ Λ) {E : Set Space}
    (S : Finset (Fin 3 → ℤ))
    (hsparse : ∀ z ∈ S, volume (E ∩ block s z) ≤ ENNReal.ofReal (Λ * s ^ 3))
    {F V : Set Space} (hFS : F ⊆ gridUnion s S) (hFE : F ⊆ E) (hFV : F ⊆ V) :
    volume F ≤ ENNReal.ofReal Λ * volume (thickening (2 * s) V) := by
  classical
  let S' := S.filter (fun z => (V ∩ gridCell s z).Nonempty)
  have hcover : F ⊆ ⋃ z ∈ S', E ∩ gridCell s z := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp (hFS hp)
    refine Set.mem_iUnion₂.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, ⟨p, hFV hp, hpz⟩⟩, hFE hp, hpz⟩
  have hcells : gridUnion s S' ⊆ thickening (2 * s) V :=
    Set.iUnion₂_subset fun z hz =>
      WangZahlLot.Obl.wz_nonflat_factored_improvement.gridCell_subset_neighborhood hs
        (Finset.mem_filter.mp hz).2
  calc
    volume F ≤ ∑ z ∈ S', volume (E ∩ gridCell s z) :=
      (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _z ∈ S', ENNReal.ofReal (Λ * s ^ 3) := by
      gcongr with z hz
      exact (measure_mono (inter_subset_inter_right _ (gridCell_subset_block s z))).trans
        (hsparse z (Finset.mem_filter.mp hz).1)
    _ = ENNReal.ofReal Λ * volume (gridUnion s S') := by
      rw [WangZahlLot.Obl.wz_nonflat_factored_improvement.gridUnion_volume hs,
        Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hΛ]
      congr 1
      ring
    _ ≤ ENNReal.ofReal Λ * volume (thickening (2 * s) V) := by
      gcongr

lemma card_gridKeys {s : ℝ} : ((gridKeys s).card : ℝ) = (2 * (⌈2 / s⌉₊ : ℝ) + 1) ^ 3 := by
  rw [WangZahlLot.Obl.wz_nonflat_factored_improvement.gridKeys, Pi.card_Icc]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  have h : ((⌈2 / s⌉₊ : ℤ) + 1 - -(⌈2 / s⌉₊ : ℤ)).toNat = 2 * ⌈2 / s⌉₊ + 1 := by omega
  rw [h]
  push_cast
  ring

lemma card_gridKeys_mul_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ((gridKeys s).card : ℝ) * s ^ 3 ≤ 343 := by
  rw [card_gridKeys]
  have hc : (⌈2 / s⌉₊ : ℝ) < 2 / s + 1 := Nat.ceil_lt_add_one (by positivity)
  have h7 : (2 * (⌈2 / s⌉₊ : ℝ) + 1) * s ≤ 7 := by
    have : (⌈2 / s⌉₊ : ℝ) * s ≤ (2 / s + 1) * s := by gcongr
    have he : (2 / s + 1) * s = 2 + s := by field_simp
    nlinarith
  have hnn : 0 ≤ (2 * (⌈2 / s⌉₊ : ℝ) + 1) * s := by positivity
  calc (2 * (⌈2 / s⌉₊ : ℝ) + 1) ^ 3 * s ^ 3 = ((2 * (⌈2 / s⌉₊ : ℝ) + 1) * s) ^ 3 := by ring
    _ ≤ 7 ^ 3 := by gcongr
    _ = 343 := by norm_num

lemma toReal_inter_block_le {s : ℝ} (hs : 0 ≤ s) (E : Set Space) (z : Fin 3 → ℤ) :
    (volume (E ∩ block s z)).toReal ≤ 27 * s ^ 3 := by
  have h := (measure_mono (inter_subset_right (s := E))).trans (volume_block_le hs z)
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

lemma inter_block_ne_top {s : ℝ} (hs : 0 ≤ s) (E : Set Space) (z : Fin 3 → ℤ) :
    volume (E ∩ block s z) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((measure_mono inter_subset_right).trans (volume_block_le hs z))

/-- Step 1: a dyadic density class of blocks carries a fixed fraction of the mass of the
shadings.  `t` is the density of the class: the blocks of `S` contain between `t` and `2t`
times `27 s³` of `⋃ Y`. -/
lemma cell_density_pigeonhole {s M : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hM : 0 < M)
    {n : ℕ} (Y : Fin n → Set Space) (hYm : ∀ i, MeasurableSet (Y i))
    (hYB : ∀ i, Y i ⊆ Metric.ball 0 1)
    (hmass : ENNReal.ofReal M ≤ ∑ i, volume (Y i))
    {K : ℕ} (hK : 0 < K) (hKlarge : 18522 * n * (1 / 2 : ℝ) ^ K ≤ M) :
    ∃ (S : Finset (Fin 3 → ℤ)) (t : ℝ), (1 / 2 : ℝ) ^ (K + 1) ≤ t ∧
      (∀ z ∈ S, ENNReal.ofReal (t * (27 * s ^ 3)) ≤ volume ((⋃ i, Y i) ∩ block s z) ∧
        volume ((⋃ i, Y i) ∩ block s z) ≤ ENNReal.ofReal (2 * t * (27 * s ^ 3))) ∧
      ENNReal.ofReal (M / (4 * K)) ≤ ∑ i, volume (Y i ∩ gridUnion s S) := by
  classical
  set E := ⋃ i, Y i with hEdef
  have hE : MeasurableSet E := MeasurableSet.iUnion hYm
  have hs3 : 0 < 27 * s ^ 3 := by positivity
  let d : (Fin 3 → ℤ) → ℝ := fun z => (volume (E ∩ block s z)).toReal / (27 * s ^ 3)
  let w : (Fin 3 → ℤ) → ℝ := fun z => ∑ i, (volume (Y i ∩ gridCell s z)).toReal
  have hd1 (z : Fin 3 → ℤ) : d z ≤ 1 :=
    (div_le_one hs3).mpr (toReal_inter_block_le hs.le E z)
  have hd0 (z : Fin 3 → ℤ) : 0 ≤ d z := by positivity
  have hYfin (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne
      (measure_mono (hYB i))
  -- total mass in the cells covering the unit ball
  have hcov (i : Fin n) : Y i ∩ gridUnion s (gridKeys s) = Y i :=
    Set.inter_eq_left.mpr ((hYB i).trans
      (WangZahlLot.Obl.wz_nonflat_factored_improvement.grid_covers_unitBall hs hs1))
  have hwsum (S : Finset (Fin 3 → ℤ)) :
      ∑ z ∈ S, w z = ∑ i, (volume (Y i ∩ gridUnion s S)).toReal := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [WangZahlLot.Obl.wz_nonflat_factored_improvement.measure_inter_gridUnion hs S (hYm i),
      ENNReal.toReal_sum]
    intro z _
    exact ne_top_of_le_ne_top (hYfin i) (measure_mono inter_subset_left)
  have hMreal : M ≤ ∑ i, (volume (Y i)).toReal := by
    rw [← ENNReal.toReal_sum (fun i _ => hYfin i)]
    exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.sum_ne_top.mpr fun i _ => hYfin i)).mp hmass
  have htotal : M ≤ ∑ z ∈ gridKeys s, w z := by
    rw [hwsum]
    simpa only [hcov] using hMreal
  have hw_le (z : Fin 3 → ℤ) : w z ≤ n * (27 * s ^ 3) * d z := by
    have hdz : (27 * s ^ 3) * d z = (volume (E ∩ block s z)).toReal := by
      dsimp [d]
      field_simp
    calc w z ≤ ∑ _i : Fin n, (volume (E ∩ block s z)).toReal := by
          refine Finset.sum_le_sum fun i _ => ENNReal.toReal_mono (inter_block_ne_top hs.le E z) ?_
          exact measure_mono (inter_subset_inter (Set.subset_iUnion Y i)
            (gridCell_subset_block s z))
      _ = n * (27 * s ^ 3) * d z := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc, hdz]
  -- the low-density blocks carry at most half of the mass
  let G := (gridKeys s).filter (fun z => (1 / 2 : ℝ) ^ K ≤ d z)
  have hlow : ∑ z ∈ (gridKeys s).filter (fun z => ¬ (1 / 2 : ℝ) ^ K ≤ d z), w z ≤ M / 2 := by
    calc
      _ ≤ ∑ _z ∈ (gridKeys s).filter (fun z => ¬ (1 / 2 : ℝ) ^ K ≤ d z),
            n * (27 * s ^ 3) * (1 / 2 : ℝ) ^ K := by
          refine Finset.sum_le_sum fun z hz => (hw_le z).trans ?_
          have := (not_le.mp (Finset.mem_filter.mp hz).2).le
          gcongr
      _ ≤ ∑ _z ∈ gridKeys s, n * (27 * s ^ 3) * (1 / 2 : ℝ) ^ K :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = 27 * (n * (1 / 2 : ℝ) ^ K) * ((gridKeys s).card * s ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 27 * (n * (1 / 2 : ℝ) ^ K) * 343 := by
          gcongr
          exact card_gridKeys_mul_le hs hs1
      _ ≤ M / 2 := by nlinarith
  have hgood : M / 2 ≤ ∑ z ∈ G, w z := by
    have he := Finset.sum_filter_add_sum_filter_not (gridKeys s)
      (fun z => (1 / 2 : ℝ) ^ K ≤ d z) w
    dsimp [G]
    linarith
  obtain ⟨S, hSG, hSmass, t, ht, hdt⟩ :=
    WangZahlLot.Obl.wz_nonflat_factored_improvement.density_selection G d w
      (ρ := 1 / 2) (by norm_num) hK (fun z _ => hd1 z) hgood (by
        have hempty : G.filter (fun z => d z < (1 / 2 : ℝ) ^ K) = ∅ := by
          ext z
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
          intro hz
          exact (Finset.mem_filter.mp hz).2
        rw [hempty, Finset.sum_empty]
        linarith)
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hSmass
    have : 0 < M / 2 / (2 * K) := by positivity
    linarith
  obtain ⟨z₀, hz₀⟩ := hSne
  have hz₀G := hSG hz₀
  refine ⟨S, t, ?_, ?_, ?_⟩
  · have h1 : (1 / 2 : ℝ) ^ K ≤ d z₀ := (Finset.mem_filter.mp hz₀G).2
    have h2 := (hdt z₀ hz₀).2
    rw [pow_succ]
    linarith
  · intro z hz
    have hdz : (27 * s ^ 3) * d z = (volume (E ∩ block s z)).toReal := by
      dsimp [d]
      field_simp
    constructor
    · rw [ENNReal.ofReal_le_iff_le_toReal (inter_block_ne_top hs.le E z), ← hdz]
      nlinarith [(hdt z hz).1]
    · rw [← ENNReal.ofReal_toReal (inter_block_ne_top hs.le E z), ← hdz]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [(hdt z hz).2]
  · have hfin (i : Fin n) : volume (Y i ∩ gridUnion s S) ≠ ⊤ :=
      ne_top_of_le_ne_top (hYfin i) (measure_mono inter_subset_left)
    rw [← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.mpr fun i _ => hfin i),
      ENNReal.toReal_sum fun i _ => hfin i, ← hwsum]
    apply ENNReal.ofReal_le_ofReal
    have : M / (4 * K) = M / 2 / (2 * K) := by
      field_simp
      ring
    linarith

/-- The two product inequalities (5.26) and (5.29) for one density class of blocks.  For
every `W` and every part `F` of `⋃ Y` inside `W` and inside the cells of the class,
`|F| ≤ 54 t |N_{2s}(W)|`; and `t |⋃_W (W ∩ N_s(F_W))| ≤ 27 |⋃ Y|`. -/
lemma two_level_product {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) {E : Set Space}
    (hE : MeasurableSet E) (S : Finset (Fin 3 → ℤ))
    (hdense : ∀ z ∈ S, ENNReal.ofReal (t * (27 * s ^ 3)) ≤ volume (E ∩ block s z) ∧
      volume (E ∩ block s z) ≤ ENNReal.ofReal (2 * t * (27 * s ^ 3)))
    {ι : Type*} (V F : ι → Set Space) (hFS : ∀ k, F k ⊆ gridUnion s S)
    (hFE : ∀ k, F k ⊆ E) (hFV : ∀ k, F k ⊆ V k) :
    (∀ k, volume (F k) ≤ ENNReal.ofReal (54 * t) * volume (thickening (2 * s) (V k))) ∧
    ENNReal.ofReal t * volume (⋃ k, V k ∩ thickening s (F k)) ≤ 27 * volume E := by
  constructor
  · intro k
    refine upper_average hs (by positivity) S (fun z hz => (hdense z hz).2.trans ?_)
      (hFS k) (hFE k) (hFV k)
    apply le_of_eq
    congr 1
    ring
  · have hsub : (⋃ k, V k ∩ thickening s (F k)) ⊆ ⋃ z ∈ S, block s z := by
      refine Set.iUnion_subset fun k => ?_
      exact (inter_subset_right).trans ((thickening_subset_of_subset s (hFS k)).trans
        (thickening_gridUnion_subset hs S))
    calc
      ENNReal.ofReal t * volume (⋃ k, V k ∩ thickening s (F k))
          ≤ ENNReal.ofReal t * volume (⋃ z ∈ S, block s z) := by gcongr
      _ ≤ 27 * volume E := by
        refine block_product hs hE S _ fun z hz => ?_
        calc ENNReal.ofReal t * volume (block s z)
            ≤ ENNReal.ofReal t * ENNReal.ofReal (27 * s ^ 3) := by
              gcongr
              exact volume_block_le hs.le z
          _ = ENNReal.ofReal (t * (27 * s ^ 3)) := by rw [ENNReal.ofReal_mul ht]
          _ ≤ volume (E ∩ block s z) := (hdense z hz).1

end

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
