-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSCubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.GridCube
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSCoarse

/-!
# Grid cubes reached by contracted shadings

Cubes of side `ρ` reached by a contracted coarse tube lie in its normalized tube,
so a coarse tube reaches boundedly many cubes per unit length; a fine tube meets a
cube in volume `O(ρ δ²)`.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- Direction of a unit tube inside a unit tube of radius `ρ`. -/
theorem dir_close_of_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (hT : Tube δ x v ⊆ Tube ρ z w) :
    min ‖v - w‖ ‖v + w‖ ≤ 4 * ρ := by
  obtain ⟨s, hs, hxs⟩ := exists_param_of_mem_Tube
    (hT (axis_mem_Tube hδ x v (t := 0) ⟨le_rfl, zero_le_one⟩))
  obtain ⟨t, ht, hxt⟩ := exists_param_of_mem_Tube
    (hT (axis_mem_Tube hδ x v (t := 1) ⟨zero_le_one, le_rfl⟩))
  simp only [zero_smul, add_zero, one_smul] at hxs hxt
  have hvw : ‖v - (t - s) • w‖ < 2 * ρ := by
    have he : v - (t - s) • w = (x + v - (z + t • w)) - (x - (z + s • w)) := by module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hts : 1 - 2 * ρ < |t - s| := by
    have h1 : ‖v‖ - ‖(t - s) • w‖ ≤ ‖v - (t - s) • w‖ := norm_sub_norm_le _ _
    rw [hv, norm_smul, hw, mul_one, Real.norm_eq_abs] at h1
    linarith
  have hts1 : |t - s| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  rcases le_or_gt 0 (t - s) with hpos | hneg
  · rw [abs_of_nonneg hpos] at hts hts1
    apply min_le_left _ _ |>.trans
    have he : v - w = (v - (t - s) • w) - (1 - (t - s)) • w := by module
    rw [he]
    calc _ ≤ ‖v - (t - s) • w‖ + ‖(1 - (t - s)) • w‖ := norm_sub_le _ _
      _ ≤ 2 * ρ + 2 * ρ := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
      _ = 4 * ρ := by ring
  · rw [abs_of_neg hneg] at hts hts1
    apply min_le_right _ _ |>.trans
    have he : v + w = (v - (t - s) • w) + (1 + (t - s)) • w := by module
    rw [he]
    calc _ ≤ ‖v - (t - s) • w‖ + ‖(1 + (t - s)) • w‖ := norm_add_le _ _
      _ ≤ 2 * ρ + 2 * ρ := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
      _ = 4 * ρ := by ring

/-- Indices of the grid cubes meeting a set. -/
def reached (s : ℝ) (A : Set Space) : Set (Fin 3 → ℤ) := {m | (gridCube s m ∩ A).Nonempty}

theorem reached_mono {s : ℝ} {A B : Set Space} (h : A ⊆ B) : reached s A ⊆ reached s B :=
  fun _ ⟨p, hp, hpA⟩ => ⟨p, hp, h hpA⟩

theorem subset_iUnion_reached {s : ℝ} (hs : 0 < s) (A : Set Space) :
    A ⊆ ⋃ m ∈ reached s A, gridCube s m := by
  intro p hp
  exact mem_iUnion₂.mpr ⟨cubeIndex s p, ⟨p, mem_gridCube_cubeIndex hs p, hp⟩,
    mem_gridCube_cubeIndex hs p⟩

/-- A cube reached by a contracted unit `ρ`-tube lies in the normalized tube. -/
theorem gridCube_subset_ntube {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 100) {z w : Space}
    {m : Fin 3 → ℤ} (hm : m ∈ reached ρ ((1 - 2 * (16 * ρ)) • Tube ρ z w)) :
    gridCube ρ m ⊆ ntube (8 * ρ) (16 * ρ) z w := by
  obtain ⟨p, hpm, hpA⟩ := hm
  obtain ⟨p', hp', rfl⟩ := Set.mem_smul_set.mp hpA
  obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_Tube hp'
  have hl : 0 < 1 - 2 * (16 * ρ) := by linarith
  have hl1 : 1 - 2 * (16 * ρ) ≤ 1 := by linarith
  intro q hq
  have hqp : dist q ((1 - 2 * (16 * ρ)) • p') < 2 * ρ := diam_le_of_mem_gridCube hρ hq hpm
  apply mem_Tube_of_param (t := 16 * ρ + (1 - 2 * (16 * ρ)) * t)
  · constructor
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  · have he : q - ((1 - 2 * (16 * ρ)) • z - (16 * ρ) • w +
        (16 * ρ + (1 - 2 * (16 * ρ)) * t) • w) =
        (q - (1 - 2 * (16 * ρ)) • p') + (1 - 2 * (16 * ρ)) • (p' - (z + t • w)) := by module
    rw [he]
    calc _ ≤ ‖q - (1 - 2 * (16 * ρ)) • p'‖ + ‖(1 - 2 * (16 * ρ)) • (p' - (z + t • w))‖ :=
          norm_add_le _ _
      _ < 2 * ρ + 1 * ρ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl, ← dist_eq_norm]
          have : (1 - 2 * (16 * ρ)) * ‖p' - (z + t • w)‖ ≤ 1 * ρ :=
            mul_le_mul hl1 hpt.le (norm_nonneg _) zero_le_one
          linarith
      _ ≤ 8 * ρ := by linarith

theorem reached_subset_image {s : ℝ} (hs : 0 < s) (A : Set Space) :
    reached s A ⊆ cubeIndex s '' A := by
  rintro m ⟨p, hpm, hpA⟩
  exact ⟨p, hpA, cubeIndex_eq_of_mem hs hpm⟩

/-- Bounded sets reach finitely many cubes. -/
theorem reached_finite {s R : ℝ} (hs : 0 < s) {A : Set Space} (hA : A ⊆ ball 0 R) :
    (reached s A).Finite := by
  apply Set.Finite.subset _ ((reached_subset_image hs A).trans (image_mono hA))
  apply Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin 3 =>
    Set.Icc (⌊-R / s⌋) ⌊R / s⌋) (fun _ => Set.finite_Icc _ _))
  rintro m ⟨p, hp, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro j
  have hpj : |p j| < R := by
    have h1 : |p j| ≤ ‖p‖ := by
      have := PiLp.norm_apply_le p j
      simpa [Real.norm_eq_abs] using this
    have h2 : ‖p‖ < R := by simpa using hp
    linarith
  rw [abs_lt] at hpj
  constructor
  · apply Int.floor_le_floor
    exact div_le_div_of_nonneg_right (by linarith) hs.le
  · apply Int.floor_le_floor
    exact div_le_div_of_nonneg_right (by linarith) hs.le

theorem Tube_subset_ball {r : ℝ} (hr : 0 ≤ r) (z w : Space) (hw : ‖w‖ = 1) :
    Tube r z w ⊆ ball 0 (‖z‖ + 1 + r + 1) := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_Tube hp
  rw [mem_ball_zero_iff]
  have h1 : ‖z + t • w‖ ≤ ‖z‖ + 1 := by
    calc ‖z + t • w‖ ≤ ‖z‖ + ‖t • w‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 1 := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have := norm_sub_le_norm_sub_add_norm_sub p (z + t • w) 0
  simp only [sub_zero] at this
  linarith

/-- A contracted unit `ρ`-tube reaches at most `24576 / ρ` cubes of side `ρ`. -/
theorem ncard_reached_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 100) (z w : Space)
    (hw : ‖w‖ = 1) :
    ((reached ρ ((1 - 2 * (16 * ρ)) • Tube ρ z w)).ncard : ℝ) ≤ 24576 / ρ := by
  have hl : 0 < 1 - 2 * (16 * ρ) := by linarith
  have hbdd : (1 - 2 * (16 * ρ)) • Tube ρ z w ⊆ ball 0 (‖z‖ + 1 + ρ + 1) := by
    rintro _ ⟨p, hp, rfl⟩
    have := Tube_subset_ball hρ.le z w hw hp
    rw [mem_ball_zero_iff] at this ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    calc (1 - 2 * (16 * ρ)) * ‖p‖ ≤ 1 * ‖p‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < _ := by linarith
  have hfin := reached_finite hρ hbdd
  set S := hfin.toFinset
  have hsub : (⋃ m ∈ S, gridCube ρ m) ⊆ ntube (8 * ρ) (16 * ρ) z w := by
    intro q hq
    obtain ⟨m, hm, hqm⟩ := mem_iUnion₂.mp hq
    exact gridCube_subset_ntube hρ hρ1 (hfin.mem_toFinset.mp hm) hqm
  have hvol := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset (fun m _ m' _ hmm => gridCube_disjoint hρ hmm)
    (fun m _ => measurableSet_gridCube ρ m)] at hvol
  simp only [volume_gridCube hρ, Finset.sum_const, nsmul_eq_mul] at hvol
  have hT := WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le (δ := 8 * ρ)
    (by positivity) (by linarith) ((1 - 2 * (16 * ρ)) • z - (16 * ρ) • w) w hw
  have h := hvol.trans hT
  rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  rw [Set.ncard_eq_toFinset_card _ hfin, le_div_iff₀ hρ]
  have hρ3 : 0 < ρ ^ 3 := by positivity
  nlinarith

/-- A unit `δ`-tube meets a ball of radius `R` in volume `O((R + δ) δ²)`. -/
theorem volume_Tube_inter_ball_le {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (x v c : Space)
    (hv : ‖v‖ = 1) :
    volume (Tube δ x v ∩ ball c R) ≤ ENNReal.ofReal (128 * (2 * (2 * R + 2 * δ) + δ) * δ ^ 2) := by
  let I : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ‖x + t • v - c‖ < R + δ}
  have hsub : Tube δ x v ∩ ball c R ⊆ thickening δ ((fun t => x + t • v) '' I) := by
    rintro p ⟨hp, hpc⟩
    obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_Tube hp
    apply mem_thickening_iff.mpr
    refine ⟨x + t • v, ⟨t, ⟨ht, ?_⟩, rfl⟩, ?_⟩
    · have := norm_sub_le_norm_sub_add_norm_sub (x + t • v) p c
      rw [mem_ball, dist_eq_norm] at hpc
      rw [norm_sub_rev] at hpt
      linarith
    · rw [dist_eq_norm]; exact hpt
  have hdiam : ∀ s ∈ I, ∀ t ∈ I, dist s t ≤ 2 * R + 2 * δ := by
    intro s hs t ht
    have h1 : ‖(x + s • v) - (x + t • v)‖ ≤ 2 * R + 2 * δ := by
      have := norm_sub_le_norm_sub_add_norm_sub (x + s • v) c (x + t • v)
      rw [norm_sub_rev c] at this
      linarith [hs.2, ht.2]
    have he : (x + s • v) - (x + t • v) = (s - t) • v := by module
    rw [he, norm_smul, hv, mul_one, Real.norm_eq_abs] at h1
    rwa [Real.dist_eq]
  exact (measure_mono hsub).trans
    (WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
      (fun t ht => ht.1) hδ (by positivity) hdiam)

/-- A finite box of cube indices. -/
def cubeBox (K : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(K : ℤ)) K)

/-- Cubes of side `s` meeting `A`, among the indices of the box. -/
noncomputable def reachedF (s : ℝ) (K : ℕ) (A : Set Space) : Finset (Fin 3 → ℤ) :=
  (cubeBox K).filter (fun m => (gridCube s m ∩ A).Nonempty)

theorem mem_reachedF {s : ℝ} (hs : 0 < s) {K : ℕ} (hK : 2 / s + 1 ≤ K) {A : Set Space}
    (hA : A ⊆ ball 0 2) {m : Fin 3 → ℤ} (hm : (gridCube s m ∩ A).Nonempty) :
    m ∈ reachedF s K A := by
  refine Finset.mem_filter.mpr ⟨?_, hm⟩
  obtain ⟨p, hpm, hpA⟩ := hm
  simp only [cubeBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro j
  have hpj : |p j| < 2 := by
    have h1 : |p j| ≤ ‖p‖ := by
      have := PiLp.norm_apply_le p j
      simpa [Real.norm_eq_abs] using this
    have h2 : ‖p‖ < 2 := by simpa using hA hpA
    linarith
  obtain ⟨h1, h2⟩ := hpm j
  rw [abs_lt] at hpj
  have hK' : (2 : ℝ) / s ≤ K - 1 := by linarith
  constructor
  · have h3 : -(K : ℝ) ≤ (m j : ℝ) := by
      have : -2 < s * ((m j : ℝ) + 1) := by linarith
      have h4 : -2 / s < (m j : ℝ) + 1 := by rw [div_lt_iff₀ hs]; linarith
      have h5 : -2 / s = -(2 / s) := by ring
      linarith
    exact_mod_cast h3
  · have h3 : (m j : ℝ) ≤ K := by
      have : s * (m j : ℝ) < 2 := by linarith
      have h4 : (m j : ℝ) < 2 / s := by rw [lt_div_iff₀ hs]; linarith
      linarith
    exact_mod_cast h3

theorem subset_iUnion_reachedF {s : ℝ} (hs : 0 < s) {K : ℕ} (hK : 2 / s + 1 ≤ K)
    {A : Set Space} (hA : A ⊆ ball 0 2) : A ⊆ ⋃ m ∈ reachedF s K A, gridCube s m := by
  intro p hp
  exact mem_iUnion₂.mpr ⟨cubeIndex s p, mem_reachedF hs hK hA
    ⟨p, mem_gridCube_cubeIndex hs p, hp⟩, mem_gridCube_cubeIndex hs p⟩

theorem reachedF_mono {s : ℝ} {K : ℕ} {A B : Set Space} (h : A ⊆ B) :
    reachedF s K A ⊆ reachedF s K B := by
  intro m hm
  obtain ⟨hbox, hne⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨hbox, hne.mono (inter_subset_inter_right _ h)⟩

/-- A subset of a contracted unit `ρ`-tube reaches at most `24576 / ρ` cubes of side `ρ`. -/
theorem card_reachedF_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 100) {K : ℕ} (z w : Space)
    (hw : ‖w‖ = 1) {A : Set Space} (hA : A ⊆ (1 - 2 * (16 * ρ)) • Tube ρ z w) :
    ((reachedF ρ K A).card : ℝ) ≤ 24576 / ρ := by
  set S := reachedF ρ K A
  have hsub : (⋃ m ∈ S, gridCube ρ m) ⊆ ntube (8 * ρ) (16 * ρ) z w := by
    intro q hq
    obtain ⟨m, hm, hqm⟩ := mem_iUnion₂.mp hq
    have hm' : m ∈ reached ρ ((1 - 2 * (16 * ρ)) • Tube ρ z w) := by
      obtain ⟨-, p, hpm, hpA⟩ := Finset.mem_filter.mp hm
      exact ⟨p, hpm, hA hpA⟩
    exact gridCube_subset_ntube hρ hρ1 hm' hqm
  have hvol := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset (fun m _ m' _ hmm => gridCube_disjoint hρ hmm)
    (fun m _ => measurableSet_gridCube ρ m)] at hvol
  simp only [volume_gridCube hρ, Finset.sum_const, nsmul_eq_mul] at hvol
  have hT := WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le (δ := 8 * ρ)
    (by positivity) (by linarith) ((1 - 2 * (16 * ρ)) • z - (16 * ρ) • w) w hw
  have h := hvol.trans hT
  rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  rw [le_div_iff₀ hρ]
  have hρ3 : 0 < ρ ^ 3 := by positivity
  nlinarith

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
