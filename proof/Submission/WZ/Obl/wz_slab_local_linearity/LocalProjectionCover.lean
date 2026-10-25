-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.LocalProjectionCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CubeGeometry
import Submission.WZ.Obl.wz_slab_local_linearity.CubeProjection
import Submission.WZ.Obl.wz_slab_local_linearity.CoverUpper
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric MeasureTheory

/-- The local projection-volume hypothesis controls projections onto the normal
at a fixed base point throughout a forty-times larger neighborhood. -/
theorem local_projection_cover {ρ B : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 100)
    (hB : 0 ≤ B) (K : Finset (Fin 3 → ℤ)) (V : Space3 → Space3)
    (hunit : ∀ q ∈ gridCubes ρ K, ‖V q‖ = 1)
    (hlip : ∀ q ∈ gridCubes ρ K, ∀ q' ∈ gridCubes ρ K, dist (V q) (V q') ≤ dist q q')
    (hlocal : ∀ q ∈ gridCubes ρ K,
      volume ((fun x : Space3 => inner ℝ (V q) x) '' (gridCubes ρ K ∩ ball q (Real.sqrt ρ))) ≤
        ENNReal.ofReal B)
    {p : Space3} (hp : p ∈ gridCubes ρ K) :
    CoverUpper
      ((fun k => inner ℝ (V p) (gridCorner ρ k)) ''
        ((K.filter fun k => dist (gridCorner ρ k) p ≤ 40 * Real.sqrt ρ) : Set (Fin 3 → ℤ)))
      ρ ((38 * (802 : ℝ) ^ 3) * B / ρ) := by
  classical
  let s := Real.sqrt ρ
  let θ := s / 10
  have hs : 0 < s := Real.sqrt_pos.mpr hρ
  have hθ : 0 < θ := div_pos hs (by norm_num)
  have hs2 : s ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hρs : 10 * ρ ≤ s := by
    have hh := mul_le_mul_of_nonneg_left hρsmall hρ.le
    nlinarith
  let P := K.filter fun k => dist (gridCorner ρ k) p ≤ 40 * s
  let key : (Fin 3 → ℤ) → (Fin 3 → ℤ) :=
    fun k => wz_balanced_cluster_cover.cell θ (gridCorner ρ k)
  let J := P.image key
  have hPK : P ⊆ K := Finset.filter_subset _ _
  have hJcard : (J.card : ℝ) ≤ (802 : ℝ) ^ 3 := by
    have hsub : J ⊆ wz_balanced_cluster_cover.box θ p (40 * s) := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      apply wz_balanced_cluster_cover.cell_mem_box hθ
      simpa only [dist_eq_norm] using (Finset.mem_filter.mp hk).2
    have hb := wz_balanced_cluster_cover.card_box_le hθ p (show 0 ≤ 40 * s by positivity)
    have he : 2 * (40 * s) / θ + 2 = (802 : ℝ) := by dsimp [θ]; field_simp; ring
    rw [he] at hb
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hb
  have hrep : ∀ j : J, ∃ k ∈ P, key k = (j : Fin 3 → ℤ) := by
    intro j
    exact Finset.mem_image.mp j.property
  choose rep hrepP hrepKey using hrep
  let Pj (j : J) := P.filter fun k => key k = (j : Fin 3 → ℤ)
  have hrepE (j : J) : gridCorner ρ (rep j) ∈ gridCubes ρ K :=
    gridCubes_corner_mem hρ (hPK (hrepP j))
  have hdist (j : J) {k : Fin 3 → ℤ} (hk : k ∈ Pj j) :
      dist (gridCorner ρ k) (gridCorner ρ (rep j)) ≤ 2 * θ := by
    rw [dist_eq_norm]
    apply wz_balanced_cluster_cover.norm_sub_le_of_cell_eq hθ
    exact (Finset.mem_filter.mp hk).2.trans (hrepKey j).symm
  have hcube (j : J) : gridCubes ρ (Pj j) ⊆
      gridCubes ρ K ∩ ball (gridCorner ρ (rep j)) s := by
    intro q hq
    obtain ⟨k, hk, hqk⟩ := mem_iUnion₂.mp hq
    refine ⟨mem_iUnion₂.mpr ⟨k, hPK (Finset.mem_filter.mp hk).1, hqk⟩, ?_⟩
    apply gridCube_subset_ball hρ (k := k) (p := gridCorner ρ (rep j)) _ hqk
    have hd := hdist j hk
    dsimp only [θ] at hd
    linarith
  let Aj (j : J) : Set ℝ :=
    (fun k => inner ℝ (V p) (gridCorner ρ k)) '' (Pj j : Set (Fin 3 → ℤ))
  have hcover (j : J) : CoverUpper (Aj j) ρ (38 * B / ρ) := by
    let q := gridCorner ρ (rep j)
    let Dj := (fun x : Space3 => inner ℝ (V q) x) '' (gridCubes ρ K ∩ ball q s)
    have hD : (fun x : Space3 => inner ℝ (V q) x) '' gridCubes ρ (Pj j) ⊆ Dj :=
      image_mono (hcube j)
    have hc : CoverUpper
        ((fun k => inner ℝ (V q) (gridCorner ρ k)) '' (Pj j : Set (Fin 3 → ℤ))) ρ (2 * B / ρ) :=
      cover_projected_corners hρ hB (Pj j) (hunit q (hrepE j)) hD (hlocal q (hrepE j))
    have hL : ‖V p - V q‖ ≤ 40 * s := by
      rw [← dist_eq_norm]
      calc dist (V p) (V q) ≤ dist p q := hlip p hp q (hrepE j)
        _ ≤ 40 * s := by
          rw [dist_comm]
          exact (Finset.mem_filter.mp (hrepP j)).2
    have hpert : ∀ x ∈ Aj j, ∃ a ∈
        ((fun k => inner ℝ (V q) (gridCorner ρ k)) '' (Pj j : Set (Fin 3 → ℤ))),
        |x - (a + inner ℝ (V p - V q) q)| ≤ (8 : ℝ) * ρ := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨inner ℝ (V q) (gridCorner ρ k), ⟨k, hk, rfl⟩, ?_⟩
      have hR : ‖gridCorner ρ k - q‖ ≤ 2 * θ := by
        simpa only [dist_eq_norm] using hdist j hk
      have hh := centered_projection_error hL hR
      have he : (40 * s) * (2 * θ) = 8 * ρ := by dsimp [θ]; nlinarith [hs2]
      rwa [he] at hh
    have hh := hc.perturb hρ 8 hpert
    convert hh using 1
    norm_num
    ring
  have hcovered := CoverUpper.iUnion hcover
  have hsub :
      (fun k => inner ℝ (V p) (gridCorner ρ k)) '' (P : Set (Fin 3 → ℤ)) ⊆ ⋃ j, Aj j := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    let j : J := ⟨key k, Finset.mem_image_of_mem _ hk⟩
    exact mem_iUnion.mpr ⟨j, k, Finset.mem_filter.mpr ⟨hk, rfl⟩, rfl⟩
  apply (hcovered.mono_set hsub).mono_bound
  simp only [Fintype.card_coe]
  calc (J.card : ℝ) * (38 * B / ρ) ≤ (802 : ℝ) ^ 3 * (38 * B / ρ) :=
        mul_le_mul_of_nonneg_right hJcard (by positivity)
    _ = (38 * (802 : ℝ) ^ 3) * B / ρ := by ring

end WangZahlLot.Obl.wz_slab_local_linearity
