-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SlabNarrowing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.TubeNormal
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzTools
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.CellPigeonhole

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set Metric
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_extremal_lipschitz_grains (cubeIndex exists_cells_cover dist_lt_of_cubeIndex_eq)
open scoped Classical

/-- Quantizing nearby exact containing planes selects one narrow slab at a
polynomial cost in the parameter radius. -/
theorem select_nearby_planes_weighted {δ w t : ℝ} (hδ : 0 < δ) (hδw : δ ≤ w)
    {n : ℕ} (x v : Fin n → Space) (weight : Fin n → ℝ) (F : Finset (Fin n))
    (e N : Space) (he : ‖e‖ = 1) (hweight : ∀ i ∈ F, 0 ≤ weight i)
    (hball : ∀ i ∈ F, Tube δ (x i) (v i) ⊆ ball 0 1)
    (u : Fin n → Space) (s : Fin n → ℝ) (hu : ∀ i, ‖u i‖ = 1)
    (hdata : ∀ i ∈ F, ‖u i - N‖ ≤ 5 * w ∧ |s i - t| ≤ 5 * w ∧
      Tube δ (x i) (v i) ⊆ {p | |inner ℝ (u i) p - s i| ≤ δ}) :
    ∃ (u : Space) (s : ℝ) (G : Finset (Fin n)), G ⊆ F ∧ ‖u‖ = 1 ∧
      (∀ i ∈ G, Tube δ (x i) (v i) ⊆ {p | |inner ℝ u p - s| ≤ 2 * δ}) ∧
      (∑ i ∈ F, weight i) ≤ (100 * w / δ) ^ 6 * (∑ i ∈ G, weight i) := by
  by_cases hF : F.Nonempty
  swap
  · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    refine ⟨e, t, ∅, Finset.empty_subset _, he, by simp, ?_⟩
    simp [hF0]
  have hw0 : 0 < w := hδ.trans_le hδw
  have hr : 0 < δ / 8 := by positivity
  let offset := fun i => (s i - t) • e
  let f := fun i => (cubeIndex (δ / 8) (u i), cubeIndex (δ / 8) (offset i))
  obtain ⟨S₁, hS₁card, hS₁⟩ := exists_cells_cover N (R := 5 * w) (by positivity) hr
  obtain ⟨S₂, hS₂card, hS₂⟩ := exists_cells_cover (0 : Space) (R := 5 * w) (by positivity) hr
  let C := F.image f
  have hC : C.Nonempty := hF.image f
  have hCsub : C ⊆ S₁.product S₂ := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_product.mpr
    constructor
    · apply hS₁
      rw [dist_eq_norm]
      exact (hdata i hi).1
    · apply hS₂
      simpa only [offset, dist_zero_right, norm_smul, Real.norm_eq_abs, he, mul_one] using
        (hdata i hi).2.1
  have hwr : 1 ≤ w / δ := (le_div_iff₀ hδ).mpr (by simpa using hδw)
  have hcard_bound : ∀ (S : Finset (Fin 3 → ℤ)),
      S.card ≤ (⌊2 * (5 * w) / (δ / 8)⌋₊ + 3) ^ 3 →
        (S.card : ℝ) ≤ (100 * w / δ) ^ 3 := by
    intro S hS
    have hc : (S.card : ℝ) ≤ ((⌊2 * (5 * w) / (δ / 8)⌋₊ : ℝ) + 3) ^ 3 := by
      exact_mod_cast hS
    have hfloor : (⌊2 * (5 * w) / (δ / 8)⌋₊ : ℝ) ≤ 80 * w / δ := by
      convert Nat.floor_le (by positivity : 0 ≤ 2 * (5 * w) / (δ / 8)) using 1 <;> ring
    refine hc.trans (pow_le_pow_left₀ (by positivity) ?_ 3)
    rw [show 80 * w / δ = 80 * (w / δ) by ring] at hfloor
    rw [show 100 * w / δ = 100 * (w / δ) by ring]
    linarith only [hwr, hfloor]
  have hCcard : (C.card : ℝ) ≤ (100 * w / δ) ^ 6 := by
    have hc : (C.card : ℝ) ≤ (S₁.card : ℝ) * S₂.card := by
      exact_mod_cast (Finset.card_le_card hCsub).trans_eq (Finset.card_product S₁ S₂)
    calc
      _ ≤ (S₁.card : ℝ) * S₂.card := hc
      _ ≤ (100 * w / δ) ^ 3 * (100 * w / δ) ^ 3 :=
        mul_le_mul (hcard_bound S₁ hS₁card) (hcard_bound S₂ hS₂card) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  let mass := fun c => ∑ i ∈ F.filter (fun i => f i = c), weight i
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image C mass hC
  obtain ⟨i₀, hi₀, hfi₀⟩ := Finset.mem_image.mp hc
  let G := F.filter (fun i => f i = c)
  have hGF : G ⊆ F := Finset.filter_subset _ _
  refine ⟨u i₀, s i₀, G, hGF, hu i₀, ?_, ?_⟩
  · intro i hi
    have hfi : f i = c := (Finset.mem_filter.mp hi).2
    have hnormal : cubeIndex (δ / 8) (u i₀) = cubeIndex (δ / 8) (u i) :=
      congrArg Prod.fst (hfi₀.trans hfi.symm)
    have hoff : cubeIndex (δ / 8) (offset i) = cubeIndex (δ / 8) (offset i₀) :=
      congrArg Prod.snd (hfi.trans hfi₀.symm)
    apply tube_slab_perturb (hball i (hGF hi)) (hdata i (hGF hi)).2.2
    · have hh := (dist_lt_of_cubeIndex_eq hr hnormal).le
      rw [dist_eq_norm] at hh
      linarith
    · have hh := (dist_lt_of_cubeIndex_eq hr hoff).le
      have heq : dist (offset i) (offset i₀) = |s i - s i₀| := by
        dsimp [offset]
        rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, he, mul_one]
        congr 1
        ring
      rw [heq] at hh
      linarith
  · have hmass_nonneg : 0 ≤ mass c := Finset.sum_nonneg fun i hi =>
      hweight i (Finset.mem_filter.mp hi).1
    calc
      _ = ∑ c ∈ C, mass c :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) weight).symm
      _ ≤ ∑ _c ∈ C, mass c := Finset.sum_le_sum fun j hj => hmax j hj
      _ = (C.card : ℝ) * mass c := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (100 * w / δ) ^ 6 * mass c := mul_le_mul_of_nonneg_right hCcard hmass_nonneg

/-- A weighted family of full tubes in a width-w slab has a subfamily in a
width-2delta slab. The loss is bounded by a fixed power of w/delta. -/
theorem narrow_slab_weighted {δ w t : ℝ} (hδ : 0 < δ) (hδw : δ ≤ w) (hw : w < 1 / 2)
    {n : ℕ} (x v : Fin n → Space) (weight : Fin n → ℝ) (F : Finset (Fin n))
    {e : Space} (he : ‖e‖ = 1) (hweight : ∀ i ∈ F, 0 ≤ weight i)
    (hv : ∀ i ∈ F, ‖v i‖ = 1) (hball : ∀ i ∈ F, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hslab : ∀ i ∈ F, Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ w}) :
    ∃ (u : Space) (s : ℝ) (G : Finset (Fin n)), G ⊆ F ∧ ‖u‖ = 1 ∧
      (∀ i ∈ G, Tube δ (x i) (v i) ⊆ {p | |inner ℝ u p - s| ≤ 2 * δ}) ∧
      (∑ i ∈ F, weight i) ≤ (100 * w / δ) ^ 6 * (∑ i ∈ G, weight i) := by
  have hw0 : 0 < w := hδ.trans_le hδw
  have hplanes : ∀ i, ∃ (u : Space) (s : ℝ), ‖u‖ = 1 ∧
      (i ∈ F → ‖u - e‖ ≤ 4 * w ∧ |s - t| ≤ 5 * w ∧
        Tube δ (x i) (v i) ⊆ {p | |inner ℝ u p - s| ≤ δ}) := by
    intro i
    by_cases hi : i ∈ F
    · obtain ⟨u, s, hu, hun, hst, hT⟩ :=
        tube_exact_plane_near hδ hw (hv i hi) he (hball i hi) (hslab i hi)
      exact ⟨u, s, hu, fun _ => ⟨hun, hst, hT⟩⟩
    · exact ⟨e, t, he, fun h => (hi h).elim⟩
  choose u s hu hdata using hplanes
  exact select_nearby_planes_weighted hδ hδw x v weight F e e he hweight hball u s hu
    (fun i hi => ⟨(hdata i hi).1.trans (by linarith), (hdata i hi).2⟩)

/-- Every bounded tube family has a planar subfamily, with a fixed polynomial
loss in the tube radius. No broadness or density is needed. -/
theorem global_slab_weighted {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {n : ℕ} (x v : Fin n → Space) (weight : Fin n → ℝ) (F : Finset (Fin n))
    (hweight : ∀ i ∈ F, 0 ≤ weight i)
    (hball : ∀ i ∈ F, Tube δ (x i) (v i) ⊆ ball 0 1) :
    ∃ (u : Space) (s : ℝ) (G : Finset (Fin n)), G ⊆ F ∧ ‖u‖ = 1 ∧
      (∀ i ∈ G, Tube δ (x i) (v i) ⊆ {p | |inner ℝ u p - s| ≤ 2 * δ}) ∧
      (∑ i ∈ F, weight i) ≤ (100 / δ) ^ 6 * (∑ i ∈ G, weight i) := by
  have hnormal : ∀ i, ∃ u : Space, ‖u‖ = 1 ∧ inner ℝ u (v i) = 0 := by
    intro i
    obtain ⟨basis, _, hi, _⟩ := wz_off_stem_brush_overlap.adapted_basis (v i) (v i)
    exact ⟨basis 2, basis.norm_eq_one 2, hi⟩
  choose u hu huv using hnormal
  let e : Space := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hdata : ∀ i ∈ F, ‖u i - 0‖ ≤ 5 * (1 : ℝ) ∧
      |inner ℝ (u i) (x i) - 0| ≤ 5 * (1 : ℝ) ∧
      Tube δ (x i) (v i) ⊆ {p | |inner ℝ (u i) p - inner ℝ (u i) (x i)| ≤ δ} := by
    intro i hi
    have hx : x i ∈ Tube δ (x i) (v i) :=
      self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
    have hxn : ‖x i‖ ≤ 1 := (mem_ball_zero_iff.mp (hball i hi hx)).le
    refine ⟨by simp [hu], ?_, tube_subset_normal_slab (hu i) (huv i)⟩
    calc
      _ = |inner ℝ (u i) (x i)| := by rw [sub_zero]
      _ ≤ ‖u i‖ * ‖x i‖ := abs_real_inner_le_norm _ _
      _ ≤ 5 * (1 : ℝ) := by rw [hu, one_mul]; linarith
  simpa only [mul_one] using select_nearby_planes_weighted hδ hδ1 x v weight F e 0 he
    hweight hball u (fun i => inner ℝ (u i) (x i)) hu hdata

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
