-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_off_stem_brush_overlap.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry
import Submission.WZ.Obl.wz_transverse_brush_selection.Geometry

namespace WangZahlLot.Obl.wz_off_stem_brush_overlap

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

abbrev Stem (x v : Space) : Set Space := Set.range (fun t : ℝ => x + t • v)

noncomputable def angle (v w : Space) : ℝ := min ‖v - w‖ ‖v + w‖

lemma tube_point {δ : ℝ} {x v p : Space} (hp : p ∈ Tube δ x v) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖p - (x + t • v)‖ < δ := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  exact ⟨t, ht, by simpa [dist_eq_norm] using hpq⟩

lemma inner_error {e p q : Space} (he : ‖e‖ = 1) {δ : ℝ}
    (h : ‖p - q‖ < δ) : |inner ℝ e p - inner ℝ e q| ≤ δ := by
  rw [← inner_sub_right]
  exact (abs_real_inner_le_norm _ _).trans (by simpa [he] using h.le)

lemma inner_angle {e v w : Space} (he : ‖e‖ = 1) (hev : inner ℝ e v = 0)
    {θ : ℝ} (ha : angle v w ≤ θ) : |inner ℝ e w| ≤ θ := by
  rcases min_le_iff.mp ha with h | h
  · have hi := abs_real_inner_le_norm e (v - w)
    simpa [inner_sub_right, hev, he] using hi.trans (by simpa [he] using h)
  · have hi := abs_real_inner_le_norm e (v + w)
    simpa [inner_add_right, hev, he] using hi.trans (by simpa [he] using h)

lemma adapted_basis (v w : Space) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space,
      inner ℝ (b 1) v = 0 ∧ inner ℝ (b 2) v = 0 ∧ inner ℝ (b 2) w = 0 := by
  let f : Fin 3 → Space := ![v, w, 0]
  have hd : Module.finrank ℝ Space = Fintype.card (Fin 3) := by simp
  refine ⟨InnerProductSpace.gramSchmidtOrthonormalBasis hd f, ?_, ?_, ?_⟩
  · simpa [f] using InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hd f
      (show (0 : Fin 3) < 1 by decide)
  · simpa [f] using InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hd f
      (show (0 : Fin 3) < 2 by decide)
  · simpa [f] using InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hd f
      (show (1 : Fin 3) < 2 by decide)

lemma inner_tube_difference {δ : ℝ} {x v e p q : Space} (he : ‖e‖ = 1)
    (hp : p ∈ Tube δ x v) (hq : q ∈ Tube δ x v) :
    |inner ℝ e p - inner ℝ e q| ≤ 2 * δ + |inner ℝ e v| := by
  obtain ⟨s, hs, hps⟩ := tube_point hp
  obtain ⟨t, ht, hqt⟩ := tube_point hq
  have h₁ := inner_error he hps
  have h₂ := inner_error he hqt
  have hst : |s - t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  have hid : inner ℝ e p - inner ℝ e q =
      (inner ℝ e p - inner ℝ e (x + s • v)) +
      (s - t) * inner ℝ e v + (inner ℝ e (x + t • v) - inner ℝ e q) := by
    simp only [inner_add_right, inner_smul_right]
    ring
  rw [hid]
  calc
    _ ≤ |inner ℝ e p - inner ℝ e (x + s • v)| +
        |(s - t) * inner ℝ e v| + |inner ℝ e (x + t • v) - inner ℝ e q| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ δ + 1 * |inner ℝ e v| + δ := by
      rw [abs_mul, abs_sub_comm (inner ℝ e (x + t • v))]
      gcongr
    _ = _ := by ring

lemma near_stem_inner {δ : ℝ} {x v y w e : Space} (he : ‖e‖ = 1)
    (hev : inner ℝ e v = 0) (hew : inner ℝ e w = 0)
    (hmeet : (Tube δ x v ∩ Tube δ y w).Nonempty) :
    |inner ℝ e x - inner ℝ e y| ≤ 2 * δ := by
  obtain ⟨p, hp, hq⟩ := hmeet
  have h₁ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab he hev x δ hp
  have h₂ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab he hew y δ hq
  calc
    _ ≤ |inner ℝ e x - inner ℝ e p| + |inner ℝ e p - inner ℝ e y| := abs_sub_le _ _ _
    _ ≤ δ + δ := by rw [abs_sub_comm (inner ℝ e x)]; exact add_le_add h₁ h₂
    _ = _ := by ring

/-- An off-stem crossing forces a brush direction to be almost parallel to
any plane containing the two reference directions. -/
lemma normal_direction {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    {x v y w z u e : Space} (he : ‖e‖ = 1) (hev : inner ℝ e v = 0)
    (hew : inner ℝ e w = 0) (hu : ‖u‖ = 1)
    (hbase : (Tube δ x v ∩ Tube δ y w).Nonempty)
    (hstem : (Tube δ z u ∩ Tube δ y w).Nonempty)
    (hoff : ((Tube δ x v \ thickening r (Stem y w)) ∩ Tube δ z u).Nonempty) :
    |inner ℝ e u| ≤ 12 * δ / r := by
  by_cases hsmall : r ≤ 6 * δ
  · have hinner : |inner ℝ e u| ≤ 1 := by simpa [he, hu] using abs_real_inner_le_norm e u
    apply hinner.trans
    apply (le_div_iff₀ hr).2
    linarith
  obtain ⟨p, ⟨hpi, hpo⟩, hpj⟩ := hoff
  obtain ⟨q, hqj, hq0⟩ := hstem
  obtain ⟨s, hs, hps⟩ := tube_point hpj
  obtain ⟨t, ht, hqt⟩ := tube_point hqj
  obtain ⟨a, ha, hqa⟩ := tube_point hq0
  have hta : ‖(z + t • u) - (y + a • w)‖ < 2 * δ := by
    calc
      _ ≤ ‖(z + t • u) - q‖ + ‖q - (y + a • w)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 2 * δ := by rw [norm_sub_rev (z + t • u)]; linarith
  have hrp : r ≤ ‖p - (y + a • w)‖ := by
    by_contra! h
    exact hpo (mem_thickening_iff.mpr ⟨y + a • w, ⟨a, rfl⟩, by simpa [dist_eq_norm] using h⟩)
  have hstnorm : ‖(z + s • u) - (z + t • u)‖ = |s - t| := by
    rw [show (z + s • u) - (z + t • u) = (s - t) • u by module]
    simp [norm_smul, hu, Real.norm_eq_abs]
  have hdist : ‖p - (y + a • w)‖ < |s - t| + 3 * δ := by
    calc
      _ ≤ ‖p - (z + s • u)‖ + ‖(z + s • u) - (y + a • w)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖p - (z + s • u)‖ +
          (‖(z + s • u) - (z + t • u)‖ + ‖(z + t • u) - (y + a • w)‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < _ := by rw [hstnorm]; linarith
  have hst : r / 2 ≤ |s - t| := by linarith
  have hxy := near_stem_inner he hev hew hbase
  have hpx := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab he hev x δ hpi
  have hps' := inner_error he hps
  have hta' := inner_error he hta
  have hid : (s - t) * inner ℝ e u =
      (inner ℝ e (z + s • u) - inner ℝ e p) +
      (inner ℝ e p - inner ℝ e x) +
      (inner ℝ e x - inner ℝ e y) +
      (inner ℝ e (y + a • w) - inner ℝ e (z + t • u)) := by
    simp only [inner_add_right, inner_smul_right, hew]
    ring
  have hbound : |s - t| * |inner ℝ e u| ≤ 6 * δ := by
    rw [← abs_mul, hid]
    have h₁ := abs_le.mp hps'
    have h₂ := abs_le.mp (show |inner ℝ e p - inner ℝ e x| ≤ δ from hpx)
    have h₃ := abs_le.mp hxy
    have h₄ := abs_le.mp hta'
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  apply (le_div_iff₀ hr).2
  nlinarith [mul_le_mul_of_nonneg_right hst (abs_nonneg (inner ℝ e u))]

lemma transverse_coordinate {δ θ : ℝ} {x v z u e : Space} (he : ‖e‖ = 1)
    (hev : inner ℝ e v = 0) (hangle : angle v u ≤ θ)
    (hmeet : (Tube δ x v ∩ Tube δ z u).Nonempty) {p : Space}
    (hp : p ∈ Tube δ z u) : |inner ℝ e (p - x)| ≤ 3 * δ + θ := by
  obtain ⟨q, hqi, hqj⟩ := hmeet
  have h₁ := inner_tube_difference he hp hqj
  have h₂ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab he hev x δ hqi
  have h₃ := inner_angle he hev hangle
  rw [inner_sub_right]
  exact (abs_sub_le (inner ℝ e p) (inner ℝ e q) (inner ℝ e x)).trans (by
      have h₂ : |inner ℝ e q - inner ℝ e x| ≤ δ := h₂
      linarith)

lemma normal_coordinate {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1)
    {x v y w z u e : Space} (he : ‖e‖ = 1) (hev : inner ℝ e v = 0)
    (hew : inner ℝ e w = 0) (hu : ‖u‖ = 1)
    (hbase : (Tube δ x v ∩ Tube δ y w).Nonempty)
    (hstem : (Tube δ z u ∩ Tube δ y w).Nonempty)
    (hoff : ((Tube δ x v \ thickening r (Stem y w)) ∩ Tube δ z u).Nonempty)
    {p : Space} (hp : p ∈ Tube δ z u) : |inner ℝ e (p - x)| ≤ 15 * δ / r := by
  obtain ⟨q, ⟨hqi, hqo⟩, hqj⟩ := hoff
  have h₁ := inner_tube_difference he hp hqj
  have h₂ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab he hev x δ hqi
  have h₃ := normal_direction hδ hr he hev hew hu hbase hstem ⟨q, ⟨hqi, hqo⟩, hqj⟩
  have hsum : |inner ℝ e (p - x)| ≤ 3 * δ + 12 * δ / r := by
    rw [inner_sub_right]
    exact (abs_sub_le (inner ℝ e p) (inner ℝ e q) (inner ℝ e x)).trans (by
      have h₂ : |inner ℝ e q - inner ℝ e x| ≤ δ := h₂
      linarith)
  apply hsum.trans
  rw [le_div_iff₀ hr]
  have hid : (3 * δ + 12 * δ / r) * r = 3 * δ * r + 12 * δ := by field_simp
  rw [hid]
  nlinarith

lemma coordinate_box_convex (b : OrthonormalBasis (Fin 3) ℝ Space) (x : Space)
    (c : Fin 3 → ℝ) :
    Convex ℝ {p : Space | ∀ k, -c k ≤ b.repr (p - x) k ∧ b.repr (p - x) k ≤ c k} := by
  intro p hp q hq a d ha hd had k
  simp only [OrthonormalBasis.repr_apply_apply, inner_sub_right] at hp hq ⊢
  have hk : inner ℝ (b k) (a • p + d • q) - inner ℝ (b k) x =
      a * (inner ℝ (b k) p - inner ℝ (b k) x) +
      d * (inner ℝ (b k) q - inner ℝ (b k) x) := by
    simp only [inner_add_right, inner_smul_right]
    nlinarith [congrArg (fun t : ℝ => t * inner ℝ (b k) x) had]
  rw [hk]
  constructor
  · have h₁ := mul_le_mul_of_nonneg_left (hp k).1 ha
    have h₂ := mul_le_mul_of_nonneg_left (hq k).1 hd
    nlinarith [congrArg (fun t : ℝ => t * c k) had]
  · have h₁ := mul_le_mul_of_nonneg_left (hp k).2 ha
    have h₂ := mul_le_mul_of_nonneg_left (hq k).2 hd
    nlinarith [congrArg (fun t : ℝ => t * c k) had]

/-- Full tubes in an angular cap meeting both a fixed tube off the stem
and the stem itself lie in one convex box. -/
lemma off_stem_container {δ r θ : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (hr1 : r ≤ 1) (hδθ : δ ≤ θ) {x v y w : Space}
    (hball : Tube δ x v ⊆ ball (0 : Space) 1)
    (hbase : (Tube δ x v ∩ Tube δ y w).Nonempty) :
    ∃ W : Set Space, Convex ℝ W ∧ volume W ≤ ENNReal.ofReal (1024 * θ * δ / r) ∧
      ∀ z u : Space, ‖u‖ = 1 → Tube δ z u ⊆ ball (0 : Space) 1 →
        (Tube δ z u ∩ Tube δ y w).Nonempty →
        ((Tube δ x v \ thickening r (Stem y w)) ∩ Tube δ z u).Nonempty →
        angle v u ≤ θ → Tube δ z u ⊆ W := by
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := adapted_basis v w
  let c : Fin 3 → ℝ := ![2, 4 * θ, 15 * δ / r]
  let W : Set Space := {p : Space | ∀ k, -c k ≤ b.repr (p - x) k ∧ b.repr (p - x) k ≤ c k}
  have hr : 0 < r := hδ.trans_le hδr
  have hθ : 0 < θ := hδ.trans_le hδθ
  refine ⟨W, coordinate_box_convex b x c, ?_, ?_⟩
  · calc
      volume W = ENNReal.ofReal (960 * θ * δ / r) := by
        rw [WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
        simp only [Fin.prod_univ_three, c, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, sub_neg_eq_add]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        change (2 + 2) * (4 * θ + 4 * θ) * (15 * δ / r + 15 * δ / r) = 960 * θ * δ / r
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr; norm_num)
  · intro z u hu hz hstem hoff hangle p hp k
    rw [← abs_le, OrthonormalBasis.repr_apply_apply]
    fin_cases k
    · have hxn : ‖x‖ < 1 := by
        have := hball (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
        simpa using this
      have hpn : ‖p‖ < 1 := by simpa using hz hp
      have hh := abs_real_inner_le_norm (b 0) (p - x)
      rw [b.norm_eq_one, one_mul] at hh
      exact hh.trans ((norm_sub_le p x).trans (by change ‖p‖ + ‖x‖ ≤ 2; linarith))
    · have hmeet : (Tube δ x v ∩ Tube δ z u).Nonempty := by
        obtain ⟨q, hqi, hqj⟩ := hoff
        exact ⟨q, hqi.1, hqj⟩
      have hh := transverse_coordinate (b.norm_eq_one 1) hb₁ hangle hmeet hp
      exact hh.trans (by change 3 * δ + θ ≤ 4 * θ; linarith)
    · exact normal_coordinate hδ hr hr1 (b.norm_eq_one 2) hb₂ hb₃ hu hbase hstem hoff hp

end WangZahlLot.Obl.wz_off_stem_brush_overlap
