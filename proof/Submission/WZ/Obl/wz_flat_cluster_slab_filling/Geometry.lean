-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Basic

/-!
Elementary geometry of tubes, slabs, frames and boxes for the proof of
`WangZahlLot.wz_flat_cluster_slab_filling`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

/-- A point of a tube is within `δ` of a point of its core segment. -/
lemma tube_point' {δ : ℝ} {x v p : Space} (hp : p ∈ Tube δ x v) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖p - (x + t • v)‖ < δ := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  exact ⟨t, ht, by simpa [dist_eq_norm] using hpq⟩

/-- A tube inside a slab forces the slab to be at least as wide as the tube. -/
lemma slab_width_ge {δ r t : ℝ} {x v u : Space} (hδ : 0 < δ) (hu : ‖u‖ = 1)
    (h : Tube δ x v ⊆ Slab u t r) : δ ≤ r := by
  by_contra hlt
  have hlt := not_le.mp hlt
  set d := (max r 0 + δ) / 2 with hd
  have hd0 : 0 ≤ d := by have := le_max_right r 0; linarith
  have hdδ : d < δ := by have : max r 0 < δ := max_lt hlt hδ; linarith
  have hdr : r < d := by have := le_max_left r 0; linarith
  have hmem : ∀ c : ℝ, |c| < δ → x + c • u ∈ Slab u t r := by
    intro c hc
    apply h
    rw [mem_thickening_iff]
    refine ⟨x, left_mem_segment ℝ x (x + v), ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs]
    exact hc
  have h1 := hmem d (by rw [abs_of_nonneg hd0]; exact hdδ)
  have h2 := hmem (-d) (by rw [abs_neg, abs_of_nonneg hd0]; exact hdδ)
  simp only [Slab, Set.mem_ofPred_eq, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hu] at h1 h2
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  norm_num at h1' h2'
  linarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-- The direction of a unit tube inside a slab is almost parallel to the slab. -/
lemma slab_inner_dir {δ r t : ℝ} {x v u : Space} (hδ : 0 < δ)
    (h : Tube δ x v ⊆ Slab u t r) : |inner ℝ u v| ≤ 2 * r := by
  have h1 : x ∈ Slab u t r := h (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have h2 : x + v ∈ Slab u t r :=
    h (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  simp only [Slab, Set.mem_ofPred_eq, inner_add_right] at h1 h2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- A unit tube inside a coarse unit tube has almost the same (unoriented) direction. -/
lemma coarse_angle {δ ρ : ℝ} {x v y w : Space} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h : Tube δ x v ⊆ Tube ρ y w) : angle v w ≤ 4 * ρ := by
  have hx := h (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hxv := h (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  obtain ⟨a, ha, hxa⟩ := tube_point' hx
  obtain ⟨a', ha', hxa'⟩ := tube_point' hxv
  have hvs : ‖v - (a' - a) • w‖ < 2 * ρ := by
    have e : v - (a' - a) • w = (x + v - (y + a' • w)) - (x - (y + a • w)) := by module
    rw [e]
    calc _ ≤ ‖x + v - (y + a' • w)‖ + ‖x - (y + a • w)‖ := norm_sub_le _ _
      _ < ρ + ρ := add_lt_add hxa' hxa
      _ = 2 * ρ := by ring
  have hsw : ‖(a' - a) • w‖ = |a' - a| := by rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
  have h1 : 1 - |a' - a| < 2 * ρ := by
    have := norm_sub_norm_le v ((a' - a) • w)
    rw [hv, hsw] at this
    linarith
  have hs1 : a' - a ≤ 1 := by linarith [ha.1, ha'.2]
  have hs2 : -1 ≤ a' - a := by linarith [ha.2, ha'.1]
  rcases le_or_gt 0 (a' - a) with hs0 | hs0
  · have : ‖v - w‖ < 4 * ρ := by
      have e : v - w = (v - (a' - a) • w) + (a' - a - 1) • w := by module
      rw [e]
      calc _ ≤ ‖v - (a' - a) • w‖ + ‖(a' - a - 1) • w‖ := norm_add_le _ _
        _ = ‖v - (a' - a) • w‖ + (1 - (a' - a)) := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
        _ < 4 * ρ := by rw [abs_of_nonneg hs0] at h1; linarith
    exact (min_le_left _ _).trans this.le
  · have : ‖v + w‖ < 4 * ρ := by
      have e : v + w = (v - (a' - a) • w) + (a' - a + 1) • w := by module
      rw [e]
      calc _ ≤ ‖v - (a' - a) • w‖ + ‖(a' - a + 1) • w‖ := norm_add_le _ _
        _ = ‖v - (a' - a) • w‖ + (1 + (a' - a)) := by
          rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; ring
        _ < 4 * ρ := by rw [abs_of_neg hs0] at h1; linarith
    exact (min_le_right _ _).trans this.le

lemma angle_comm (v w : Space) : angle v w = angle w v := by
  show min ‖v - w‖ ‖v + w‖ = min ‖w - v‖ ‖w + v‖
  rw [norm_sub_rev, add_comm]

/-- Triangle inequality for the unoriented angle. -/
lemma angle_triangle (u v w : Space) : angle u w ≤ angle u v + angle v w := by
  show min ‖u - w‖ ‖u + w‖ ≤ min ‖u - v‖ ‖u + v‖ + min ‖v - w‖ ‖v + w‖
  rcases min_choice ‖u - v‖ ‖u + v‖ with h1 | h1 <;>
    rcases min_choice ‖v - w‖ ‖v + w‖ with h2 | h2 <;> rw [h1, h2]
  · have := norm_add_le (u - v) (v - w)
    rw [show u - v + (v - w) = u - w by abel] at this
    exact (min_le_left _ _).trans this
  · have := norm_add_le (u - v) (v + w)
    rw [show u - v + (v + w) = u + w by abel] at this
    exact (min_le_right _ _).trans this
  · have := norm_sub_le (u + v) (v - w)
    rw [show u + v - (v - w) = u + w by abel] at this
    exact (min_le_right _ _).trans this
  · have := norm_sub_le (u + v) (v + w)
    rw [show u + v - (v + w) = u - w by abel] at this
    exact (min_le_left _ _).trans this

private lemma norm_sq_coords (z : Space) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

private lemma abs_coord_le (z : Space) (k : Fin 3) : |z k| ≤ ‖z‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z k

private lemma abs_frame_coord_le (g : Space ≃ₗᵢ[ℝ] Space) (z : Space) (k : Fin 3) :
    |g z k| ≤ ‖z‖ :=
  (abs_coord_le (g z) k).trans (LinearIsometryEquiv.norm_map g z).le

/-- An orthonormal frame adapted to a direction `v` and a slab normal `u`: the last
coordinate is the `v`-coordinate, and the first coordinate of a vector is controlled by its
`u`-component. -/
lemma adapted_frame {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : |inner ℝ u v| ≤ 1 / 2) :
    ∃ g : Space ≃ₗᵢ[ℝ] Space, (∀ p, g p 2 = inner ℝ v p) ∧
      ∀ w, |g w 0| ≤ 2 * (|inner ℝ u w| + |inner ℝ u v| * ‖w‖) := by
  let f : Fin 3 → Space := ![v, u, 0]
  have hd : Module.finrank ℝ Space = Fintype.card (Fin 3) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hd f
  have hgs : InnerProductSpace.gramSchmidt ℝ f 0 = v := by
    rw [show (0 : Fin 3) = ⊥ from rfl, InnerProductSpace.gramSchmidt_bot]
    rfl
  have hn : InnerProductSpace.gramSchmidtNormed ℝ f 0 = v := by
    simp [InnerProductSpace.gramSchmidtNormed, hgs, hv]
  have hb0 : b 0 = v := by
    rw [InnerProductSpace.gramSchmidtOrthonormalBasis_apply hd (by
      rw [hn]; intro h0; rw [h0, norm_zero] at hv; exact zero_ne_one hv), hn]
  have hb1v : inner ℝ (b 1) v = 0 := by
    simpa [f] using InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hd f
      (show (0 : Fin 3) < 1 by decide)
  have hb2v : inner ℝ (b 2) v = 0 := by
    simpa [f] using InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hd f
      (show (0 : Fin 3) < 2 by decide)
  have hb2u : inner ℝ (b 2) u = 0 := by
    simpa [f] using InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hd f
      (show (1 : Fin 3) < 2 by decide)
  let c := b.reindex (finRotate 3).symm
  have hc0 : c 0 = b 1 := by
    simp only [c, OrthonormalBasis.reindex_apply, Equiv.symm_symm]; rfl
  have hc2 : c 2 = b 0 := by
    simp only [c, OrthonormalBasis.reindex_apply, Equiv.symm_symm]; rfl
  refine ⟨c.repr, ?_, ?_⟩
  · intro p
    rw [OrthonormalBasis.repr_apply_apply, hc2, hb0]
  · intro w
    rw [OrthonormalBasis.repr_apply_apply, hc0]
    have hsum : ∀ z : Space, inner ℝ u z =
        inner ℝ u v * inner ℝ v z + inner ℝ u (b 1) * inner ℝ (b 1) z := by
      intro z
      have := b.sum_inner_mul_inner u z
      rw [Fin.sum_univ_three, hb0, real_inner_comm (b 2) u, hb2u, zero_mul, add_zero] at this
      exact this.symm
    have huu := hsum u
    rw [real_inner_self_eq_norm_sq, hu, real_inner_comm u v, real_inner_comm u (b 1)] at huu
    have hn1 : 1 / 2 ≤ |inner ℝ u (b 1)| := by
      have hsq : inner ℝ u v ^ 2 ≤ 1 / 4 := by
        have := sq_abs (inner ℝ u v)
        nlinarith [abs_nonneg (inner ℝ u v)]
      by_contra hcon
      have hcon := not_le.mp hcon
      have : inner ℝ u (b 1) ^ 2 < 1 / 4 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (inner ℝ u (b 1))]
      nlinarith
    have hw := hsum w
    have hvw : |inner ℝ v w| ≤ ‖w‖ := by
      have := abs_real_inner_le_norm v w
      rwa [hv, one_mul] at this
    have key : |inner ℝ u (b 1)| * |inner ℝ (b 1) w| ≤
        |inner ℝ u w| + |inner ℝ u v| * ‖w‖ := by
      rw [← abs_mul]
      have e : inner ℝ u (b 1) * inner ℝ (b 1) w = inner ℝ u w - inner ℝ u v * inner ℝ v w := by
        linarith
      rw [e]
      calc _ ≤ |inner ℝ u w| + |inner ℝ u v * inner ℝ v w| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul]
          gcongr
    nlinarith [abs_nonneg (inner ℝ (b 1) w), abs_nonneg (inner ℝ u (b 1))]

/-- In a frame whose last coordinate is the `v`-coordinate, `v` is the last basis vector. -/
lemma frame_v {g : Space ≃ₗᵢ[ℝ] Space} {v : Space} (hv : ‖v‖ = 1)
    (hg : ∀ p, g p 2 = inner ℝ v p) : g v 0 = 0 ∧ g v 1 = 0 ∧ g v 2 = 1 := by
  have h2 : g v 2 = 1 := by rw [hg, real_inner_self_eq_norm_sq, hv]; norm_num
  have hn := norm_sq_coords (g v)
  rw [LinearIsometryEquiv.norm_map, hv, h2] at hn
  refine ⟨?_, ?_, h2⟩
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (by nlinarith [sq_nonneg (g v 0), sq_nonneg (g v 1)])
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (by nlinarith [sq_nonneg (g v 0), sq_nonneg (g v 1)])

/-- The other coordinates of a unit vector are controlled by its angle with `v`. -/
lemma frame_coord_le_angle {g : Space ≃ₗᵢ[ℝ] Space} {v : Space} (hv : ‖v‖ = 1)
    (hg : ∀ p, g p 2 = inner ℝ v p) (w : Space) (k : Fin 3) (hk : k ≠ 2) :
    |g w k| ≤ angle w v := by
  have hvk : g v k = 0 := by
    obtain ⟨h0, h1, -⟩ := frame_v hv hg
    fin_cases k
    · exact h0
    · exact h1
    · exact absurd rfl hk
  have e1 : g w k = g (w - v) k := by simp [map_sub, hvk]
  have e2 : g w k = g (w + v) k := by simp [map_add, hvk]
  apply le_min
  · rw [e1]; exact abs_frame_coord_le g _ k
  · rw [e2]; exact abs_frame_coord_le g _ k

/-- A tube lies in the `10δ × b × 2` box centred at its midpoint and aligned with it. -/
lemma tube_subset_box {δ b : ℝ} {x v : Space} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hb : 2 * δ ≤ b) (hδ2 : δ ≤ 1 / 2)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : ∀ p, g p 2 = inner ℝ v p) :
    Tube δ x v ⊆ Box (10 * δ) b 2 (x + (1 / 2 : ℝ) • v) g := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := tube_point' hp
  obtain ⟨h0, h1, h2⟩ := frame_v hv hg
  have hpz : p - (x + (1 / 2 : ℝ) • v) = (t - 1 / 2) • v + (p - (x + t • v)) := by module
  have hgε : ∀ k, |g (p - (x + t • v)) k| < δ := fun k =>
    (abs_frame_coord_le g _ k).trans_lt hpt
  have hcoord : ∀ k, g (p - (x + (1 / 2 : ℝ) • v)) k =
      (t - 1 / 2) * g v k + g (p - (x + t • v)) k := by
    intro k
    rw [hpz, map_add, map_smul]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoord, h0, mul_zero, zero_add]; linarith [hgε 0]
  · rw [hcoord, h1, mul_zero, zero_add]; linarith [hgε 1]
  · rw [hcoord, h2, mul_one]
    calc |(t - 1 / 2) + g (p - (x + t • v)) 2| ≤ |t - 1 / 2| + |g (p - (x + t • v)) 2| :=
          abs_add_le _ _
      _ ≤ 1 / 2 + δ := add_le_add (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          (hgε 2).le
      _ ≤ 2 / 2 := by linarith


/-- The part near `p` of a tube crossing the tube `[x, x+v]` at `p` stays in its box when the
crossing tube is almost parallel to the box's plane. -/
lemma piece_subset_box {δ b L κ0 κ1 : ℝ} {x v y w p : Space} (hδ : 0 < δ)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : ∀ p, g p 2 = inner ℝ v p)
    (hp : p ∈ Tube δ x v) (hpw : p ∈ Tube δ y w)
    (h0 : |g w 0| ≤ κ0) (h1 : |g w 1| ≤ κ1)
    (hκ0 : 3 * δ + κ0 * (L + 2 * δ) ≤ 5 * δ) (hκ1 : 3 * δ + κ1 * (L + 2 * δ) ≤ b / 2)
    (hL : 1 / 2 + δ + L ≤ 1) :
    Tube δ y w ∩ ball p L ⊆ Box (10 * δ) b 2 (x + (1 / 2 : ℝ) • v) g := by
  rintro q ⟨hq, hqL⟩
  rw [mem_ball, dist_eq_norm] at hqL
  obtain ⟨s, hs, hps⟩ := tube_point' hp
  obtain ⟨a, ha, hpa⟩ := tube_point' hpw
  obtain ⟨a', ha', hqa⟩ := tube_point' hq
  obtain ⟨gv0, gv1, gv2⟩ := frame_v hv hg
  have hqz : q - (x + (1 / 2 : ℝ) • v) = (a' - a) • w +
      ((q - (y + a' • w)) - (p - (y + a • w))) + (s - 1 / 2) • v + (p - (x + s • v)) := by
    module
  have hτ : |a' - a| ≤ L + 2 * δ := by
    have e : (a' - a) • w = (q - p) - ((q - (y + a' • w)) - (p - (y + a • w))) := by module
    have hn : ‖(a' - a) • w‖ = |a' - a| := by rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
    rw [← hn, e]
    calc _ ≤ ‖q - p‖ + ‖(q - (y + a' • w)) - (p - (y + a • w))‖ := norm_sub_le _ _
      _ ≤ ‖q - p‖ + (‖q - (y + a' • w)‖ + ‖p - (y + a • w)‖) := by
          gcongr; exact norm_sub_le _ _
      _ ≤ L + 2 * δ := by linarith
  have hcoord : ∀ k, g (q - (x + (1 / 2 : ℝ) • v)) k = (a' - a) * g w k +
      (g (q - (y + a' • w)) k - g (p - (y + a • w)) k) + (s - 1 / 2) * g v k +
        g (p - (x + s • v)) k := by
    intro k
    rw [hqz]
    simp only [map_add, map_sub, map_smul, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
  have hside : ∀ k, k ≠ 2 → ∀ κ, |g w k| ≤ κ → g v k = 0 →
      |g (q - (x + (1 / 2 : ℝ) • v)) k| ≤ 3 * δ + κ * (L + 2 * δ) := by
    intro k _ κ hκ hvk
    rw [hcoord, hvk, mul_zero, add_zero]
    have e1 := (abs_frame_coord_le g (q - (y + a' • w)) k).trans hqa.le
    have e2 := (abs_frame_coord_le g (p - (y + a • w)) k).trans hpa.le
    have e3 := (abs_frame_coord_le g (p - (x + s • v)) k).trans hps.le
    have e4 : |(a' - a) * g w k| ≤ (L + 2 * δ) * κ := by
      rw [abs_mul]
      exact mul_le_mul hτ hκ (abs_nonneg _) (by linarith [abs_nonneg (a' - a)])
    calc _ ≤ |(a' - a) * g w k + (g (q - (y + a' • w)) k - g (p - (y + a • w)) k)| +
          |g (p - (x + s • v)) k| := abs_add_le _ _
      _ ≤ |(a' - a) * g w k| + |g (q - (y + a' • w)) k - g (p - (y + a • w)) k| +
          |g (p - (x + s • v)) k| := by gcongr; exact abs_add_le _ _
      _ ≤ |(a' - a) * g w k| + (|g (q - (y + a' • w)) k| + |g (p - (y + a • w)) k|) +
          |g (p - (x + s • v)) k| := by gcongr; exact abs_sub _ _
      _ ≤ (L + 2 * δ) * κ + (δ + δ) + δ := by gcongr
      _ = 3 * δ + κ * (L + 2 * δ) := by ring
  refine ⟨?_, ?_, ?_⟩
  · have := hside 0 (by decide) κ0 h0 gv0
    linarith
  · have := hside 1 (by decide) κ1 h1 gv1
    linarith
  · rw [hg]
    have e : q - (x + (1 / 2 : ℝ) • v) = (q - p) + (s - 1 / 2) • v + (p - (x + s • v)) := by
      module
    rw [e, inner_add_right, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    have e1 : |inner ℝ v (q - p)| ≤ L := by
      have := abs_real_inner_le_norm v (q - p)
      rw [hv, one_mul] at this
      linarith
    have e2 : |inner ℝ v (p - (x + s • v))| ≤ δ := by
      have := abs_real_inner_le_norm v (p - (x + s • v))
      rw [hv, one_mul] at this
      linarith
    have e3 : |s - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    calc _ ≤ |inner ℝ v (q - p) + (s - 1 / 2) * 1 ^ 2| + |inner ℝ v (p - (x + s • v))| :=
          abs_add_le _ _
      _ ≤ |inner ℝ v (q - p)| + |(s - 1 / 2) * 1 ^ 2| + |inner ℝ v (p - (x + s • v))| := by
          gcongr; exact abs_add_le _ _
      _ ≤ L + 1 / 2 + δ := by
          rw [one_pow, mul_one]
          linarith
      _ ≤ 2 / 2 := by linarith

/-- Two crossing tubes through points `p, p'` of the tube `[x,x+v]` that meet near both
points have directions separated proportionally to the distance between `p` and `p'`. -/
lemma meeting_angle {δ L θ : ℝ} {x v y w y' w' p p' q : Space} (hδ : 0 < δ)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : ∀ p, g p 2 = inner ℝ v p)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 2 * δ ≤ L)
    (hp : p ∈ Tube δ x v) (hp' : p' ∈ Tube δ x v)
    (hpw : p ∈ Tube δ y w) (hpw' : p' ∈ Tube δ y' w')
    (hq : q ∈ Tube δ y w) (hq' : q ∈ Tube δ y' w')
    (hqp : ‖q - p‖ < L) (hqp' : ‖q - p'‖ < L)
    (hcross : θ / 2 ≤ |g w' 1|) :
    θ * |inner ℝ v (p' - p)| ≤ 8 * L * angle w w' + 16 * δ := by
  obtain ⟨gv0, gv1, gv2⟩ := frame_v hv hg
  obtain ⟨s, hs, hps⟩ := tube_point' hp
  obtain ⟨s', hs', hps'⟩ := tube_point' hp'
  obtain ⟨a1, ha1, hpa⟩ := tube_point' hpw
  obtain ⟨a2, ha2, hqa⟩ := tube_point' hq
  obtain ⟨b1, hb1, hpb⟩ := tube_point' hpw'
  obtain ⟨b2, hb2, hqb⟩ := tube_point' hq'
  -- the error vector of the decomposition `p' - p = t • w - t' • w' + E`
  set E : Space := ((q - (y + a2 • w)) - (p - (y + a1 • w))) -
    ((q - (y' + b2 • w')) - (p' - (y' + b1 • w'))) with hE
  have hEn : ‖E‖ < 4 * δ := by
    calc ‖E‖ ≤ ‖(q - (y + a2 • w)) - (p - (y + a1 • w))‖ +
          ‖(q - (y' + b2 • w')) - (p' - (y' + b1 • w'))‖ := norm_sub_le _ _
      _ ≤ (‖q - (y + a2 • w)‖ + ‖p - (y + a1 • w)‖) +
          (‖q - (y' + b2 • w')‖ + ‖p' - (y' + b1 • w')‖) :=
          add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ < (δ + δ) + (δ + δ) := by gcongr
      _ = 4 * δ := by ring
  have hpp : p' - p = (a2 - a1) • w - (b2 - b1) • w' + E := by rw [hE]; module
  -- `|t| ≤ L + 2δ`
  have ht : ∀ {y w : Space} {a1 a2 : ℝ} {p : Space}, ‖w‖ = 1 → ‖q - p‖ < L →
      ‖p - (y + a1 • w)‖ < δ → ‖q - (y + a2 • w)‖ < δ → |a2 - a1| ≤ L + 2 * δ := by
    intro y w a1 a2 p hw hqp hpa hqa
    have e : (a2 - a1) • w = (q - p) - ((q - (y + a2 • w)) - (p - (y + a1 • w))) := by module
    have hn : ‖(a2 - a1) • w‖ = |a2 - a1| := by rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
    rw [← hn, e]
    calc _ ≤ ‖q - p‖ + ‖(q - (y + a2 • w)) - (p - (y + a1 • w))‖ := norm_sub_le _ _
      _ ≤ ‖q - p‖ + (‖q - (y + a2 • w)‖ + ‖p - (y + a1 • w)‖) := by
          gcongr; exact norm_sub_le _ _
      _ ≤ L + 2 * δ := by linarith
  have htt := ht hw hqp hpa hqa
  have htt' := ht hw' hqp' hpb hqb
  -- coordinates
  have hcoord : ∀ k, g (p' - p) k = (a2 - a1) * g w k - (b2 - b1) * g w' k + g E k := by
    intro k
    rw [hpp]
    simp only [map_add, map_sub, map_smul, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
  -- coordinate 1 is small since `p, p'` lie in the tube along `v`
  have hpp1 : |g (p' - p) 1| < 2 * δ := by
    have e : p' - p = (s' - s) • v + ((p' - (x + s' • v)) - (p - (x + s • v))) := by module
    have hc : g (p' - p) 1 =
        (s' - s) * g v 1 + (g (p' - (x + s' • v)) 1 - g (p - (x + s • v)) 1) := by
      rw [e, map_add, map_smul, map_sub]
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hc, gv1, mul_zero, zero_add]
    calc _ ≤ |g (p' - (x + s' • v)) 1| + |g (p - (x + s • v)) 1| := abs_sub _ _
      _ < δ + δ := add_lt_add ((abs_frame_coord_le g _ 1).trans_lt hps')
          ((abs_frame_coord_le g _ 1).trans_lt hps)
      _ = 2 * δ := by ring
  have hE1 := (abs_frame_coord_le g E 1).trans_lt hEn
  have hE2 := (abs_frame_coord_le g E 2).trans_lt hEn
  have hQ : |(a2 - a1) * g w 1 - (b2 - b1) * g w' 1| ≤ 6 * δ := by
    have e : (a2 - a1) * g w 1 - (b2 - b1) * g w' 1 = g (p' - p) 1 - g E 1 := by
      rw [hcoord]; ring
    rw [e]
    calc _ ≤ |g (p' - p) 1| + |g E 1| := abs_sub _ _
      _ ≤ 2 * δ + 4 * δ := by linarith
      _ = 6 * δ := by ring
  have hP : |inner ℝ v (p' - p) - ((a2 - a1) * g w 2 - (b2 - b1) * g w' 2)| ≤ 4 * δ := by
    rw [← hg, hcoord]
    have e : (a2 - a1) * g w 2 - (b2 - b1) * g w' 2 + g E 2 -
        ((a2 - a1) * g w 2 - (b2 - b1) * g w' 2) = g E 2 := by ring
    rw [e]
    exact hE2.le
  -- the angle controls the cross term
  have hcw'1 : |g w' 1| ≤ 1 := (abs_frame_coord_le g w' 1).trans hw'.le
  have hcw'2 : |g w' 2| ≤ 1 := (abs_frame_coord_le g w' 2).trans hw'.le
  have hR : |g w 2 * g w' 1 - g w 1 * g w' 2| ≤ 2 * angle w w' := by
    have key : ∀ d : Space, ∀ σ : ℝ, w = σ • w' + d → σ * σ = 1 →
        |g w 2 * g w' 1 - g w 1 * g w' 2| ≤ 2 * ‖d‖ := by
      intro d σ hd _
      have e2 : g w 2 = σ * g w' 2 + g d 2 := by
        rw [hd]; simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have e1 : g w 1 = σ * g w' 1 + g d 1 := by
        rw [hd]; simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have e : g w 2 * g w' 1 - g w 1 * g w' 2 = g d 2 * g w' 1 - g d 1 * g w' 2 := by
        rw [e1, e2]; ring
      rw [e]
      have hd1 := abs_frame_coord_le g d 1
      have hd2 := abs_frame_coord_le g d 2
      calc _ ≤ |g d 2 * g w' 1| + |g d 1 * g w' 2| := abs_sub _ _
        _ = |g d 2| * |g w' 1| + |g d 1| * |g w' 2| := by rw [abs_mul, abs_mul]
        _ ≤ ‖d‖ * 1 + ‖d‖ * 1 := by
            gcongr
        _ = 2 * ‖d‖ := by ring
    rcases min_choice ‖w - w'‖ ‖w + w'‖ with hm | hm
    · have := key (w - w') 1 (by module) (by norm_num)
      show _ ≤ 2 * min ‖w - w'‖ ‖w + w'‖
      rw [hm]; exact this
    · have := key (w + w') (-1) (by module) (by norm_num)
      show _ ≤ 2 * min ‖w - w'‖ ‖w + w'‖
      rw [hm]; exact this
  -- algebra
  set t := a2 - a1 with ht_def
  set t' := b2 - b1 with ht'_def
  set D := inner ℝ v (p' - p) with hD
  set P := t * g w 2 - t' * g w' 2 with hP_def
  set Q := t * g w 1 - t' * g w' 1 with hQ_def
  set R := g w 2 * g w' 1 - g w 1 * g w' 2 with hR_def
  set A := angle w w' with hA
  have hA0 : 0 ≤ A := le_min (norm_nonneg _) (norm_nonneg _)
  have hid : g w' 1 * P = t * R + g w' 2 * Q := by
    simp only [hP_def, hQ_def, hR_def]; ring
  have h1 : |g w' 1| * |P| ≤ (L + 2 * δ) * (2 * A) + 6 * δ := by
    rw [← abs_mul, hid]
    calc _ ≤ |t * R| + |g w' 2 * Q| := abs_add_le _ _
      _ = |t| * |R| + |g w' 2| * |Q| := by rw [abs_mul, abs_mul]
      _ ≤ (L + 2 * δ) * (2 * A) + 1 * (6 * δ) := by
          gcongr
          linarith [abs_nonneg t]
      _ = _ := by ring
  have h2 : θ * |P| ≤ 8 * L * A + 12 * δ := by
    have := mul_le_mul_of_nonneg_right hcross (abs_nonneg P)
    nlinarith
  have h3 : |D| ≤ |P| + 4 * δ := by
    have := abs_sub_abs_le_abs_sub D P
    linarith
  calc θ * |D| ≤ θ * (|P| + 4 * δ) := mul_le_mul_of_nonneg_left h3 hθ.le
    _ = θ * |P| + θ * (4 * δ) := by ring
    _ ≤ (8 * L * A + 12 * δ) + 1 * (4 * δ) := by
        gcongr
    _ = 8 * L * A + 16 * δ := by ring

/-- A unit vector making angle more than `θ` with `v` and almost orthogonal to the first
frame vector has a large second coordinate. -/
lemma inplane_large {θ : ℝ} {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : ∀ p, g p 2 = inner ℝ v p)
    (hθ : 0 ≤ θ) (hang : θ < angle w v) (h0 : |g w 0| ≤ θ / 4) :
    θ / 2 ≤ |g w 1| := by
  have hn := norm_sq_coords (g w)
  rw [LinearIsometryEquiv.norm_map, hw, hg] at hn
  have hang' := lt_min_iff.mp hang
  have hm : ‖w - v‖ ^ 2 = 2 - 2 * inner ℝ v w := by
    rw [norm_sub_sq_real, hw, hv, real_inner_comm]; ring
  have hp : ‖w + v‖ ^ 2 = 2 + 2 * inner ℝ v w := by
    rw [norm_add_sq_real, hw, hv, real_inner_comm]; ring
  have hθm : θ ^ 2 < 2 - 2 * inner ℝ v w := by
    rw [← hm]; exact pow_lt_pow_left₀ hang'.1 hθ two_ne_zero
  have hθp : θ ^ 2 < 2 + 2 * inner ℝ v w := by
    rw [← hp]; exact pow_lt_pow_left₀ hang'.2 hθ two_ne_zero
  have hvw : |inner ℝ v w| ≤ 1 := by
    have := abs_real_inner_le_norm v w
    rw [hv, hw] at this
    linarith
  have hA : |inner ℝ v w| < 1 - θ ^ 2 / 2 := by
    rcases abs_cases (inner ℝ v w) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have ha2 : inner ℝ v w ^ 2 ≤ |inner ℝ v w| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (inner ℝ v w)]
  have h0sq : g w 0 ^ 2 ≤ θ ^ 2 / 16 := by
    rw [← sq_abs]
    have := abs_nonneg (g w 0)
    nlinarith
  have hα : θ ^ 2 / 4 ≤ g w 1 ^ 2 := by
    nlinarith [sq_nonneg θ]
  by_contra hcon
  have hcon := not_le.mp hcon
  have : |g w 1| ^ 2 < (θ / 2) ^ 2 := by
    exact pow_lt_pow_left₀ hcon (abs_nonneg _) two_ne_zero
  rw [sq_abs] at this
  nlinarith

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
