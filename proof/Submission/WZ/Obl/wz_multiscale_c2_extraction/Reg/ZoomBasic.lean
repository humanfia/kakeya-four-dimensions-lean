-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.ZoomBasic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.Isometry

/-!
# Zooming a tube family about a point

`zoom r c p = r • (p - c)`.  A unit tube passing near `c` is replaced by the unit piece of its
zoomed axis centred at the zoomed closest point of its axis to `c`.  The zoomed shading, cut by
the slab `|⟪p - c, v⟫| ≤ 1/(2r)`, lies in the piece, and containment of a fine tube in a coarse
tube becomes containment of the pieces after fattening the coarse radius by `8 r`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- The homothety of ratio `r` sending `c` to the origin. -/
def zoom (r : ℝ) (c p : Space) : Space := r • (p - c)

/-- The parameter of the point of the line `x + t v` closest to `c`. -/
def cpar (c x v : Space) : ℝ := ⟪c - x, v⟫

/-- The point of the line `x + t v` closest to `c`. -/
def cpt (c x v : Space) : Space := x + cpar c x v • v

/-- The base point of the zoomed unit piece centred at the zoomed closest point. -/
def pieceBase (r : ℝ) (c x v : Space) : Space := zoom r c (cpt c x v) - (1 / 2 : ℝ) • v

theorem zoom_sub (r : ℝ) (c p q : Space) : zoom r c p - zoom r c q = r • (p - q) := by
  simp only [zoom]; module

theorem norm_zoom_sub {r : ℝ} (hr : 0 ≤ r) (c p q : Space) :
    ‖zoom r c p - zoom r c q‖ = r * ‖p - q‖ := by
  rw [zoom_sub, norm_smul, Real.norm_of_nonneg hr]

theorem inner_cpt_sub {c x v : Space} (hv : ‖v‖ = 1) : ⟪cpt c x v - c, v⟫ = 0 := by
  have h1 : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have he : cpt c x v - c = (x - c) + cpar c x v • v := by simp only [cpt]; abel
  rw [he, inner_add_left, inner_smul_left, h1]
  simp only [cpar, conj_trivial, mul_one]
  rw [← inner_add_left]
  simp

/-- Pythagoras along the axis: `p - (cpt + s v)` is orthogonal to `v` when `s = ⟪p - c, v⟫`. -/
theorem inner_proj_perp {c x v p : Space} (hv : ‖v‖ = 1) :
    ⟪p - (cpt c x v + ⟪p - c, v⟫ • v), v⟫ = 0 := by
  have h1 : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have he : p - (cpt c x v + ⟪p - c, v⟫ • v) = (p - c) - (cpt c x v - c) - ⟪p - c, v⟫ • v := by
    abel
  rw [he, inner_sub_left, inner_sub_left, inner_cpt_sub hv, inner_smul_left, h1]
  simp

/-- The orthogonal projection onto the axis is the closest point of the axis. -/
theorem norm_proj_le {c x v p : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖p - (cpt c x v + ⟪p - c, v⟫ • v)‖ ≤ ‖p - (x + t • v)‖ := by
  set q := cpt c x v + ⟪p - c, v⟫ • v
  have hperp : ⟪p - q, v⟫ = 0 := inner_proj_perp hv
  have he : p - (x + t • v) = (p - q) + (cpar c x v + ⟪p - c, v⟫ - t) • v := by
    simp only [q, cpt]; module
  rw [he]
  have hsq : ‖(p - q) + (cpar c x v + ⟪p - c, v⟫ - t) • v‖ ^ 2 =
      ‖p - q‖ ^ 2 + (cpar c x v + ⟪p - c, v⟫ - t) ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hperp, norm_smul, Real.norm_eq_abs, hv,
      mul_one, mul_zero, mul_zero, add_zero, sq_abs]
  have h2 : ‖p - q‖ ^ 2 ≤ ‖(p - q) + (cpar c x v + ⟪p - c, v⟫ - t) • v‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg (cpar c x v + ⟪p - c, v⟫ - t)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h2

/-- A point of a tube whose axial coordinate relative to `c` is at most `1/(2r)` is zoomed
into the unit piece. -/
theorem zoom_mem_piece {r δ : ℝ} (hr : 0 < r) {c x v p : Space} (hv : ‖v‖ = 1)
    (hp : p ∈ Tube δ x v) (hslab : |⟪p - c, v⟫| ≤ 1 / (2 * r)) :
    zoom r c p ∈ Tube (r * δ) (pieceBase r c x v) v := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, -, rfl⟩ := hq
  rw [add_sub_cancel_left] at hpq
  set s := ⟪p - c, v⟫
  have hproj : ‖p - (cpt c x v + s • v)‖ < δ :=
    (norm_proj_le hv t).trans_lt (by rwa [dist_eq_norm] at hpq)
  have hrs : |r * s| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hr]
    calc r * |s| ≤ r * (1 / (2 * r)) := mul_le_mul_of_nonneg_left hslab hr.le
      _ = 1 / 2 := by field_simp
  obtain ⟨hrs1, hrs2⟩ := abs_le.mp hrs
  apply mem_thickening_iff.mpr
  refine ⟨pieceBase r c x v + (r * s + 1 / 2) • v, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨r * s + 1 / 2, ⟨by linarith, by linarith⟩, by simp⟩
  · rw [dist_eq_norm]
    have he : zoom r c p - (pieceBase r c x v + (r * s + 1 / 2) • v) =
        r • (p - (cpt c x v + s • v)) := by
      simp only [pieceBase, zoom]; module
    rw [he, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_of_pos_left hproj hr

/-- The unit piece lies in the unit ball when its centre is in the ball of radius `1/4`. -/
theorem piece_subset_ball {r δ' : ℝ} {c x v : Space} (hv : ‖v‖ = 1)
    (hcen : ‖zoom r c (cpt c x v)‖ ≤ 1 / 4) (hδ' : δ' ≤ 1 / 8) :
    Tube δ' (pieceBase r c x v) v ⊆ ball 0 1 := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  rw [mem_ball, dist_zero_right]
  have hq : ‖pieceBase r c x v + t • v‖ ≤ 3 / 4 := by
    have he : pieceBase r c x v + t • v = zoom r c (cpt c x v) + (t - 1 / 2) • v := by
      simp only [pieceBase]; module
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one]
    have : |t - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    linarith
  rw [dist_eq_norm] at hpq
  simp only [add_sub_cancel_left] at hpq
  calc ‖p‖ = ‖(p - (pieceBase r c x v + t • v)) + (pieceBase r c x v + t • v)‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖p - (pieceBase r c x v + t • v)‖ + ‖pieceBase r c x v + t • v‖ := norm_add_le _ _
    _ < 1 := by linarith


/-- A point of a tube is within the radius of some point of its axis segment. -/
theorem exists_param_of_mem_tube' {δ : ℝ} {x v q : Space} (h : q ∈ Tube δ x v) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖q - (x + t • v)‖ < δ :=
  WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube h

/-- Containment of a unit tube in a unit tube aligns the directions up to sign. -/
theorem direction_of_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : Tube δ x v ⊆ Tube ρ z w) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖v - σ • w‖ < 4 * ρ := by
  obtain ⟨a, ha, hxa⟩ := exists_param_of_mem_tube'
    (hT (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))))
  obtain ⟨b, hb, hxb⟩ := exists_param_of_mem_tube'
    (hT (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))))
  have hn : ‖v - (b - a) • w‖ < 2 * ρ := by
    have he : v - (b - a) • w = (x + v - (z + b • w)) - (x - (z + a • w)) := by module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hu : |b - a| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hlow : 1 - |b - a| < 2 * ρ := by
    have h1 : ‖v‖ ≤ ‖(b - a) • w‖ + ‖v - (b - a) • w‖ := by
      calc ‖v‖ = ‖(b - a) • w + (v - (b - a) • w)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [norm_smul, Real.norm_eq_abs, hw, hv] at h1
    linarith
  rcases le_or_gt 0 (b - a) with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    have he : v - (1 : ℝ) • w = (v - (b - a) • w) + (b - a - 1) • w := by module
    rw [he]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one, abs_of_nonpos (by linarith [hu, le_abs_self (b - a)])]
    rw [abs_of_nonneg hpos] at hlow
    linarith
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have he : v - (-1 : ℝ) • w = (v - (b - a) • w) + (b - a + 1) • w := by module
    rw [he]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
    rw [abs_of_neg hneg] at hlow
    have hnn : 0 ≤ b - a + 1 := by linarith [neg_abs_le (b - a), hu]
    rw [abs_of_nonneg hnn]
    linarith

/-- Containment of a fine tube passing near `c` in a coarse tube: the closest points to `c`
are within `5 ρ`, and the closest point of the coarse axis has parameter near `[0, 1]`. -/
theorem coarse_near {δ ρ R : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hR : R ≤ 1 / 4) {c x v z w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hT : Tube δ x v ⊆ Tube ρ z w) (hcen : ‖cpt c x v - c‖ ≤ R)
    (hpar : cpar c x v ∈ Icc (-R) (1 + R)) :
    ‖cpt c x v - cpt c z w‖ < 5 * ρ ∧ cpar c z w ∈ Icc (-R - 3 * ρ) (1 + R + 3 * ρ) := by
  have hw1 : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hcen
  obtain ⟨σ, hσ, hvσ⟩ := direction_of_subset hδ hv hw hT
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set t := cpar c x v
  set t' := max 0 (min t 1)
  have ht' : t' ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have htt' : |t - t'| ≤ R := by
    rw [abs_le]
    constructor
    · rcases le_total t 1 with h | h
      · simp only [t', min_eq_left h]
        rcases le_total 0 t with h0 | h0
        · rw [max_eq_right h0]; linarith
        · rw [max_eq_left h0]; linarith [hpar.1]
      · simp only [t', min_eq_right h, max_eq_right zero_le_one]; linarith
    · rcases le_total t 1 with h | h
      · simp only [t', min_eq_left h]
        rcases le_total 0 t with h0 | h0
        · rw [max_eq_right h0]; linarith
        · rw [max_eq_left h0]; linarith
      · simp only [t', min_eq_right h, max_eq_right zero_le_one]; linarith [hpar.2]
  have hxt : x + t' • v ∈ Tube δ x v := by
    apply self_subset_thickening hδ
    rw [segment_eq_image']
    exact ⟨t', ht', by simp⟩
  obtain ⟨a', ha'01, ha'⟩ := exists_param_of_mem_tube' (hT hxt)
  set m := cpt c x v
  set q' := z + (a' + (t - t') * σ) • w
  have hmq : ‖m - q'‖ < 2 * ρ := by
    have he : m - q' = (x + t' • v - (z + a' • w)) + (t - t') • (v - σ • w) := by
      simp only [m, q', cpt, t]; module
    rw [he]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, Real.norm_eq_abs]
    have : |t - t'| * ‖v - σ • w‖ ≤ R * (4 * ρ) :=
      mul_le_mul htt' hvσ.le (norm_nonneg _) hR0
    nlinarith
  set mj := cpt c z w
  have hsplit : q' - mj = ⟪q' - c, w⟫ • w := by
    have h1 : ⟪q' - c, w⟫ = a' + (t - t') * σ - ⟪c - z, w⟫ := by
      have he : q' - c = (z - c) + (a' + (t - t') * σ) • w := by simp only [q']; abel
      rw [he, inner_add_left, inner_smul_left, hw1]
      simp only [conj_trivial, mul_one]
      rw [← neg_sub c z, inner_neg_left]
      ring
    rw [h1]
    simp only [q', mj, cpt, cpar]
    module
  have hinner : |⟪m - c, w⟫| ≤ R * (4 * ρ) := by
    have he : ⟪m - c, w⟫ = σ * ⟪m - c, σ • w - v⟫ := by
      rw [inner_sub_right, inner_smul_right, inner_cpt_sub hv, sub_zero, ← mul_assoc, hσ2,
        one_mul]
    rw [he, abs_mul, hσabs, one_mul]
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul hcen ?_ (norm_nonneg _) hR0
    rw [norm_sub_rev]
    exact hvσ.le
  have hs : |⟪q' - c, w⟫| < 3 * ρ := by
    have he : ⟪q' - c, w⟫ = ⟪q' - m, w⟫ + ⟪m - c, w⟫ := by
      rw [← inner_add_left]; congr 1; abel
    rw [he]
    refine (abs_add_le _ _).trans_lt ?_
    have h1 : |⟪q' - m, w⟫| ≤ ‖q' - m‖ := by
      have := abs_real_inner_le_norm (q' - m) w
      rwa [hw, mul_one] at this
    rw [norm_sub_rev] at h1
    nlinarith
  have hmm : ‖m - mj‖ < 5 * ρ := by
    have he : m - mj = (m - q') + (q' - mj) := by abel
    rw [he, hsplit]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
    linarith
  refine ⟨hmm, ?_⟩
  have hc : cpar c z w = a' + (t - t') * σ - ⟪q' - c, w⟫ := by
    have h1 : ⟪q' - c, w⟫ = a' + (t - t') * σ - ⟪c - z, w⟫ := by
      have he : q' - c = (z - c) + (a' + (t - t') * σ) • w := by simp only [q']; abel
      rw [he, inner_add_left, inner_smul_left, hw1]
      simp only [conj_trivial, mul_one]
      rw [← neg_sub c z, inner_neg_left]
      ring
    rw [h1]; simp only [cpar]; ring
  have hts : |(t - t') * σ| ≤ R := by rw [abs_mul, hσabs, mul_one]; exact htt'
  rw [hc]
  obtain ⟨h1, h2⟩ := abs_le.mp hts
  obtain ⟨h3, h4⟩ := abs_lt.mp hs
  constructor <;> linarith [ha'01.1, ha'01.2]

/-- Containment of a fine tube in a coarse tube survives zooming to unit pieces, with the
coarse radius fattened to `8 r ρ`. -/
theorem piece_subset_piece {r δ ρ R : ℝ} (hr : 1 ≤ r) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hR : R ≤ 1 / 4) {c x v z w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hT : Tube δ x v ⊆ Tube ρ z w) (hcen : ‖cpt c x v - c‖ ≤ R)
    (hpar : cpar c x v ∈ Icc (-R) (1 + R)) :
    Tube (r * δ) (pieceBase r c x v) v ⊆ Tube (8 * r * ρ) (pieceBase r c z w) w := by
  have hw1 : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hcen
  obtain ⟨σ, hσ, hvσ⟩ := direction_of_subset hδ hv hw hT
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set t := cpar c x v
  set t' := max 0 (min t 1)
  have ht' : t' ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have htt' : |t - t'| ≤ R := by
    rw [abs_le]
    constructor
    · rcases le_total t 1 with h | h
      · simp only [t', min_eq_left h]
        rcases le_total 0 t with h0 | h0
        · rw [max_eq_right h0]; linarith
        · rw [max_eq_left h0]; linarith [hpar.1]
      · simp only [t', min_eq_right h, max_eq_right zero_le_one]; linarith
    · rcases le_total t 1 with h | h
      · simp only [t', min_eq_left h]
        rcases le_total 0 t with h0 | h0
        · rw [max_eq_right h0]; linarith
        · rw [max_eq_left h0]; linarith
      · simp only [t', min_eq_right h, max_eq_right zero_le_one]; linarith [hpar.2]
  have hxt : x + t' • v ∈ Tube δ x v := by
    apply self_subset_thickening hδ
    rw [segment_eq_image']
    exact ⟨t', ht', by simp⟩
  obtain ⟨a', -, ha'⟩ := exists_param_of_mem_tube' (hT hxt)
  set m := cpt c x v
  set q' := z + (a' + (t - t') * σ) • w
  have hmq : ‖m - q'‖ < 2 * ρ := by
    have he : m - q' = (x + t' • v - (z + a' • w)) + (t - t') • (v - σ • w) := by
      simp only [m, q', cpt, t]; module
    rw [he]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, Real.norm_eq_abs]
    have : |t - t'| * ‖v - σ • w‖ ≤ R * (4 * ρ) :=
      mul_le_mul htt' hvσ.le (norm_nonneg _) hR0
    nlinarith
  set mj := cpt c z w
  have hsplit : q' - mj = ⟪q' - c, w⟫ • w := by
    have h1 : ⟪q' - c, w⟫ = a' + (t - t') * σ - ⟪c - z, w⟫ := by
      have he : q' - c = (z - c) + (a' + (t - t') * σ) • w := by simp only [q']; abel
      rw [he, inner_add_left, inner_smul_left, hw1]
      simp only [conj_trivial, mul_one]
      rw [← neg_sub c z, inner_neg_left]
      ring
    rw [h1]
    simp only [q', mj, cpt, cpar]
    module
  have hinner : |⟪m - c, w⟫| ≤ R * (4 * ρ) := by
    have he : ⟪m - c, w⟫ = σ * ⟪m - c, σ • w - v⟫ := by
      rw [inner_sub_right, inner_smul_right, inner_cpt_sub hv, sub_zero, ← mul_assoc, hσ2,
        one_mul]
    rw [he, abs_mul, hσabs, one_mul]
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul hcen ?_ (norm_nonneg _) hR0
    rw [norm_sub_rev]
    exact hvσ.le
  have hs : |⟪q' - c, w⟫| < 3 * ρ := by
    have he : ⟪q' - c, w⟫ = ⟪q' - m, w⟫ + ⟪m - c, w⟫ := by
      rw [← inner_add_left]; congr 1; abel
    rw [he]
    refine (abs_add_le _ _).trans_lt ?_
    have h1 : |⟪q' - m, w⟫| ≤ ‖q' - m‖ := by
      have := abs_real_inner_le_norm (q' - m) w
      rwa [hw, mul_one] at this
    rw [norm_sub_rev] at h1
    nlinarith
  have hmm : ‖m - mj‖ < 5 * ρ := by
    have he : m - mj = (m - q') + (q' - mj) := by abel
    rw [he, hsplit]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
    linarith
  intro p hp
  obtain ⟨θ, hθ, hpθ⟩ := exists_param_of_mem_tube' hp
  apply mem_thickening_iff.mpr
  set θ' := (θ - 1 / 2) * σ + 1 / 2
  have hθ' : θ' ∈ Icc (0 : ℝ) 1 := by
    have hb : |(θ - 1 / 2) * σ| ≤ 1 / 2 := by
      rw [abs_mul, hσabs, mul_one, abs_le]; constructor <;> linarith [hθ.1, hθ.2]
    obtain ⟨h1, h2⟩ := abs_le.mp hb
    exact ⟨by simp only [θ']; linarith, by simp only [θ']; linarith⟩
  refine ⟨pieceBase r c z w + θ' • w, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨θ', hθ', by simp⟩
  · rw [dist_eq_norm]
    have he : p - (pieceBase r c z w + θ' • w) =
        (p - (pieceBase r c x v + θ • v)) + (zoom r c m - zoom r c mj) +
          (θ - 1 / 2) • (v - σ • w) := by
      simp only [pieceBase, θ', m, mj]; module
    rw [he]
    have h1 : ‖zoom r c m - zoom r c mj‖ < r * (5 * ρ) := by
      rw [norm_zoom_sub (by linarith)]
      exact mul_lt_mul_of_pos_left hmm (by linarith)
    have h2 : ‖(θ - 1 / 2) • (v - σ • w)‖ ≤ 1 / 2 * (4 * ρ) := by
      rw [norm_smul, Real.norm_eq_abs]
      have : |θ - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
      exact mul_le_mul this hvσ.le (norm_nonneg _) (by norm_num)
    have h3 : r * δ ≤ r * ρ := mul_le_mul_of_nonneg_left hδρ (by linarith)
    have h4 : ρ ≤ r * ρ := le_mul_of_one_le_left hρ.le hr
    calc ‖(p - (pieceBase r c x v + θ • v)) + (zoom r c m - zoom r c mj) +
          (θ - 1 / 2) • (v - σ • w)‖
        ≤ ‖p - (pieceBase r c x v + θ • v)‖ + ‖zoom r c m - zoom r c mj‖ +
          ‖(θ - 1 / 2) • (v - σ • w)‖ := norm_add₃_le
      _ < 8 * r * ρ := by nlinarith

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
