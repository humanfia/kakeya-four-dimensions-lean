-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.Net.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Basic
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.wz_tube_packing_bound

/-!
# Exact unit tubes around prisms, and an essentially distinct net

`cTube b c u` is the unit tube of radius `4 b` centred at the centre `c` of a prism, along its
(sign-normalised) long axis `axisDir u`. `net_cover` selects, among the prisms of one cell, a
subfamily of these tubes that are pairwise essentially distinct (half-volume condition), with
disjoint nonempty fibres of prisms contained in them, retaining a fixed fraction `netConst` of
all the prisms.

Construction: discretise the sign-normalised axis direction `ẽ` (spacing `50 b`) and the foot
`p = c - ⟪c, ẽ⟫ ẽ` of the axis line (spacing `b / 4`) in each coordinate, together with the chart
of `ẽ`; colour the grid cells by their indices modulo `K = 8001`; keep the most popular colour.
Prisms of one cell lie in the tube of any member of the cell; representatives of distinct cells
of one colour have either far directions (`intersection_le_half` of
`wz_direction_density_transfer`) or far axis lines (disjoint tubes).
-/

namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Sign-normalised long axis of a frame: its chart coordinate is nonnegative. -/
def axisDir (u : Fin 3 → Space) : Space :=
  if 0 ≤ (u 2) (WangZahlLot.Obl.wz_tube_packing_bound.chart (u 2)) then u 2 else -(u 2)

/-- The output tube attached to a prism: radius `4 b`, unit length, centred at `c`. -/
def cTube (b : ℝ) (c : Space) (u : Fin 3 → Space) : Set Space :=
  tube (4 * b) (c - (1 / 2 : ℝ) • axisDir u) (axisDir u)

theorem norm_axisDir {u : Fin 3 → Space} (hu : Orthonormal ℝ u) : ‖axisDir u‖ = 1 := by
  unfold axisDir
  split_ifs <;> simp [hu.1 2]

private theorem net_inner_axisDir_smul (u : Fin 3 → Space) (x : Space) :
    inner ℝ (axisDir u) x • axisDir u = inner ℝ (u 2) x • u 2 := by
  unfold axisDir
  split_ifs <;> simp [inner_neg_left]

private theorem net_abs_inner_axisDir (u : Fin 3 → Space) (x : Space) :
    |inner ℝ (axisDir u) x| = |inner ℝ (u 2) x| := by
  unfold axisDir
  split_ifs <;> simp [inner_neg_left]

private theorem net_half_le_axisDir_chart {u : Fin 3 → Space} (hu : Orthonormal ℝ u) :
    1 / 2 ≤ axisDir u (WangZahlLot.Obl.wz_tube_packing_bound.chart (u 2)) := by
  have h := WangZahlLot.Obl.wz_tube_packing_bound.half_le_abs_chart (hu.1 2)
  unfold axisDir
  split_ifs with h0
  · rwa [abs_of_nonneg h0] at h
  · rw [not_le] at h0
    rw [abs_of_neg h0] at h
    simpa using h

/-- Membership in `cTube` via a point of the axis. -/
private theorem net_mem_cTube {b : ℝ} {c : Space} {u : Fin 3 → Space} {z : Space} {t : ℝ}
    (ht : |t| ≤ 1 / 2) (hz : dist z (c + t • axisDir u) < 4 * b) : z ∈ cTube b c u := by
  unfold cTube tube
  rw [mem_thickening_iff]
  refine ⟨c + t • axisDir u, ?_, hz⟩
  rw [segment_eq_image']
  refine ⟨t + 1 / 2, ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩, ?_⟩
  simp only
  module

/-- A point of `cTube` is close to a point of the axis. -/
private theorem net_of_mem_cTube {b : ℝ} {c : Space} {u : Fin 3 → Space} {z : Space}
    (hz : z ∈ cTube b c u) : ∃ t : ℝ, |t| ≤ 1 / 2 ∧ dist z (c + t • axisDir u) < 4 * b := by
  unfold cTube tube at hz
  rw [mem_thickening_iff] at hz
  obtain ⟨y, hy, hzy⟩ := hz
  rw [segment_eq_image'] at hy
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hy
  refine ⟨θ - 1 / 2, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · convert hzy using 2
    module

theorem cTube_subset_ball {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1 / 1000) {c : Space}
    {u : Fin 3 → Space} (hu : Orthonormal ℝ u) (hc : ‖c‖ < 1 / 100) :
    cTube b c u ⊆ ball (0 : Space) 1 := by
  intro z hz
  obtain ⟨t, ht, hzt⟩ := net_of_mem_cTube hz
  rw [mem_ball_zero_iff]
  have h1 : ‖c + t • axisDir u‖ ≤ ‖c‖ + |t| := by
    calc ‖c + t • axisDir u‖ ≤ ‖c‖ + ‖t • axisDir u‖ := norm_add_le _ _
      _ = ‖c‖ + |t| := by rw [norm_smul, norm_axisDir hu, Real.norm_eq_abs, mul_one]
  have h2 := norm_sub_norm_le z (c + t • axisDir u)
  rw [dist_eq_norm] at hzt
  linarith

/-- Splitting off the long-axis component of a vector, in a frame. -/
private theorem net_norm_sub_axis_le {a b : ℝ} {u : Fin 3 → Space} (hu : Orthonormal ℝ u)
    {y : Space} (h0 : |inner ℝ (u 0) y| ≤ a) (h1 : |inner ℝ (u 1) y| ≤ b) :
    ‖y - inner ℝ (axisDir u) y • axisDir u‖ ≤ a + b := by
  have e := eq_sum_frame hu y
  have hw : y - inner ℝ (axisDir u) y • axisDir u =
      inner ℝ (u 0) y • u 0 + inner ℝ (u 1) y • u 1 := by
    rw [net_inner_axisDir_smul]
    linear_combination (norm := module) e
  rw [hw]
  calc ‖inner ℝ (u 0) y • u 0 + inner ℝ (u 1) y • u 1‖
      ≤ ‖inner ℝ (u 0) y • u 0‖ + ‖inner ℝ (u 1) y • u 1‖ := norm_add_le _ _
    _ = |inner ℝ (u 0) y| + |inner ℝ (u 1) y| := by
        rw [norm_smul, norm_smul, hu.1 0, hu.1 1, Real.norm_eq_abs, Real.norm_eq_abs,
          mul_one, mul_one]
    _ ≤ a + b := add_le_add h0 h1

theorem ball_subset_cTube {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {c : Space}
    {u : Fin 3 → Space} (hu : Orthonormal ℝ u) {x : Space} (hx : x ∈ prism a b c u) :
    ball x (2 * b) ⊆ cTube b c u := by
  intro q hq
  obtain ⟨h0, h1, h2⟩ := hx
  have hr : |inner ℝ (axisDir u) (x - c)| ≤ 1 / 1000 := by
    rw [net_abs_inner_axisDir]; exact h2
  apply net_mem_cTube (t := inner ℝ (axisDir u) (x - c)) (by linarith)
  have hw := net_norm_sub_axis_le hu h0 h1
  have e : x - (c + inner ℝ (axisDir u) (x - c) • axisDir u) =
      (x - c) - inner ℝ (axisDir u) (x - c) • axisDir u := by abel
  rw [mem_ball, dist_eq_norm] at hq
  rw [dist_eq_norm]
  calc ‖q - (c + inner ℝ (axisDir u) (x - c) • axisDir u)‖
      ≤ ‖q - x‖ + ‖x - (c + inner ℝ (axisDir u) (x - c) • axisDir u)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < 2 * b + (a + b) := by rw [e]; exact add_lt_add_of_lt_of_le hq hw
    _ ≤ 4 * b := by linarith

theorem prism_subset_cTube {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) {c : Space}
    {u : Fin 3 → Space} (hu : Orthonormal ℝ u) : prism a b c u ⊆ cTube b c u := by
  intro x hx
  exact ball_subset_cTube ha hab hu hx (mem_ball_self (by positivity))

/-- The fraction of prisms retained by the net. -/
def netConst : ℝ := 1 / (3 * 8001 ^ 6)

theorem netConst_pos : 0 < netConst := by
  unfold netConst; positivity

/-! ### Helper lemmas for `net_cover` -/

/-- A vector with all coordinates at most `g` in absolute value has norm at most `2 g`. -/
private theorem net_norm_le_two_mul {x : Space} {g : ℝ} (h : ∀ m, |x m| ≤ g) : ‖x‖ ≤ 2 * g := by
  have hg : 0 ≤ g := (abs_nonneg _).trans (h 0)
  have hsq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have h0 := sq_le_sq' (abs_le.mp (h 0)).1 (abs_le.mp (h 0)).2
  have h1 := sq_le_sq' (abs_le.mp (h 1)).1 (abs_le.mp (h 1)).2
  have h2 := sq_le_sq' (abs_le.mp (h 2)).1 (abs_le.mp (h 2)).2
  have : ‖x‖ ^ 2 ≤ (2 * g) ^ 2 := by nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) this

/-- The foot of the axis line `c + ℝ ẽ` (the point of it orthogonal to `ẽ`). -/
private def net_foot (c : Space) (u : Fin 3 → Space) : Space :=
  c - inner ℝ (axisDir u) c • axisDir u

private theorem net_abs_inner_axisDir_lt {c : Space} {u : Fin 3 → Space}
    (hu : Orthonormal ℝ u) (hc : ‖c‖ < 1 / 100) : |inner ℝ (axisDir u) c| < 1 / 100 := by
  calc |inner ℝ (axisDir u) c| ≤ ‖axisDir u‖ * ‖c‖ := abs_real_inner_le_norm _ _
    _ = ‖c‖ := by rw [norm_axisDir hu, one_mul]
    _ < 1 / 100 := hc

/-- A prism lies in the tube of a prism with nearby axis direction and foot. -/
private theorem net_prism_subset {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b)
    {c c' : Space} {u u' : Fin 3 → Space} (hu : Orthonormal ℝ u) (hu' : Orthonormal ℝ u')
    (hc : ‖c‖ < 1 / 100) (hc' : ‖c'‖ < 1 / 100)
    (hE : ‖axisDir u - axisDir u'‖ ≤ 100 * b)
    (hP : ‖net_foot c u - net_foot c' u'‖ ≤ b / 2) :
    prism a b c u ⊆ cTube b c' u' := by
  intro q hq
  obtain ⟨h0, h1, h2⟩ := hq
  have hs := net_abs_inner_axisDir_lt hu hc
  have hs' := net_abs_inner_axisDir_lt hu' hc'
  have hr : |inner ℝ (axisDir u) (q - c)| ≤ 1 / 1000 := by
    rw [net_abs_inner_axisDir]; exact h2
  have hw := net_norm_sub_axis_le hu h0 h1
  have key : q - (c' + (inner ℝ (axisDir u) c + inner ℝ (axisDir u) (q - c) -
        inner ℝ (axisDir u') c') • axisDir u') =
      (net_foot c u - net_foot c' u') +
        (inner ℝ (axisDir u) c + inner ℝ (axisDir u) (q - c)) • (axisDir u - axisDir u') +
        ((q - c) - inner ℝ (axisDir u) (q - c) • axisDir u) := by
    unfold net_foot
    module
  set s := inner ℝ (axisDir u) c with hsdef
  set s' := inner ℝ (axisDir u') c' with hs'def
  set r := inner ℝ (axisDir u) (q - c) with hrdef
  have habs : |s + r - s'| ≤ 1 / 2 := by
    rw [abs_le] at hr ⊢
    rw [abs_lt] at hs hs'
    constructor <;> linarith [hr.1, hr.2, hs.1, hs.2, hs'.1, hs'.2]
  have hsr : |s + r| ≤ 11 / 1000 := by
    rw [abs_le] at hr ⊢
    rw [abs_lt] at hs
    constructor <;> linarith [hr.1, hr.2, hs.1, hs.2]
  apply net_mem_cTube habs
  rw [dist_eq_norm, key]
  calc ‖(net_foot c u - net_foot c' u') + (s + r) • (axisDir u - axisDir u') +
        ((q - c) - r • axisDir u)‖
      ≤ ‖net_foot c u - net_foot c' u'‖ + ‖(s + r) • (axisDir u - axisDir u')‖ +
        ‖(q - c) - r • axisDir u‖ := norm_add₃_le
    _ ≤ b / 2 + (11 / 1000) * (100 * b) + (a + b) := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul hsr hE (norm_nonneg _) (by norm_num)
    _ < 4 * b := by linarith

/-- Two tubes with nearby directions and far feet are disjoint. -/
private theorem net_cTube_inter_eq_empty {b : ℝ} (hb : 0 < b) {c c' : Space}
    {u u' : Fin 3 → Space} (hu : Orthonormal ℝ u) (hu' : Orthonormal ℝ u')
    (hc : ‖c‖ < 1 / 100)
    (hE : ‖axisDir u - axisDir u'‖ ≤ 100 * b)
    (hP : 2000 * b ≤ ‖net_foot c u - net_foot c' u'‖) :
    cTube b c u ∩ cTube b c' u' = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hz, hz'⟩
  obtain ⟨t, ht, hzt⟩ := net_of_mem_cTube hz
  obtain ⟨t', ht', hzt'⟩ := net_of_mem_cTube hz'
  have hne : ‖axisDir u‖ = 1 := norm_axisDir hu
  have hne' : ‖axisDir u'‖ = 1 := norm_axisDir hu'
  have hs := net_abs_inner_axisDir_lt hu hc
  have hpe : inner ℝ (net_foot c u) (axisDir u) = 0 := by
    unfold net_foot
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hne,
      real_inner_comm]
    ring
  have hpe' : inner ℝ (net_foot c' u') (axisDir u') = 0 := by
    unfold net_foot
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hne',
      real_inner_comm]
    ring
  have hpn : ‖net_foot c u‖ ≤ 2 / 100 := by
    unfold net_foot
    calc ‖c - inner ℝ (axisDir u) c • axisDir u‖
        ≤ ‖c‖ + ‖inner ℝ (axisDir u) c • axisDir u‖ := norm_sub_le _ _
      _ = ‖c‖ + |inner ℝ (axisDir u) c| := by rw [norm_smul, hne, mul_one, Real.norm_eq_abs]
      _ ≤ 2 / 100 := by linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]
  have key : (c + t • axisDir u) - (c' + t' • axisDir u') =
      ((net_foot c u - net_foot c' u') +
        (inner ℝ (axisDir u) c + t) • (axisDir u - axisDir u')) +
        ((inner ℝ (axisDir u) c + t) - (inner ℝ (axisDir u') c' + t')) • axisDir u' := by
    unfold net_foot
    module
  have hα : |inner ℝ (axisDir u) c + t| ≤ 51 / 100 := by
    rw [abs_le] at ht ⊢
    rw [abs_lt] at hs
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  set e := axisDir u with he
  set e' := axisDir u' with he'
  set p := net_foot c u with hp
  set p' := net_foot c' u' with hp'
  set α := inner ℝ e c + t with hαdef
  set β := inner ℝ e' c' + t' with hβdef
  set Y := (p - p') + α • (e - e') with hY
  have hdist : ‖Y + (α - β) • e'‖ < 8 * b := by
    rw [← key]
    calc ‖(c + t • e) - (c' + t' • e')‖ = dist (c + t • e) (c' + t' • e') :=
          (dist_eq_norm _ _).symm
      _ ≤ dist (c + t • e) z + dist z (c' + t' • e') := dist_triangle _ _ _
      _ < 4 * b + 4 * b := by rw [dist_comm]; exact add_lt_add hzt hzt'
      _ = 8 * b := by ring
  have hsq : ‖Y + (α - β) • e'‖ ^ 2 = ‖Y‖ ^ 2 + 2 * (α - β) * inner ℝ Y e' + (α - β) ^ 2 := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_right, hne', Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  have hYe : inner ℝ Y e' = inner ℝ p (e' - e) + α * inner ℝ (e - e') e' := by
    rw [hY, inner_add_left, inner_sub_left, real_inner_smul_left, hpe', inner_sub_right, hpe]
  have hYe_abs : |inner ℝ Y e'| ≤ 53 * b := by
    rw [hYe]
    have h1 : |inner ℝ p (e' - e)| ≤ 2 / 100 * (100 * b) := by
      calc |inner ℝ p (e' - e)| ≤ ‖p‖ * ‖e' - e‖ := abs_real_inner_le_norm _ _
        _ ≤ 2 / 100 * (100 * b) := by
            rw [norm_sub_rev]; exact mul_le_mul hpn hE (norm_nonneg _) (by norm_num)
    have h2 : |α * inner ℝ (e - e') e'| ≤ 51 / 100 * (100 * b) := by
      rw [abs_mul]
      have : |inner ℝ (e - e') e'| ≤ 100 * b := by
        calc |inner ℝ (e - e') e'| ≤ ‖e - e'‖ * ‖e'‖ := abs_real_inner_le_norm _ _
          _ = ‖e - e'‖ := by rw [hne', mul_one]
          _ ≤ 100 * b := hE
      exact mul_le_mul hα this (abs_nonneg _) (by norm_num)
    calc |inner ℝ p (e' - e) + α * inner ℝ (e - e') e'|
        ≤ |inner ℝ p (e' - e)| + |α * inner ℝ (e - e') e'| := abs_add_le _ _
      _ ≤ 2 / 100 * (100 * b) + 51 / 100 * (100 * b) := add_le_add h1 h2
      _ = 53 * b := by ring
  have hYn : 1949 * b ≤ ‖Y‖ := by
    have h1 : ‖α • (e - e')‖ ≤ 51 / 100 * (100 * b) := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul hα hE (norm_nonneg _) (by norm_num)
    have h3 : ‖p - p'‖ ≤ ‖Y‖ + ‖α • (e - e')‖ := by
      calc ‖p - p'‖ = ‖Y - α • (e - e')‖ := by rw [hY]; congr 1; abel
        _ ≤ ‖Y‖ + ‖α • (e - e')‖ := norm_sub_le _ _
    linarith
  have hY2 : (1949 * b) ^ 2 ≤ ‖Y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hYn 2
  have hYe2 : inner ℝ Y e' ^ 2 ≤ (53 * b) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hYe_abs 2
  have hd2 : ‖Y + (α - β) • e'‖ ^ 2 < (8 * b) ^ 2 :=
    pow_lt_pow_left₀ hdist (norm_nonneg _) two_ne_zero
  rw [hsq] at hd2
  nlinarith [sq_nonneg ((α - β) + inner ℝ Y e'), mul_pos hb hb]

/-- Distinct integers with equal residues modulo `K` differ by at least `K`. -/
private theorem net_le_abs_sub_of_emod_eq {x y K : ℤ} (hne : x ≠ y)
    (h : x % K = y % K) : K ≤ |x - y| := by
  have hd : K ∣ x - y := Int.ModEq.dvd (h.symm : Int.ModEq K y x)
  exact Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hne)) ((dvd_abs _ _).mpr hd)

/-- Equal grid indices force nearby values. -/
private theorem net_abs_sub_lt_of_floor_eq {g x y : ℝ} (hg : 0 < g)
    (h : ⌊x / g⌋ = ⌊y / g⌋) : |x - y| < g := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hg, div_lt_one hg] at h1
  exact h1

/-- Grid indices at least `K` apart force values more than `(K - 1) g` apart. -/
private theorem net_lt_abs_sub_of_floor {g x y : ℝ} {K : ℤ} (hg : 0 < g)
    (h : K ≤ |⌊x / g⌋ - ⌊y / g⌋|) : ((K : ℝ) - 1) * g < |x - y| := by
  have hx1 := Int.floor_le (x / g)
  have hx2 := Int.lt_floor_add_one (x / g)
  have hy1 := Int.floor_le (y / g)
  have hy2 := Int.lt_floor_add_one (y / g)
  have h' : (K : ℝ) - 1 < |x / g - y / g| := by
    rcases le_abs'.mp h with h1 | h1
    · have h2 : ((⌊x / g⌋ : ℤ) : ℝ) - ⌊y / g⌋ ≤ -K := by exact_mod_cast h1
      rw [lt_abs]; right; linarith
    · have h2 : (K : ℝ) ≤ ((⌊x / g⌋ : ℤ) : ℝ) - ⌊y / g⌋ := by exact_mod_cast h1
      rw [lt_abs]; left; linarith
  rw [← sub_div, abs_div, abs_of_pos hg, lt_div_iff₀ hg] at h'
  exact h'

/-- The grid cell of a prism: chart of the axis, grid indices of the axis direction (spacing
`50 b`) and of the foot of the axis line (spacing `b / 4`). -/
private def net_cell (b : ℝ) (c : Space) (u : Fin 3 → Space) :
    Fin 3 × (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (WangZahlLot.Obl.wz_tube_packing_bound.chart (u 2), fun m => ⌊axisDir u m / (50 * b)⌋,
    fun m => ⌊net_foot c u m / (b / 4)⌋)

/-- The colour of a cell: its indices modulo `8001`. -/
private def net_red (x : Fin 3 × (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    Fin 3 × (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (x.1, fun m => x.2.1 m % 8001, fun m => x.2.2 m % 8001)

/-- A finite set of colours containing all colours. (Kept abstract in uses: unfolding the
concrete product of intervals would be expensive.) -/
private theorem net_exists_T : ∃ T : Finset (Fin 3 × (Fin 3 → ℤ) × (Fin 3 → ℤ)),
    T.card = 3 * 8001 ^ 6 ∧ ∀ x, net_red x ∈ T := by
  refine ⟨Finset.univ ×ˢ (Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) 8001) ×ˢ
    (Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) 8001), ?_, ?_⟩
  · simp [Finset.card_product, Fintype.card_piFinset, Int.card_Ico]
  · intro x
    simp only [net_red, Finset.mem_product, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, Finset.mem_Ico]
    exact ⟨fun m => ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩,
      fun m => ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩⟩

/-- Prisms of one cell lie in the tube of any member of the cell. -/
private theorem net_prism_subset_of_cell_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b)
    {c c' : Space} {u u' : Fin 3 → Space} (hu : Orthonormal ℝ u) (hu' : Orthonormal ℝ u')
    (hc : ‖c‖ < 1 / 100) (hc' : ‖c'‖ < 1 / 100) (h : net_cell b c u = net_cell b c' u') :
    prism a b c u ⊆ cTube b c' u' := by
  have hE : ∀ m, ⌊axisDir u m / (50 * b)⌋ = ⌊axisDir u' m / (50 * b)⌋ := fun m =>
    congrFun (congrArg (fun x => x.2.1) h) m
  have hP : ∀ m, ⌊net_foot c u m / (b / 4)⌋ = ⌊net_foot c' u' m / (b / 4)⌋ := fun m =>
    congrFun (congrArg (fun x => x.2.2) h) m
  apply net_prism_subset ha hab hb hu hu' hc hc'
  · have := net_norm_le_two_mul (x := axisDir u - axisDir u') (g := 50 * b) (fun m => by
      rw [PiLp.sub_apply]; exact (net_abs_sub_lt_of_floor_eq (by positivity) (hE m)).le)
    linarith
  · have := net_norm_le_two_mul (x := net_foot c u - net_foot c' u') (g := b / 4) (fun m => by
      rw [PiLp.sub_apply]; exact (net_abs_sub_lt_of_floor_eq (by positivity) (hP m)).le)
    linarith

/-- Tubes of two prisms of distinct cells of one colour are essentially distinct. -/
private theorem net_half_of_red_eq {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1 / 1000000) {c c' : Space}
    {u u' : Fin 3 → Space} (hu : Orthonormal ℝ u) (hu' : Orthonormal ℝ u')
    (hc : ‖c‖ < 1 / 100)
    (hne : net_cell b c u ≠ net_cell b c' u')
    (h : net_red (net_cell b c u) = net_red (net_cell b c' u')) :
    volume (cTube b c u ∩ cTube b c' u') ≤ (1 / 2 : ℝ≥0∞) * volume (cTube b c u) := by
  have hch : WangZahlLot.Obl.wz_tube_packing_bound.chart (u 2) =
      WangZahlLot.Obl.wz_tube_packing_bound.chart (u' 2) := congrArg (fun x => x.1) h
  have hEr : ∀ m, ⌊axisDir u m / (50 * b)⌋ % 8001 = ⌊axisDir u' m / (50 * b)⌋ % 8001 :=
    fun m => congrFun (congrArg (fun x => x.2.1) h) m
  have hPr : ∀ m, ⌊net_foot c u m / (b / 4)⌋ % 8001 = ⌊net_foot c' u' m / (b / 4)⌋ % 8001 :=
    fun m => congrFun (congrArg (fun x => x.2.2) h) m
  by_cases hE : ∀ m, ⌊axisDir u m / (50 * b)⌋ = ⌊axisDir u' m / (50 * b)⌋
  · by_cases hP : ∀ m, ⌊net_foot c u m / (b / 4)⌋ = ⌊net_foot c' u' m / (b / 4)⌋
    · exact absurd (Prod.ext hch (Prod.ext (funext hE) (funext hP))) hne
    · -- far feet: the tubes are disjoint
      rw [not_forall] at hP
      obtain ⟨m, hm⟩ := hP
      have hK := net_le_abs_sub_of_emod_eq hm (hPr m)
      have hfar := net_lt_abs_sub_of_floor (by positivity : (0 : ℝ) < b / 4) hK
      have hEn : ‖axisDir u - axisDir u'‖ ≤ 100 * b := by
        have := net_norm_le_two_mul (x := axisDir u - axisDir u') (g := 50 * b) (fun m => by
          rw [PiLp.sub_apply]; exact (net_abs_sub_lt_of_floor_eq (by positivity) (hE m)).le)
        linarith
      have hPn : 2000 * b ≤ ‖net_foot c u - net_foot c' u'‖ := by
        have h1 := WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm
          (net_foot c u - net_foot c' u') m
        rw [PiLp.sub_apply] at h1
        push_cast at hfar
        linarith
      rw [net_cTube_inter_eq_empty hb hu hu' hc hEn hPn, measure_empty]
      exact zero_le
  · -- far directions
    rw [not_forall] at hE
    obtain ⟨m, hm⟩ := hE
    have hK := net_le_abs_sub_of_emod_eq hm (hEr m)
    have hfar := net_lt_abs_sub_of_floor (by positivity : (0 : ℝ) < 50 * b) hK
    have hsub : 100000 * (4 * b) ≤ ‖axisDir u - axisDir u'‖ := by
      have h1 := WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm
        (axisDir u - axisDir u') m
      rw [PiLp.sub_apply] at h1
      push_cast at hfar
      linarith
    have hadd : 100000 * (4 * b) ≤ ‖axisDir u + axisDir u'‖ := by
      have h1 := WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm
        (axisDir u + axisDir u') (WangZahlLot.Obl.wz_tube_packing_bound.chart (u 2))
      rw [PiLp.add_apply] at h1
      have h2 := net_half_le_axisDir_chart hu
      have h3 := net_half_le_axisDir_chart hu'
      rw [← hch] at h3
      rw [abs_of_nonneg (by linarith)] at h1
      linarith
    have := WangZahlLot.Obl.wz_direction_density_transfer.intersection_le_half
      (δ := 4 * b) (x := c - (1 / 2 : ℝ) • axisDir u) (y := c' - (1 / 2 : ℝ) • axisDir u')
      (by positivity) (norm_axisDir hu) (norm_axisDir hu') hsub hadd
    exact this

/-- An essentially distinct net of exact unit tubes covering a fixed fraction of the prisms. -/
theorem net_cover {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : 0 < b) (hb1 : b ≤ 1 / 1000000) (c : Fin n → Space)
    (u : Fin n → Fin 3 → Space) (hu : ∀ i ∈ I, Orthonormal ℝ (u i))
    (hc : ∀ i ∈ I, ‖c i‖ < 1 / 100) :
    ∃ (M : ℕ) (k : Fin M → Fin n) (F : Fin M → Finset (Fin n)),
      0 < M ∧ (∀ α, k α ∈ I) ∧ (∀ α, F α ⊆ I) ∧ (∀ α, (F α).Nonempty) ∧
      (∀ α β, α ≠ β → Disjoint (F α) (F β)) ∧
      netConst * (I.card : ℝ) ≤ ∑ α, ((F α).card : ℝ) ∧
      (∀ α, ∀ i ∈ F α, prism a b (c i) (u i) ⊆ cTube b (c (k α)) (u (k α))) ∧
      (∀ α β, α ≠ β → volume (cTube b (c (k α)) (u (k α)) ∩ cTube b (c (k β)) (u (k β))) ≤
        (1 / 2 : ℝ≥0∞) * volume (cTube b (c (k α)) (u (k α)))) := by
  classical
  -- cells and colours
  let cell : Fin n → Fin 3 × (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i => net_cell b (c i) (u i)
  let col : Fin n → Fin 3 × (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i => net_red (cell i)
  obtain ⟨T, hTcard, hTmem⟩ := net_exists_T
  have hmaps : ∀ i ∈ I, col i ∈ T := fun i _ => hTmem (cell i)
  have hT : (T.card : ℝ) = 3 * 8001 ^ 6 := by rw [hTcard]; norm_num
  have hTpos : (0 : ℝ) < T.card := by rw [hT]; positivity
  -- the most popular colour
  obtain ⟨κ, -, hκ⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps
    ⟨_, hTmem (0, fun _ => 0, fun _ => 0)⟩ (b := (I.card : ℝ) / T.card)
    (le_of_eq (by rw [nsmul_eq_mul]; field_simp))
  obtain ⟨J, hJ⟩ : ∃ J, J = I.filter (fun i => col i = κ) := ⟨_, rfl⟩
  rw [← hJ] at hκ
  have hJI : J ⊆ I := hJ ▸ Finset.filter_subset _ _
  have hJcol : ∀ i ∈ J, col i = κ := by
    intro i hi
    rw [hJ] at hi
    exact (Finset.mem_filter.mp hi).2
  have hJcard : netConst * (I.card : ℝ) ≤ (J.card : ℝ) := by
    calc netConst * (I.card : ℝ) = (I.card : ℝ) / T.card := by
          rw [hT]; unfold netConst; ring
      _ ≤ J.card := hκ
  have hJne : J.Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
    have h2 : (0 : ℝ) < J.card := lt_of_lt_of_le (mul_pos netConst_pos h1) hJcard
    exact_mod_cast h2
  -- the cells of that colour
  obtain ⟨S, hS⟩ : ∃ S, S = J.image cell := ⟨_, rfl⟩
  have hSne : S.Nonempty := hS ▸ hJne.image _
  let σ : Fin S.card → Fin 3 × (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun α => (S.equivFin.symm α).1
  have hσS : ∀ α, σ α ∈ S := fun α => (S.equivFin.symm α).2
  have hσinj : Function.Injective σ := fun α β h => S.equivFin.symm.injective (Subtype.ext h)
  let F : Fin S.card → Finset (Fin n) := fun α => J.filter (fun i => cell i = σ α)
  have hFne : ∀ α, ∃ i, i ∈ F α := by
    intro α
    have h := hσS α
    rw [hS] at h
    obtain ⟨i, hiJ, hi⟩ := Finset.mem_image.mp h
    exact ⟨i, Finset.mem_filter.mpr ⟨hiJ, hi⟩⟩
  choose k hk using hFne
  refine ⟨S.card, k, F, Finset.card_pos.mpr hSne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α
    exact hJI (Finset.mem_filter.mp (hk α)).1
  · intro α
    exact (Finset.filter_subset _ _).trans hJI
  · intro α
    exact ⟨k α, hk α⟩
  · intro α β hαβ
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    exact hαβ (hσinj (h1.symm.trans h2))
  · have hsum : ∑ α, (F α).card = J.card := by
      rw [Finset.card_eq_sum_card_image cell J, ← hS, ← Finset.sum_coe_sort S]
      exact Equiv.sum_comp S.equivFin.symm (fun x => (J.filter (fun a => cell a = x.1)).card)
    calc netConst * (I.card : ℝ) ≤ J.card := hJcard
      _ = ∑ α, ((F α).card : ℝ) := by rw [← hsum, Nat.cast_sum]
  · intro α i hi
    have hi' := Finset.mem_filter.mp hi
    have hk' := Finset.mem_filter.mp (hk α)
    have hiI := hJI hi'.1
    have hkI := hJI hk'.1
    exact net_prism_subset_of_cell_eq ha hab hb (hu i hiI) (hu _ hkI) (hc i hiI) (hc _ hkI)
      (hi'.2.trans hk'.2.symm)
  · intro α β hαβ
    have hkα := Finset.mem_filter.mp (hk α)
    have hkβ := Finset.mem_filter.mp (hk β)
    have hIα := hJI hkα.1
    have hIβ := hJI hkβ.1
    refine net_half_of_red_eq hb hb1 (hu _ hIα) (hu _ hIβ) (hc _ hIα) ?_ ?_
    · intro h
      exact hαβ (hσinj (hkα.2.symm.trans (h.trans hkβ.2)))
    · exact (hJcol _ hkα.1).trans (hJcol _ hkβ.1).symm

end

end WangZahlLot.Obl.wz_transverse_cell_weighted_cover
