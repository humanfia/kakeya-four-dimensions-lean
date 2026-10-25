-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.ZoomCenter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomSelect

/-!
# Choosing the zoom centre

Every point of a shading lies within `1/(16 r)` of a point of a grid of spacing `1/(32 r)`; the
tube then passes near that grid point and the point lies in the slab cut out there.  Hence the
shading masses near grid points add up to at least the total mass, and some grid point carries
at least the average share.  Zooming multiplies volumes by `r ^ 3`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory Finset
open scoped ENNReal RealInnerProductSpace Classical

noncomputable section

theorem volume_zoom_image {r : ℝ} (hr : 0 < r) (c : Space) (S : Set Space) :
    volume (zoom r c '' S) = ENNReal.ofReal (r ^ 3) * volume S := by
  have he : zoom r c '' S = (fun p => p + -c) '' (AffineMap.homothety c r '' S) := by
    rw [image_image]
    congr 1
    funext p
    simp only [zoom, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    abel
  rw [he, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_image_homothety,
    finrank_euclideanSpace_fin, abs_of_pos (by positivity)]

/-- The closest point is closer to `c` than any point of the axis. -/
theorem norm_cpt_sub_le {c x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖cpt c x v - c‖ ≤ ‖(x + t • v) - c‖ := by
  have h := norm_proj_le (c := c) (x := x) (v := v) (p := c) hv t
  simp only [sub_self, inner_zero_left, zero_smul, add_zero] at h
  rwa [norm_sub_rev c (cpt c x v), norm_sub_rev c (x + t • v)] at h

/-- A point of a tube close to `c` makes the tube pass near `c`, and lies in the slab. -/
theorem fnear_of_point {r δ : ℝ} (hr : 0 < r) (hδr : δ ≤ 1 / (16 * r)) {c x v p : Space}
    (hv : ‖v‖ = 1) (hp : p ∈ Tube δ x v) (hpc : ‖p - c‖ ≤ 1 / (16 * r)) :
    FNear r c x v ∧ p ∈ zslab r c v := by
  obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_tube' hp
  have hqc : ‖(x + t • v) - c‖ ≤ 1 / (8 * r) := by
    have he : (x + t • v) - c = (p - c) - (p - (x + t • v)) := by abel
    rw [he]
    have : 1 / (8 * r) = 1 / (16 * r) + 1 / (16 * r) := by field_simp; ring
    exact (norm_sub_le _ _).trans (by linarith)
  have hinner : |⟪c - (x + t • v), v⟫| ≤ 1 / (8 * r) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hv, mul_one, norm_sub_rev]; exact hqc
  have hpar : cpar c x v = t + ⟪c - (x + t • v), v⟫ := by
    simp only [cpar]
    rw [show c - x = (c - (x + t • v)) + t • v by abel, inner_add_left, inner_smul_left,
      real_inner_self_eq_norm_sq, hv]
    simp only [conj_trivial, one_pow, mul_one]
    ring
  refine ⟨⟨(norm_cpt_sub_le hv t).trans hqc, ?_, ?_⟩, ?_⟩
  · rw [hpar]; linarith [(abs_le.mp hinner).1, ht.1]
  · rw [hpar]; linarith [(abs_le.mp hinner).2, ht.2]
  · show |⟪p - c, v⟫| ≤ 1 / (2 * r)
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hv, mul_one]
    refine hpc.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- The grid point with coordinates `-1 + k i / (32 r)`. -/
def gridPt (r : ℝ) {N : ℕ} (k : Fin 3 → Fin N) : Space :=
  WithLp.toLp 2 (fun i => -1 + (k i : ℝ) / (32 * r))

theorem exists_gridPt {r : ℝ} (hr : 1 ≤ r) {p : Space} (hp : ‖p‖ < 1) :
    ∃ k : Fin 3 → Fin (⌈64 * r⌉₊ + 1), ‖p - gridPt r k‖ ≤ 1 / (16 * r) := by
  have hr0 : 0 < r := by linarith
  have hg : 0 < 32 * r := by positivity
  have hcoord : ∀ i : Fin 3, |p i| < 1 := fun i =>
    (by simpa using PiLp.norm_apply_le p i : |p i| ≤ ‖p‖).trans_lt hp
  let kk : Fin 3 → ℕ := fun i => ⌊(p i + 1) * (32 * r)⌋₊
  have hk : ∀ i, kk i < ⌈64 * r⌉₊ + 1 := by
    intro i
    have h1 : (p i + 1) * (32 * r) < 64 * r := by
      have := (abs_lt.mp (hcoord i)).2; nlinarith
    have h2 : (kk i : ℝ) ≤ (p i + 1) * (32 * r) :=
      Nat.floor_le (by have := (abs_lt.mp (hcoord i)).1; nlinarith)
    have h3 : (64 * r : ℝ) ≤ ⌈64 * r⌉₊ := Nat.le_ceil _
    have : (kk i : ℝ) < ⌈64 * r⌉₊ + 1 := by linarith
    exact_mod_cast this
  refine ⟨fun i => ⟨kk i, hk i⟩, ?_⟩
  have hdiff : ∀ i : Fin 3, |p i - (-1 + (kk i : ℝ) / (32 * r))| ≤ 1 / (32 * r) := by
    intro i
    have hpos : 0 ≤ (p i + 1) * (32 * r) := by
      have := (abs_lt.mp (hcoord i)).1; nlinarith
    have h2 : (kk i : ℝ) ≤ (p i + 1) * (32 * r) := Nat.floor_le hpos
    have h3 : (p i + 1) * (32 * r) < kk i + 1 := Nat.lt_floor_add_one _
    have h4 : (kk i : ℝ) / (32 * r) ≤ p i + 1 := by rw [div_le_iff₀ hg]; linarith
    have h5 : p i + 1 < ((kk i : ℝ) + 1) / (32 * r) := by rw [lt_div_iff₀ hg]; linarith
    have h6 : ((kk i : ℝ) + 1) / (32 * r) = (kk i : ℝ) / (32 * r) + 1 / (32 * r) := by ring
    have h7 : 0 < 1 / (32 * r) := one_div_pos.mpr hg
    rw [abs_le]
    constructor <;> linarith
  rw [EuclideanSpace.norm_eq]
  have hsq : ∑ i, ‖(p - gridPt r (fun i => ⟨kk i, hk i⟩)) i‖ ^ 2 ≤ 3 * (1 / (32 * r)) ^ 2 := by
    rw [Fin.sum_univ_three]
    have hb : ∀ i : Fin 3, ‖(p - gridPt r (fun i => ⟨kk i, hk i⟩)) i‖ ^ 2 ≤ (1 / (32 * r)) ^ 2 := by
      intro i
      rw [Real.norm_eq_abs, sq_abs]
      have := hdiff i
      simp only [gridPt, PiLp.sub_apply]
      exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    linarith [hb 0, hb 1, hb 2]
  calc Real.sqrt (∑ i, ‖(p - gridPt r (fun i => ⟨kk i, hk i⟩)) i‖ ^ 2)
      ≤ Real.sqrt (3 * (1 / (32 * r)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ ≤ 1 / (16 * r) := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (1 / (16 * r)) ^ 2 = 4 * (1 / (32 * r)) ^ 2 := by field_simp; ring
      rw [this]; nlinarith [sq_nonneg (1 / (32 * r))]

/-- Some grid point carries at least the average share of the shading mass. -/
theorem exists_zoom_centre {n : ℕ} {r δ : ℝ} (hr : 1 ≤ r) (hδr : δ ≤ 1 / (16 * r))
    (x v : Fin n → Space) (Y : Fin n → Set Space) (hv : ∀ i, ‖v i‖ = 1)
    (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i)) (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) :
    ∃ c : Space, ∑ i, volume (Y i) ≤
      (((⌈64 * r⌉₊ + 1) ^ 3 : ℕ) : ℝ≥0∞) *
        ∑ i ∈ univ.filter (fun i => FNear r c (x i) (v i)), volume (Y i ∩ zslab r c (v i)) := by
  have hr0 : 0 < r := by linarith
  set N := ⌈64 * r⌉₊ + 1
  let m : (Fin 3 → Fin N) → ℝ≥0∞ := fun k =>
    ∑ i ∈ univ.filter (fun i => FNear r (gridPt r k) (x i) (v i)),
      volume (Y i ∩ zslab r (gridPt r k) (v i))
  have hcover : ∀ i, volume (Y i) ≤ ∑ k ∈ (univ : Finset (Fin 3 → Fin N)).filter
      (fun k => FNear r (gridPt r k) (x i) (v i)), volume (Y i ∩ zslab r (gridPt r k) (v i)) := by
    intro i
    refine (measure_mono ?_).trans (measure_biUnion_finset_le _ _)
    intro p hp
    have hpT := hY i hp
    obtain ⟨k, hk⟩ := exists_gridPt hr (by simpa using hball i hpT)
    obtain ⟨hn, hs⟩ := fnear_of_point hr0 hδr (hv i) hpT hk
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨mem_univ _, hn⟩, hp, hs⟩
  have hswap : ∑ i, ∑ k ∈ (univ : Finset (Fin 3 → Fin N)).filter
      (fun k => FNear r (gridPt r k) (x i) (v i)),
      volume (Y i ∩ zslab r (gridPt r k) (v i)) = ∑ k, m k := by
    simp only [m, Finset.sum_filter]
    exact Finset.sum_comm
  obtain ⟨k₀, -, hmax⟩ := Finset.exists_max_image univ m univ_nonempty
  refine ⟨gridPt r k₀, ?_⟩
  calc ∑ i, volume (Y i) ≤ ∑ k, m k := (Finset.sum_le_sum fun i _ => hcover i).trans_eq hswap
    _ ≤ ∑ _k : Fin 3 → Fin N, m k₀ := Finset.sum_le_sum fun k hk => hmax k hk
    _ = ((N ^ 3 : ℕ) : ℝ≥0∞) * m k₀ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [Fintype.card_fin]

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
