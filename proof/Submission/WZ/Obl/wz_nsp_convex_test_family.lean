-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_convex_test_family.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_nsp_convex_test_family`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_nsp_convex_test_family`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_nsp_convex_test_family/`
belong to this obligation.
-/

namespace WangZahlLot.Obl.wz_nsp_convex_test_family

open MeasureTheory

local notation "E" => LeanEval.Analysis.WangZahlKakeya.Space

/-! ### Six times the signed volume of a tetrahedron -/

/-- Six times the signed volume of the simplex `p 0, p 1, p 2, p 3`, as a polynomial. -/
noncomputable def vol6 (p : Fin 4 → E) : ℝ :=
  (p 1 0 - p 0 0) * ((p 2 1 - p 0 1) * (p 3 2 - p 0 2) - (p 2 2 - p 0 2) * (p 3 1 - p 0 1))
  - (p 1 1 - p 0 1) * ((p 2 0 - p 0 0) * (p 3 2 - p 0 2) - (p 2 2 - p 0 2) * (p 3 0 - p 0 0))
  + (p 1 2 - p 0 2) * ((p 2 0 - p 0 0) * (p 3 1 - p 0 1) - (p 2 1 - p 0 1) * (p 3 0 - p 0 0))

theorem vol6_update_sum (p : Fin 4 → E) (x : E) :
    vol6 (Function.update p 0 x) + vol6 (Function.update p 1 x) + vol6 (Function.update p 2 x)
      + vol6 (Function.update p 3 x) = vol6 p := by
  simp only [vol6, Function.update_apply]
  simp
  ring

theorem vol6_update_combo (p : Fin 4 → E) (x : E) (i : Fin 3) :
    vol6 (Function.update p 0 x) * p 0 i + vol6 (Function.update p 1 x) * p 1 i
      + vol6 (Function.update p 2 x) * p 2 i + vol6 (Function.update p 3 x) * p 3 i
      = vol6 p * x i := by
  simp only [vol6, Function.update_apply]
  fin_cases i <;> simp <;> ring

theorem vol6_update_affine (p : Fin 4 → E) (j : Fin 4) (x y : E) (a b : ℝ) (hab : a + b = 1) :
    vol6 (Function.update p j (a • x + b • y))
      = a * vol6 (Function.update p j x) + b * vol6 (Function.update p j y) := by
  obtain rfl : b = 1 - a := by linarith
  simp only [vol6, Function.update_apply]
  fin_cases j <;> simp <;> ring

/-! ### Coordinates and norms -/

theorem norm_sq_eq_coords (y : E) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem abs_coord_le_norm (y : E) (j : Fin 3) : |y j| ≤ ‖y‖ := by
  have h := norm_sq_eq_coords y
  have hsq : (y j) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [h]
    fin_cases j <;> simp <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
  have := sq_le_sq.mp hsq
  rwa [abs_norm] at this

/-! ### Reference sets and affine maps -/

/-- The reference set: barycentric coordinates bounded by `3`. -/
def refBox : Set E := {y | (∀ j, |y j| ≤ 3) ∧ |1 - (y 0 + y 1 + y 2)| ≤ 3}

/-- The standard simplex. -/
def refSimplex : Set E := {y | (∀ j, 0 ≤ y j) ∧ y 0 + y 1 + y 2 ≤ 1}

theorem refBox_convex : Convex ℝ refBox := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨fun j => ?_, ?_⟩
  · have h1 := hx1 j
    have h2 := hy1 j
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [abs_le] at *
    constructor <;> nlinarith
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [abs_le] at *
    obtain rfl : b = 1 - a := by linarith
    constructor <;> nlinarith

theorem refBox_isClosed : IsClosed refBox := by
  have : refBox = (⋂ j : Fin 3, {y : E | |y j| ≤ 3}) ∩ {y : E | |1 - (y 0 + y 1 + y 2)| ≤ 3} := by
    ext y; simp [refBox]
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun j => ?_) ?_
  · exact isClosed_le (by fun_prop) continuous_const
  · exact isClosed_le (by fun_prop) continuous_const

theorem refBox_subset_closedBall : refBox ⊆ Metric.closedBall (0 : E) 6 := by
  intro y hy
  rw [mem_closedBall_zero_iff]
  have h := norm_sq_eq_coords y
  have h0 := abs_le.1 (hy.1 0)
  have h1 := abs_le.1 (hy.1 1)
  have h2 := abs_le.1 (hy.1 2)
  nlinarith [norm_nonneg y]

theorem refBox_isCompact : IsCompact refBox :=
  Metric.isCompact_of_isClosed_isBounded refBox_isClosed
    (Metric.isBounded_closedBall.subset refBox_subset_closedBall)

theorem refSimplex_subset_refBox : refSimplex ⊆ refBox := by
  rintro y ⟨h1, h2⟩
  have a0 := h1 0
  have a1 := h1 1
  have a2 := h1 2
  refine ⟨fun j => ?_, ?_⟩
  · have := h1 j
    rw [abs_le]
    constructor
    · linarith
    · fin_cases j <;> simp <;> linarith
  · rw [abs_le]; constructor <;> linarith

theorem ball_subset_refSimplex :
    Metric.ball (WithLp.toLp 2 (fun _ : Fin 3 => (1 / 8 : ℝ)) : E) (1 / 8) ⊆ refSimplex := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hc : ∀ j, |y j - 1 / 8| < 1 / 8 := by
    intro j
    have := abs_coord_le_norm (y - WithLp.toLp 2 (fun _ : Fin 3 => (1 / 8 : ℝ))) j
    simp only [PiLp.sub_apply] at this
    linarith
  have h0 := abs_lt.1 (hc 0)
  have h1 := abs_lt.1 (hc 1)
  have h2 := abs_lt.1 (hc 2)
  refine ⟨fun j => ?_, by linarith⟩
  have := abs_lt.1 (hc j)
  linarith

theorem refSimplex_volume_pos : 0 < volume refSimplex :=
  lt_of_lt_of_le (Metric.measure_ball_pos volume _ (by norm_num))
    (measure_mono ball_subset_refSimplex)

theorem refBox_volume_ne_top : volume refBox ≠ ⊤ :=
  refBox_isCompact.measure_lt_top.ne

theorem refSimplex_volume_ne_top : volume refSimplex ≠ ⊤ :=
  ((measure_mono refSimplex_subset_refBox).trans_lt refBox_isCompact.measure_lt_top).ne

/-- The linear part of the affine map sending the reference simplex onto `conv p`. -/
noncomputable def linPart (p : Fin 4 → E) : E →ₗ[ℝ] E where
  toFun y := y 0 • (p 1 - p 0) + y 1 • (p 2 - p 0) + y 2 • (p 3 - p 0)
  map_add' x y := by
    simp only [PiLp.add_apply, add_smul]
    abel
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]

theorem linPart_apply (p : Fin 4 → E) (y : E) :
    linPart p y = y 0 • (p 1 - p 0) + y 1 • (p 2 - p 0) + y 2 • (p 3 - p 0) := rfl

/-- The affine map sending the reference simplex onto `conv p`. -/
noncomputable def aff (p : Fin 4 → E) (y : E) : E := p 0 + linPart p y

theorem volume_aff_image (p : Fin 4 → E) (s : Set E) :
    volume (aff p '' s) = ENNReal.ofReal |LinearMap.det (linPart p)| * volume s := by
  have : aff p '' s = (fun z => p 0 + z) '' (linPart p '' s) := by
    rw [Set.image_image]; rfl
  rw [this, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap]

theorem continuous_aff (p : Fin 4 → E) : Continuous (aff p) := by
  unfold aff
  exact continuous_const.add (LinearMap.continuous_of_finiteDimensional _)

theorem convex_aff_image (p : Fin 4 → E) {s : Set E} (hs : Convex ℝ s) :
    Convex ℝ (aff p '' s) := by
  have : aff p '' s = (fun z => p 0 + z) '' (linPart p '' s) := by
    rw [Set.image_image]; rfl
  rw [this]
  exact (hs.linear_image _).translate _

theorem aff_image_refSimplex_subset (p : Fin 4 → E) {W : Set E} (hW : Convex ℝ W)
    (hp : ∀ j, p j ∈ W) : aff p '' refSimplex ⊆ W := by
  rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
  have hmem := hW.sum_mem (t := Finset.univ) (w := ![1 - (y 0 + y 1 + y 2), y 0, y 1, y 2])
    (z := p) ?_ ?_ (fun j _ => hp j)
  · convert hmem using 1
    ext i
    simp [aff, linPart_apply, Fin.sum_univ_four]
    ring
  · intro j _
    fin_cases j <;> simp <;> linarith [hy1 0, hy1 1, hy1 2]
  · simp [Fin.sum_univ_four]
    ring

theorem mem_aff_image_of_bounds (p : Fin 4 → E) (hp : vol6 p ≠ 0) (x : E)
    (hx : ∀ j, |vol6 (Function.update p j x)| ≤ 3 * |vol6 p|) : x ∈ aff p '' refBox := by
  set V := vol6 p with hV_def
  set y : E := WithLp.toLp 2 ![vol6 (Function.update p 1 x) / V,
    vol6 (Function.update p 2 x) / V, vol6 (Function.update p 3 x) / V] with hy
  have hV : 0 < |V| := abs_pos.2 hp
  have key : ∀ j, |vol6 (Function.update p j x) / V| ≤ 3 := by
    intro j
    rw [abs_div, div_le_iff₀ hV]
    exact hx j
  have hsum := vol6_update_sum p x
  refine ⟨y, ⟨fun j => ?_, ?_⟩, ?_⟩
  · fin_cases j
    · simpa [hy] using key 1
    · simpa [hy] using key 2
    · simpa [hy] using key 3
  · have : 1 - (y 0 + y 1 + y 2) = vol6 (Function.update p 0 x) / V := by
      simp only [hy, PiLp.toLp_apply]
      simp
      field_simp
      linarith
    rw [this]; exact key 0
  · ext i
    have hc := vol6_update_combo p x i
    simp only [aff, linPart_apply, hy, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]
    simp
    field_simp
    linear_combination hc - p 0 i * hsum

/-! ### Test sets -/

/-- The test set attached to a quadruple of points. -/
noncomputable def testSet (p : Fin 4 → E) : Set E :=
  if volume (aff p '' refBox) = 0 then refBox else aff p '' refBox

theorem testSet_convex (p : Fin 4 → E) : Convex ℝ (testSet p) := by
  unfold testSet
  split_ifs
  · exact refBox_convex
  · exact convex_aff_image p refBox_convex

theorem aff_image_refBox_isCompact (p : Fin 4 → E) : IsCompact (aff p '' refBox) :=
  refBox_isCompact.image (continuous_aff p)

theorem testSet_measurableSet (p : Fin 4 → E) : MeasurableSet (testSet p) := by
  unfold testSet
  split_ifs
  · exact refBox_isClosed.measurableSet
  · exact (aff_image_refBox_isCompact p).isClosed.measurableSet

theorem testSet_volume_pos (p : Fin 4 → E) : 0 < volume (testSet p) := by
  unfold testSet
  split_ifs with h
  · exact lt_of_lt_of_le refSimplex_volume_pos (measure_mono refSimplex_subset_refBox)
  · exact pos_iff_ne_zero.2 h

theorem testSet_volume_ne_top (p : Fin 4 → E) : volume (testSet p) ≠ ⊤ := by
  unfold testSet
  split_ifs
  · exact refBox_volume_ne_top
  · exact (aff_image_refBox_isCompact p).measure_lt_top.ne

/-! ### Grid points -/

/-- The grid point with integer coordinates `w` and mesh `δ`. -/
noncomputable def gridPt (δ : ℝ) (w : Fin 3 → ℤ) : E := WithLp.toLp 2 (fun i => δ * (w i : ℝ))

theorem gridPt_apply (δ : ℝ) (w : Fin 3 → ℤ) (i : Fin 3) : gridPt δ w i = δ * (w i : ℝ) := rfl

/-- A point lies in every convex set containing the corners of its grid cube. -/
theorem mem_of_grid_corners {S : Set E} (hS : Convex ℝ S) {δ : ℝ} (hδ : 0 < δ) (y : E)
    (h : ∀ w : Fin 3 → ℤ, (∀ i, |δ * (w i : ℝ) - y i| ≤ δ) → gridPt δ w ∈ S) : y ∈ S := by
  set n : Fin 3 → ℤ := fun i => ⌊y i / δ⌋ with hn
  have hlo : ∀ i, δ * (n i : ℝ) ≤ y i := by
    intro i
    have := Int.floor_le (y i / δ)
    rw [le_div_iff₀ hδ] at this
    simp only [hn]; linarith
  have hhi : ∀ i, y i ≤ δ * ((n i : ℝ) + 1) := by
    intro i
    have := Int.lt_floor_add_one (y i / δ)
    rw [div_lt_iff₀ hδ] at this
    simp only [hn]; linarith
  let C : Set (Fin 3 → ℝ) := Set.univ.pi (fun i => {δ * (n i : ℝ), δ * ((n i : ℝ) + 1)})
  have hy : y.ofLp ∈ convexHull ℝ C := by
    rw [convexHull_pi]
    intro i _
    show y.ofLp i ∈ convexHull ℝ {_, _}
    rw [convexHull_pair, segment_eq_Icc (by nlinarith)]
    exact ⟨hlo i, hhi i⟩
  let L := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm
  have hy' : y ∈ convexHull ℝ (L '' C) := by
    have h1 := LinearMap.image_convexHull L.toLinearMap C
    rw [LinearEquiv.coe_coe] at h1
    rw [← h1]
    exact ⟨y.ofLp, hy, rfl⟩
  refine convexHull_min ?_ hS hy'
  rintro _ ⟨v, hv, rfl⟩
  have hv' : ∀ i, ∃ m : ℤ, v i = δ * (m : ℝ) ∧ |δ * (m : ℝ) - y i| ≤ δ := by
    intro i
    rcases hv i (Set.mem_univ i) with h1 | h1
    · refine ⟨n i, h1, ?_⟩
      rw [abs_le]; constructor <;> nlinarith [hlo i, hhi i]
    · refine ⟨n i + 1, by rw [h1]; push_cast; ring, ?_⟩
      rw [abs_le]; push_cast; constructor <;> nlinarith [hlo i, hhi i]
  choose w hw using hv'
  have hLv : L v = gridPt δ w := by
    ext i
    simp [L, gridPt_apply, (hw i).1]
  rw [hLv]
  exact h w (fun i => (hw i).2)

/-- A grid point near `y` in the sup distance is near `y` in norm. -/
theorem norm_gridPt_sub_lt {δ : ℝ} (hδ : 0 < δ) {y : E} {w : Fin 3 → ℤ}
    (hw : ∀ i, |δ * (w i : ℝ) - y i| ≤ δ) : ‖gridPt δ w - y‖ < 2 * δ := by
  have h := norm_sq_eq_coords (gridPt δ w - y)
  simp only [PiLp.sub_apply, gridPt_apply] at h
  have h0 := sq_le_sq' (abs_le.1 (hw 0)).1 (abs_le.1 (hw 0)).2
  have h1 := sq_le_sq' (abs_le.1 (hw 1)).1 (abs_le.1 (hw 1)).2
  have h2 := sq_le_sq' (abs_le.1 (hw 2)).1 (abs_le.1 (hw 2)).2
  have hsq : ‖gridPt δ w - y‖ ^ 2 < (2 * δ) ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

/-- Index of grid points in the cube `[-N, N]^3`. -/
noncomputable def gridIdx (N : ℕ) (δ : ℝ) (u : Fin 3 → Fin (2 * N + 1)) : E :=
  gridPt δ (fun i => ((u i : ℕ) : ℤ) - N)

theorem exists_gridIdx {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (hN : 2 / δ ≤ N) {w : Fin 3 → ℤ}
    (hw : gridPt δ w ∈ Metric.ball (0 : E) 2) : ∃ u, gridIdx N δ u = gridPt δ w := by
  have hb : ∀ i, |(w i : ℝ)| < N := by
    intro i
    have h1 := abs_coord_le_norm (gridPt δ w) i
    rw [mem_ball_zero_iff] at hw
    rw [gridPt_apply, abs_mul, abs_of_pos hδ] at h1
    have : |(w i : ℝ)| < 2 / δ := by
      rw [lt_div_iff₀ hδ]; linarith
    linarith
  have hb' : ∀ i, -(N : ℤ) < w i ∧ w i < N := by
    intro i
    have := abs_lt.1 (hb i)
    constructor
    · have h1 : (-(N : ℝ)) < (w i : ℝ) := this.1
      exact_mod_cast h1
    · exact_mod_cast this.2
  refine ⟨fun i => ⟨(w i + N).toNat, ?_⟩, ?_⟩
  · have := hb' i
    omega
  · ext i
    simp only [gridIdx, gridPt_apply]
    have := hb' i
    congr 2
    have h3 : ((w i + N).toNat : ℤ) = w i + N := Int.toNat_of_nonneg (by omega)
    rw [h3]; ring

/-! ### The core covering lemma -/

/-- A convex set containing `ball c r` and `w` contains a half-radius ball around their
midpoint. -/
theorem ball_midpoint_subset {W : Set E} (hW : Convex ℝ W) {c w : E} {r : ℝ}
    (hc : Metric.ball c r ⊆ W) (hw : w ∈ W) :
    Metric.ball ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • c) (r / 2) ⊆ W := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 : c + (2 : ℝ) • (z - ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • c)) ∈ W := by
    apply hc
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [Real.norm_ofNat]
    linarith
  have := hW hw h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  convert this using 1
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

/-- The covering lemma: a convex `W ⊆ B(0,2)` containing an `r`-ball lies in one of the test
sets built on grid points of mesh `r / 8`, whose volume is at most a fixed multiple of
`volume W`. -/
theorem core {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 16 / r ≤ N) {W : Set E}
    (hW : Convex ℝ W) (hW2 : W ⊆ Metric.ball 0 2) {c : E} (hc : Metric.ball c r ⊆ W) :
    ∃ z : Fin 4 → Fin 3 → Fin (2 * N + 1),
      W ⊆ testSet (fun j => gridIdx N (r / 8) (z j)) ∧
      volume (testSet (fun j => gridIdx N (r / 8) (z j))) ≤
        volume refBox / volume refSimplex * volume W := by
  classical
  set δ := r / 8 with hδ_def
  have hδ : 0 < δ := by positivity
  have hNδ : 2 / δ ≤ N := by
    have : 2 / δ = 16 / r := by rw [hδ_def]; field_simp; norm_num
    rw [this]; exact hN
  -- grid points close to a deep point of `W` lie in `W`
  have deep : ∀ y : E, Metric.ball y (r / 2) ⊆ W → ∀ w : Fin 3 → ℤ,
      (∀ i, |δ * (w i : ℝ) - y i| ≤ δ) → gridPt δ w ∈ W := by
    intro y hy w hw
    apply hy
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖gridPt δ w - y‖ < 2 * δ := norm_gridPt_sub_lt hδ hw
      _ ≤ r / 2 := by rw [hδ_def]; linarith
  have hcdeep : Metric.ball c (r / 2) ⊆ W := (Metric.ball_subset_ball (by linarith)).trans hc
  -- the finite set of admissible quadruples
  let pts : (Fin 4 → Fin 3 → Fin (2 * N + 1)) → Fin 4 → E := fun z j => gridIdx N δ (z j)
  let T := Finset.univ.filter
    (fun z : Fin 4 → Fin 3 → Fin (2 * N + 1) => ∀ j, pts z j ∈ W)
  -- a nondegenerate admissible quadruple: corners of the grid cube of `c`
  obtain ⟨z0, hz0T, hz0⟩ : ∃ z0 ∈ T, vol6 (pts z0) ≠ 0 := by
    set n : Fin 3 → ℤ := fun i => ⌊c i / δ⌋ with hn
    have hlo : ∀ i, δ * (n i : ℝ) ≤ c i := by
      intro i
      have := Int.floor_le (c i / δ)
      rw [le_div_iff₀ hδ] at this
      simp only [hn]; linarith
    have hhi : ∀ i, c i ≤ δ * ((n i : ℝ) + 1) := by
      intro i
      have := Int.lt_floor_add_one (c i / δ)
      rw [div_lt_iff₀ hδ] at this
      simp only [hn]; linarith
    let w : Fin 4 → Fin 3 → ℤ := fun j i => n i + if (j : ℕ) = (i : ℕ) + 1 then 1 else 0
    have hw : ∀ j, gridPt δ (w j) ∈ W := by
      intro j
      apply deep c hcdeep
      intro i
      simp only [w]
      split_ifs
      · push_cast; rw [abs_le]; constructor <;> linarith [hlo i, hhi i]
      · push_cast; rw [abs_le]; constructor <;> linarith [hlo i, hhi i]
    choose u hu using fun j => exists_gridIdx hδ hNδ (hW2 (hw j))
    refine ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => ?_⟩, ?_⟩
    · show gridIdx N δ (u j) ∈ W
      rw [hu j]; exact hw j
    · have : pts u = fun j => gridPt δ (w j) := funext fun j => hu j
      rw [this]
      have hv : vol6 (fun j => gridPt δ (w j)) = δ ^ 3 := by
        simp [vol6, gridPt_apply, w]
        ring
      rw [hv]
      positivity
  obtain ⟨z, hzT, hzmax⟩ := T.exists_max_image (fun z => |vol6 (pts z)|) ⟨z0, hz0T⟩
  set p := pts z with hp_def
  have hpW : ∀ j, p j ∈ W := (Finset.mem_filter.1 hzT).2
  have hVp : vol6 p ≠ 0 := by
    intro h0
    have := hzmax z0 hz0T
    simp only [h0, abs_zero] at this
    exact hz0 (abs_nonpos_iff.1 this)
  -- the barycentric region of `p`
  set Bar : Set E := {x | ∀ j, |vol6 (Function.update p j x)| ≤ |vol6 p|} with hBar
  have hBarconv : Convex ℝ Bar := by
    intro x hx y hy a b ha hb hab j
    rw [vol6_update_affine p j x y a b hab]
    calc |a * vol6 (Function.update p j x) + b * vol6 (Function.update p j y)|
        ≤ |a * vol6 (Function.update p j x)| + |b * vol6 (Function.update p j y)| :=
          abs_add_le _ _
      _ = a * |vol6 (Function.update p j x)| + b * |vol6 (Function.update p j y)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * |vol6 p| + b * |vol6 p| :=
          add_le_add (mul_le_mul_of_nonneg_left (hx j) ha) (mul_le_mul_of_nonneg_left (hy j) hb)
      _ = |vol6 p| := by rw [← add_mul, hab, one_mul]
  -- maximality: every grid point of `W` is in the barycentric region
  have grid_in : ∀ w, gridPt δ w ∈ W → gridPt δ w ∈ Bar := by
    intro w hw j
    obtain ⟨u, hu⟩ := exists_gridIdx hδ hNδ (hW2 hw)
    have hmem : Function.update z j u ∈ T := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j' => ?_⟩
      by_cases hj : j' = j
      · subst hj
        show gridIdx N δ (Function.update z j' u j') ∈ W
        rw [Function.update_self, hu]; exact hw
      · show gridIdx N δ (Function.update z j u j') ∈ W
        rw [Function.update_of_ne hj]; exact hpW j'
    have hupd : pts (Function.update z j u) = Function.update p j (gridPt δ w) := by
      funext j'
      by_cases hj : j' = j
      · subst hj
        show gridIdx N δ (Function.update z j' u j') = _
        rw [Function.update_self, Function.update_self, hu]
      · show gridIdx N δ (Function.update z j u j') = _
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
    have := hzmax _ hmem
    rw [hupd] at this
    exact this
  have deep_in : ∀ y, Metric.ball y (r / 2) ⊆ W → y ∈ Bar := fun y hy =>
    mem_of_grid_corners hBarconv hδ y (fun w hw => grid_in w (deep y hy w hw))
  have hc_in : c ∈ Bar := deep_in c hcdeep
  -- `W` lies in the image of the reference box
  have hWsub : W ⊆ aff p '' refBox := by
    intro w hw
    apply mem_aff_image_of_bounds p hVp w
    intro j
    have hm := deep_in _ (ball_midpoint_subset hW hc hw) j
    have hcj := hc_in j
    have hw_eq : w = (2 : ℝ) • ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • c) + (-1 : ℝ) • c := by
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hw_eq, vol6_update_affine p j _ _ 2 (-1) (by norm_num)]
    calc |2 * vol6 (Function.update p j ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • c))
          + -1 * vol6 (Function.update p j c)|
        ≤ |2 * vol6 (Function.update p j ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • c))|
          + |-1 * vol6 (Function.update p j c)| := abs_add_le _ _
      _ = 2 * |vol6 (Function.update p j ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • c))|
          + |vol6 (Function.update p j c)| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * |vol6 p| + |vol6 p| := by gcongr
      _ = 3 * |vol6 p| := by ring
  -- volume comparison
  have hWpos : 0 < volume W :=
    lt_of_lt_of_le (Metric.measure_ball_pos volume c hr) (measure_mono hc)
  have hRne : volume (aff p '' refBox) ≠ 0 := by
    intro h0
    have := measure_mono (μ := volume) hWsub
    rw [h0] at this
    exact hWpos.ne' (nonpos_iff_eq_zero.1 this)
  have htest : testSet p = aff p '' refBox := by simp [testSet, hRne]
  refine ⟨z, ?_, ?_⟩
  · show W ⊆ testSet p
    rw [htest]; exact hWsub
  · show volume (testSet p) ≤ _
    rw [htest, volume_aff_image]
    have hS := measure_mono (μ := volume) (aff_image_refSimplex_subset p hW hpW)
    rw [volume_aff_image] at hS
    calc ENNReal.ofReal |LinearMap.det (linPart p)| * volume refBox
        = volume refBox / volume refSimplex *
            (ENNReal.ofReal |LinearMap.det (linPart p)| * volume refSimplex) := by
          rw [mul_left_comm, ENNReal.div_mul_cancel refSimplex_volume_pos.ne'
            refSimplex_volume_ne_top]
      _ ≤ volume refBox / volume refSimplex * volume W := by gcongr

/-! ### The theorem -/

theorem main : ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∃ D : ℝ, 1 ≤ D ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∃ (H : ℕ) (P : Fin H → Set LeanEval.Analysis.WangZahlKakeya.Space), (H : ℝ) ≤ D * r ^ (-D) ∧ (∀ h : Fin H, Convex ℝ (P h) ∧ MeasurableSet (P h) ∧ 0 < MeasureTheory.volume (P h) ∧ MeasureTheory.volume (P h) ≠ ⊤) ∧ ∀ (K m n : ℕ) (x v : Fin m × Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (g : Fin n → Fin K) (B : ℝ), (∀ q : Fin m × Fin n, ‖v q‖ = 1 ∧ T r (x q) (v q) ⊆ Metric.ball 0 2) → (∀ (k : Fin K) (h : Fin H), ENNReal.ofReal (((Set.ncard {q : Fin m × Fin n | g q.2 = k ∧ T r (x q) (v q) ⊆ (P h)} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal B * MeasureTheory.volume (P h)) → ∀ (k : Fin K) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {q : Fin m × Fin n | g q.2 = k ∧ T r (x q) (v q) ⊆ W} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal (D * B) * MeasureTheory.volume W := by
  intro T hT
  subst hT
  set κ := volume refBox / volume refSimplex
  have hκtop : κ ≠ ⊤ := ENNReal.div_ne_top refBox_volume_ne_top refSimplex_volume_pos.ne'
  refine ⟨max κ.toReal (35 ^ 12), le_max_of_le_right (by norm_num), fun r hr hr1 => ?_⟩
  set D := max κ.toReal (35 ^ 12)
  have hD12 : (35 : ℝ) ^ 12 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD12
  have hκD : κ ≤ ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_toReal hκtop]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  set N := ⌈16 / r⌉₊
  have hN16 : 16 / r ≤ N := Nat.le_ceil _
  let e := Fintype.equivFin (Fin 4 → Fin 3 → Fin (2 * N + 1))
  refine ⟨Fintype.card (Fin 4 → Fin 3 → Fin (2 * N + 1)),
    fun h => testSet (fun j => gridIdx N (r / 8) (e.symm h j)), ?_, ?_, ?_⟩
  · -- the number of test sets
    have hcard : (Fintype.card (Fin 4 → Fin 3 → Fin (2 * N + 1)) : ℝ)
        = ((2 * N + 1 : ℕ) : ℝ) ^ 12 := by
      simp only [Fintype.card_fun, Fintype.card_fin]
      push_cast
      ring
    rw [hcard]
    have hN1 : (N : ℝ) < 16 / r + 1 := Nat.ceil_lt_add_one (by positivity)
    have h35 : ((2 * N + 1 : ℕ) : ℝ) ≤ 35 / r := by
      push_cast
      have h3 : 3 ≤ 3 / r := by rw [le_div_iff₀ hr]; linarith
      have : 35 / r = 2 * (16 / r) + 3 / r := by ring
      linarith
    have hrpow : r ^ (-(12 : ℝ)) ≤ r ^ (-D) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
    have h12 : r ^ (-(12 : ℝ)) = 1 / r ^ 12 := by
      rw [Real.rpow_neg hr.le, one_div]
      norm_cast
    calc ((2 * N + 1 : ℕ) : ℝ) ^ 12 ≤ (35 / r) ^ 12 := by gcongr
      _ = 35 ^ 12 * (1 / r ^ 12) := by rw [div_pow]; ring
      _ ≤ D * r ^ (-D) := by
          rw [← h12]
          exact mul_le_mul hD12 hrpow (by positivity) hD0
  · intro h
    exact ⟨testSet_convex _, testSet_measurableSet _, testSet_volume_pos _,
      testSet_volume_ne_top _⟩
  · intro K m n x v g B hv hP k W hW
    beta_reduce at hv hP ⊢
    by_cases hne : ∃ q : Fin m × Fin n,
        g q.2 = k ∧ Metric.thickening r (segment ℝ (x q) (x q + v q)) ⊆ W
    · obtain ⟨q0, -, hq0⟩ := hne
      have hball : Metric.ball (x q0) r ⊆ W ∩ Metric.ball 0 2 :=
        (Metric.ball_subset_thickening (left_mem_segment ℝ _ _) r).trans
          (Set.subset_inter hq0 (hv q0).2)
      obtain ⟨z, hzsub, hzvol⟩ :=
        core hr hN16 (hW.inter (convex_ball 0 2)) Set.inter_subset_right hball
      have hPh : (fun j => gridIdx N (r / 8) (e.symm (e z) j))
          = fun j => gridIdx N (r / 8) (z j) := by
        simp
      have hsub : {q : Fin m × Fin n | g q.2 = k ∧
            Metric.thickening r (segment ℝ (x q) (x q + v q)) ⊆ W} ⊆
          {q : Fin m × Fin n | g q.2 = k ∧ Metric.thickening r (segment ℝ (x q) (x q + v q)) ⊆
            testSet (fun j => gridIdx N (r / 8) (e.symm (e z) j))} := by
        rintro q ⟨hq1, hq2⟩
        refine ⟨hq1, ?_⟩
        rw [hPh]
        exact (Set.subset_inter hq2 (hv q).2).trans hzsub
      have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
      calc ENNReal.ofReal (((Set.ncard {q : Fin m × Fin n | g q.2 = k ∧
              Metric.thickening r (segment ℝ (x q) (x q + v q)) ⊆ W} : ℕ) : ℝ) * r ^ 2)
          ≤ ENNReal.ofReal (((Set.ncard {q : Fin m × Fin n | g q.2 = k ∧
              Metric.thickening r (segment ℝ (x q) (x q + v q)) ⊆
                testSet (fun j => gridIdx N (r / 8) (e.symm (e z) j))} : ℕ) : ℝ) * r ^ 2) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg r))
        _ ≤ ENNReal.ofReal B * volume (testSet (fun j => gridIdx N (r / 8) (e.symm (e z) j))) :=
            hP k (e z)
        _ ≤ ENNReal.ofReal B * (κ * volume (W ∩ Metric.ball 0 2)) := by
            rw [hPh]
            gcongr
        _ ≤ ENNReal.ofReal B * (ENNReal.ofReal D * volume W) := by
            gcongr
            exact Set.inter_subset_left
        _ = ENNReal.ofReal (D * B) * volume W := by
            rw [ENNReal.ofReal_mul hD0]
            ring
    · push Not at hne
      have hempty : {q : Fin m × Fin n | g q.2 = k ∧
          Metric.thickening r (segment ℝ (x q) (x q + v q)) ⊆ W} = ∅ := by
        ext q
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        exact hne q
      rw [hempty]
      simp

end WangZahlLot.Obl.wz_nsp_convex_test_family

theorem WangZahlLot.wz_nsp_convex_test_family : ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∃ D : ℝ, 1 ≤ D ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∃ (H : ℕ) (P : Fin H → Set LeanEval.Analysis.WangZahlKakeya.Space), (H : ℝ) ≤ D * r ^ (-D) ∧ (∀ h : Fin H, Convex ℝ (P h) ∧ MeasurableSet (P h) ∧ 0 < MeasureTheory.volume (P h) ∧ MeasureTheory.volume (P h) ≠ ⊤) ∧ ∀ (K m n : ℕ) (x v : Fin m × Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (g : Fin n → Fin K) (B : ℝ), (∀ q : Fin m × Fin n, ‖v q‖ = 1 ∧ T r (x q) (v q) ⊆ Metric.ball 0 2) → (∀ (k : Fin K) (h : Fin H), ENNReal.ofReal (((Set.ncard {q : Fin m × Fin n | g q.2 = k ∧ T r (x q) (v q) ⊆ (P h)} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal B * MeasureTheory.volume (P h)) → ∀ (k : Fin K) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {q : Fin m × Fin n | g q.2 = k ∧ T r (x q) (v q) ⊆ W} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal (D * B) * MeasureTheory.volume W :=
  WangZahlLot.Obl.wz_nsp_convex_test_family.main
