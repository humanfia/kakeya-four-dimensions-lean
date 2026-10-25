-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.Grains.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_polynomial_grains_partition.PolyMethod.ZeroNull
import Submission.WZ.Obl.wz_polynomial_grains_partition.PolyMethod.TubeCells

/-!
# Grains decomposition: grid, sign patterns, walls (adapted from x0325, o005 branch x0325)

Coordinate boxes and their `D^3` subcubes, the grid index of a point, strict sign patterns of a
family of polynomials, the wall (the thickening of a zero set and of the grid planes), and the
counting of the sign-pattern/subcube pieces that a `δ`-tube meets (`child_ncard_le`) and of the
subcubes it meets (`tube_subbox_ncard`). The Wongkew thinness bound of x0325's version is not
needed here and has been dropped.
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
namespace Grains

open MeasureTheory

/-- Three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The closed coordinate cube with corner `a` and side `ℓ`. -/
def box (a : Fin 3 → ℝ) (ℓ : ℝ) : Set Space := {x | ∀ i, a i ≤ x i ∧ x i ≤ a i + ℓ}

/-- The closed subcube with index `q` of the subdivision of `box a ℓ` into `D^3` cubes. -/
def subbox (a : Fin 3 → ℝ) (ℓ : ℝ) {D : ℕ} (q : Fin 3 → Fin D) : Set Space :=
  box (fun r => a r + (q r : ℝ) * (ℓ / D)) (ℓ / D)


namespace SubboxAux

/-- A point `p` within distance `< h` of a point `y` of the `k`-th cell `[c + k h, c + (k+1) h]`
of the grid of mesh `h` lies in a cell of index `k - 1`, `k` or `k + 1`. -/
lemma floor_bounds {y p c h : ℝ} {k : ℕ} (hh : 0 < h) (hy1 : c + k * h ≤ y)
    (hy2 : y ≤ c + k * h + h) (hyp : |y - p| < h) :
    (k : ℤ) - 1 ≤ ⌊(p - c) / h⌋ ∧ ⌊(p - c) / h⌋ ≤ (k : ℤ) + 1 := by
  rw [abs_lt] at hyp
  obtain ⟨h1, h2⟩ := hyp
  constructor
  · rw [Int.le_floor, le_div_iff₀ hh]
    push_cast
    linarith
  · rw [← Int.lt_add_one_iff, Int.floor_lt, div_lt_iff₀ hh]
    push_cast
    linarith

/-- Along the line `t ↦ x + t v`, the grid index, multiplied by the sign of `v`, is monotone. -/
lemma signed_floor_mono {x v c h : ℝ} (hh : 0 < h) {t t' : ℝ} (htt : t ≤ t') :
    (if 0 ≤ v then (1 : ℤ) else -1) * ⌊(x + t * v - c) / h⌋ ≤
      (if 0 ≤ v then (1 : ℤ) else -1) * ⌊(x + t' * v - c) / h⌋ := by
  split_ifs with hv
  · rw [one_mul, one_mul]
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hh.le
    have := mul_le_mul_of_nonneg_right htt hv
    linarith
  · rw [neg_one_mul, neg_one_mul, neg_le_neg_iff]
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hh.le
    have := mul_le_mul_of_nonpos_right htt (le_of_lt (not_le.1 hv))
    linarith

lemma signed_bound {v : ℝ} {k q D : ℤ} (hD : 1 ≤ D) (hq0 : 0 ≤ q) (hqD : q + 1 ≤ D)
    (h1 : q - 1 ≤ k) (h2 : k ≤ q + 1) :
    -D ≤ (if 0 ≤ v then (1 : ℤ) else -1) * k ∧ (if 0 ≤ v then (1 : ℤ) else -1) * k ≤ D := by
  split_ifs <;> omega

lemma signed_cancel {v : ℝ} {k k' : ℤ}
    (h : (if 0 ≤ v then (1 : ℤ) else -1) * k = (if 0 ≤ v then (1 : ℤ) else -1) * k') :
    k = k' := by
  split_ifs at h <;> omega

lemma ncard_Icc_neg_one_one : (Set.Icc (-1 : Fin 3 → ℤ) 1).ncard = 27 := by
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Pi.card_Icc]
  simp

lemma ncard_Icc_int (D : ℕ) : (Set.Icc (-(3 * D : ℤ)) (3 * D)).ncard = 6 * D + 1 := by
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
  omega

end SubboxAux

open SubboxAux in
/-- A `δ`-tube (thickening of a segment of length `≤ 1`) meets at most `400 D` of the closed
subcubes of `box a ℓ` when the subcube side `ℓ / D` is at least `δ`. -/
theorem tube_subbox_ncard (a : Fin 3 → ℝ) {ℓ δ : ℝ} (hδ : 0 < δ) {D : ℕ} (hD : 1 ≤ D)
    (hδℓ : δ ≤ ℓ / D) (x v : Space) (hv : ‖v‖ ≤ 1) :
    ({q : Fin 3 → Fin D | (Metric.thickening δ (segment ℝ x (x + v)) ∩ subbox a ℓ q).Nonempty}.ncard
      : ℝ) ≤ 400 * D := by
  -- the bound does not use `‖v‖ ≤ 1`: the subcubes are confined to the box
  have _ := hv
  classical
  have hh : 0 < ℓ / D := lt_of_lt_of_le hδ hδℓ
  -- the grid index of the point `x + t • v`, and the signs of the coordinates of `v`
  let κ : ℝ → Fin 3 → ℤ := fun t r => ⌊(x r + t * v r - a r) / (ℓ / D)⌋
  let s : Fin 3 → ℤ := fun r => if 0 ≤ v r then 1 else -1
  have key : ∀ q : Fin 3 → Fin D, ∃ t : ℝ,
      (Metric.thickening δ (segment ℝ x (x + v)) ∩ subbox a ℓ q).Nonempty →
        ∀ r, ((q r : ℕ) : ℤ) - 1 ≤ κ t r ∧ κ t r ≤ ((q r : ℕ) : ℤ) + 1 := by
    intro q
    by_cases hq : (Metric.thickening δ (segment ℝ x (x + v)) ∩ subbox a ℓ q).Nonempty
    · obtain ⟨y, hy1, hy2⟩ := hq
      obtain ⟨p, hp, hdist⟩ := Metric.mem_thickening_iff.1 hy1
      rw [segment_eq_image'] at hp
      obtain ⟨t, -, rfl⟩ := hp
      refine ⟨t, fun _ r => ?_⟩
      have hyr : a r + ((q r : ℕ) : ℝ) * (ℓ / D) ≤ y r ∧
          y r ≤ a r + ((q r : ℕ) : ℝ) * (ℓ / D) + ℓ / D := hy2 r
      have hcoord : |y r - (x + t • (x + v - x)) r| < ℓ / D := by
        have h1 := PiLp.dist_apply_le y (x + t • (x + v - x)) r
        rw [Real.dist_eq] at h1
        exact lt_of_le_of_lt h1 (lt_of_lt_of_le hdist hδℓ)
      simp only [add_sub_cancel_left, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hcoord
      exact floor_bounds hh hyr.1 hyr.2 hcoord
    · exact ⟨0, fun h => absurd h hq⟩
  choose T hT using key
  set S := {q : Fin 3 → Fin D |
    (Metric.thickening δ (segment ℝ x (x + v)) ∩ subbox a ℓ q).Nonempty} with hS
  let f : (Fin 3 → Fin D) → ℤ × (Fin 3 → ℤ) := fun q =>
    (∑ r, s r * κ (T q) r, fun r => ((q r : ℕ) : ℤ) - κ (T q) r)
  have hmaps : ∀ q ∈ S, f q ∈ Set.Icc (-(3 * D : ℤ)) (3 * D) ×ˢ Set.Icc (-1 : Fin 3 → ℤ) 1 := by
    intro q hq
    have hb := hT q hq
    have hb' : ∀ r, -(D : ℤ) ≤ s r * κ (T q) r ∧ s r * κ (T q) r ≤ D := fun r =>
      signed_bound (by exact_mod_cast hD) (Nat.cast_nonneg _)
        (by have := (q r).isLt; omega) (hb r).1 (hb r).2
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [f, Fin.sum_univ_three]
      have := (hb' 0).1; have := (hb' 1).1; have := (hb' 2).1
      linarith
    · simp only [f, Fin.sum_univ_three]
      have := (hb' 0).2; have := (hb' 1).2; have := (hb' 2).2
      linarith
    · intro r
      simp only [f, Pi.neg_apply, Pi.one_apply]
      have := hb r
      omega
    · intro r
      simp only [f, Pi.one_apply]
      have := hb r
      omega
  have hinj : Set.InjOn f S := by
    intro q hq q' hq' hqq
    simp only [f, Prod.mk.injEq] at hqq
    obtain ⟨hsum, hdiff⟩ := hqq
    have hκ : κ (T q) = κ (T q') := by
      rcases le_total (T q) (T q') with hle | hle
      · have hmono : ∀ r ∈ Finset.univ, s r * κ (T q) r ≤ s r * κ (T q') r :=
          fun r _ => signed_floor_mono hh hle
        have := (Finset.sum_eq_sum_iff_of_le hmono).1 hsum
        funext r
        exact signed_cancel (this r (Finset.mem_univ r))
      · have hmono : ∀ r ∈ Finset.univ, s r * κ (T q') r ≤ s r * κ (T q) r :=
          fun r _ => signed_floor_mono hh hle
        have := (Finset.sum_eq_sum_iff_of_le hmono).1 hsum.symm
        funext r
        exact (signed_cancel (this r (Finset.mem_univ r))).symm
    funext r
    have h1 := congrFun hdiff r
    rw [hκ] at h1
    apply Fin.ext
    omega
  have hcard := Set.ncard_le_ncard_of_injOn f hmaps hinj
    ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  rw [Set.ncard_prod, ncard_Icc_int, ncard_Icc_neg_one_one] at hcard
  have : S.ncard ≤ 400 * D := by omega
  exact_mod_cast this

namespace SplitAux

/-- Volume of a coordinate box with corner `lo` and side lengths `w`. -/
lemma volume_coordBox (lo w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    volume {x : Space | ∀ i, lo i ≤ x i ∧ x i ≤ lo i + w i} =
      ENNReal.ofReal (w 0 * w 1 * w 2) := by
  have hset : {x : Space | ∀ i, lo i ≤ x i ∧ x i ≤ lo i + w i} =
      (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹' Set.Icc lo (fun i => lo i + w i) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def]
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
  rw [hset, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [add_sub_cancel_left, Fin.prod_univ_three]
  rw [← ENNReal.ofReal_mul (hw 0), ← ENNReal.ofReal_mul (mul_nonneg (hw 0) (hw 1))]

lemma volume_box_eq (c : Fin 3 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    volume (box c s) = ENNReal.ofReal (s * s * s) :=
  volume_coordBox c (fun _ => s) (fun _ => hs)

/-- The grid index of a point. -/
noncomputable def idx (a : Fin 3 → ℝ) (h : ℝ) {D : ℕ} (hD : 0 < D) (x : Space) :
    Fin 3 → Fin D := fun r =>
  ⟨min ⌊(x r - a r) / h⌋₊ (D - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hD one_pos)⟩

lemma idx_spec (a : Fin 3 → ℝ) {h : ℝ} (hh : 0 < h) {D : ℕ} (hD : 0 < D) {x : Space}
    (r : Fin 3) (hx1 : a r ≤ x r) (hx2 : x r ≤ a r + D * h) :
    a r + ((idx a h hD x r : ℕ) : ℝ) * h ≤ x r ∧
      x r ≤ a r + ((idx a h hD x r : ℕ) : ℝ) * h + h := by
  set t := (x r - a r) / h with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hh.le
  have htD : t ≤ D := by rw [ht, div_le_iff₀ hh]; linarith
  have hval : ((idx a h hD x r : ℕ) : ℝ) = ((min ⌊t⌋₊ (D - 1) : ℕ) : ℝ) := rfl
  have hxr : x r = a r + t * h := by rw [ht]; field_simp; ring
  rw [hval, hxr]
  rcases le_total ⌊t⌋₊ (D - 1) with hle | hle
  · rw [min_eq_left hle]
    have h1 := Nat.floor_le ht0
    have h2 := Nat.lt_floor_add_one t
    constructor
    · nlinarith
    · nlinarith
  · rw [min_eq_right hle]
    have hD1 : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hD.ne'), Nat.cast_one]
    rw [hD1]
    have h1 : ((D - 1 : ℕ) : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hle
    rw [hD1] at h1
    have h2 := Nat.floor_le ht0
    constructor
    · nlinarith
    · nlinarith

lemma idx_mem_subbox (a : Fin 3 → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) {D : ℕ} (hD : 0 < D)
    {x : Space}
    (hx : x ∈ box a ℓ) : x ∈ subbox a ℓ (idx a (ℓ / D) hD x) := by
  have hDR : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hh : 0 < ℓ / D := div_pos hℓ hDR
  intro r
  have hDh : (D : ℝ) * (ℓ / D) = ℓ := by field_simp
  exact idx_spec a hh hD r (hx r).1 (by rw [hDh]; exact (hx r).2)

lemma measurableSet_idx_eq (a : Fin 3 → ℝ) (h : ℝ) {D : ℕ} (hD : 0 < D)
    (q : Fin 3 → Fin D) :
    MeasurableSet {x : Space | idx a h hD x = q} := by
  have hset : {x : Space | idx a h hD x = q} =
      ⋂ r, (fun x : Space => min ⌊(x r - a r) / h⌋₊ (D - 1)) ⁻¹' {(q r : ℕ)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
      funext_iff, idx, Fin.ext_iff]
  rw [hset]
  refine MeasurableSet.iInter fun r => ?_
  have h1 : Measurable fun x : Space => (x r - a r) / h :=
    (by fun_prop : Continuous fun x : Space => (x r - a r) / h).measurable
  have hm : Measurable fun x : Space => min ⌊(x r - a r) / h⌋₊ (D - 1) :=
    (measurable_from_nat (f := fun n : ℕ => min n (D - 1))).comp (Nat.measurable_floor.comp h1)
  exact hm (measurableSet_singleton _)

/-- The strict sign pattern of a point. -/
noncomputable def sgn {J : ℕ} (P : Fin J → MvPolynomial (Fin 3) ℝ) (x : Space) :
    Fin J → Bool :=
  fun j => decide (0 < MvPolynomial.eval (fun i => x i) (P j))

lemma measurableSet_sgn_eq {J : ℕ} (P : Fin J → MvPolynomial (Fin 3) ℝ) (s : Fin J → Bool) :
    MeasurableSet {x : Space | sgn P x = s} := by
  have hset : {x : Space | sgn P x = s} =
      ⋂ j, {x : Space | decide (0 < MvPolynomial.eval (fun i => x i) (P j)) = s j} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff, sgn]
  rw [hset]
  refine MeasurableSet.iInter fun j => ?_
  have hm := PartitionAux.measurable_eval (P j)
  cases s j
  · simp only [decide_eq_false_iff_not, not_lt]
    exact measurableSet_le hm measurable_const
  · simp only [decide_eq_true_eq]
    exact measurableSet_lt measurable_const hm


/-- Zero set of a polynomial. -/
def zeroSet (Q : MvPolynomial (Fin 3) ℝ) : Set Space :=
  {x | MvPolynomial.eval (fun i => x i) Q = 0}

/-- The grid planes `x r = a r + k h`, `0 ≤ k ≤ D`. -/
def planes (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) : Set Space :=
  {x | ∃ r, ∃ k : Fin (D + 1), x r = a r + ((k : ℕ) : ℝ) * h}

/-- The wall: the `ρ`-thickening of the zero set and of the grid planes. -/
noncomputable def wall (Q : MvPolynomial (Fin 3) ℝ) (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ)
    (ρ : ℝ) : Set Space :=
  Metric.thickening ρ (zeroSet Q ∪ planes a h D)

/-- `tube_sign_cells_ncard` for a family indexed by any finite type. -/
lemma tube_sign_cells_ncard_fintype {ι : Type*} [Fintype ι] (P : ι → MvPolynomial (Fin 3) ℝ)
    (a u : Space) (δ : ℝ) :
    {s : ι → Bool | ∃ x ∈ Metric.thickening δ (segment ℝ a (a + u)),
        (∀ y ∈ Metric.ball x δ, ∀ j, MvPolynomial.eval (fun i => y i) (P j) ≠ 0) ∧
        ∀ j, if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
             else MvPolynomial.eval (fun i => x i) (P j) < 0}.ncard ≤
      (∑ j, (P j).totalDegree) + 1 := by
  classical
  set e := Fintype.equivFin ι
  have h := tube_sign_cells_ncard (Fintype.card ι) (fun j => P (e.symm j)) a u δ
  have hsum : ∑ j, (P (e.symm j)).totalDegree = ∑ j, (P j).totalDegree :=
    Equiv.sum_comp e.symm (fun j => (P j).totalDegree)
  rw [hsum] at h
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun s => s ∘ e.symm) ?_ ?_ (Set.toFinite _)) h
  · rintro s ⟨x, hx, hball, hs⟩
    exact ⟨x, hx, fun y hy j => hball y hy _, fun j => hs _⟩
  · intro s _ t _ hst
    funext i
    have := congrFun hst (e i)
    simpa using this

/-- The grid plane polynomials `X r - (a r + k h)`. -/
noncomputable def planePoly (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) (rk : Fin 3 × Fin (D + 1)) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X rk.1 - MvPolynomial.C (a rk.1 + ((rk.2 : ℕ) : ℝ) * h)

lemma eval_planePoly (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) (rk : Fin 3 × Fin (D + 1))
    (y : Space) :
    MvPolynomial.eval (fun i => y i) (planePoly a h D rk) =
      y rk.1 - (a rk.1 + ((rk.2 : ℕ) : ℝ) * h) := by
  simp [planePoly]

lemma totalDegree_planePoly_le (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) (rk : Fin 3 × Fin (D + 1)) :
    (planePoly a h D rk).totalDegree ≤ 1 := by
  unfold planePoly
  exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (MvPolynomial.totalDegree_X _).le

lemma mem_zeroSet_prod {J : ℕ} (P : Fin J → MvPolynomial (Fin 3) ℝ) {x : Space} :
    x ∈ zeroSet (∏ j, P j) ↔ ∃ j, MvPolynomial.eval (fun i => x i) (P j) = 0 := by
  simp [zeroSet, map_prod, Finset.prod_eq_zero_iff]

/-- The children: points of `A` off the wall, by sign pattern and subcube. -/
noncomputable def child (A W : Set Space) {J : ℕ} (P : Fin J → MvPolynomial (Fin 3) ℝ)
    (a : Fin 3 → ℝ) (h : ℝ) {D : ℕ} (hD : 0 < D)
    (i : (Fin J → Bool) × (Fin 3 → Fin D)) :
    Set Space :=
  {x | x ∈ A ∧ x ∉ W ∧ sgn P x = i.1 ∧ idx a h hD x = i.2}

/-- The leaves: points of `A` on the wall, by subcube. -/
noncomputable def leaf (A W : Set Space) (a : Fin 3 → ℝ) (h : ℝ) {D : ℕ} (hD : 0 < D)
    (q : Fin 3 → Fin D) : Set Space :=
  {x | x ∈ A ∧ x ∈ W ∧ idx a h hD x = q}

/-- The sign map of a child: its polynomial signs, and the plane signs determined by its
subcube. -/
def childSign {J D : ℕ} (i : (Fin J → Bool) × (Fin 3 → Fin D)) :
    Fin J ⊕ (Fin 3 × Fin (D + 1)) → Bool :=
  Sum.elim i.1 (fun rk => decide ((rk.2 : ℕ) ≤ (i.2 rk.1 : ℕ)))

lemma childSign_injective {J D : ℕ} : Function.Injective (childSign (J := J) (D := D)) := by
  intro i i' hii
  have h1 : i.1 = i'.1 := by
    funext j
    have := congrFun hii (Sum.inl j)
    simpa [childSign] using this
  have h2 : i.2 = i'.2 := by
    funext r
    have ha := congrFun hii (Sum.inr (r, ⟨(i.2 r : ℕ), by omega⟩))
    have hb := congrFun hii (Sum.inr (r, ⟨(i'.2 r : ℕ), by omega⟩))
    simp only [childSign, Sum.elim_inr, decide_eq_decide] at ha hb
    exact Fin.ext (le_antisymm (ha.mp le_rfl) (hb.mpr le_rfl))
  exact Prod.ext h1 h2

/-- A `δ`-tube meets at most `∑ deg + 3 (D + 1) + 1` children. -/
lemma child_ncard_le (A : Set Space) {J : ℕ} (P : Fin J → MvPolynomial (Fin 3) ℝ)
    (a : Fin 3 → ℝ) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) {D : ℕ} (hD : 0 < D)
    (hAQ : A ⊆ box a ℓ) (x v : Space) :
    {i | (Metric.thickening δ (segment ℝ x (x + v)) ∩
        child A (wall (∏ j, P j) a (ℓ / D) D (100 * δ)) P a (ℓ / D) hD i).Nonempty}.ncard ≤
      (∑ j, (P j).totalDegree) + 3 * (D + 1) + 1 := by
  classical
  set h : ℝ := ℓ / (D : ℝ) with hhdef
  have hh : 0 < h := div_pos hℓ (Nat.cast_pos.mpr hD)
  set Pall : Fin J ⊕ (Fin 3 × Fin (D + 1)) → MvPolynomial (Fin 3) ℝ :=
    Sum.elim P (planePoly a h D) with hPall
  have hdeg : ∑ k, (Pall k).totalDegree ≤ (∑ j, (P j).totalDegree) + 3 * (D + 1) := by
    rw [Fintype.sum_sum_type]
    simp only [hPall, Sum.elim_inl, Sum.elim_inr]
    have : ∑ rk : Fin 3 × Fin (D + 1), (planePoly a h D rk).totalDegree ≤ 3 * (D + 1) := by
      calc ∑ rk : Fin 3 × Fin (D + 1), (planePoly a h D rk).totalDegree
          ≤ ∑ _rk : Fin 3 × Fin (D + 1), 1 :=
            Finset.sum_le_sum fun rk _ => totalDegree_planePoly_le a h D rk
        _ = 3 * (D + 1) := by simp
    omega
  have hT := tube_sign_cells_ncard_fintype Pall x v δ
  refine le_trans (Set.ncard_le_ncard_of_injOn childSign ?_ childSign_injective.injOn
    (Set.toFinite _)) (hT.trans (by omega))
  rintro i ⟨y, hyT, hyA, hyW, hys, hyq⟩
  -- points off the wall are off the zero sets and the planes, and so is their `δ`-ball
  have hoff : ∀ z ∈ Metric.ball y δ, z ∉ zeroSet (∏ j, P j) ∪ planes a h D := by
    intro z hz hzZ
    apply hyW
    refine Metric.mem_thickening_iff.mpr ⟨z, hzZ, ?_⟩
    rw [Metric.mem_ball, dist_comm] at hz
    linarith
  have hyoff := hoff y (Metric.mem_ball_self hδ)
  have hsub := idx_mem_subbox a hℓ hD (hAQ hyA)
  refine ⟨y, hyT, ?_, ?_⟩
  · intro z hz k
    have hzoff := hoff z hz
    rcases k with j | rk
    · simp only [hPall, Sum.elim_inl]
      intro h0
      exact hzoff (Or.inl ((mem_zeroSet_prod P).mpr ⟨j, h0⟩))
    · simp only [hPall, Sum.elim_inr, eval_planePoly]
      intro h0
      exact hzoff (Or.inr ⟨rk.1, rk.2, by linarith⟩)
  · intro k
    rcases k with j | ⟨r, k⟩
    · simp only [hPall, Sum.elim_inl, childSign]
      rw [← hys]
      simp only [sgn]
      by_cases hpos : 0 < MvPolynomial.eval (fun i => y i) (P j)
      · simp [hpos]
      · simp only [hpos, decide_false, Bool.false_eq_true, ite_false]
        refine lt_of_le_of_ne (not_lt.mp hpos) fun h0 => hyoff (Or.inl ?_)
        exact (mem_zeroSet_prod P).mpr ⟨j, h0⟩
    · simp only [hPall, Sum.elim_inr, childSign, eval_planePoly]
      rw [← hyq]
      have hyr := hsub r
      have hne : y r ≠ a r + ((k : ℕ) : ℝ) * h := fun he => hyoff (Or.inr ⟨r, k, he⟩)
      by_cases hk : (k : ℕ) ≤ (idx a h hD y r : ℕ)
      · simp only [hk, decide_true, ite_true]
        have : ((k : ℕ) : ℝ) * h ≤ ((idx a h hD y r : ℕ) : ℝ) * h :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le
        have hle : a r + ((k : ℕ) : ℝ) * h ≤ y r := by
          have := hyr.1
          linarith
        have := lt_of_le_of_ne hle (Ne.symm hne)
        linarith
      · simp only [hk, decide_false, Bool.false_eq_true, ite_false]
        push Not at hk
        have hk1 : ((idx a h hD y r : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk
        have : ((idx a h hD y r : ℕ) : ℝ) * h + h ≤ ((k : ℕ) : ℝ) * h := by nlinarith
        have hle : y r ≤ a r + ((k : ℕ) : ℝ) * h := by
          have := hyr.2
          linarith
        have := lt_of_le_of_ne hle hne
        linarith

end SplitAux

end Grains
end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
