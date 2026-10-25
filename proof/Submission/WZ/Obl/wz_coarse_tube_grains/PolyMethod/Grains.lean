-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod.Grains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.ZeroNull
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.TubeCells
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.Wongkew

/-!
# Polynomial-partitioning grains decomposition (WZ Prop A.4, in the form used by Lemma A.5)

Recursion on pieces `A` contained in coordinate cubes of side `ℓ = 2 D^(-t)`, `D = 2^p`: partition
`Leb|A` into `D^3` strict sign cells (`guth_katz_partitioning_ac`), cut by the `D^3` subcubes, and
let the wall `W` be the `100δ`-thickening of the zero sets and of the grid planes. Children are the
cell-subcube pieces of `A \ W` (a `δ`-tube meets `≤ 20 D` of them, `tube_sign_cells_ncard`);
leaves are the subcube pieces of `A ∩ W` (thin by `Wongkew.volume_thickening_zeroSet_cube_le`,
and a `δ`-tube meets `≤ 400 D` of them). Pigeonholing a level and a dyadic mass class gives
the final pieces.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
namespace Grains

open MeasureTheory

/-- Three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The closed coordinate cube with corner `a` and side `ℓ`. -/
def box (a : Fin 3 → ℝ) (ℓ : ℝ) : Set Space := {x | ∀ i, a i ≤ x i ∧ x i ≤ a i + ℓ}

/-- The closed subcube with index `q` of the subdivision of `box a ℓ` into `D^3` cubes. -/
def subbox (a : Fin 3 → ℝ) (ℓ : ℝ) {D : ℕ} (q : Fin 3 → Fin D) : Set Space :=
  box (fun r => a r + (q r : ℝ) * (ℓ / D)) (ℓ / D)

/-- Thinness constant of one step. -/
noncomputable def Kthin (D : ℕ) : ℝ := 2000000 * 3 ^ (12 * D)

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
  rw [hset, Wongkew.CountAux.volume_box]
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

/-- Products of three side lengths, one of them `ρ`. -/
lemma prod_ite_three (r : Fin 3) (ρ h : ℝ) :
    (if (0 : Fin 3) = r then ρ else h) * (if (1 : Fin 3) = r then ρ else h) *
      (if (2 : Fin 3) = r then ρ else h) = ρ * h ^ 2 := by
  fin_cases r <;> simp <;> ring

/-- Thinness: the wall meets each subcube in volume `≲ 3^d ρ h^2`. -/
lemma volume_wall_inter_subbox_le (a : Fin 3 → ℝ) {ℓ ρ : ℝ} (hℓ : 0 < ℓ) (hρ : 0 < ρ)
    {D : ℕ} (hD : 0 < D) (d : ℕ) (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q ≠ 0)
    (hdeg : Q.totalDegree ≤ d)
    (q : Fin 3 → Fin D) :
    volume (wall Q a (ℓ / D) D ρ ∩ subbox a ℓ q) ≤
      ENNReal.ofReal ((12000 * 3 ^ d + 6) * ρ * (ℓ / D) ^ 2) := by
  set h : ℝ := ℓ / (D : ℝ) with hhdef
  have hh : 0 < h := div_pos hℓ (Nat.cast_pos.mpr hD)
  set c : Fin 3 → ℝ := fun r => a r + ((q r : ℕ) : ℝ) * h with hc
  have hsubeq : subbox a ℓ q = {x : Space | ∀ i, c i ≤ x i ∧ x i ≤ c i + h} := rfl
  have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  by_cases hρh : ρ ≤ h
  · set w : Fin 3 → Fin 3 → ℝ := fun r i => if i = r then ρ else h with hw
    set lo : Fin 3 → Fin 3 → ℝ := fun r i => if i = r then c i + h - ρ else c i with hlo
    have hw0 : ∀ r i, 0 ≤ w r i := fun r i => by
      simp only [hw]; split_ifs <;> linarith
    have hcov : wall Q a h D ρ ∩ subbox a ℓ q ⊆
        (Metric.thickening ρ {z : Space | MvPolynomial.eval (fun i => z i) Q = 0} ∩
          {x : Space | ∀ i, (WithLp.toLp 2 c : Space) i ≤ x i ∧
            x i ≤ (WithLp.toLp 2 c : Space) i + h}) ∪
        ⋃ r : Fin 3, ({x : Space | ∀ i, c i ≤ x i ∧ x i ≤ c i + w r i} ∪
          {x : Space | ∀ i, lo r i ≤ x i ∧ x i ≤ lo r i + w r i}) := by
      rintro x ⟨hxW, hxS⟩
      rw [hsubeq] at hxS
      simp only [Set.mem_ofPred_eq] at hxS
      rw [wall, Metric.thickening_union] at hxW
      rcases hxW with hx1 | hx2
      · exact Or.inl ⟨hx1, hxS⟩
      · right
        obtain ⟨y, ⟨r, k, hyk⟩, hdist⟩ := Metric.mem_thickening_iff.mp hx2
        have hcoord : |x r - y r| < ρ := by
          have := PiLp.dist_apply_le x y r
          rw [Real.dist_eq] at this
          linarith
        rw [abs_lt] at hcoord
        refine Set.mem_iUnion.mpr ⟨r, ?_⟩
        rcases le_or_gt (k : ℕ) (q r : ℕ) with hkq | hkq
        · left
          intro i
          by_cases hir : i = r
          · subst hir
            simp only [hw, ite_true]
            have : ((k : ℕ) : ℝ) * h ≤ ((q i : ℕ) : ℝ) * h :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hkq) hh.le
            have hci : c i = a i + ((q i : ℕ) : ℝ) * h := rfl
            constructor
            · exact (hxS i).1
            · linarith
          · simp only [hw, hir, ite_false]
            exact hxS i
        · right
          intro i
          by_cases hir : i = r
          · subst hir
            simp only [hw, hlo, ite_true]
            have hk1 : ((q i : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hkq
            have : ((q i : ℕ) : ℝ) * h + h ≤ ((k : ℕ) : ℝ) * h := by nlinarith
            have hci : c i = a i + ((q i : ℕ) : ℝ) * h := rfl
            constructor
            · linarith
            · linarith [(hxS i).2]
          · simp only [hw, hlo, hir, ite_false]
            exact hxS i
    have hY : 0 ≤ ρ * h ^ 2 := by positivity
    have hvolw : ∀ r (lo' : Fin 3 → ℝ),
        volume {x : Space | ∀ i, lo' i ≤ x i ∧ x i ≤ lo' i + w r i} ≤
          ENNReal.ofReal (ρ * h ^ 2) := by
      intro r lo'
      rw [volume_coordBox lo' (w r) (hw0 r)]
      simp only [hw]
      rw [prod_ite_three]
    calc volume (wall Q a (ℓ / D) D ρ ∩ subbox a ℓ q)
        ≤ volume ((Metric.thickening ρ {z : Space | MvPolynomial.eval (fun i => z i) Q = 0} ∩
          {x : Space | ∀ i, (WithLp.toLp 2 c : Space) i ≤ x i ∧
            x i ≤ (WithLp.toLp 2 c : Space) i + h}) ∪
        ⋃ r : Fin 3, ({x : Space | ∀ i, c i ≤ x i ∧ x i ≤ c i + w r i} ∪
          {x : Space | ∀ i, lo r i ≤ x i ∧ x i ≤ lo r i + w r i})) := measure_mono hcov
      _ ≤ volume (Metric.thickening ρ {z : Space | MvPolynomial.eval (fun i => z i) Q = 0} ∩
          {x : Space | ∀ i, (WithLp.toLp 2 c : Space) i ≤ x i ∧
            x i ≤ (WithLp.toLp 2 c : Space) i + h}) +
          ∑ r : Fin 3, (volume {x : Space | ∀ i, c i ≤ x i ∧ x i ≤ c i + w r i} +
            volume {x : Space | ∀ i, lo r i ≤ x i ∧ x i ≤ lo r i + w r i}) := by
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (12000 * 3 ^ d * ρ * h ^ 2) +
          ∑ r : Fin 3, (ENNReal.ofReal (ρ * h ^ 2) + ENNReal.ofReal (ρ * h ^ 2)) := by
          refine add_le_add ?_
            (Finset.sum_le_sum fun r _ => add_le_add (hvolw r c) (hvolw r (lo r)))
          exact Wongkew.volume_thickening_zeroSet_cube_le d Q hQ hdeg _ hρ hρh
      _ = ENNReal.ofReal ((12000 * 3 ^ d + 6) * ρ * (ℓ / D) ^ 2) := by
          rw [Fin.sum_univ_three, ← ENNReal.ofReal_add hY hY,
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [← hhdef]
          ring
  · push Not at hρh
    calc volume (wall Q a (ℓ / D) D ρ ∩ subbox a ℓ q) ≤ volume (subbox a ℓ q) :=
          measure_mono Set.inter_subset_right
      _ = ENNReal.ofReal (h * h * h) := volume_box_eq _ hh.le
      _ ≤ ENNReal.ofReal ((12000 * 3 ^ d + 6) * ρ * (ℓ / D) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← hhdef]
          have h2 : 0 ≤ h ^ 2 := by positivity
          have e1 : h * h * h ≤ ρ * h ^ 2 := by
            have : h * h * h = h * h ^ 2 := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right hρh.le h2
          have e2 : ρ * h ^ 2 ≤ (12000 * 3 ^ d + 6) * ρ * h ^ 2 := by
            have h0 : 0 ≤ ρ * h ^ 2 := by positivity
            have : (12000 * 3 ^ d + 6) * ρ * h ^ 2 = (12000 * 3 ^ d + 6) * (ρ * h ^ 2) := by ring
            rw [this]
            nlinarith
          linarith

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

open SplitAux in
/-- One step of the grains recursion. -/
theorem split_step (p : ℕ) (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) (A : Set Space)
    (hA : MeasurableSet A) (a : Fin 3 → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hAQ : A ⊆ box a ℓ) :
    ∃ (C : (Fin (3 * p) → Bool) × (Fin 3 → Fin (2 ^ p)) → Set Space)
      (L : (Fin 3 → Fin (2 ^ p)) → Set Space),
      (∀ i, MeasurableSet (C i) ∧ C i ⊆ A ∧ C i ⊆ subbox a ℓ i.2) ∧
      (∀ q, MeasurableSet (L q) ∧ L q ⊆ A ∧ L q ⊆ subbox a ℓ q) ∧
      (Pairwise fun i j => Disjoint (C i) (C j)) ∧
      (Pairwise fun q q' => Disjoint (L q) (L q')) ∧
      (∀ i q, Disjoint (C i) (L q)) ∧
      A = (⋃ i, C i) ∪ ⋃ q, L q ∧
      (∀ i, ((2 : ENNReal) ^ p) ^ 3 * volume (C i) ≤ volume A) ∧
      (∀ q, volume (L q) ≤ ENNReal.ofReal (Kthin (2 ^ p) * δ * (ℓ / 2 ^ p) ^ 2)) ∧
      (∀ x v : Space, ‖v‖ ≤ 1 →
        ({i | (Metric.thickening δ (segment ℝ x (x + v)) ∩ C i).Nonempty}.ncard : ℝ) ≤
          20 * 2 ^ p) ∧
      (∀ x v : Space, ‖v‖ ≤ 1 → δ ≤ ℓ / 2 ^ p →
        ({q | (Metric.thickening δ (segment ℝ x (x + v)) ∩ L q).Nonempty}.ncard : ℝ) ≤
          400 * 2 ^ p) := by
  classical
  have hD : 0 < 2 ^ p := pow_pos (by norm_num) p
  have hDR : ((2 ^ p : ℕ) : ℝ) = (2 : ℝ) ^ p := by push_cast; ring
  set h : ℝ := ℓ / ((2 ^ p : ℕ) : ℝ) with hhdef
  -- `volume.restrict A` is a finite measure, absolutely continuous w.r.t. `volume`
  have hAfin : volume A < ⊤ :=
    calc volume A ≤ volume (box a ℓ) := measure_mono hAQ
      _ = ENNReal.ofReal (ℓ * ℓ * ℓ) := volume_box_eq a hℓ.le
      _ < ⊤ := ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (volume.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAfin⟩
  have hμ : volume.restrict A ≪ volume :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  obtain ⟨P, hP0, hPdeg, hPμ, -⟩ := guth_katz_partitioning_ac (volume.restrict A) hμ (3 * p)
  -- degree budget
  have hS : ∑ j, (P j).totalDegree ≤ 12 * 2 ^ p := by
    have h1 := sum_totalDegree_cube_le (3 * p) P hPdeg
    have h2 : 1600 * 2 ^ (3 * p) ≤ (12 * 2 ^ p) ^ 3 := by
      rw [mul_pow, ← pow_mul, mul_comm p 3]
      exact Nat.mul_le_mul_right _ (by norm_num)
    exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num)).mp (h1.trans h2)
  have hQ0 : (∏ j, P j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hP0 j
  have hQdeg : (∏ j, P j).totalDegree ≤ 12 * 2 ^ p :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans hS
  set W : Set Space := wall (∏ j, P j) a h (2 ^ p) (100 * δ) with hW
  have hWmeas : MeasurableSet W := Metric.isOpen_thickening.measurableSet
  have hsubbox : ∀ x ∈ A, x ∈ subbox a ℓ (idx a h hD x) := fun x hx =>
    idx_mem_subbox a hℓ hD (hAQ hx)
  refine ⟨child A W P a h hD, leaf A W a h hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- children: measurable, in `A`, in their subcube
    intro i
    refine ⟨?_, fun x hx => hx.1, fun x hx => ?_⟩
    · exact hA.inter (hWmeas.compl.inter
        ((measurableSet_sgn_eq P i.1).inter (measurableSet_idx_eq a h hD i.2)))
    · rw [← hx.2.2.2]
      exact hsubbox x hx.1
  · -- leaves: measurable, in `A`, in their subcube
    intro q
    refine ⟨?_, fun x hx => hx.1, fun x hx => ?_⟩
    · exact hA.inter (hWmeas.inter (measurableSet_idx_eq a h hD q))
    · rw [← hx.2.2]
      exact hsubbox x hx.1
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact hij (Prod.ext (hxi.2.2.1.symm.trans hxj.2.2.1) (hxi.2.2.2.symm.trans hxj.2.2.2))
  · intro q q' hqq
    rw [Set.disjoint_left]
    intro x hxq hxq'
    exact hqq (hxq.2.2.symm.trans hxq'.2.2)
  · intro i q
    rw [Set.disjoint_left]
    intro x hxi hxq
    exact hxi.2.1 hxq.2.1
  · apply Set.Subset.antisymm
    · intro x hxA
      by_cases hxW : x ∈ W
      · exact Or.inr (Set.mem_iUnion.mpr ⟨idx a h hD x, hxA, hxW, rfl⟩)
      · exact Or.inl (Set.mem_iUnion.mpr ⟨(sgn P x, idx a h hD x), hxA, hxW, rfl, rfl⟩)
    · exact Set.union_subset (Set.iUnion_subset fun i x hx => hx.1)
        (Set.iUnion_subset fun q x hx => hx.1)
  · -- mass of the children
    intro i
    have hcell := hPμ i.1
    rw [Measure.restrict_apply_univ, Measure.restrict_apply' hA] at hcell
    refine le_trans ?_ hcell
    rw [← pow_mul, mul_comm p 3]
    refine mul_le_mul_right (measure_mono ?_) _
    intro x hx
    obtain ⟨hxA, hxW, hxs, -⟩ := hx
    refine ⟨fun j => ?_, hxA⟩
    have hne : MvPolynomial.eval (fun i => x i) (P j) ≠ 0 := fun h0 =>
      hxW (Metric.self_subset_thickening (by positivity) _
        (Or.inl ((mem_zeroSet_prod P).mpr ⟨j, h0⟩)))
    rw [← hxs]
    simp only [sgn]
    by_cases hpos : 0 < MvPolynomial.eval (fun i => x i) (P j)
    · simp [hpos]
    · simp only [hpos, decide_false, Bool.false_eq_true, ite_false]
      exact lt_of_le_of_ne (not_lt.mp hpos) hne
  · -- thinness of the leaves
    intro q
    calc volume (leaf A W a h hD q) ≤ volume (W ∩ subbox a ℓ q) := by
          refine measure_mono fun x hx => ⟨hx.2.1, ?_⟩
          rw [← hx.2.2]
          exact hsubbox x hx.1
      _ ≤ ENNReal.ofReal ((12000 * 3 ^ (12 * 2 ^ p) + 6) * (100 * δ) *
            (ℓ / ((2 ^ p : ℕ) : ℝ)) ^ 2) :=
          volume_wall_inter_subbox_le a hℓ (by positivity) hD _ _ hQ0 hQdeg q
      _ ≤ ENNReal.ofReal (Kthin (2 ^ p) * δ * (ℓ / 2 ^ p) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hDR, Kthin]
          have h3 : (1 : ℝ) ≤ 3 ^ (12 * 2 ^ p) := one_le_pow₀ (by norm_num)
          have hpos : 0 ≤ δ * (ℓ / 2 ^ p) ^ 2 := by positivity
          nlinarith
  · -- a tube meets few children
    intro x v _
    have h1 := child_ncard_le A P a hℓ hδ hD hAQ x v
    have h2 : (∑ j, (P j).totalDegree) + 3 * (2 ^ p + 1) + 1 ≤ 20 * 2 ^ p := by
      have : 1 ≤ 2 ^ p := hD
      omega
    exact_mod_cast h1.trans h2
  · -- a tube meets few leaves
    intro x v hv hδℓ
    have hsub :
        {q | (Metric.thickening δ (segment ℝ x (x + v)) ∩ leaf A W a h hD q).Nonempty} ⊆
        {q | (Metric.thickening δ (segment ℝ x (x + v)) ∩ subbox a ℓ q).Nonempty} := by
      rintro q ⟨y, hy1, hy2⟩
      refine ⟨y, hy1, ?_⟩
      rw [← hy2.2.2]
      exact hsubbox y hy2.1
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := tube_subbox_ncard a hδ (D := 2 ^ p) hD (by rw [hDR]; exact hδℓ) x v hv
    refine le_trans (Nat.cast_le.mpr h1) (h2.trans_eq ?_)
    rw [hDR]

namespace RecAux

/-- Index of the children produced by one split step. -/
abbrev I (p : ℕ) := (Fin (3 * p) → Bool) × (Fin 3 → Fin (2 ^ p))

/-- Index of the subcubes (leaves) of one split step. -/
abbrev Q (p : ℕ) := Fin 3 → Fin (2 ^ p)

/-- The properties of the data provided by `split_step`. -/
def StepProp (p : ℕ) (δ : ℝ) (A : Set Space) (a : Fin 3 → ℝ) (ℓ : ℝ)
    (C : I p → Set Space) (L : Q p → Set Space) : Prop :=
  (∀ i, MeasurableSet (C i) ∧ C i ⊆ A ∧ C i ⊆ subbox a ℓ i.2) ∧
  (∀ q, MeasurableSet (L q) ∧ L q ⊆ A ∧ L q ⊆ subbox a ℓ q) ∧
  (Pairwise fun i j => Disjoint (C i) (C j)) ∧
  (Pairwise fun q q' => Disjoint (L q) (L q')) ∧
  (∀ i q, Disjoint (C i) (L q)) ∧
  A = (⋃ i, C i) ∪ ⋃ q, L q ∧
  (∀ i, ((2 : ENNReal) ^ p) ^ 3 * volume (C i) ≤ volume A) ∧
  (∀ q, volume (L q) ≤ ENNReal.ofReal (Kthin (2 ^ p) * δ * (ℓ / 2 ^ p) ^ 2)) ∧
  (∀ x v : Space, ‖v‖ ≤ 1 →
    ({i | (Metric.thickening δ (segment ℝ x (x + v)) ∩ C i).Nonempty}.ncard : ℝ) ≤
      20 * 2 ^ p) ∧
  (∀ x v : Space, ‖v‖ ≤ 1 → δ ≤ ℓ / 2 ^ p →
    ({q | (Metric.thickening δ (segment ℝ x (x + v)) ∩ L q).Nonempty}.ncard : ℝ) ≤
      400 * 2 ^ p)

open Classical in
/-- The (chosen) data of one split step, or empty data when the hypotheses fail. -/
noncomputable def step (p : ℕ) (δ : ℝ) (A : Set Space) (a : Fin 3 → ℝ) (ℓ : ℝ) :
    (I p → Set Space) × (Q p → Set Space) :=
  if h : 1 ≤ p ∧ 0 < δ ∧ MeasurableSet A ∧ 0 < ℓ ∧ A ⊆ box a ℓ then
    ((split_step p h.1 h.2.1 A h.2.2.1 a h.2.2.2.1 h.2.2.2.2).choose,
      (split_step p h.1 h.2.1 A h.2.2.1 a h.2.2.2.1 h.2.2.2.2).choose_spec.choose)
  else (fun _ => ∅, fun _ => ∅)

theorem step_spec {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) {A : Set Space}
    (hA : MeasurableSet A) {a : Fin 3 → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hAQ : A ⊆ box a ℓ) :
    StepProp p δ A a ℓ (step p δ A a ℓ).1 (step p δ A a ℓ).2 := by
  have h : 1 ≤ p ∧ 0 < δ ∧ MeasurableSet A ∧ 0 < ℓ ∧ A ⊆ box a ℓ := ⟨hp, hδ, hA, hℓ, hAQ⟩
  rw [step, dite_eq_left h]
  exact (split_step p h.1 h.2.1 A h.2.2.1 a h.2.2.2.1 h.2.2.2.2).choose_spec.choose_spec

/-- Side of the cubes at level `t`. -/
noncomputable def scale (p t : ℕ) : ℝ := 2 / ((2 : ℝ) ^ p) ^ t

/-- Corner of the subcube `q`. -/
noncomputable def subc (p : ℕ) (a : Fin 3 → ℝ) (ℓ : ℝ) (q : Q p) : Fin 3 → ℝ :=
  fun r => a r + ((q r : ℕ) : ℝ) * (ℓ / 2 ^ p)

theorem subbox_eq (p : ℕ) (a : Fin 3 → ℝ) (ℓ : ℝ) (q : Q p) :
    subbox a ℓ q = box (subc p a ℓ q) (ℓ / 2 ^ p) := by
  simp [subbox]
  rfl

theorem scale_pos (p t : ℕ) : 0 < scale p t := by
  unfold scale; positivity

theorem scale_succ (p t : ℕ) : scale p (t + 1) = scale p t / 2 ^ p := by
  unfold scale; rw [pow_succ, div_div]

theorem scale_le_two (p t : ℕ) : scale p t ≤ 2 := by
  unfold scale
  have : (1 : ℝ) ≤ ((2 : ℝ) ^ p) ^ t := one_le_pow₀ (one_le_pow₀ (by norm_num))
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem scale_anti (p : ℕ) {t t' : ℕ} (h : t ≤ t') : scale p t' ≤ scale p t := by
  unfold scale
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) h

theorem box_subset_closedBall (a : Fin 3 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    box a s ⊆ Metric.closedBall (WithLp.toLp 2 a : Space) (2 * s) := by
  intro x hx
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq]
  have h : ∀ i, dist (x i) ((WithLp.toLp 2 a : Space) i) ^ 2 ≤ s ^ 2 := by
    intro i
    have h1 := hx i
    have h2 : |x i - a i| ≤ s := abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have h3 : dist (x i) ((WithLp.toLp 2 a : Space) i) = |x i - a i| := Real.dist_eq _ _
    rw [h3]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  calc √(∑ i, dist (x i) ((WithLp.toLp 2 a : Space) i) ^ 2) ≤ √((2 * s) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [Fin.sum_univ_three]
        nlinarith [h 0, h 1, h 2]
    _ = 2 * s := Real.sqrt_sq (by linarith)

theorem volume_box_eq (a : Fin 3 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    volume (box a s) = ENNReal.ofReal (s ^ 3) := by
  have : box a s = (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹' Set.Icc a (fun i => a i + s) := by
    ext x
    simp only [box, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def, forall_and]
  rw [this, Wongkew.CountAux.volume_box]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hs]

theorem ball_subset_box : Metric.ball (0 : Space) 1 ⊆ box (fun _ => -1) 2 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  intro i
  have h1 := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at h1
  have h2 := abs_le.1 (h1.trans hx.le)
  constructor <;> linarith [h2.1, h2.2]

theorem ncard_setOf_eq_card {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    {a | P a}.ncard = (Finset.univ.filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp

/-- The pieces of level `t` of the recursion, with the corners of their cubes. -/
noncomputable def node (p : ℕ) (δ : ℝ) (E : Set Space) :
    (t : ℕ) → (Fin t → I p) → Set Space × (Fin 3 → ℝ)
  | 0, _ => (E, fun _ => -1)
  | t + 1, σ =>
    ((step p δ (node p δ E t (Fin.tail σ)).1 (node p δ E t (Fin.tail σ)).2 (scale p t)).1 (σ 0),
      subc p (node p δ E t (Fin.tail σ)).2 (scale p t) (σ 0).2)

/-- The leaves produced at level `t`. -/
noncomputable def leaf (p : ℕ) (δ : ℝ) (E : Set Space) (t : ℕ) (σ : Fin t → I p) (q : Q p) :
    Set Space :=
  (step p δ (node p δ E t σ).1 (node p δ E t σ).2 (scale p t)).2 q

theorem node_succ (p : ℕ) (δ : ℝ) (E : Set Space) (t : ℕ) (σ : Fin (t + 1) → I p) :
    node p δ E (t + 1) σ =
      ((step p δ (node p δ E t (Fin.tail σ)).1 (node p δ E t (Fin.tail σ)).2 (scale p t)).1 (σ 0),
        subc p (node p δ E t (Fin.tail σ)).2 (scale p t) (σ 0).2) := rfl

theorem node_cons (p : ℕ) (δ : ℝ) (E : Set Space) (t : ℕ) (i : I p) (τ : Fin t → I p) :
    node p δ E (t + 1) (Fin.cons i τ) =
      ((step p δ (node p δ E t τ).1 (node p δ E t τ).2 (scale p t)).1 i,
        subc p (node p δ E t τ).2 (scale p t) i.2) := by
  rw [node_succ, Fin.tail_cons, Fin.cons_zero]

/-- Hypotheses of the recursion. -/
structure Hyp (p : ℕ) (δ : ℝ) (E : Set Space) : Prop where
  hp : 1 ≤ p
  hδ : 0 < δ
  hE : MeasurableSet E
  hEb : E ⊆ box (fun _ => -1) 2

section
variable {p : ℕ} {δ : ℝ} {E : Set Space}

theorem node_props (H : Hyp p δ E) (t : ℕ) : ∀ σ : Fin t → I p,
    MeasurableSet (node p δ E t σ).1 ∧ (node p δ E t σ).1 ⊆ box (node p δ E t σ).2 (scale p t) ∧
    (node p δ E t σ).1 ⊆ E ∧
    (((2 : ENNReal) ^ p) ^ 3) ^ t * volume (node p δ E t σ).1 ≤ volume E := by
  induction t with
  | zero =>
    intro σ
    refine ⟨H.hE, ?_, subset_rfl, ?_⟩
    · have : scale p 0 = 2 := by simp [scale]
      rw [this]
      exact H.hEb
    · simp [node]
  | succ t ih =>
    intro σ
    obtain ⟨h1, h2, h3, h4⟩ := ih (Fin.tail σ)
    obtain ⟨hC, -, -, -, -, -, hvol, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
    rw [node_succ]
    refine ⟨(hC (σ 0)).1, ?_, (hC (σ 0)).2.1.trans h3, ?_⟩
    · have := (hC (σ 0)).2.2
      rwa [subbox_eq, ← scale_succ] at this
    · calc (((2 : ENNReal) ^ p) ^ 3) ^ (t + 1) *
            volume ((step p δ (node p δ E t (Fin.tail σ)).1 (node p δ E t (Fin.tail σ)).2
              (scale p t)).1 (σ 0))
          = (((2 : ENNReal) ^ p) ^ 3) ^ t * (((2 : ENNReal) ^ p) ^ 3 *
            volume ((step p δ (node p δ E t (Fin.tail σ)).1 (node p δ E t (Fin.tail σ)).2
              (scale p t)).1 (σ 0))) := by
            rw [pow_succ, mul_assoc]
        _ ≤ (((2 : ENNReal) ^ p) ^ 3) ^ t * volume (node p δ E t (Fin.tail σ)).1 := by
            gcongr
            exact hvol (σ 0)
        _ ≤ volume E := h4

theorem node_disj (H : Hyp p δ E) (t : ℕ) :
    Pairwise fun σ τ : Fin t → I p => Disjoint (node p δ E t σ).1 (node p δ E t τ).1 := by
  induction t with
  | zero => intro σ τ h; exact absurd (Subsingleton.elim σ τ) h
  | succ t ih =>
    intro σ τ hστ
    obtain ⟨h1, h2, -, -⟩ := node_props H t (Fin.tail σ)
    obtain ⟨h1', h2', -, -⟩ := node_props H t (Fin.tail τ)
    have hS := step_spec H.hp H.hδ h1 (scale_pos p t) h2
    have hS' := step_spec H.hp H.hδ h1' (scale_pos p t) h2'
    show Disjoint (node p δ E (t + 1) σ).1 (node p δ E (t + 1) τ).1
    rw [node_succ, node_succ]
    by_cases htail : Fin.tail σ = Fin.tail τ
    · have h0 : σ 0 ≠ τ 0 := by
        intro h0
        apply hστ
        rw [← Fin.cons_self_tail σ, ← Fin.cons_self_tail τ, h0, htail]
      rw [← htail]
      exact hS.2.2.1 h0
    · exact (ih htail).mono (hS.1 (σ 0)).2.1 (hS'.1 (τ 0)).2.1

theorem mass_step (H : Hyp p δ E) (t : ℕ) (τ : Fin t → I p) :
    volume (node p δ E t τ).1 =
      ∑ i, volume (node p δ E (t + 1) (Fin.cons i τ)).1 + ∑ q, volume (leaf p δ E t τ q) := by
  obtain ⟨h1, h2, -, -⟩ := node_props H t τ
  obtain ⟨hC, hL, hCd, hLd, hCL, hU, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
  simp only [node_cons, leaf]
  conv_lhs => rw [hU]
  rw [measure_union (Set.disjoint_iUnion_left.2 fun i => Set.disjoint_iUnion_right.2 fun q =>
      hCL i q) (MeasurableSet.iUnion fun q => (hL q).1), measure_iUnion hCd (fun i => (hC i).1),
    measure_iUnion hLd (fun q => (hL q).1), tsum_fintype, tsum_fintype]

theorem mass_eq (H : Hyp p δ E) (t : ℕ) :
    volume E = ∑ σ : Fin t → I p, volume (node p δ E t σ).1 +
      ∑ t' ∈ Finset.range t, ∑ σ : Fin t' → I p, ∑ q, volume (leaf p δ E t' σ q) := by
  induction t with
  | zero => simp [node]
  | succ t ih =>
    rw [ih, Finset.sum_range_succ]
    have key : ∑ σ : Fin t → I p, volume (node p δ E t σ).1 =
        ∑ σ : Fin (t + 1) → I p, volume (node p δ E (t + 1) σ).1 +
          ∑ σ : Fin t → I p, ∑ q, volume (leaf p δ E t σ q) := by
      rw [Finset.sum_congr rfl (fun τ _ => mass_step H t τ), Finset.sum_add_distrib]
      congr 1
      have := Fintype.sum_equiv (Fin.consEquiv fun _ => I p)
        (fun y => volume (node p δ E (t + 1) (Fin.cons y.1 y.2)).1)
        (fun σ => volume (node p δ E (t + 1) σ).1) (fun y => rfl)
      rw [← this, Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [key]
    ring

theorem card_fiber_le {α β : Type*} [Fintype α] [DecidableEq β]
    (P : α → Prop) [DecidablePred P] (f : α → β) (S : Finset β) (c : ℝ)
    (hS : ∀ a, P a → f a ∈ S)
    (hfib : ∀ b ∈ S, ((Finset.univ.filter fun a => P a ∧ f a = b).card : ℝ) ≤ c) :
    ((Finset.univ.filter P).card : ℝ) ≤ S.card * c := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S) (fun a ha => hS a (by simpa using ha))]
  push_cast
  calc ∑ b ∈ S, (((Finset.univ.filter P).filter fun a => f a = b).card : ℝ) ≤ ∑ b ∈ S, c := by
        apply Finset.sum_le_sum
        intro b hb
        rw [Finset.filter_filter]
        exact hfib b hb
    _ = S.card * c := by rw [Finset.sum_const, nsmul_eq_mul]

theorem node_tube (H : Hyp p δ E) (x v : Space) (hv : ‖v‖ ≤ 1) (t : ℕ) :
    ({σ : Fin t → I p | (Metric.thickening δ (segment ℝ x (x + v)) ∩
      (node p δ E t σ).1).Nonempty}.ncard : ℝ) ≤ (20 * 2 ^ p) ^ t := by
  classical
  induction t with
  | zero =>
    rw [pow_zero]
    have : {σ : Fin 0 → I p | (Metric.thickening δ (segment ℝ x (x + v)) ∩
        (node p δ E 0 σ).1).Nonempty}.ncard ≤ 1 := by
      calc _ ≤ (Set.univ : Set (Fin 0 → I p)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
        _ = 1 := by rw [Set.ncard_univ]; simp
    exact_mod_cast this
  | succ t ih =>
    rw [ncard_setOf_eq_card] at ih ⊢
    calc _ ≤ ((Finset.univ.filter fun τ : Fin t → I p =>
            (Metric.thickening δ (segment ℝ x (x + v)) ∩ (node p δ E t τ).1).Nonempty).card : ℝ) *
            (20 * 2 ^ p) := by
          apply card_fiber_le _ Fin.tail
          · intro σ hσ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            obtain ⟨h1, h2, -, -⟩ := node_props H t (Fin.tail σ)
            obtain ⟨hC, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
            rw [node_succ] at hσ
            exact hσ.mono (Set.inter_subset_inter_right _ (hC (σ 0)).2.1)
          · intro τ _
            obtain ⟨h1, h2, -, -⟩ := node_props H t τ
            obtain ⟨-, -, -, -, -, -, -, -, htC, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
            have hc := htC x v hv
            rw [ncard_setOf_eq_card] at hc
            refine le_trans ?_ hc
            have hsub : (Finset.univ.filter fun σ : Fin (t + 1) → I p =>
                (Metric.thickening δ (segment ℝ x (x + v)) ∩ (node p δ E (t + 1) σ).1).Nonempty ∧
                  Fin.tail σ = τ) ⊆
                (Finset.univ.filter fun i => (Metric.thickening δ (segment ℝ x (x + v)) ∩
                  (step p δ (node p δ E t τ).1 (node p δ E t τ).2 (scale p t)).1 i).Nonempty).image
                  (fun i => (Fin.cons i τ : Fin (t + 1) → I p)) := by
              intro σ hσ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
              obtain ⟨hσ1, hσ2⟩ := hσ
              rw [Finset.mem_image]
              refine ⟨σ 0, ?_, ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [node_succ, hσ2] at hσ1
                exact hσ1
              · rw [← hσ2, Fin.cons_self_tail]
            exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
      _ ≤ (20 * 2 ^ p) ^ t * (20 * 2 ^ p) := by gcongr
      _ = (20 * 2 ^ p) ^ (t + 1) := (pow_succ _ _).symm

theorem leaf_props (H : Hyp p δ E) (t : ℕ) (σ : Fin t → I p) (q : Q p) :
    MeasurableSet (leaf p δ E t σ q) ∧ leaf p δ E t σ q ⊆ (node p δ E t σ).1 ∧
    leaf p δ E t σ q ⊆ box (subc p (node p δ E t σ).2 (scale p t) q) (scale p (t + 1)) ∧
    volume (leaf p δ E t σ q) ≤ ENNReal.ofReal (Kthin (2 ^ p) * δ * scale p (t + 1) ^ 2) := by
  obtain ⟨h1, h2, -, -⟩ := node_props H t σ
  obtain ⟨-, hL, -, -, -, -, -, hthin, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
  refine ⟨(hL q).1, (hL q).2.1, ?_, ?_⟩
  · have := (hL q).2.2
    rwa [subbox_eq, ← scale_succ] at this
  · rw [scale_succ]
    exact hthin q

theorem leaf_disj (H : Hyp p δ E) (t : ℕ) :
    Pairwise fun y z : (Fin t → I p) × Q p =>
      Disjoint (leaf p δ E t y.1 y.2) (leaf p δ E t z.1 z.2) := by
  intro y z hyz
  by_cases h : y.1 = z.1
  · have hq : y.2 ≠ z.2 := fun h' => hyz (Prod.ext h h')
    obtain ⟨h1, h2, -, -⟩ := node_props H t y.1
    obtain ⟨-, -, -, hLd, -⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
    show Disjoint (leaf p δ E t y.1 y.2) (leaf p δ E t z.1 z.2)
    unfold leaf
    rw [← h]
    exact hLd hq
  · exact (node_disj H t h).mono (leaf_props H t y.1 y.2).2.1 (leaf_props H t z.1 z.2).2.1

theorem leaf_tube (H : Hyp p δ E) (x v : Space) (hv : ‖v‖ ≤ 1) (t : ℕ)
    (hδt : δ ≤ scale p (t + 1)) :
    ({y : (Fin t → I p) × Q p | (Metric.thickening δ (segment ℝ x (x + v)) ∩
      leaf p δ E t y.1 y.2).Nonempty}.ncard : ℝ) ≤ (20 * 2 ^ p) ^ t * (400 * 2 ^ p) := by
  classical
  have ih := node_tube H x v hv t
  rw [ncard_setOf_eq_card] at ih ⊢
  calc _ ≤ ((Finset.univ.filter fun τ : Fin t → I p =>
          (Metric.thickening δ (segment ℝ x (x + v)) ∩ (node p δ E t τ).1).Nonempty).card : ℝ) *
          (400 * 2 ^ p) := by
        apply card_fiber_le _ Prod.fst
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hy.mono (Set.inter_subset_inter_right _ (leaf_props H t y.1 y.2).2.1)
        · intro τ _
          obtain ⟨h1, h2, -, -⟩ := node_props H t τ
          obtain ⟨-, -, -, -, -, -, -, -, -, htL⟩ := step_spec H.hp H.hδ h1 (scale_pos p t) h2
          have hc := htL x v hv (by rw [← scale_succ]; exact hδt)
          rw [ncard_setOf_eq_card] at hc
          refine le_trans ?_ hc
          have hsub : (Finset.univ.filter fun y : (Fin t → I p) × Q p =>
              (Metric.thickening δ (segment ℝ x (x + v)) ∩ leaf p δ E t y.1 y.2).Nonempty ∧
                y.1 = τ) ⊆
              (Finset.univ.filter fun q => (Metric.thickening δ (segment ℝ x (x + v)) ∩
                (step p δ (node p δ E t τ).1 (node p δ E t τ).2 (scale p t)).2 q).Nonempty).image
                (fun q => (τ, q)) := by
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            obtain ⟨hy1, hy2⟩ := hy
            rw [Finset.mem_image]
            refine ⟨y.2, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              unfold leaf at hy1
              rw [hy2] at hy1
              exact hy1
            · rw [← hy2]
          exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ (20 * 2 ^ p) ^ t * (400 * 2 ^ p) := by gcongr

end

/-- Selection of a dyadic mass class among the pieces of one level, and enumeration. -/
theorem select {ι : Type*} [Fintype ι] (P : ι → Set Space) (c : ι → Space)
    {E : Set Space} {ε δ s K : ℝ} (hK : 0 < K) (hδ : 0 < δ) (k₀ N : ℕ) (hk₀ : 1 ≤ k₀)
    (hmeas : ∀ i, MeasurableSet (P i)) (hsubE : ∀ i, P i ⊆ E)
    (hball : ∀ i, P i ⊆ Metric.closedBall (c i) (2 * s))
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j))
    (hthin : ∀ i, volume (P i) ≤ ENNReal.ofReal (K * δ * s ^ 2))
    (hup : ∀ i, volume (P i) ≤ ENNReal.ofReal (K * s ^ 3) * volume E)
    (htube : ∀ x v : Space, ‖v‖ ≤ 1 →
      ({i | (Metric.thickening δ (segment ℝ x (x + v)) ∩ P i).Nonempty}.ncard : ℝ) ≤
        K * δ ^ (-ε) / s)
    (hcard : 2 * Fintype.card ι ≤ 2 ^ k₀)
    (hEfin : volume E ≠ ⊤)
    (hmass : volume E ≤ (N : ENNReal) * ∑ i, volume (P i))
    (hN : (2 * k₀ * N : ℝ) ≤ K * δ ^ (-ε)) :
    ∃ (m : ℝ) (G : ℕ) (P' : Fin G → Set Space) (c' : Fin G → Space),
      0 ≤ m ∧
      (∀ j, MeasurableSet (P' j) ∧ P' j ⊆ E ∧ P' j ⊆ Metric.closedBall (c' j) (2 * s)) ∧
      (Pairwise fun j k => Disjoint (P' j) (P' k)) ∧
      (∀ j, ENNReal.ofReal m ≤ volume (P' j) ∧ volume (P' j) ≤ ENNReal.ofReal (2 * m)) ∧
      (∀ j, volume (P' j) ≤ ENNReal.ofReal (K * δ * s ^ 2)) ∧
      ENNReal.ofReal (δ ^ ε / K) * volume E ≤ ∑ j, volume (P' j) ∧
      ENNReal.ofReal m ≤ ENNReal.ofReal (K * s ^ 3) * volume E ∧
      ∀ x v : Space, ‖v‖ ≤ 1 →
        ({j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ P' j).Nonempty}.ncard : ℝ) ≤
          K * δ ^ (-ε) / s := by
  classical
  -- real weights
  have hfin : ∀ i, volume (P i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hEfin (measure_mono (hsubE i))
  set w : ι → ℝ := fun i => (volume (P i)).toReal with hw_def
  have hw : ∀ i, volume (P i) = ENNReal.ofReal (w i) := fun i =>
    (ENNReal.ofReal_toReal (hfin i)).symm
  have hw0 : ∀ i, 0 ≤ w i := fun i => ENNReal.toReal_nonneg
  set F : ℝ := ∑ i, w i with hF_def
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => hw0 i
  have hwF : ∀ i, w i ≤ F := fun i =>
    Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)
  have hsumP : ∀ S : Finset ι, ∑ i ∈ S, volume (P i) = ENNReal.ofReal (∑ i ∈ S, w i) := by
    intro S
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i)]
    exact Finset.sum_congr rfl fun i _ => hw i
  -- the big pieces carry at least half of the mass
  set Sb := Finset.univ.filter fun i => F / 2 ^ k₀ < w i with hSb_def
  have hSb : F / 2 ≤ ∑ i ∈ Sb, w i := by
    have h1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => F / 2 ^ k₀ < w i) w
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ F / 2 ^ k₀ < w i), w i ≤
        Fintype.card ι * (F / 2 ^ k₀) := by
      calc _ ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ F / 2 ^ k₀ < w i), F / 2 ^ k₀ :=
            Finset.sum_le_sum fun i hi => not_lt.1 (Finset.mem_filter.1 hi).2
        _ = (Finset.univ.filter (fun i => ¬ F / 2 ^ k₀ < w i)).card * (F / 2 ^ k₀) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Fintype.card ι * (F / 2 ^ k₀) := by
            gcongr
            exact_mod_cast Finset.card_le_univ _
    have h3 : (Fintype.card ι : ℝ) * (F / 2 ^ k₀) ≤ F / 2 := by
      have h4 : (2 * Fintype.card ι : ℝ) ≤ 2 ^ k₀ := by exact_mod_cast hcard
      have h5 : (0 : ℝ) < 2 ^ k₀ := by positivity
      rw [mul_div_assoc', div_le_div_iff₀ h5 (by norm_num)]
      nlinarith
    linarith
  -- dyadic classes of the big pieces
  have hbig : ∀ i ∈ Sb, F / 2 ^ (k₀ - 1 + 1) < w i := by
    intro i hi
    rw [Nat.sub_add_cancel hk₀]
    exact (Finset.mem_filter.1 hi).2
  let cls : ι → ℕ := fun i => if h : ∃ k : ℕ, F / 2 ^ (k + 1) < w i then Nat.find h else 0
  have hcls : ∀ i ∈ Sb, cls i < k₀ ∧ F / 2 ^ (cls i + 1) < w i ∧ w i ≤ F / 2 ^ cls i := by
    intro i hi
    have h : ∃ k : ℕ, F / 2 ^ (k + 1) < w i := ⟨k₀ - 1, hbig i hi⟩
    have hc : cls i = Nat.find h := dite_eq_left h
    rw [hc]
    refine ⟨?_, Nat.find_spec h, ?_⟩
    · have := Nat.find_min' h (hbig i hi)
      omega
    · rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
      · rw [h0, pow_zero, div_one]
        exact hwF i
      · have := Nat.find_min h (show Nat.find h - 1 < Nat.find h by omega)
        rw [Nat.sub_add_cancel hpos] at this
        exact not_lt.1 this
  have hk₀R : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  obtain ⟨k, -, hkS⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (s := Sb) (t := Finset.range k₀) (f := cls) (w := w) (b := F / (2 * k₀))
    (fun i hi => Finset.mem_range.2 (hcls i hi).1) ⟨0, Finset.mem_range.2 hk₀⟩
    (by
      rw [Finset.card_range, nsmul_eq_mul]
      calc (k₀ : ℝ) * (F / (2 * k₀)) = F / 2 := by field_simp
        _ ≤ _ := hSb)
  set S := Sb.filter fun i => cls i = k with hS_def
  set m : ℝ := F / 2 ^ (k + 1) with hm_def
  have hSprop : ∀ i ∈ S, m < w i ∧ w i ≤ 2 * m := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨-, h1, h2⟩ := hcls i hi1
    rw [hi2] at h1 h2
    refine ⟨h1, ?_⟩
    calc w i ≤ F / 2 ^ k := h2
      _ = 2 * m := by rw [hm_def, pow_succ]; field_simp
  have hS0 : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg fun i _ => hw0 i
  have hFS : F ≤ 2 * k₀ * ∑ i ∈ S, w i := by
    rw [div_le_iff₀ (by positivity)] at hkS
    linarith
  refine ⟨m, S.card, fun j => P (S.equivFin.symm j).1, fun j => c (S.equivFin.symm j).1,
    by positivity, fun j => ⟨hmeas _, hsubE _, hball _⟩, ?_, ?_, fun j => hthin _, ?_, ?_, ?_⟩
  · intro j j' hjj'
    apply hdisj
    intro h
    apply hjj'
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro j
    have hj := hSprop _ (S.equivFin.symm j).2
    rw [hw]
    exact ⟨ENNReal.ofReal_le_ofReal hj.1.le, ENNReal.ofReal_le_ofReal hj.2⟩
  · have hsum : ∑ j, volume (P (S.equivFin.symm j).1) = ENNReal.ofReal (∑ i ∈ S, w i) := by
      rw [← hsumP S, Fintype.sum_equiv S.equivFin.symm _ (fun x => volume (P x.1))
        (fun j => rfl)]
      exact Finset.sum_coe_sort S (fun i => volume (P i))
    rw [hsum]
    have hmass' : volume E ≤ (N : ENNReal) * ENNReal.ofReal F := by
      have := hsumP Finset.univ
      rw [this] at hmass
      exact hmass
    have hpos : 0 < δ ^ ε := Real.rpow_pos_of_pos hδ ε
    calc ENNReal.ofReal (δ ^ ε / K) * volume E
        ≤ ENNReal.ofReal (δ ^ ε / K) * ((N : ENNReal) * ENNReal.ofReal F) := by gcongr
      _ = ENNReal.ofReal (δ ^ ε / K * N * F) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast, mul_assoc]
      _ ≤ ENNReal.ofReal (∑ i ∈ S, w i) := by
          apply ENNReal.ofReal_le_ofReal
          have hδK : δ ^ ε / K * N * (2 * k₀) ≤ 1 := by
            have h1 : δ ^ ε * δ ^ (-ε) = 1 := by
              rw [← Real.rpow_add hδ]
              simp
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_one hK]
            calc δ ^ ε * N * (2 * k₀) = δ ^ ε * (2 * k₀ * N) := by ring
              _ ≤ δ ^ ε * (K * δ ^ (-ε)) := by gcongr
              _ = K := by rw [mul_left_comm, h1, mul_one]
          calc δ ^ ε / K * N * F ≤ δ ^ ε / K * N * (2 * k₀ * ∑ i ∈ S, w i) := by gcongr
            _ = (δ ^ ε / K * N * (2 * k₀)) * ∑ i ∈ S, w i := by ring
            _ ≤ 1 * ∑ i ∈ S, w i := by gcongr
            _ = ∑ i ∈ S, w i := one_mul _
  · rcases S.eq_empty_or_nonempty with hSe | ⟨i, hi⟩
    · have hF : F ≤ 0 := by
        rw [hSe, Finset.sum_empty] at hFS
        linarith
      have hm0 : m = 0 := by
        rw [hm_def, le_antisymm hF hF0, zero_div]
      rw [hm0, ENNReal.ofReal_zero]
      exact zero_le
    · calc ENNReal.ofReal m ≤ ENNReal.ofReal (w i) := ENNReal.ofReal_le_ofReal (hSprop i hi).1.le
        _ = volume (P i) := (hw i).symm
        _ ≤ _ := hup i
  · intro x v hv
    refine le_trans ?_ (htube x v hv)
    have := Set.ncard_le_ncard_of_injOn
      (s := {j : Fin S.card | (Metric.thickening δ (segment ℝ x (x + v)) ∩
        P (S.equivFin.symm j).1).Nonempty})
      (t := {i | (Metric.thickening δ (segment ℝ x (x + v)) ∩ P i).Nonempty})
      (fun j => (S.equivFin.symm j).1) (fun j hj => hj)
      (fun j _ j' _ h => S.equivFin.symm.injective (Subtype.ext h)) (Set.toFinite _)
    exact_mod_cast this

/-- A node of the last level whose scale is below `2 ^ p δ / |E|` is thin by its mass bound. -/
theorem node_thin_of_mass {p T : ℕ} {δ K : ℝ} {A E : Set Space} (hδ : 0 < δ)
    (hK : 100 * 2 ^ p ≤ K)
    (hA : (((2 : ENNReal) ^ p) ^ 3) ^ T * volume A ≤ volume E)
    (hE : ENNReal.ofReal (scale p T) * volume E ≤ ENNReal.ofReal (2 ^ p * δ)) :
    volume A ≤ ENNReal.ofReal (K * δ * scale p T ^ 2) := by
  have hs : 0 < scale p T := scale_pos p T
  set D : ℝ := ((2 : ℝ) ^ p) ^ T with hD_def
  have hD0 : 0 < D := by positivity
  have hDs : D * scale p T = 2 := by
    rw [hD_def]; unfold scale; field_simp
  have hcast : (((2 : ENNReal) ^ p) ^ 3) ^ T = ENNReal.ofReal (D ^ 3) := by
    rw [hD_def, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    ring
  rw [hcast] at hA
  have h1 : ENNReal.ofReal (scale p T * D ^ 3) * volume A ≤ ENNReal.ofReal (2 ^ p * δ) := by
    rw [ENNReal.ofReal_mul hs.le, mul_assoc]
    exact (mul_le_mul_right hA _).trans hE
  have hfin : volume A ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)] at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h1)
  rw [← ENNReal.ofReal_toReal hfin] at h1 ⊢
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  apply ENNReal.ofReal_le_ofReal
  have ha : 0 ≤ (volume A).toReal := ENNReal.toReal_nonneg
  have hp1 : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hkey : scale p T * D ^ 3 * scale p T ^ 2 = 8 := by
    have : scale p T * D ^ 3 * scale p T ^ 2 = (D * scale p T) ^ 3 := by ring
    rw [this, hDs]; norm_num
  have h3 : 8 * (volume A).toReal ≤ 2 ^ p * δ * scale p T ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 (sq_nonneg (scale p T))
    calc 8 * (volume A).toReal = scale p T * D ^ 3 * scale p T ^ 2 * (volume A).toReal := by
          rw [hkey]
      _ = scale p T * D ^ 3 * (volume A).toReal * scale p T ^ 2 := by ring
      _ ≤ _ := this
  have h4 : 2 ^ p * δ * scale p T ^ 2 ≤ 8 * (K * δ * scale p T ^ 2) := by
    have h8 : (2 : ℝ) ^ p ≤ 8 * K := by linarith
    have h9 := mul_le_mul_of_nonneg_right h8 (by positivity : (0 : ℝ) ≤ δ * scale p T ^ 2)
    calc 2 ^ p * δ * scale p T ^ 2 = 2 ^ p * (δ * scale p T ^ 2) := by ring
      _ ≤ 8 * K * (δ * scale p T ^ 2) := h9
      _ = 8 * (K * δ * scale p T ^ 2) := by ring
  linarith

/-- Pigeonholing a level. -/
theorem level_pigeon (T : ℕ) (f : ℕ → ENNReal) :
    ∃ t ∈ Finset.range (T + 1),
      ∑ t' ∈ Finset.range (T + 1), f t' ≤ ((T + 1 : ℕ) : ENNReal) * f t := by
  by_contra h
  push Not at h
  have := ENNReal.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 (Nat.succ_pos T)⟩ h
  rw [Finset.sum_const, Finset.card_range, ← Finset.mul_sum, nsmul_eq_mul] at this
  exact lt_irrefl _ this

theorem exists_p {ε : ℝ} (hε : 0 < ε) : ∃ p : ℕ, 1 ≤ p ∧ (20 : ℝ) ≤ ((2 : ℝ) ^ p) ^ ε := by
  refine ⟨⌈5 / ε⌉₊ + 1, by omega, ?_⟩
  have h1 : ((5 : ℕ) : ℝ) ≤ ((⌈5 / ε⌉₊ + 1 : ℕ) : ℝ) * ε := by
    have h2 := Nat.le_ceil (5 / ε)
    have h3 : 5 / ε * ε = 5 := by field_simp
    push_cast
    nlinarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  calc (20 : ℝ) ≤ 2 ^ ((5 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1

theorem pow_le_rpow_neg {ε δ D : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hD : 1 ≤ D) (h20 : 20 ≤ D ^ ε)
    (T : ℕ) (hT : D ^ T ≤ 1 / δ) : (20 : ℝ) ^ T ≤ δ ^ (-ε) := by
  calc (20 : ℝ) ^ T ≤ (D ^ ε) ^ T := pow_le_pow_left₀ (by norm_num) h20 T
    _ = (D ^ T) ^ ε := Real.rpow_pow_comm (by linarith) ε T
    _ ≤ (1 / δ) ^ ε := Real.rpow_le_rpow (by positivity) hT hε.le
    _ = δ ^ (-ε) := by rw [Real.rpow_neg hδ.le, one_div, Real.inv_rpow hδ.le]

theorem card_bound (a b t T : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (ht : t ≤ T) :
    2 * (a ^ t * b) ≤ 2 ^ (a * b * (T + 1) + 1) := by
  have h1 : a ^ t * b ≤ (a * b) ^ (T + 1) := by
    calc a ^ t * b ≤ (a * b) ^ t * (a * b) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right a hb) t)
            (Nat.le_mul_of_pos_left b ha)
      _ = (a * b) ^ (t + 1) := (pow_succ _ _).symm
      _ ≤ (a * b) ^ (T + 1) := Nat.pow_le_pow_right (Nat.mul_pos ha hb) (by omega)
  have h2 : (a * b) ^ (T + 1) ≤ 2 ^ (a * b * (T + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  calc 2 * (a ^ t * b) ≤ 2 * 2 ^ (a * b * (T + 1)) := Nat.mul_le_mul_left _ (h1.trans h2)
    _ = 2 ^ (a * b * (T + 1) + 1) := by ring

theorem count_bound (M T : ℕ) : 2 * (M * (T + 1) + 1) * (T + 1) ≤ 2 * (M + 1) * 20 ^ T := by
  have h1 : T + 1 ≤ 2 ^ T := Nat.lt_two_pow_self
  have h2 : (T + 1) * (T + 1) ≤ 20 ^ T := by
    calc (T + 1) * (T + 1) ≤ 2 ^ T * 2 ^ T := Nat.mul_le_mul h1 h1
      _ = 4 ^ T := by rw [← mul_pow]; norm_num
      _ ≤ 20 ^ T := Nat.pow_le_pow_left (by norm_num) T
  calc 2 * (M * (T + 1) + 1) * (T + 1) ≤ 2 * (M + 1) * ((T + 1) * (T + 1)) := by nlinarith
    _ ≤ 2 * (M + 1) * 20 ^ T := Nat.mul_le_mul_left _ h2

theorem tube_leaf_bound {p t : ℕ} {K X : ℝ} (hX : (20 : ℝ) ^ t ≤ X) (hK : 800 ≤ K) :
    (20 * (2 : ℝ) ^ p) ^ t * (400 * 2 ^ p) ≤ K * X / scale p (t + 1) := by
  rw [le_div_iff₀ (scale_pos p (t + 1))]
  have e : (20 * (2 : ℝ) ^ p) ^ t * (400 * 2 ^ p) * scale p (t + 1) = 800 * 20 ^ t := by
    unfold scale
    rw [mul_pow, pow_succ]
    field_simp
    ring
  rw [e]
  have : (0 : ℝ) ≤ 20 ^ t := by positivity
  nlinarith

theorem tube_node_bound {p T : ℕ} {K X : ℝ} (hX : (20 : ℝ) ^ T ≤ X) (hK : 2 ≤ K) :
    (20 * (2 : ℝ) ^ p) ^ T ≤ K * X / scale p T := by
  rw [le_div_iff₀ (scale_pos p T)]
  have e : (20 * (2 : ℝ) ^ p) ^ T * scale p T = 2 * 20 ^ T := by
    unfold scale
    rw [mul_pow]
    field_simp
  rw [e]
  have : (0 : ℝ) ≤ 20 ^ T := by positivity
  nlinarith

theorem ennreal_pow_eq (p t : ℕ) :
    (((2 : ENNReal) ^ p) ^ 3) ^ t = ENNReal.ofReal ((((2 : ℝ) ^ p) ^ 3) ^ t) := by
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem mul_vol_mono (X : ENNReal) {A B : Set Space} (h : A ⊆ B) :
    X * volume A ≤ X * volume B := by
  gcongr

theorem up_aux {X v e c : ENNReal} (h1 : 1 ≤ c * X) (h2 : X * v ≤ e) : v ≤ c * e :=
  calc v = 1 * v := (one_mul v).symm
    _ ≤ (c * X) * v := by gcongr
    _ = c * (X * v) := mul_assoc _ _ _
    _ ≤ c * e := by gcongr

theorem up_factor_leaf {p t : ℕ} {K : ℝ} (hK : ((2 : ℝ) ^ p) ^ 3 ≤ K) :
    1 ≤ ENNReal.ofReal (K * scale p (t + 1) ^ 3) * (((2 : ENNReal) ^ p) ^ 3) ^ t := by
  have hD : (0 : ℝ) < 2 ^ p := by positivity
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  rw [ennreal_pow_eq, ← ENNReal.ofReal_mul (by have := scale_pos p (t + 1); positivity),
    ENNReal.one_le_ofReal]
  have e : K * scale p (t + 1) ^ 3 * (((2 : ℝ) ^ p) ^ 3) ^ t = 8 * K / ((2 : ℝ) ^ p) ^ 3 := by
    unfold scale
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith

theorem up_factor_node {p T : ℕ} {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ ENNReal.ofReal (K * scale p T ^ 3) * (((2 : ENNReal) ^ p) ^ 3) ^ T := by
  have hD : (0 : ℝ) < 2 ^ p := by positivity
  rw [ennreal_pow_eq, ← ENNReal.ofReal_mul (by have := scale_pos p T; positivity),
    ENNReal.one_le_ofReal]
  have e : K * scale p T ^ 3 * (((2 : ℝ) ^ p) ^ 3) ^ T = 8 * K := by
    unfold scale
    field_simp
    ring
  rw [e]
  linarith

end RecAux

/-- The grains decomposition: disjoint thin pieces of `E` at a common scale `s`, of comparable
masses carrying a `δ^ε` share of `E`, each `δ`-tube meeting at most `K δ^(-ε) / s` of them. -/
theorem grains_partition (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
    ∀ E : Set Space, MeasurableSet E → E ⊆ Metric.ball (0 : Space) 1 →
    ∃ (s m : ℝ) (G : ℕ) (P : Fin G → Set Space) (c : Fin G → Space),
      δ ≤ s ∧ s ≤ 2 ∧ 0 ≤ m ∧
      (ENNReal.ofReal δ ≤ ENNReal.ofReal s * volume E ∨ s = 2) ∧
      (∀ j, MeasurableSet (P j) ∧ P j ⊆ E ∧ P j ⊆ Metric.closedBall (c j) (2 * s)) ∧
      (Pairwise fun j k => Disjoint (P j) (P k)) ∧
      (∀ j, ENNReal.ofReal m ≤ volume (P j) ∧ volume (P j) ≤ ENNReal.ofReal (2 * m)) ∧
      (∀ j, volume (P j) ≤ ENNReal.ofReal (K * δ * s ^ 2)) ∧
      ENNReal.ofReal (δ ^ ε / K) * volume E ≤ ∑ j, volume (P j) ∧
      ENNReal.ofReal m ≤ ENNReal.ofReal (K * s ^ 3) * volume E ∧
      ∀ x v : Space, ‖v‖ ≤ 1 →
        ({j | (Metric.thickening δ (segment ℝ x (x + v)) ∩ P j).Nonempty}.ncard : ℝ) ≤
          K * δ ^ (-ε) / s := by
  classical
  obtain ⟨p, hp1, h20⟩ := RecAux.exists_p hε
  set M : ℕ := Fintype.card (RecAux.I p) * Fintype.card (RecAux.Q p) with hM
  have hKthin : 0 ≤ Kthin (2 ^ p) := by unfold Kthin; positivity
  have hD1 : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hD3 : (0 : ℝ) ≤ ((2 : ℝ) ^ p) ^ 3 := by positivity
  set K : ℝ := Kthin (2 ^ p) + 100 * 2 ^ p + ((2 : ℝ) ^ p) ^ 3 + 800 + 2 * (M + 1) with hK_def
  have hK800 : 800 ≤ K := by rw [hK_def]; linarith
  have hKpos : 0 < K := by linarith
  have hKthinK : Kthin (2 ^ p) ≤ K := by rw [hK_def]; linarith
  have hK100 : 100 * 2 ^ p ≤ K := by rw [hK_def]; linarith
  have hKD3 : ((2 : ℝ) ^ p) ^ 3 ≤ K := by rw [hK_def]; linarith
  have hKM : 2 * ((M : ℝ) + 1) ≤ K := by rw [hK_def]; linarith
  refine ⟨K, by linarith, 1, one_pos, ?_⟩
  intro δ hδ hδ1 E hE hEball
  have H : RecAux.Hyp p δ E := ⟨hp1, hδ, hE, hEball.trans RecAux.ball_subset_box⟩
  have hEfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne
      (measure_mono hEball)
  -- the number `T` of levels
  have hex : ∃ t : ℕ, RecAux.scale p t ≤ 100 * 2 ^ p * δ ∨
      ENNReal.ofReal (RecAux.scale p t) * volume E ≤ ENNReal.ofReal (2 ^ p * δ) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / (100 * 2 ^ p * δ))
      (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega : p ≠ 0))
    refine ⟨n, Or.inl ?_⟩
    unfold RecAux.scale
    rw [div_lt_iff₀ (by positivity)] at hn
    rw [div_le_iff₀ (by positivity)]
    linarith
  set T := Nat.find hex with hT_def
  have hT := Nat.find_spec hex
  have hTmin' : ∀ t < T, 100 * 2 ^ p * δ < RecAux.scale p t ∧
      ENNReal.ofReal (2 ^ p * δ) < ENNReal.ofReal (RecAux.scale p t) * volume E :=
    fun t ht => by
      have h := Nat.find_min hex ht
      rw [not_or, not_le, not_le] at h
      exact h
  have hTmin : ∀ t < T, 100 * 2 ^ p * δ < RecAux.scale p t := fun t ht => (hTmin' t ht).1
  -- the Guth lower bound for every scale `≥ scale p T`
  have hguth : ∀ s : ℝ, RecAux.scale p T ≤ s →
      ENNReal.ofReal δ ≤ ENNReal.ofReal s * volume E ∨ RecAux.scale p T = 2 := by
    intro s hs
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · right; rw [h0]; simp [RecAux.scale]
    · left
      have h1 := (hTmin' (T - 1) (by omega)).2
      have hsc : RecAux.scale p (T - 1) = 2 ^ p * RecAux.scale p T := by
        have := RecAux.scale_succ p (T - 1)
        rw [Nat.sub_add_cancel hpos] at this
        rw [this]; field_simp
      rw [hsc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        mul_assoc] at h1
      have h2 := lt_of_mul_lt_mul_left' h1
      calc ENNReal.ofReal δ ≤ ENNReal.ofReal (RecAux.scale p T) * volume E := h2.le
        _ ≤ ENNReal.ofReal s * volume E := by gcongr
  have hDT : ((2 : ℝ) ^ p) ^ T ≤ 1 / δ := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · rw [h0, pow_zero, le_div_iff₀ hδ]
      linarith
    · have h1 := hTmin (T - 1) (by omega)
      unfold RecAux.scale at h1
      rw [lt_div_iff₀ (by positivity)] at h1
      have hDT' : ((2 : ℝ) ^ p) ^ T = 2 ^ p * ((2 : ℝ) ^ p) ^ (T - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [le_div_iff₀ hδ, hDT']
      have : (0 : ℝ) ≤ 2 ^ p * ((2 : ℝ) ^ p) ^ (T - 1) * δ := by positivity
      nlinarith
  have h20T : (20 : ℝ) ^ T ≤ δ ^ (-ε) := RecAux.pow_le_rpow_neg hε hδ hD1 h20 T hDT
  have hδs : ∀ t ≤ T, δ ≤ RecAux.scale p t := by
    intro t ht
    refine le_trans ?_ (RecAux.scale_anti p ht)
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · rw [h0]
      have : RecAux.scale p 0 = 2 := by simp [RecAux.scale]
      rw [this]
      linarith
    · have h1 := hTmin (T - 1) (by omega)
      have hs : RecAux.scale p T = RecAux.scale p (T - 1) / 2 ^ p := by
        rw [← RecAux.scale_succ]
        congr 1
        omega
      rw [hs, le_div_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ 2 ^ p * δ := by positivity
      nlinarith
  -- pigeonholing a level
  have hmassT := RecAux.mass_eq H T
  obtain ⟨t, ht, hft⟩ := RecAux.level_pigeon T (fun t => if t < T then
    ∑ σ : Fin t → RecAux.I p, ∑ q, volume (RecAux.leaf p δ E t σ q)
    else ∑ σ : Fin T → RecAux.I p, volume (RecAux.node p δ E T σ).1)
  have hsumf : ∑ t' ∈ Finset.range (T + 1), (if t' < T then
      ∑ σ : Fin t' → RecAux.I p, ∑ q, volume (RecAux.leaf p δ E t' σ q)
      else ∑ σ : Fin T → RecAux.I p, volume (RecAux.node p δ E T σ).1) = volume E := by
    rw [Finset.sum_range_succ, ite_eq_right (lt_irrefl T),
      Finset.sum_congr rfl (fun t' ht' => ite_eq_left (Finset.mem_range.1 ht')), hmassT,
      add_comm]
  rw [hsumf] at hft
  -- counting constants
  have hcount : 2 * ((M * (T + 1) + 1 : ℕ) : ℝ) * ((T + 1 : ℕ) : ℝ) ≤ K * δ ^ (-ε) := by
    have h1 : ((2 * (M * (T + 1) + 1) * (T + 1) : ℕ) : ℝ) ≤ ((2 * (M + 1) * 20 ^ T : ℕ) : ℝ) := by
      exact_mod_cast RecAux.count_bound M T
    push_cast at h1 ⊢
    have h2 : (0 : ℝ) ≤ 20 ^ T := by positivity
    calc _ ≤ 2 * ((M : ℝ) + 1) * 20 ^ T := h1
      _ ≤ K * δ ^ (-ε) := mul_le_mul hKM h20T h2 hKpos.le
  have hcardI : 1 ≤ Fintype.card (RecAux.I p) :=
    Fintype.card_pos_iff.2 ⟨(fun _ => true, fun _ => ⟨0, by positivity⟩)⟩
  have hcardQ : 1 ≤ Fintype.card (RecAux.Q p) :=
    Fintype.card_pos_iff.2 ⟨fun _ => ⟨0, by positivity⟩⟩
  by_cases htT : t < T
  · -- the leaves of level `t`
    rw [ite_eq_left htT] at hft
    have hδt : δ ≤ RecAux.scale p (t + 1) := hδs (t + 1) htT
    have h20t : (20 : ℝ) ^ t ≤ δ ^ (-ε) :=
      le_trans (pow_le_pow_right₀ (by norm_num) htT.le) h20T
    obtain ⟨m, G, P', c', hm, h1, h2, h3, h4, h5, h6, h7⟩ :=
      RecAux.select (ι := (Fin t → RecAux.I p) × RecAux.Q p)
        (fun y => RecAux.leaf p δ E t y.1 y.2)
        (fun y => WithLp.toLp 2
          (RecAux.subc p (RecAux.node p δ E t y.1).2 (RecAux.scale p t) y.2))
        (E := E) (ε := ε) (s := RecAux.scale p (t + 1)) hKpos hδ (M * (T + 1) + 1) (T + 1)
        (by omega)
        (fun y => (RecAux.leaf_props H t y.1 y.2).1)
        (fun y => (RecAux.leaf_props H t y.1 y.2).2.1.trans (RecAux.node_props H t y.1).2.2.1)
        (fun y => (RecAux.leaf_props H t y.1 y.2).2.2.1.trans
          (RecAux.box_subset_closedBall _ (RecAux.scale_pos p (t + 1)).le))
        (RecAux.leaf_disj H t)
        (fun y => (RecAux.leaf_props H t y.1 y.2).2.2.2.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKthinK hδ.le) (sq_nonneg _))))
        (fun y => RecAux.up_aux (RecAux.up_factor_leaf hKD3)
          ((RecAux.mul_vol_mono _ (RecAux.leaf_props H t y.1 y.2).2.1).trans
            (RecAux.node_props H t y.1).2.2.2))
        (fun x v hv => (RecAux.leaf_tube H x v hv t hδt).trans
          (RecAux.tube_leaf_bound h20t hK800))
        (by
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
          exact RecAux.card_bound _ _ t T hcardI hcardQ htT.le)
        hEfin
        (by rw [Fintype.sum_prod_type]; exact hft)
        hcount
    refine ⟨RecAux.scale p (t + 1), m, G, P', c', hδt, RecAux.scale_le_two p _, hm, ?_, h1, h2,
      h3, h4, h5, h6, h7⟩
    rcases hguth (RecAux.scale p (t + 1)) (RecAux.scale_anti p (by omega)) with h | h
    · exact Or.inl h
    · exfalso
      have h0 : T ≠ 0 := by omega
      have hlt := hTmin 0 (Nat.pos_of_ne_zero h0)
      have hs0 : RecAux.scale p 0 = 2 := by simp [RecAux.scale]
      have hanti := RecAux.scale_anti p (show 1 ≤ T by omega)
      have hstep : RecAux.scale p 1 = RecAux.scale p 0 / 2 ^ p := RecAux.scale_succ p 0
      rw [hs0] at hstep
      have hD : (1 : ℝ) < 2 ^ p := one_lt_pow₀ (by norm_num) (by omega)
      have : RecAux.scale p 1 < 2 := by rw [hstep, div_lt_iff₀ (by positivity)]; linarith
      linarith
  · -- the pieces of the last level `T`
    rw [ite_eq_right htT] at hft
    have hsT := RecAux.scale_pos p T
    obtain ⟨m, G, P', c', hm, h1, h2, h3, h4, h5, h6, h7⟩ :=
      RecAux.select (ι := Fin T → RecAux.I p)
        (fun σ => (RecAux.node p δ E T σ).1)
        (fun σ => WithLp.toLp 2 (RecAux.node p δ E T σ).2)
        (E := E) (ε := ε) (s := RecAux.scale p T) hKpos hδ (M * (T + 1) + 1) (T + 1)
        (by omega)
        (fun σ => (RecAux.node_props H T σ).1)
        (fun σ => (RecAux.node_props H T σ).2.2.1)
        (fun σ => (RecAux.node_props H T σ).2.1.trans
          (RecAux.box_subset_closedBall _ hsT.le))
        (RecAux.node_disj H T)
        (fun σ => by
          rcases hT with hT | hT
          · calc volume (RecAux.node p δ E T σ).1
                ≤ volume (box (RecAux.node p δ E T σ).2 (RecAux.scale p T)) :=
                  measure_mono (RecAux.node_props H T σ).2.1
              _ = ENNReal.ofReal (RecAux.scale p T ^ 3) := RecAux.volume_box_eq _ hsT.le
              _ ≤ ENNReal.ofReal (K * δ * RecAux.scale p T ^ 2) := by
                apply ENNReal.ofReal_le_ofReal
                have hsK : RecAux.scale p T ≤ K * δ :=
                  le_trans hT (mul_le_mul_of_nonneg_right hK100 hδ.le)
                calc RecAux.scale p T ^ 3 = RecAux.scale p T * RecAux.scale p T ^ 2 := by ring
                  _ ≤ (K * δ) * RecAux.scale p T ^ 2 := by gcongr
                  _ = K * δ * RecAux.scale p T ^ 2 := by ring
          · exact RecAux.node_thin_of_mass hδ hK100 (RecAux.node_props H T σ).2.2.2 hT)
        (fun σ => RecAux.up_aux (RecAux.up_factor_node (by linarith))
          (RecAux.node_props H T σ).2.2.2)
        (fun x v hv => (RecAux.node_tube H x v hv T).trans
          (RecAux.tube_node_bound h20T (by linarith)))
        (by
          rw [Fintype.card_fun, Fintype.card_fin]
          exact le_trans (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ hcardQ))
            (RecAux.card_bound _ _ T T hcardI hcardQ le_rfl))
        hEfin hft hcount
    refine ⟨RecAux.scale p T, m, G, P', c', hδs T le_rfl, RecAux.scale_le_two p _, hm, ?_, h1, h2,
      h3, h4, h5, h6, h7⟩
    exact hguth _ le_rfl

end Grains
end WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
