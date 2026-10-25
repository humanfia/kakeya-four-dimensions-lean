-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.AngularClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0720 Columns/AngularClasses.lean (758215d).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.WidePacking
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.AtScale
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.ClassMass
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.UniformFibers

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators Classical

/-- Angular errors up to sign control the absolute value of every unit
linear functional. -/
theorem abs_inner_of_unoriented_close {e f u : E2} {R : ℝ} (hu : ‖u‖ = 1)
    (hclose : dist e f ≤ R ∨ dist e (-f) ≤ R) :
    |inner ℝ f u| ≤ |inner ℝ e u| + R := by
  rcases hclose with hh | hh
  · have hnorm : ‖f - e‖ ≤ R := by simpa only [dist_eq_norm, norm_sub_rev] using hh
    have hid : inner ℝ f u = inner ℝ e u + inner ℝ (f - e) u := by rw [inner_sub_left]; ring
    have hperturb := abs_real_inner_le_norm (f - e) u
    rw [hu, mul_one] at hperturb
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add_right (hperturb.trans hnorm) _)
  · have hnorm : ‖f + e‖ ≤ R := by simpa only [dist_eq_norm, sub_neg_eq_add, add_comm] using hh
    have hid : inner ℝ f u = -inner ℝ e u + inner ℝ (f + e) u := by rw [inner_add_left]; ring
    have hperturb := abs_real_inner_le_norm (f + e) u
    rw [hu, mul_one] at hperturb
    rw [hid]
    exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add_right (hperturb.trans hnorm) _)

/-- Only a constant number of separated coarse classes can arise at a
fixed pin from normals in one angular grid square. -/
theorem coarse_classes_in_arc_le {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8)
    {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep R j j')
    (hcls : ∀ q ∈ D, cls q ∈ J)
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R))
    {p u : E2} (hp : ‖p‖ ≤ 4) (hu : u ∈ bushOf D p) :
    ((((bushOf D p).filter fun e => arcOf R e = arcOf R u).image
      fun e => cls (p, e)).card : ℝ) ≤ 67080 := by
  let C := ((bushOf D p).filter fun e => arcOf R e = arcOf R u).image fun e => cls (p, e)
  let v := WangZahlLot.Obl.wz_nonconcentrated_dot_products.perp u
  have hv : ‖v‖ = 1 := by
    rw [WangZahlLot.Obl.wz_nonconcentrated_dot_products.perp_norm]
    exact hunit (p, u) (mem_bushOf.mp hu)
  have huv : inner ℝ u v = 0 := WangZahlLot.Obl.wz_nonconcentrated_dot_products.perp_inner u
  have hCJ : C ⊆ J := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact hcls (p, e) (mem_bushOf.mp (Finset.mem_filter.mp he).1)
  have hbound := wide_frame_count hv hR (by positivity : 0 ≤ 4 * R)
    (by positivity : 0 ≤ 32 * R) C (fun j hj j' hj' hne => hsep j (hCJ hj) j' (hCJ hj') hne) (by
      intro j hj
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨heD, heArc⟩ := Finset.mem_filter.mp he
      have heD' := mem_bushOf.mp heD
      have heclose := dist_le_of_arcOf_eq hR heArc
      have heangle : |inner ℝ e v| ≤ 2 * R := by
        have hid : inner ℝ e v = inner ℝ (e - u) v := by rw [inner_sub_left, huv, sub_zero]
        rw [hid]
        calc
          _ ≤ ‖e - u‖ * ‖v‖ := abs_real_inner_le_norm _ _
          _ = dist e u := by rw [hv, mul_one, dist_eq_norm]
          _ ≤ 2 * R := heclose
      have hg := hgeo (p, e) heD'
      have hangle : |inner ℝ (cls (p, e)).2 v| ≤ 4 * R := by
        have hh := abs_inner_of_unoriented_close hv (hg.2.imp le_of_lt le_of_lt)
        linarith
      refine ⟨(hJ _ (hcls _ heD')).2,
        norm_le_eight_of_norm_le_four hp (hJ _ (hcls _ heD')).1, ?_, hangle, hg.1.le⟩
      rw [← sq_abs]
      have hz := abs_nonneg (inner ℝ (cls (p, e)).2 v)
      nlinarith)
  have heq : 2 * (64 * (4 * R) / R + 2) * (4 * (32 * R) / R + 2) = 67080 := by
    field_simp
    <;> ring
  exact hbound.trans_eq heq

/-- The coarse star of a pin has at most a constant times its number of
occupied angular grid squares. -/
theorem coarse_star_le_arc_count {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8)
    {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep R j j')
    (hcls : ∀ q ∈ D, cls q ∈ J)
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R))
    {p : E2} (hp : ‖p‖ ≤ 4) :
    (((bushOf D p).image fun e => cls (p, e)).card : ℝ) ≤
      67080 * ((bushOf D p).image (arcOf R)).card := by
  let A := (bushOf D p).image (arcOf R)
  let C (a : ℤ × ℤ) := ((bushOf D p).filter fun e => arcOf R e = a).image fun e => cls (p, e)
  have hcover : (bushOf D p).image (fun e => cls (p, e)) ⊆ A.biUnion C := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_biUnion.mpr ⟨arcOf R e, Finset.mem_image_of_mem _ he,
      Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩⟩
  calc
    _ ≤ ((A.biUnion C).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ a ∈ A, ((C a).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (67080 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      exact coarse_classes_in_arc_le hR hRsmall hJ hsep hcls hunit hgeo hp hu
    _ = _ := by simp [A, mul_comm]

/-- Labels at one pin are in bijection with their normals, also after
restricting by an arbitrary class map. -/
theorem pin_map_fiber_card {Y : Type*} (D : Finset (E2 × E2))
    (f : E2 × E2 → Y) (p : E2) (y : Y) :
    (D.filter fun q => q.1 = p ∧ f q = y).card =
      ((bushOf D p).filter fun e => f (p, e) = y).card := by
  have heq : (D.filter fun q => q.1 = p ∧ f q = y) =
      ((bushOf D p).filter fun e => f (p, e) = y).image (fun e => (p, e)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqD, hqp, hqy⟩ := Finset.mem_filter.mp hq
      have hpair : (p, q.2) = q := Prod.ext hqp.symm rfl
      exact Finset.mem_image.mpr ⟨q.2,
        Finset.mem_filter.mpr ⟨mem_bushOf.mpr (hpair.symm ▸ hqD), hpair.symm ▸ hqy⟩, hpair⟩
    · intro hq
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_filter.mpr ⟨mem_bushOf.mp (Finset.mem_filter.mp he).1,
        rfl, (Finset.mem_filter.mp he).2⟩
  rw [heq, Finset.card_image_of_injective _ (fun _ _ hh => (Prod.mk.inj hh).2)]

/-- Balance of the joint pin/map partition restricts to every bush. -/
theorem balanced_bush_map {Y : Type*} (D : Finset (E2 × E2))
    (f : E2 × E2 → Y) {K : ℝ}
    (hbal : Balanced D (fun q => (q.1, f q)) K) (p : E2) :
    Balanced (bushOf D p) (fun e => f (p, e)) K := by
  intro e he e' he'
  have hh := hbal (p, e) (mem_bushOf.mp he) (p, e') (mem_bushOf.mp he')
  have hfib (u : E2) : (leafFiber D (fun q => (q.1, f q)) (p, u)).card =
      (leafFiber (bushOf D p) (fun e => f (p, e)) u).card := by
    simp only [leafFiber, Prod.mk.injEq]
    exact pin_map_fiber_card D f p (f (p, u))
  rwa [hfib, hfib] at hh

/-- Separated coarse classes and joint pin/class balance force a large
original-normal fiber at every occupied pin/class pair. -/
theorem coarse_pin_fiber_mass {R K : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hK : 0 ≤ K)
    {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep R j j')
    (hcls : ∀ q ∈ D, cls q ∈ J)
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R))
    (hbal : Balanced D (fun q => (q.1, cls q)) K)
    {p u : E2} (hp : ‖p‖ ≤ 4) (hu : u ∈ bushOf D p) :
    ((bushOf D p).card : ℝ) ≤
      67080 * K * ((bushOf D p).image (arcOf R)).card *
        (((bushOf D p).filter fun e => cls (p, e) = cls (p, u)).card : ℝ) := by
  have hstar := coarse_star_le_arc_count hR hRsmall hJ hsep hcls hunit hgeo hp
  have hb := WangZahlLot.Obl.wz_normalized_projection_coarse_fine.balanced_fiber_card_bounds
    (bushOf D p) (fun e => cls (p, e)) (balanced_bush_map D cls hbal p) hu
  calc
    _ ≤ K * ((bushOf D p).image (fun e => cls (p, e))).card *
        (((bushOf D p).filter fun e => cls (p, e) = cls (p, u)).card : ℝ) := by simpa only [leafFiber] using hb.2
    _ ≤ K * (67080 * ((bushOf D p).image (arcOf R)).card) *
        (((bushOf D p).filter fun e => cls (p, e) = cls (p, u)).card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstar hK) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Global joint balance compares any occupied pin/map fiber to the average
fiber of one fixed reference bush. -/
theorem pin_fiber_global_bounds {Y : Type*} [DecidableEq Y]
    (D : Finset (E2 × E2)) (f : E2 × E2 → Y) {K : ℝ}
    (hbal : Balanced D (fun q => (q.1, f q)) K) (p₀ : E2)
    {q : E2 × E2} (hq : q ∈ D) :
    (((bushOf D p₀).image fun e => f (p₀, e)).card : ℝ) *
        (leafFiber D (fun q => (q.1, f q)) q).card ≤ K * (bushOf D p₀).card ∧
      ((bushOf D p₀).card : ℝ) ≤ K * ((bushOf D p₀).image fun e => f (p₀, e)).card *
        (leafFiber D (fun q => (q.1, f q)) q).card := by
  let E := bushOf D p₀
  let A := E.image fun e => f (p₀, e)
  let w (y : Y) : ℝ := ((E.filter fun e => f (p₀, e) = y).card : ℝ)
  let m : ℝ := (leafFiber D (fun q => (q.1, f q)) q).card
  have hsum : (E.card : ℝ) = ∑ y ∈ A, w y := by
    dsimp only [A, w]
    exact_mod_cast Finset.card_eq_sum_card_image (fun e => f (p₀, e)) E
  have hb (y : Y) (hy : y ∈ A) : w y ≤ K * m ∧ m ≤ K * w y := by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    have hh := hbal (p₀, e) (mem_bushOf.mp he) q hq
    have hh' := hbal q hq (p₀, e) (mem_bushOf.mp he)
    have hfib : (leafFiber D (fun q => (q.1, f q)) (p₀, e)).card =
        (E.filter fun u => f (p₀, u) = f (p₀, e)).card := by
      simp only [leafFiber, Prod.mk.injEq]
      dsimp only [E]
      convert pin_map_fiber_card D f p₀ (f (p₀, e)) using 1 <;>
        congr 1 <;> ext z <;> simp only [Finset.mem_filter]
    rw [hfib] at hh hh'
    exact ⟨hh, hh'⟩
  constructor
  · calc
      (A.card : ℝ) * m = ∑ _y ∈ A, m := by simp
      _ ≤ ∑ y ∈ A, K * w y := Finset.sum_le_sum fun y hy => (hb y hy).2
      _ = K * E.card := by rw [hsum, Finset.mul_sum]
  · calc
      (E.card : ℝ) = ∑ y ∈ A, w y := hsum
      _ ≤ ∑ _y ∈ A, K * m := Finset.sum_le_sum fun y hy => (hb y hy).1
      _ = K * A.card * m := by simp; ring

/-- Every occupied coarse pin/class fiber has the mass predicted by the
angular profile of a single reference bush, with an absolute packing loss. -/
theorem coarse_pin_fiber_mass_global {R K : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8)
    (hK : 0 ≤ K) {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep R j j')
    (hcls : ∀ q ∈ D, cls q ∈ J)
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R))
    (hbal : Balanced D (fun q => (q.1, cls q)) K)
    (p₀ : E2) (hp₀ : ‖p₀‖ ≤ 4) {q : E2 × E2} (hq : q ∈ D) :
    ((bushOf D p₀).card : ℝ) ≤
      67080 * K * ((bushOf D p₀).image (arcOf R)).card *
        (leafFiber D (fun q => (q.1, cls q)) q).card := by
  have hstar := coarse_star_le_arc_count hR hRsmall hJ hsep hcls hunit hgeo hp₀
  have hh := (pin_fiber_global_bounds D cls hbal p₀ hq).2
  calc
    _ ≤ K * ((bushOf D p₀).image fun e => cls (p₀, e)).card *
        (leafFiber D (fun q => (q.1, cls q)) q).card := hh
    _ ≤ K * (67080 * ((bushOf D p₀).image (arcOf R)).card) *
        (leafFiber D (fun q => (q.1, cls q)) q).card :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstar hK) (Nat.cast_nonneg _)
    _ = _ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
