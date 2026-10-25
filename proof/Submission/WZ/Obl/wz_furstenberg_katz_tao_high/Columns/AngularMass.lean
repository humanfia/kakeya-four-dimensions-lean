-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.AngularMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0720 Columns/AngularMass.lean (758215d).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.AngularClasses
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.GridCounts
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.CoarsePalette

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators Classical

/-- Joint pin/map balance bounds a subset of any bush using the fiber
average in a single reference bush. -/
theorem bush_subset_mass_global {Y : Type*} [DecidableEq Y]
    (D : Finset (E2 × E2)) (f : E2 × E2 → Y) {K : ℝ}
    (hbal : Balanced D (fun q => (q.1, f q)) K)
    (p₀ p : E2) (Q : Finset E2) (hQ : Q ⊆ bushOf D p) :
    (Q.card : ℝ) * ((bushOf D p₀).image fun e => f (p₀, e)).card ≤
      K * (bushOf D p₀).card * (Q.image fun e => f (p, e)).card := by
  have hsum : (Q.card : ℝ) = ∑ y ∈ Q.image (fun e => f (p, e)),
      ((Q.filter fun e => f (p, e) = y).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (fun e => f (p, e)) Q
  rw [hsum, Finset.sum_mul]
  calc
    _ ≤ ∑ _y ∈ Q.image (fun e => f (p, e)), K * ((bushOf D p₀).card : ℝ) := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
      have hpe : (p, e) ∈ D := mem_bushOf.mp (hQ he)
      have hb := (pin_fiber_global_bounds D f hbal p₀ hpe).1
      have hfib : (leafFiber D (fun q => (q.1, f q)) (p, e)).card =
          ((bushOf D p).filter fun u => f (p, u) = f (p, e)).card := by
        simp only [leafFiber, Prod.mk.injEq]
        convert pin_map_fiber_card D f p (f (p, e)) using 1 <;>
          congr 1 <;> ext z <;> simp only [Finset.mem_filter]
      rw [hfib] at hb
      have hc : ((Q.filter fun u => f (p, u) = f (p, e)).card : ℝ) ≤
          (((bushOf D p).filter fun u => f (p, u) = f (p, e)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.monotone_filter_left _ hQ))
      exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans (by nlinarith only [hb])
    _ = _ := by simp [mul_comm, mul_left_comm]

/-- Arbitrary-radius cap counts from one reference angular profile. -/
theorem bush_ball_global (D : Finset (E2 × E2)) {σ θ K : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (hK : 0 ≤ K)
    (hbal : Balanced D (fun q => (q.1, arcOf σ q.2)) K) (p₀ p u : E2) :
    (((bushOf D p).filter fun e => dist e u ≤ θ).card : ℝ) *
      ((bushOf D p₀).image (arcOf σ)).card ≤
        K * (bushOf D p₀).card * (2 * θ / σ + 2) ^ 2 := by
  let Q := (bushOf D p).filter fun e => dist e u ≤ θ
  have hmass := bush_subset_mass_global D (fun q => arcOf σ q.2) hbal p₀ p Q
    (Finset.filter_subset _ _)
  have hgrid := cell_count_ball Q hσ hθ u (fun e he => (Finset.mem_filter.mp he).2)
  exact hmass.trans (mul_le_mul_of_nonneg_left hgrid (mul_nonneg hK (Nat.cast_nonneg _)))

/-- Cap counts expressed by the angular profile of one reference bush.
This is uniform over all pins of the original label family. -/
theorem bush_cap_global (D : Finset (E2 × E2)) {σ θ K : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (hθσ : θ ≤ σ) (hK : 0 ≤ K)
    (hbal : Balanced D (fun q => (q.1, arcOf σ q.2)) K) (p₀ p u : E2) :
    (((bushOf D p).filter fun e => dist e u ≤ θ).card : ℝ) *
      ((bushOf D p₀).image (arcOf σ)).card ≤ 16 * K * (bushOf D p₀).card := by
  let Q := (bushOf D p).filter fun e => dist e u ≤ θ
  have hmass := bush_subset_mass_global D (fun q => arcOf σ q.2) hbal p₀ p Q
    (Finset.filter_subset _ _)
  have hgrid : ((Q.image (arcOf σ)).card : ℝ) ≤ 16 := by
    have hh := cell_count_ball Q hσ hθ u (fun e he => (Finset.mem_filter.mp he).2)
    have hratio : 2 * θ / σ ≤ 2 := by rw [div_le_iff₀ hσ]; linarith
    have hratio0 : 0 ≤ 2 * θ / σ := by positivity
    have hsquare : (2 * θ / σ + 2) ^ 2 ≤ 16 := by nlinarith
    exact hh.trans hsquare
  calc
    _ ≤ K * (bushOf D p₀).card * (Q.image (arcOf σ)).card := hmass
    _ ≤ K * (bushOf D p₀).card * 16 :=
      mul_le_mul_of_nonneg_left hgrid (mul_nonneg hK (Nat.cast_nonneg _))
    _ = _ := by ring

/-- The original-bush cardinality cancels from the common-class estimate.
Both profiles are measured on one reference bush. -/
theorem coarse_common_classes_le_arc_ratio {R σ K : ℝ}
    (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hσ : 0 < σ) (hK : 0 < K)
    {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep R j j')
    (hcls : ∀ q ∈ D, cls q ∈ J) (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R))
    (hbal : Balanced D (fun q => (q.1, cls q)) K)
    (harc : Balanced D (fun q => (q.1, arcOf σ q.2)) K)
    (p₀ : E2) (hp₀ : ‖p₀‖ ≤ 4) (hne : (bushOf D p₀).Nonempty)
    {p p' : E2} (hp : ‖p‖ ≤ 4) (hp' : ‖p'‖ ≤ 4)
    (hσpair : 288 * (2 * R) / max (dist p p') (144 * (2 * R)) ≤ σ) :
    ((J.filter fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j).card : ℝ) ≤
      2146560 * K ^ 2 * ((bushOf D p₀).image (arcOf R)).card /
        ((bushOf D p₀).image (arcOf σ)).card := by
  let n : ℝ := (bushOf D p₀).card
  let A : ℝ := ((bushOf D p₀).image (arcOf R)).card
  let Aσ : ℝ := ((bushOf D p₀).image (arcOf σ)).card
  have hn : 0 < n := Nat.cast_pos.mpr hne.card_pos
  have hA : 0 < A := Nat.cast_pos.mpr (hne.image _).card_pos
  have hAσ : 0 < Aσ := Nat.cast_pos.mpr (hne.image _).card_pos
  let m := n / (67080 * K * A)
  let V := 16 * K * n / Aσ
  have hm : 0 < m := by dsimp [m]; positivity
  have hcap : ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter fun e => dist e u ≤ σ).card : ℝ) ≤ V := by
    intro u hu
    dsimp [V]
    rw [le_div_iff₀ hAσ]
    exact bush_cap_global D hσ hσ le_rfl hK.le harc p₀ p u
  have hmin : ∀ j ∈ J, p ∈ pinsOf D cls j →
      m ≤ (((bushOf D p).filter fun e => cls (p, e) = j).card : ℝ) := by
    intro j hj hpj
    obtain ⟨e, he, hce⟩ := mem_pinsOf.mp hpj
    have hh := coarse_pin_fiber_mass_global hR hRsmall hK.le hJ hsep hcls hunit hgeo hbal p₀ hp₀ he
    have hfib : (leafFiber D (fun q => (q.1, cls q)) (p, e)).card =
        ((bushOf D p).filter fun u => cls (p, u) = j).card := by
      simp only [leafFiber, Prod.mk.injEq, hce]
      convert pin_map_fiber_card D cls p j using 1 <;>
        congr 1 <;> ext z <;> simp only [Finset.mem_filter]
    rw [hfib] at hh
    dsimp [m]
    rw [div_le_iff₀ (by positivity : 0 < 67080 * K * A)]
    nlinarith only [hh]
  have hg : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * (2 * R) ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R) := by
    intro q hq
    exact ⟨(hgeo q hq).1.trans (by linarith), (hgeo q hq).2⟩
  have hh := coarse_common_classes_le_of_cap (r := R) (R := 2 * R) (by linarith)
    (by positivity) (by linarith) hm hunit hg hp hp' hσpair hcap hmin
  have heq : 2 * V / m = 2146560 * K ^ 2 * A / Aσ := by
    dsimp [V, m]
    field_simp
    <;> ring
  exact hh.trans_eq heq

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
