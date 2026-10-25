-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.TubeWeights.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0720 Columns/TubeWeights.lean (758215d).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.AngularMass
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.PrunedEnergy

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators Classical

/-- Angular closeness up to orientation composes. -/
theorem unoriented_dist_trans {e f g : E2} {a b : ℝ}
    (hef : dist e f ≤ a ∨ dist e (-f) ≤ a)
    (hfg : dist f g ≤ b ∨ dist f (-g) ≤ b) :
    dist e g ≤ a + b ∨ dist e (-g) ≤ a + b := by
  rcases hef with hef | hef <;> rcases hfg with hfg | hfg
  · exact Or.inl ((dist_triangle e f g).trans (add_le_add hef hfg))
  · exact Or.inr ((dist_triangle e f (-g)).trans (add_le_add hef hfg))
  · exact Or.inr ((dist_triangle e (-f) (-g)).trans
      (add_le_add hef (by simpa only [dist_neg_neg] using hfg)))
  · exact Or.inl ((dist_triangle e (-f) g).trans
      (add_le_add hef (by simpa only [dist_neg_neg, neg_neg] using
        (show dist (-f) (-(-g)) ≤ b by rwa [dist_neg_neg]))))

/-- Counting classes from below by the disjoint normal fibers over a pin. -/
theorem pin_class_mass_bound (D J : Finset (E2 × E2))
    (cls : E2 × E2 → E2 × E2) (p : E2) {m : ℝ}
    (hmin : ∀ j ∈ J, p ∈ pinsOf D cls j →
      m ≤ (((bushOf D p).filter fun e => cls (p, e) = j).card : ℝ)) :
    m * ((J.filter fun j => p ∈ pinsOf D cls j).card : ℝ) ≤
      ((bushOf D p).filter fun e => cls (p, e) ∈ J).card := by
  let C := J.filter fun j => p ∈ pinsOf D cls j
  let F (j : E2 × E2) := (bushOf D p).filter fun e => cls (p, e) = j
  have hdisj : (C : Set (E2 × E2)).PairwiseDisjoint F := by
    intro j hj j' hj' hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro e he he'
    exact hne ((Finset.mem_filter.mp he).2.symm.trans (Finset.mem_filter.mp he').2)
  have hsub : C.biUnion F ⊆ (bushOf D p).filter fun e => cls (p, e) ∈ J := by
    intro e he
    obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨heD, hec⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨heD, hec ▸ (Finset.mem_filter.mp hj).1⟩
  calc
    m * (C.card : ℝ) = ∑ _j ∈ C, m := by simp [mul_comm]
    _ ≤ ∑ j ∈ C, ((F j).card : ℝ) :=
      Finset.sum_le_sum fun j hj => hmin j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    _ = ((C.biUnion F).card : ℝ) := by rw [Finset.card_biUnion hdisj, Nat.cast_sum]
    _ ≤ _ := Nat.cast_le.mpr (Finset.card_le_card hsub)

/-- Joint balance supplies the minimum fiber used in the counting estimates. -/
theorem coarse_pin_class_min {R K : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1 / 8)
    (hK : 0 < K) {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep R j j')
    (hcls : ∀ q ∈ D, cls q ∈ J) (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R))
    (hbal : Balanced D (fun q => (q.1, cls q)) K)
    (p₀ : E2) (hp₀ : ‖p₀‖ ≤ 4) (hne : (bushOf D p₀).Nonempty)
    {p : E2} {j : E2 × E2} (hpj : p ∈ pinsOf D cls j) :
    (bushOf D p₀).card / (67080 * K * ((bushOf D p₀).image (arcOf R)).card) ≤
      (((bushOf D p).filter fun e => cls (p, e) = j).card : ℝ) := by
  obtain ⟨e, he, hce⟩ := mem_pinsOf.mp hpj
  have hh := coarse_pin_fiber_mass_global hR hRsmall hK.le hJ hsep hcls hunit hgeo hbal p₀ hp₀ he
  have hfib : (leafFiber D (fun q => (q.1, cls q)) (p, e)).card =
      ((bushOf D p).filter fun u => cls (p, u) = j).card := by
    simp only [leafFiber, Prod.mk.injEq, hce]
    convert pin_map_fiber_card D cls p j using 1 <;>
      congr 1 <;> ext z <;> simp only [Finset.mem_filter]
  rw [hfib] at hh
  have hA : (0 : ℝ) < ((bushOf D p₀).image (arcOf R)).card :=
    Nat.cast_pos.mpr (hne.image _).card_pos
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [hh]

/-- The number of coarse classes at a pin in a larger tube is controlled
by the ratio of angular counts in one fixed reference bush. -/
theorem coarse_pin_tube_incidence_le {R Δ K : ℝ}
    (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hRΔ : R ≤ Δ) (hK : 0 < K)
    {D J : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep R j j')
    (hcls : ∀ q ∈ D, cls q ∈ J) (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R))
    (htb : ∀ j ∈ J, dist j.2 (tb j).2 < Δ ∨ dist j.2 (-(tb j).2) < Δ)
    (hbal : Balanced D (fun q => (q.1, cls q)) K)
    (harc : Balanced D (fun q => (q.1, arcOf Δ q.2)) K)
    (p₀ : E2) (hp₀ : ‖p₀‖ ≤ 4) (hne : (bushOf D p₀).Nonempty)
    (p : E2) (t : E2 × E2) :
    (((J.filter fun j => tb j = t).filter fun j => p ∈ pinsOf D cls j).card : ℝ) ≤
      8586240 * K ^ 2 * ((bushOf D p₀).image (arcOf R)).card /
        ((bushOf D p₀).image (arcOf Δ)).card := by
  have hΔ : 0 < Δ := hR.trans_le hRΔ
  let n : ℝ := (bushOf D p₀).card
  let A : ℝ := ((bushOf D p₀).image (arcOf R)).card
  let AΔ : ℝ := ((bushOf D p₀).image (arcOf Δ)).card
  let m := n / (67080 * K * A)
  have hn : 0 < n := Nat.cast_pos.mpr hne.card_pos
  have hA : 0 < A := Nat.cast_pos.mpr (hne.image _).card_pos
  have hAΔ : 0 < AΔ := Nat.cast_pos.mpr (hne.image _).card_pos
  have hm : 0 < m := by dsimp [m]; positivity
  let Q := (bushOf D p).filter fun e => cls (p, e) ∈ J.filter (fun j => tb j = t)
  have hmass := pin_class_mass_bound D (J.filter fun j => tb j = t) cls p
    (m := m) (fun j hj hpj => coarse_pin_class_min hR hRsmall hK hJ hsep hcls hunit hgeo
      hbal p₀ hp₀ hne hpj)
  let Q₁ := (bushOf D p).filter fun e => dist e t.2 ≤ 3 * Δ
  let Q₂ := (bushOf D p).filter fun e => dist e (-t.2) ≤ 3 * Δ
  have hsub : Q ⊆ Q₁ ∪ Q₂ := by
    intro e he
    obtain ⟨heD, heJ⟩ := Finset.mem_filter.mp he
    obtain ⟨heJ, het⟩ := Finset.mem_filter.mp heJ
    have hangle := unoriented_dist_trans
      ((hgeo (p, e) (mem_bushOf.mp heD)).2.imp le_of_lt le_of_lt)
      ((htb _ heJ).imp le_of_lt le_of_lt)
    rw [het] at hangle
    rcases hangle with ha | ha
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heD, ha.trans (by linarith)⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heD, ha.trans (by linarith)⟩)
  have hcap (u : E2) :
      (((bushOf D p).filter fun e => dist e u ≤ 3 * Δ).card : ℝ) * AΔ ≤ 64 * K * n := by
    have hh := bush_ball_global D hΔ (by positivity : 0 < 3 * Δ) hK.le harc p₀ p u
    have heq : (2 * (3 * Δ) / Δ + 2) ^ 2 = 64 := by field_simp; ring
    rw [heq] at hh
    nlinarith only [hh]
  have hQ : (Q.card : ℝ) * AΔ ≤ 128 * K * n := by
    have hcard : (Q.card : ℝ) ≤ Q₁.card + Q₂.card :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (by exact_mod_cast Finset.card_union_le Q₁ Q₂)
    have hh := mul_le_mul_of_nonneg_right hcard hAΔ.le
    have hh₁ := hcap t.2
    have hh₂ := hcap (-t.2)
    nlinarith only [hh, hh₁, hh₂]
  have hout : (((J.filter fun j => tb j = t).filter fun j => p ∈ pinsOf D cls j).card : ℝ) ≤
      128 * K * n / (m * AΔ) := by
    rw [le_div_iff₀ (mul_pos hm hAΔ)]
    have hh := mul_le_mul_of_nonneg_right hmass hAΔ.le
    nlinarith only [hh, hQ]
  have heq : 128 * K * n / (m * AΔ) = 8586240 * K ^ 2 * A / AΔ := by
    dsimp [m]
    field_simp
    <;> ring
  exact hout.trans_eq heq

/-- Every fiber of a balanced partition has at most its average times K. -/
theorem balanced_cell_fiber_le {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (P : Finset X) (f : X → Y) {K : ℝ} (hK : 0 ≤ K)
    (hP : P.Nonempty) (hbal : Balanced P f K) (c : Y) :
    ((P.filter fun p => f p = c).card : ℝ) ≤ K * P.card / (P.image f).card := by
  have hN : (0 : ℝ) < (P.image f).card := Nat.cast_pos.mpr (hP.image f).card_pos
  by_cases hc : c ∈ P.image f
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    have hh := (WangZahlLot.Obl.wz_normalized_projection_coarse_fine.balanced_fiber_card_bounds
      P f hbal hp).1
    rw [le_div_iff₀ hN]
    have heq : leafFiber P f p = P.filter (fun x => f x = f p) := by
      ext x
      simp only [leafFiber, Finset.mem_filter]
    rw [heq] at hh
    nlinarith only [hh]
  · have he : P.filter (fun p => f p = c) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp, hpc⟩ := Finset.mem_filter.mp hp
      exact hc (Finset.mem_image.mpr ⟨p, hp, hpc⟩)
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Actual balanced point and angular counts bound the pin-class mass of
every cell inside a coarse tube. -/
theorem coarse_cell_tube_mass {R Δ K : ℝ}
    (hR : 0 < R) (hRsmall : R ≤ 1 / 8) (hRΔ : R ≤ Δ) (hK : 0 < K)
    {D J : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep R j j')
    (hcls : ∀ q ∈ D, cls q ∈ J) (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < 2 * R ∨ dist q.2 (-(cls q).2) < 2 * R))
    (htb : ∀ j ∈ J, dist j.2 (tb j).2 < Δ ∨ dist j.2 (-(tb j).2) < Δ)
    (hbal : Balanced D (fun q => (q.1, cls q)) K)
    (harc : Balanced D (fun q => (q.1, arcOf Δ q.2)) K)
    (p₀ : E2) (hp₀ : ‖p₀‖ ≤ 4) (hne : (bushOf D p₀).Nonempty)
    (P : Finset E2) (hP : P.Nonempty) (hcell : Balanced P (cellOf Δ) K)
    (c : ℤ × ℤ) (t : E2 × E2) :
    (∑ j ∈ J.filter (fun j => tb j = t),
        ((cellPins D cls P (cellOf Δ) j c).card : ℝ)) ≤
      8586240 * K ^ 3 * P.card * ((bushOf D p₀).image (arcOf R)).card /
        ((P.image (cellOf Δ)).card * ((bushOf D p₀).image (arcOf Δ)).card) := by
  have hh := cell_incidence_mass_le D (J.filter fun j => tb j = t) cls P (cellOf Δ) c
    (by positivity : 0 ≤ 8586240 * K ^ 2 * ((bushOf D p₀).image (arcOf R)).card /
      ((bushOf D p₀).image (arcOf Δ)).card)
    (balanced_cell_fiber_le P (cellOf Δ) hK.le hP hcell c)
    (fun p _ => coarse_pin_tube_incidence_le hR hRsmall hRΔ hK hJ hsep hcls hunit hgeo htb
      hbal harc p₀ hp₀ hne p t)
  convert hh using 1 <;> field_simp <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
