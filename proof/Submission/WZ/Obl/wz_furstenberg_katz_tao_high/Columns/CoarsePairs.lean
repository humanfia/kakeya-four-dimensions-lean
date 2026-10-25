-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.CoarsePairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o222/x0720 Columns/CoarsePairs.lean (ccadf1f, 8169359).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.CommonClasses

/-!
Common coarse classes are counted using all the original fine normals in
an occupied pin/class fiber.  Consequently the estimate gains the size of
that fiber; the pins themselves need not be replaced at the coarse scale.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators Classical

/-- A finite family of unit normals almost perpendicular to a long vector
lies in two antipodal caps. -/
theorem unit_normals_two_caps (E : Finset E2) {v : E2} {A d : ℝ}
    (hA : 0 < A) (hd : 2 * A ≤ d) (hv : d ≤ ‖v‖)
    (hunit : ∀ e ∈ E, ‖e‖ = 1)
    (hinner : ∀ e ∈ E, |inner ℝ v e| < A) :
    ∃ u : E2, ‖u‖ = 1 ∧ ∀ e ∈ E,
      dist e u ≤ 4 * A / d ∨ dist e (-u) ≤ 4 * A / d := by
  have hdpos : 0 < d := by linarith
  by_cases hE : E.Nonempty
  · obtain ⟨u, hu⟩ := hE
    refine ⟨u, hunit u hu, ?_⟩
    intro e he
    have hratio : (A / d) ^ 2 ≤ 1 / 2 := by
      have hle : A / d ≤ 1 / 2 := by rw [div_le_iff₀ hdpos]; linarith
      have hnonneg : 0 ≤ A / d := by positivity
      nlinarith
    have hh := normals_close_of_long_vector hdpos (hunit e he) (hunit u hu) hv
      (hinner e he) (hinner u hu) hratio hratio
    have heq : (A + A) / d = 2 * (A / d) := by ring
    have heq' : 4 * A / d = 4 * (A / d) := by ring
    rw [heq] at hh
    rw [heq', dist_eq_norm, dist_eq_norm]
    have hpos : 0 < A / d := by positivity
    rcases hh with hh | hh
    · left
      nlinarith [sq_nonneg (‖e - u‖ - 4 * (A / d))]
    · right
      nlinarith [sq_nonneg (‖e - -u‖ - 4 * (A / d))]
  · obtain ⟨u, hu⟩ : ∃ u : E2, ‖u‖ = 1 := exists_norm_eq E2 zero_le_one
    exact ⟨u, hu, fun e he => (hE ⟨e, he⟩).elim⟩

/-- Geometry of assigned coarse classes, with room for two successive
class assignments. No separation assumption on the classes is needed. -/
theorem coarse_shared_inner {R : ℝ} {D : Finset (E2 × E2)}
    {cls : E2 × E2 → E2 × E2}
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < R ∨ dist q.2 (-(cls q).2) < R))
    {p p' e : E2} (hp : ‖p‖ ≤ 4) (hp' : ‖p'‖ ≤ 4)
    (he : e ∈ sharedNormals D cls p p') :
    |inner ℝ (p - p') e| < 72 * R := by
  obtain ⟨hb, hshare⟩ := Finset.mem_filter.mp he
  obtain ⟨e', he', hcls⟩ := mem_pinsOf.mp hshare
  have h₁ := hgeo (p, e) (mem_bushOf.mp hb)
  have h₂ := hgeo (p', e') he'
  rw [hcls] at h₂
  let n := (cls (p, e)).2
  have hcoarse : |inner ℝ (p - p') n| < 64 * R := by
    have hid : p - p' = (p - (cls (p, e)).1) - (p' - (cls (p, e)).1) := by abel
    rw [hid, inner_sub_left]
    exact (abs_sub _ _).trans_lt (by dsimp [n]; linarith [h₁.1, h₂.1])
  have hnorm : ‖p - p'‖ ≤ 8 := (norm_sub_le _ _).trans (by linarith)
  have hperturb : ∀ f : E2, ‖e - f‖ < R →
      |inner ℝ (p - p') (e - f)| ≤ 8 * R := by
    intro f hf
    have hR : 0 ≤ R := (norm_nonneg _).trans hf.le
    calc
      |inner ℝ (p - p') (e - f)| ≤ ‖p - p'‖ * ‖e - f‖ := abs_real_inner_le_norm _ _
      _ ≤ 8 * R := mul_le_mul hnorm hf.le (norm_nonneg _) (by norm_num)
  rcases h₁.2 with ha | ha
  · have hid : inner ℝ (p - p') e = inner ℝ (p - p') n + inner ℝ (p - p') (e - n) := by
      rw [inner_sub_right]; ring
    rw [dist_eq_norm] at ha
    rw [hid]
    exact (abs_add_le _ _).trans_lt (by linarith [hperturb n ha])
  · have hid : inner ℝ (p - p') e = -inner ℝ (p - p') n + inner ℝ (p - p') (e - -n) := by
      rw [inner_sub_right, inner_neg_right]; ring
    rw [dist_eq_norm] at ha
    rw [hid]
    have hh := hperturb (-n) ha
    exact (abs_add_le _ _).trans_lt (by rw [abs_neg]; linarith)

/-- Shared fine normals obey the original cap bound even for thick coarse
classes. The near-diagonal truncation makes the angular radius at most two. -/
theorem coarse_shared_le_capBound {r R : ℝ} (hrR : r ≤ R) (hR : 0 < R) (hR1 : R ≤ 1)
    {D : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < R ∨ dist q.2 (-(cls q).2) < R))
    (Bd : ℝ → ℝ) {p p' : E2} (hp : ‖p‖ ≤ 4) (hp' : ‖p'‖ ≤ 4)
    (hcap : ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter fun e => dist e u ≤ ρ).card : ℝ) ≤ Bd ρ) :
    ((sharedNormals D cls p p').card : ℝ) ≤
      2 * Bd (288 * R / max (dist p p') (144 * R)) := by
  have hdist : dist p p' ≤ 8 := by rw [dist_eq_norm]; exact (norm_sub_le _ _).trans (by linarith)
  have hsharedunit : ∀ e ∈ sharedNormals D cls p p', ‖e‖ = 1 :=
    fun e he => hunit (p, e) (mem_bushOf.mp (Finset.mem_filter.mp he).1)
  by_cases hfar : 144 * R ≤ dist p p'
  · have hdpos : 0 < dist p p' := by linarith
    obtain ⟨u, hu, hcover⟩ := unit_normals_two_caps (sharedNormals D cls p p')
      (v := p - p') (A := 72 * R) (d := dist p p') (by positivity) (by linarith)
      (by rw [dist_eq_norm]) hsharedunit (fun e he => coarse_shared_inner hgeo hp hp' he)
    let ρ := 288 * R / dist p p'
    have hρ : r ≤ ρ := by
      apply hrR.trans
      dsimp [ρ]
      rw [le_div_iff₀ hdpos]
      nlinarith
    have hsub : sharedNormals D cls p p' ⊆
        ((bushOf D p).filter fun e => dist e u ≤ ρ) ∪
        ((bushOf D p).filter fun e => dist e (-u) ≤ ρ) := by
      intro e he
      have hb := (Finset.mem_filter.mp he).1
      have hh := hcover e he
      have heq : 4 * (72 * R) / dist p p' = ρ := by dsimp [ρ]; ring
      rw [heq] at hh
      rcases hh with hh | hh
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, hh⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, hh⟩)
    rw [max_eq_left hfar]
    calc
      ((sharedNormals D cls p p').card : ℝ) ≤
          (((bushOf D p).filter fun e => dist e u ≤ ρ).card : ℝ) +
          (((bushOf D p).filter fun e => dist e (-u) ≤ ρ).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      _ ≤ Bd ρ + Bd ρ := add_le_add (hcap u hu ρ hρ) (hcap (-u) (by simpa using hu) ρ hρ)
      _ = _ := by dsimp [ρ]; ring
  · have hnear : dist p p' ≤ 144 * R := le_of_not_ge hfar
    obtain ⟨u, hu⟩ : ∃ u : E2, ‖u‖ = 1 := exists_norm_eq E2 zero_le_one
    have hsub : sharedNormals D cls p p' ⊆ (bushOf D p).filter fun e => dist e u ≤ 2 := by
      intro e he
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, ?_⟩
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by rw [hsharedunit e he, hu]; norm_num)
    have hh := hcap u hu 2 (hrR.trans (by linarith))
    have hh0 : 0 ≤ Bd 2 := (Nat.cast_nonneg _).trans hh
    rw [max_eq_right hnear, show 288 * R / (144 * R) = 2 by field_simp; ring]
    have hc : ((sharedNormals D cls p p').card : ℝ) ≤ Bd 2 :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hh
    linarith

/-- Every occupied pin/class fiber contributes all its fine normals to the
common-normal count. -/
theorem mass_mul_common_classes_le_shared (D J : Finset (E2 × E2))
    (cls : E2 × E2 → E2 × E2) (p p' : E2) {m : ℝ}
    (hmin : ∀ j ∈ J, p ∈ pinsOf D cls j →
      m ≤ (((bushOf D p).filter fun e => cls (p, e) = j).card : ℝ)) :
    m * ((J.filter fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j).card : ℝ) ≤
      (sharedNormals D cls p p').card := by
  let C := J.filter fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j
  let F (j : E2 × E2) := (bushOf D p).filter fun e => cls (p, e) = j
  have hdisj : (C : Set (E2 × E2)).PairwiseDisjoint F := by
    intro j hj j' hj' hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro e he he'
    exact hne ((Finset.mem_filter.mp he).2.symm.trans (Finset.mem_filter.mp he').2)
  have hsub : C.biUnion F ⊆ sharedNormals D cls p p' := by
    intro e he
    obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨heD, hec⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨heD, ?_⟩
    rw [hec]
    exact (Finset.mem_filter.mp hj).2.2
  calc
    m * (C.card : ℝ) = ∑ _j ∈ C, m := by simp [mul_comm]
    _ ≤ ∑ j ∈ C, ((F j).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hmin j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2.1
    _ = ((C.biUnion F).card : ℝ) := by rw [Finset.card_biUnion hdisj, Nat.cast_sum]
    _ ≤ (sharedNormals D cls p p').card := Nat.cast_le.mpr (Finset.card_le_card hsub)

/-- The coarse common-class estimate with the crucial pin/class mass gain. -/
theorem coarse_common_classes_le {r R m : ℝ} (hrR : r ≤ R) (hR : 0 < R) (hR1 : R ≤ 1)
    (hm : 0 < m) {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < R ∨ dist q.2 (-(cls q).2) < R))
    (Bd : ℝ → ℝ) {p p' : E2} (hp : ‖p‖ ≤ 4) (hp' : ‖p'‖ ≤ 4)
    (hcap : ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter fun e => dist e u ≤ ρ).card : ℝ) ≤ Bd ρ)
    (hmin : ∀ j ∈ J, p ∈ pinsOf D cls j →
      m ≤ (((bushOf D p).filter fun e => cls (p, e) = j).card : ℝ)) :
    ((J.filter fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j).card : ℝ) ≤
      2 * Bd (288 * R / max (dist p p') (144 * R)) / m := by
  rw [le_div_iff₀ hm, mul_comm]
  exact (mass_mul_common_classes_le_shared D J cls p p' hmin).trans
    (coarse_shared_le_capBound hrR hR hR1 hunit hgeo Bd hp hp' hcap)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
