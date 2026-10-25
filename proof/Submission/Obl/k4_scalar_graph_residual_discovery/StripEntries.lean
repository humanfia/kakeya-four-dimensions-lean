/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file StripEntries.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.CurveCells

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

def stripLabel (b ρ p : ℝ) (row : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (w : Fin 3 → ℤ) : (Fin 3 → ℤ) × ℤ :=
  (cell ρ (leftCorner b w),
    ⌊normalCoordinate (row (cell ρ (leftCorner b w))) (leftCorner b w) / p⌋)

def stripRecord (b ρ p : ℝ) (row : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (z : ScalarIncidence) : (Fin 3 → ℤ) × ℤ :=
  stripLabel b ρ p row (cell b (scalarPosition z))

/-- Strip assignment is a measurable function of the entire fine physical
state, even when the row representatives are chosen arbitrarily. -/
theorem measurable_stripRecord (b ρ p : ℝ) (row : (Fin 3 → ℤ) → Fin 2 → ℝ) :
    Measurable (stripRecord b ρ p row) :=
  (measurable_of_countable (stripLabel b ρ p row)).comp
    (measurable_cell b measurable_scalarPosition)

/-- Endpoint derivative control also bounds the normal coordinates of the
assigned fine-state centers, uniformly within one coarse physical cell. -/
theorem normal_center_variation (row : Fin 2 → ℝ) (l : ScalarLine)
    {b ρ A D t u : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (hA : 1 + |row 0| + |row 1| ≤ A)
    (ht : |(normalPolynomial row l).derivative.eval t| ≤ D)
    (hu : |(normalPolynomial row l).derivative.eval u| ≤ D)
    (hcell : cell ρ (leftCorner b (cell b (scalarPosition (l, t)))) =
      cell ρ (leftCorner b (cell b (scalarPosition (l, u))))) :
    |normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t)))) -
      normalCoordinate row (leftCorner b (cell b (scalarPosition (l, u))))| ≤
        D * (ρ + 2 * b) + 2 * A * b := by
  have hD : 0 ≤ D := (abs_nonneg _).trans ht
  have hgap : |t - u| ≤ ρ + 2 * b := by
    have htime : |t - u| ≤ ‖scalarPosition (l, t) - scalarPosition (l, u)‖ :=
      norm_le_pi_norm (scalarPosition (l, t) - scalarPosition (l, u)) 0
    exact htime.trans (same_assigned_cell_distance hb hρ _ _ hcell)
  have hvar : |normalCoordinate row (scalarPosition (l, t)) -
      normalCoordinate row (scalarPosition (l, u))| ≤ D * (ρ + 2 * b) := by
    have hv := quadratic_variation_of_endpoint_bounds (normalPolynomial row l)
      (normalPolynomial_degree row l) ht hu
    rw [normalPolynomial_eval, normalPolynomial_eval] at hv
    exact hv.trans (mul_le_mul_of_nonneg_left hgap hD)
  have he (v : ℝ) : |normalCoordinate row (scalarPosition (l, v)) -
      normalCoordinate row (leftCorner b (cell b (scalarPosition (l, v))))| ≤ A * b :=
    (normalCoordinate_center_error hb row _).trans
      (mul_le_mul_of_nonneg_right hA hb.le)
  calc
    _ ≤ |normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t)))) -
          normalCoordinate row (scalarPosition (l, t))| +
        |normalCoordinate row (scalarPosition (l, t)) -
          normalCoordinate row (leftCorner b (cell b (scalarPosition (l, u))))| :=
      abs_sub_le _ _ _
    _ ≤ |normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t)))) -
          normalCoordinate row (scalarPosition (l, t))| +
        (|normalCoordinate row (scalarPosition (l, t)) -
            normalCoordinate row (scalarPosition (l, u))| +
          |normalCoordinate row (scalarPosition (l, u)) -
            normalCoordinate row (leftCorner b (cell b (scalarPosition (l, u))))|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ A * b + (D * (ρ + 2 * b) + A * b) := by
      exact add_le_add (by simpa only [abs_sub_comm] using he t) (add_le_add hvar (he u))
    _ = _ := by ring

/-- Each original trajectory has a bounded list of normal-strip labels in a
fixed assigned physical cell, even when its labeled times have gaps. -/
theorem trajectory_cell_normal_list (row : Fin 2 → ℝ) (l : ScalarLine) (T : Set ℝ)
    (q : Fin 3 → ℤ) {b ρ p A D : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (hp : 0 < p)
    (hA : 1 + |row 0| + |row 1| ≤ A) (hD : 0 ≤ D)
    (hderiv : ∀ t ∈ T,
      cell ρ (leftCorner b (cell b (scalarPosition (l, t)))) = q →
        |(normalPolynomial row l).derivative.eval t| ≤ D) :
    ∃ L : Finset ℤ, (L.card : ℝ) ≤ 2 * (D * (ρ + 2 * b) + 2 * A * b) / p + 2 ∧
      ∀ t ∈ T, cell ρ (leftCorner b (cell b (scalarPosition (l, t)))) = q →
        ⌊normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t)))) / p⌋ ∈ L := by
  classical
  let s : Set ℝ := (fun t => normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t))))) ''
    {t | t ∈ T ∧ cell ρ (leftCorner b (cell b (scalarPosition (l, t)))) = q}
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ 1 + |row 0| + |row 1|).trans hA
  have hbound : 0 ≤ D * (ρ + 2 * b) + 2 * A * b := by positivity
  have hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ D * (ρ + 2 * b) + 2 * A * b := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
    simpa only [Real.dist_eq] using normal_center_variation row l hb hρ hA
      (hderiv t ht.1 ht.2) (hderiv u hu.1 hu.2) (ht.2.trans hu.2.symm)
  obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    s hbound hp 0 hdiam
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rwa [← Set.ncard_eq_toFinset_card _ hfin]
  · intro t ht hq
    apply hfin.mem_toFinset.mpr
    refine ⟨normalCoordinate row (leftCorner b (cell b (scalarPosition (l, t)))), ?_, ?_⟩
    · exact ⟨t, ⟨ht, hq⟩, rfl⟩
    · simp only [sub_zero]

/-- Combining the physical-cell and within-cell normal lists gives the
trajectory entry count needed before summing all short-duration deletions. -/
theorem trajectory_strip_entry_list (row : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (l : ScalarLine) (T : Set ℝ) {H b ρ p A D : ℝ}
    (hH : 1 ≤ H) (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ) (hp : 0 < p)
    (hcoeff : ∀ e, |l.2 e| ≤ H) (hT : T ⊆ Icc (0 : ℝ) 1)
    (hA : ∀ q, 1 + |row q 0| + |row q 1| ≤ A) (hD : 0 ≤ D)
    (hderiv : ∀ t ∈ T,
      |(normalPolynomial
        (row (cell ρ (leftCorner b (cell b (scalarPosition (l, t)))))) l).derivative.eval t| ≤ D) :
    ∃ L : Finset ((Fin 3 → ℤ) × ℤ),
      (L.card : ℝ) ≤ 343 * (3 * H / ρ + 2) *
        (2 * (D * (ρ + 2 * b) + 2 * A * b) / p + 2) ∧
      ∀ t ∈ T,
        (cell ρ (leftCorner b (cell b (scalarPosition (l, t)))),
          ⌊normalCoordinate (row (cell ρ (leftCorner b (cell b (scalarPosition (l, t))))))
            (leftCorner b (cell b (scalarPosition (l, t)))) / p⌋) ∈ L := by
  classical
  obtain ⟨Q, hQcard, hQmem⟩ := scalar_trajectory_assigned_cell_list hH hρ hb hbρ l hcoeff
  have hcellList (q : Fin 3 → ℤ) := trajectory_cell_normal_list (row q) l T q
    hb hρ hp (hA q) hD (by
      intro t ht hq
      simpa only [hq] using hderiv t ht)
  choose F hFcard hFmem using hcellList
  let L := Q.biUnion (fun q => (F q).image (Prod.mk q))
  let B : ℝ := 2 * (D * (ρ + 2 * b) + 2 * A * b) / p + 2
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ 1 + |row 0 0| + |row 0 1|).trans (hA 0)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨L, ?_, ?_⟩
  · calc
      (L.card : ℝ) ≤ ∑ q ∈ Q, (((F q).image (Prod.mk q)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := Q) (t := fun q => (F q).image (Prod.mk q))
      _ ≤ ∑ q ∈ Q, ((F q).card : ℝ) := Finset.sum_le_sum (fun q _ => by
        exact_mod_cast Finset.card_image_le)
      _ ≤ ∑ _q ∈ Q, B := Finset.sum_le_sum (fun q _ => hFcard q)
      _ = (Q.card : ℝ) * B := by simp [nsmul_eq_mul]
      _ ≤ 343 * (3 * H / ρ + 2) * B := mul_le_mul_of_nonneg_right hQcard hB
      _ = _ := rfl
  · intro t ht
    let q := cell ρ (leftCorner b (cell b (scalarPosition (l, t))))
    exact Finset.mem_biUnion.mpr ⟨q, hQmem t (hT ht),
      Finset.mem_image.mpr ⟨_, hFmem q t ht rfl, rfl⟩⟩

end

end Submission.Obl.k4_scalar_graph_residual_discovery
