-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PlanarRow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PlanarGeometry
import Submission.WZ.Obl.wz_off_stem_brush_overlap.Counts
import Submission.WZ.Obl.wz_off_stem_brush_overlap.Summation
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PlanarRow.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_off_stem_brush_overlap (angle)

/-- The planar angular count and reciprocal intersection bound yield a full overlap row,
with an arbitrarily small power loss in place of the dyadic logarithm. -/
lemma planar_overlap_row (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b δ r D : ℝ), 0 < a → a ≤ b → b ≤ 1 →
      δ ≤ r → 0 < r → r ≤ 1 → 0 ≤ D → ∀ (n : ℕ) (x v : Fin n → Space)
      (c e₁ e₂ e₃ : Space),
      Orthonormal ℝ ![e₁, e₂, e₃] → (∀ i, ‖v i‖ = 1) →
      (∀ i, tube δ (x i) (v i) ⊆ prism a b c e₁ e₂ e₃) →
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) *
          volume (prism a b c e₁ e₂ e₃) ≤ ENNReal.ofReal (D * n) * volume U) →
      ∀ i : Fin n,
        (∑ j : Fin n, (volume (tube r (x i) (v i) ∩ tube r (x j) (v j))).toReal) ≤
          C * r ^ (-ε) * (D * n * r ^ 3 / b) := by
  classical
  obtain ⟨C, hC, hsum⟩ := WangZahlLot.Obl.wz_off_stem_brush_overlap.power_weighted_sum ε hε
  refine ⟨131072 * C, by positivity, ?_⟩
  intro a b δ r D ha hab hb hδr hr hr1 hD n x v c e₁ e₂ e₃ he hv hP hcount i
  have hb0 : 0 < b := ha.trans_le hab
  let F : Finset (Fin n) := Finset.univ.filter fun j =>
    (tube r (x i) (v i) ∩ tube r (x j) (v j)).Nonempty
  let m : Fin n → ℝ := fun j => (volume (tube r (x i) (v i) ∩ tube r (x j) (v j))).toReal
  let d : Fin n → ℝ := fun j => max r (angle (v i) (v j))
  have hrow := hsum F m d r (8 * D * n / b) (8192 * r ^ 3) hr hr1
    (by positivity) (by positivity) (fun j _ => ENNReal.toReal_nonneg)
    (fun j _ => ⟨le_max_left _ _, max_le (hr1.trans (by norm_num))
      (WangZahlLot.Obl.wz_off_stem_brush_overlap.angle_le_two (hv i) (hv j))⟩)
    (by
      intro j _
      have h := WangZahlLot.Obl.wz_off_stem_brush_overlap.regularized_intersection (x := x i) (y := x j) hr hr1 (hv i) (hv j)
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rw [ENNReal.toReal_ofReal (by positivity)] at ht
      exact ht)
    (by
      intro θ hθ
      apply planar_cap_count ha hab hb hδr hr hθ hD x v he hP hcount i
      intro j hj
      obtain ⟨hjF, hjθ⟩ := Finset.mem_filter.mp hj
      refine ⟨(Finset.mem_filter.mp hjF).2, ?_⟩
      exact (le_max_right _ _).trans hjθ)
  have heq : ∑ j : Fin n, m j = ∑ j ∈ F, m j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hempty : tube r (x i) (v i) ∩ tube r (x j) (v j) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hj'
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩)
    simp only [m, hempty, measure_empty, ENNReal.toReal_zero]
  rw [← heq] at hrow
  calc
    _ ≤ C * r ^ (-ε) * (2 * (8 * D * n / b) * (8192 * r ^ 3)) := hrow
    _ = _ := by ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
