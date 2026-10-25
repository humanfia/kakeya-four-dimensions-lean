-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Saturation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoverCounts

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file Saturation.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization
  (Upper count count_univ ncard_fintype cancel_scaled_measure)

attribute [local instance] Classical.propDecidable

/-- Saturating a convex-count bound gives balance, counting above, and Frostman
control below.  The common volume is an explicit real parameter. -/
theorem saturated_cover_bounds {n p : ℕ} (A : Fin n → Set Space)
    (P : Fin p → Set Space) {w V c L D : ℝ}
    (hw : 0 < w) (hV : 0 ≤ V) (hc : 0 < c) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hupper : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((contained A U : ℝ) * w) ≤ ENNReal.ofReal c * volume U)
    (hP : ∀ j, Convex ℝ (P j) ∧ volume (P j) = ENNReal.ofReal V)
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hsat : ∀ j, c * V ≤ L * (contained A (P j) : ℝ) * w) :
    (∀ j j', (contained A (P j) : ℝ) ≤ L * contained A (P j')) ∧
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((contained P U : ℝ) * V) ≤ ENNReal.ofReal (L * D) * volume U) ∧
    (∀ j (U : Set Space), Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * V) ≤
        ENNReal.ofReal (L * contained A (P j)) * volume U) := by
  classical
  have hu : Upper A w Finset.univ c := by
    intro U hU
    rw [count_univ]
    exact hupper U hU
  have hbound (j) : (contained A (P j) : ℝ) * w ≤ c * V := by
    have hh := hupper (P j) (hP j).1
    rw [(hP j).2, ← ENNReal.ofReal_mul hc.le] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc.le hV)).mp hh
  refine ⟨?_, ?_, ?_⟩
  · intro j j'
    apply (mul_le_mul_iff_left₀ hw).mp
    exact (hbound j).trans (hsat j')
  · intro U hU
    let J := Finset.univ.filter fun j => P j ⊆ U
    have hscale : c * ((contained P U : ℝ) * V) ≤
        (L * D) * ((contained A U : ℝ) * w) := by
      calc
        _ = ∑ _j ∈ J, c * V := by rw [contained_eq_card]; simp [J]; ring
        _ ≤ ∑ j ∈ J, L * (contained A (P j) : ℝ) * w :=
          Finset.sum_le_sum fun j _ => hsat j
        _ = L * (∑ j ∈ J, (contained A (P j) : ℝ)) * w := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ ≤ L * (D * contained A U) * w := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (cover_incidence_le A P hD hdegree U) hL) hw.le
        _ = _ := by ring
    exact cancel_scaled_measure (by positivity) (by positivity) hc hscale (hupper U hU)
  · intro j U hU
    have hscale : c * V ≤ (L * contained A (P j)) * w := hsat j
    have hh := ((hu.subset hw.le (Finset.filter_subset (fun i => A i ⊆ P j) Finset.univ)).rescale
      hw hV hc.le (by positivity) hscale) U hU
    convert hh using 1
    congr 3
    rw [ncard_fintype]
    simp only [count, Finset.filter_filter]
    congr 1
    ext i
    simp

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
