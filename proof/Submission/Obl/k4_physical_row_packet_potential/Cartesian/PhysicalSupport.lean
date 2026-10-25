-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/PhysicalSupport.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/PhysicalSupport.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/PhysicalSupport.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.MeasureCapture

/-!
A global count pays for deleting light physical cells. Surviving cell
floors and the old coarse mass ceilings then give hereditary support
counts against the same original incidence law.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- The total original mass of globally light code cells is charged only
to the number of cells, without normalizing the surviving mass. -/
theorem light_code_mass_le {n : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (code : X → Fin n) (hcode : Measurable code) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {x | codeWeight μ code (code x) < a} ≤ (n : ℝ) * a := by
  classical
  rw [← sum_codeWeight_predicate μ code hcode (fun i => codeWeight μ code i < a)]
  calc
    _ ≤ ∑ _i : Fin n, a := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : codeWeight μ code i < a
      · simpa only [ite_eq_left hi] using hi.le
      · simp only [ite_eq_right hi]
        exact ha
    _ = (n : ℝ) * a := by simp

/-- Fine cell floors and an unchanged coarse mass cap bound the number of
fine cells contained in the coarse event. -/
theorem code_cell_count_from_floor {n : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (code : X → Fin n) (hcode : Measurable code) (I : Finset (Fin n))
    (E : Set X) (a U : ℝ) (ha : 0 < a)
    (hfloor : ∀ i ∈ I, a ≤ codeWeight μ code i)
    (hcontain : ∀ i ∈ I, code ⁻¹' {i} ⊆ E) (hcap : μ.real E ≤ U) :
    (I.card : ℝ) ≤ U / a := by
  classical
  have hsum : (∑ i ∈ I, codeWeight μ code i) ≤ μ.real E := by
    have h := sum_codeWeight_predicate μ code hcode (fun i => i ∈ I)
    have hfilter : Finset.univ.filter (fun i => i ∈ I) = I := by ext i; simp
    rw [← Finset.sum_filter, hfilter] at h
    rw [h]
    exact measureReal_mono (fun x hx => hcontain (code x) hx (by simp))
  apply (le_div_iff₀ ha).mpr
  calc
    (I.card : ℝ) * a = ∑ _i ∈ I, a := by simp
    _ ≤ ∑ i ∈ I, codeWeight μ code i := Finset.sum_le_sum fun i hi => hfloor i hi
    _ ≤ U := hsum.trans hcap

/-- The hereditary `(w/p)^alpha` support count after light-cell deletion. -/
theorem hereditary_code_count {n : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (code : X → Fin n) (hcode : Measurable code) (I : Finset (Fin n))
    (E : Set X) (K p w α : ℝ) (hK : 0 < K) (hp : 0 < p) (hw : 0 < w)
    (hfloor : ∀ i ∈ I, p ^ α / K ≤ codeWeight μ code i)
    (hcontain : ∀ i ∈ I, code ⁻¹' {i} ⊆ E) (hcap : μ.real E ≤ K * w ^ α) :
    (I.card : ℝ) ≤ K ^ 2 * (w / p) ^ α := by
  have h := code_cell_count_from_floor μ code hcode I E (p ^ α / K) (K * w ^ α)
    (by positivity) hfloor hcontain hcap
  refine h.trans_eq ?_
  rw [Real.div_rpow hw.le hp.le]
  field_simp

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
