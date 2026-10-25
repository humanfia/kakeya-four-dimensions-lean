/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/SourceBounds.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
/- The base/native witness bounds are adapted from this LOT tree, obligation
   o200, session x0829, commit a965423f,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ModelNativeCalibration.lean.
   Here the data and Basic predicate are imported from accepted o238. -/
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.Model
import Submission.Lib.K4CommonLocalChoice
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.OriginalMarking

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4CommonLocalChoice (cell)

noncomputable section

theorem data_z_eq_cell {α : Type} [MeasurableSpace α] (D : Data α)
    (k : ℕ) (N r : ℝ) (p : α × ℝ) :
    D.z k N r p = cell (N ^ (-r)) (D.x k p.1 p.2 ∘ Fin.castSucc) := by
  funext j
  fin_cases j <;> rfl

/-- Every original incidence has a bounded three-dimensional base. The
hidden trajectory coefficients are deliberately absent from this estimate. -/
theorem basic_base_bound {α : Type} [MeasurableSpace α]
    (D : Data α) (hK : ∀ k, 1 ≤ D.K k) (h1 : D.Basic) (k : ℕ) :
    ∀ᵐ p ∂D.μ k, ∀ j : Fin 3, |D.x k p.1 p.2 j.castSucc| ≤ D.K k := by
  obtain ⟨hb, hν, hπ, hdom, hρ, hsupp, hmass, hdeg, hcoeff, hnative⟩ := h1 k
  haveI := hν
  have hbμ : ∀ᵐ p ∂D.μ k,
      |D.b k p.1 0| + |D.b k p.1 1| + |D.b k p.1 3| + |D.b k p.1 4| ≤ D.K k := by
    apply ae_mono hdom
    apply Measure.ae_smul_measure
    exact (Measure.quasiMeasurePreserving_fst (μ := D.ν k) (ν := (volume : Measure ℝ))).ae hcoeff
  have htμ : ∀ᵐ p ∂D.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    convert hsupp using 1
    congr 1
    ext p
    simp
  filter_upwards [hbμ, htμ] with p hp ht j
  have htbound : |p.2| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hlin (i j : Fin 6) :
      |D.b k p.1 i + p.2 * D.b k p.1 j| ≤ |D.b k p.1 i| + |D.b k p.1 j| := by
    calc
      _ ≤ |D.b k p.1 i| + |p.2| * |D.b k p.1 j| := by
        simpa only [abs_mul] using abs_add_le (D.b k p.1 i) (p.2 * D.b k p.1 j)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right htbound (abs_nonneg (D.b k p.1 j))
        simpa only [one_mul] using add_le_add_right hh |D.b k p.1 i|
  fin_cases j
  · change |p.2| ≤ D.K k
    exact htbound.trans (hK k)
  · change |D.b k p.1 0 + p.2 * D.b k p.1 3| ≤ D.K k
    exact (hlin 0 3).trans (by linarith [abs_nonneg (D.b k p.1 1), abs_nonneg (D.b k p.1 4)])
  · change |D.b k p.1 1 + p.2 * D.b k p.1 4| ≤ D.K k
    exact (hlin 1 4).trans (by linarith [abs_nonneg (D.b k p.1 0), abs_nonneg (D.b k p.1 3)])

theorem basic_native_value_bounds {α : Type} [MeasurableSpace α]
    (D : Data α) (h1 : D.Basic) (k : ℕ) :
    ∀ᵐ p ∂D.μ k,
      |eval (D.x k p.1 p.2) (D.P k)| ≤ D.K k ∧
      |eval (D.x k p.1 p.2) (pderiv 3 (D.P k))| ≤ D.K k ∧
      |eval (D.x k p.1 p.2) (pderiv 3 (pderiv 3 (D.P k)))| ≤ D.K k := by
  obtain ⟨_, _, _, _, _, hsupp, _, _, _, hnative⟩ := h1 k
  have htμ : ∀ᵐ p ∂D.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    convert hsupp using 1
    congr 1
    ext p
    simp
  filter_upwards [htμ, hnative] with p hp hn
  exact hn.1 p.2 hp


/-- Unit time support and original product domination make the source finite. -/
theorem basic_incidence_finite {α : Type} [MeasurableSpace α]
    (D : Data α) (h : D.Basic) (k : ℕ) : IsFiniteMeasure (D.μ k) := by
  letI : IsProbabilityMeasure (D.ν k) := (h k).2.1
  have hb := Submission.Obl.k4_scalar_marked_coefficient_smoothing.original_time_support
    (D.ν k) (D.μ k) (h k).2.2.2.1 (h k).2.2.2.2.2.1
  exact ⟨hb.2.trans_lt ENNReal.ofReal_lt_top⟩

theorem basic_residual_finite {α : Type} [MeasurableSpace α]
    (D : Data α) (h : D.Basic) (k : ℕ) : IsFiniteMeasure (D.ρ k) := by
  letI := basic_incidence_finite D h k
  exact isFiniteMeasure_of_le (D.μ k) (h k).2.2.2.2.1

end
end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
