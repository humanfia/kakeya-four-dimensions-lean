import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Interface
import Submission.Lib.K4ModelReduction.FiniteTable
import Submission.Lib.K4ContinuousPlanks.Discretization

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

/-- A finite measurable rounding of all five coefficients, retaining exact prior masses. -/
theorem finite_coefficient_rounding {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (b : α → Coeff) (hb : Measurable b)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hbound : ∀ l i, |b l i| ≤ K) :
    ∃ (H : ℕ) (tag : α → Fin H) (b₀ : Fin H → Coeff) (w : Fin H → ℝ),
      Measurable tag ∧
      (∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}) ∧
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
      (∀ l i, |b l i - b₀ (tag l) i| ≤ δ) ∧
      (∀ j i, |b₀ j i| ≤ K + δ) ∧
      (H : ℝ) ≤ (2 * K / δ + 2) ^ 5 := by
  classical
  let C := Submission.Lib.K4ModelReduction.meshCodes (Fin 5) δ K
  let e : C ≃ Fin C.card := C.equivFin
  let code : α → C := fun l =>
    ⟨Submission.Lib.K4ModelReduction.meshTag δ (b l),
      Submission.Lib.K4ModelReduction.meshTag_mem_codes hδ (b l) (hbound l)⟩
  let tag : α → Fin C.card := fun l => e (code l)
  let b₀ : Fin C.card → Coeff := fun j =>
    Submission.Lib.K4ModelReduction.meshRepresentative δ (e.symm j).val
  let w : Fin C.card → ℝ := fun j => (ν {l | tag l = j}).toReal
  have hcode : Measurable code :=
    (Submission.Lib.K4ModelReduction.meshTag_measurable δ |>.comp hb).subtype_mk
  have htag : Measurable tag := (measurable_of_countable e).comp hcode
  refine ⟨C.card, tag, b₀, w, htag, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ENNReal.ofReal_toReal (measure_ne_top ν _)
  · intro j
    exact ENNReal.toReal_nonneg
  · have h := Submission.Lib.K4ContinuousPlanks.finite_fiber_real_mass
      ν tag htag Finset.univ
    simpa [w, Set.preimage, measure_univ] using h
  · intro l i
    have h := (Submission.Lib.K4ModelReduction.meshTag_eq_iff hδ (b l)
      (Submission.Lib.K4ModelReduction.meshTag δ (b l))).mp rfl i
    have heq : b₀ (tag l) i = δ *
        ((Submission.Lib.K4ModelReduction.meshTag δ (b l) i : ℤ) : ℝ) := by
      simp [b₀, tag, code, Submission.Lib.K4ModelReduction.meshRepresentative]
    rw [heq, abs_of_nonneg (sub_nonneg.mpr h.1)]
    linarith [h.2]
  · intro j i
    have hc : (e.symm j).val ∈
        Submission.Lib.K4ModelReduction.meshCodes (Fin 5) δ K := (e.symm j).property
    simp only [Submission.Lib.K4ModelReduction.meshCodes, Fintype.mem_piFinset] at hc
    have hi := Finset.mem_Icc.mp (hc i)
    have hlow := Int.lt_floor_add_one (-K / δ)
    have hhigh := Int.floor_le (K / δ)
    have hlo : -K / δ - 1 ≤ (((e.symm j).val i : ℤ) : ℝ) := by
      have hh : (⌊-K / δ⌋ : ℝ) ≤ (((e.symm j).val i : ℤ) : ℝ) := by exact_mod_cast hi.1
      linarith
    have hhi : (((e.symm j).val i : ℤ) : ℝ) ≤ K / δ := by
      exact le_trans (by exact_mod_cast hi.2) hhigh
    change |δ * (((e.symm j).val i : ℤ) : ℝ)| ≤ K + δ
    rw [abs_le]
    constructor
    · have hh := mul_le_mul_of_nonneg_left hlo hδ.le
      field_simp at hh
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left hhi hδ.le
      field_simp at hh
      nlinarith
  · simpa [C] using
      (Submission.Lib.K4ModelReduction.meshCodes_card_le (ι := Fin 5) hδ hK)

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
