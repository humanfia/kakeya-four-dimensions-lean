import Submission.Obl.k4_horizon_chart_assembly.Groups
import Submission.Obl.k4_horizon_chart_assembly.TimeTransport
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped BigOperators ENNReal
open Submission.Obl.k4_eligibility_sign_description

noncomputable section

private abbrev BF {n : ℕ} (H : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) :=
  Submission.Obl.k4_dyadic_crop_worlds.BoolFormat H D A

/-- Use the sign-format bridge at its exact Boolean test count. -/
theorem fmt_of_signRep {n m d : ℕ} {H : ℝ} {S : Set (Fin n → ℝ)}
    (h : SignRep (fun x : Fin n → ℝ => x) m d (fun x => x ∈ S))
    (hcount : ((m + m : ℕ) : ℝ) ≤ H) : Fmt n H d S := by
  simpa only [PolynomialFormat, pow_one] using
    (polynomialFormat_of_signRep (N := H) (M := 1) h (by simpa using hcount))

/-- A half-open time interval uses precisely two Boolean polynomial tests. -/
theorem fmt_time_interval {n : ℕ} (e : Fin n) (s t : ℝ) :
    Fmt n 2 1 {x : Fin n → ℝ | x e ∈ Ico s t} := by
  classical
  refine ⟨2, le_rfl, ![X e - C s, X e - C t], ?_,
    fun b => b 0 && !(b 1), ?_⟩
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    all_goals exact (totalDegree_sub_C_le _ _).trans (by simp)
  · intro x
    simp only [mem_setOf_eq, mem_Ico, Bool.and_eq_true, Bool.not_eq_true',
      Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, eval_X, eval_C,
      decide_eq_true_eq, decide_eq_false_iff_not, not_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The coefficient section of an assignment lifts to the incidence coordinates
without adding tests or increasing degree. -/
theorem fmt_incident_assignment {H : ℝ} {D : ℕ} {A : Set (ℕ × (Fin 6 → ℝ))}
    (hA : ∀ i, Fmt 6 H D {x | (i, x) ∈ A}) (i : ℕ) :
    Fmt 7 H D {z : Fin 7 → ℝ | (i, fun e : Fin 6 => z e.castSucc) ∈ A} := by
  have h := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.affine_preimage (hA i)
    (fun e : Fin 6 => (X e.castSucc : MvPolynomial (Fin 7) ℝ)) (by intro e; simp)
  change BF H D {z : Fin 7 → ℝ | (i, fun e : Fin 6 => z e.castSucc) ∈ A}
  simpa only [eval_X, Set.preimage_setOf_eq] using h

/-- The selected incidences are measured under the original product law. -/
def selectedEvent (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (A : Set (ℕ × (Fin 6 → ℝ))) (P : MvPolynomial (Fin 4) ℝ)
    (floor s q : ℝ) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  E ∩ (A ×ˢ Ico s (s + q)) ∩
    Submission.Obl.k4_quadratic_atlas_normalization.derivativeFloorSet P floor

def derivativeEvent (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : MvPolynomial (Fin 4) ℝ) (floor : ℝ) :=
  E ∩ Submission.Obl.k4_quadratic_atlas_normalization.derivativeFloorSet P floor

theorem selectedEvent_eq (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (A : Set (ℕ × (Fin 6 → ℝ))) (P : MvPolynomial (Fin 4) ℝ) (floor s q : ℝ) :
    selectedEvent E A P floor s q = derivativeEvent E P floor ∩ (A ×ˢ Ico s (s + q)) := by
  ext p
  simp only [selectedEvent, derivativeEvent, mem_inter_iff]
  tauto

theorem selectedEvent_measurable {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {A : Set (ℕ × (Fin 6 → ℝ))} (hE : MeasurableSet E) (hA : MeasurableSet A)
    (P : MvPolynomial (Fin 4) ℝ) (floor s q : ℝ) :
    MeasurableSet (selectedEvent E A P floor s q) :=
  (hE.inter (hA.prod measurableSet_Ico)).inter
    (Submission.Obl.k4_quadratic_atlas_normalization.measurableSet_derivativeFloorSet P floor)

/-- Selection adds the original event format, two time tests, and two tests for
the derivative floor. -/
theorem selectedEvent_format {H HA : ℝ} {D DA : ℕ}
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (A : Set (ℕ × (Fin 6 → ℝ)))
    (hE : ∀ i, Fmt 7 H D {z : Fin 7 → ℝ |
      ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ E})
    (hA : ∀ i, Fmt 6 HA DA {x | (i, x) ∈ A})
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (floor s q : ℝ) (i : ℕ) :
    Fmt 7 (H + HA + 4) (max D (max DA 2)) {z : Fin 7 → ℝ |
      ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ selectedEvent E A P floor s q} := by
  have hAf := fmt_incident_assignment hA i
  have hT := fmt_time_interval (6 : Fin 7) s (s + q)
  have hD := Submission.Obl.k4_quadratic_atlas_normalization.format_derivativeFloorSet P hP floor i
  have h := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter
    (Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter (hE i)
      (Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter hAf hT)) hD
  change BF (H + HA + 4) (max D (max DA 2)) _
  convert h using 1
  · ring
  · omega
  · ext z
    simp only [selectedEvent, mem_inter_iff, mem_prod, mem_setOf_eq]

/-- The per-group physical sum and the normalized residual give the full
original derivative-cut block mass exactly. -/
theorem packet_physical_mass_identity (ν : Measure (ℕ × (Fin 6 → ℝ))) [SFinite ν]
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hE : MeasurableSet E)
    (P : MvPolynomial (Fin 4) ℝ) (floor s : ℝ) {q : ℝ} (hq : 0 < q)
    {U : Set (ℕ × (Fin 6 → ℝ))} (hU : MeasurableSet U)
    (b u : (ℕ × (Fin 6 → ℝ)) → Plane) (hb : Measurable b) (hu : Measurable u)
    {D m : ℕ} (p : Fin m → Submission.Lib.K4FinitePlankAtlases.PhysicalPlank D) :
    (∑ i, (ν.prod volume) (selectedEvent E (packetAssignment U b u p i) P floor s q)) +
      ENNReal.ofReal q * (ν.prod volume)
        (normalizedEvent (derivativeEvent E P floor) s q ∩ (packetResidual U b u p ×ˢ univ)) =
      (ν.prod volume) (selectedEvent E U P floor s q) := by
  have hE' : MeasurableSet (derivativeEvent E P floor) := hE.inter
    (Submission.Obl.k4_quadratic_atlas_normalization.measurableSet_derivativeFloorSet P floor)
  have h := congrArg (fun a : ENNReal => ENNReal.ofReal q * a)
    (packet_incidence_identity ν (normalizedEvent (derivativeEvent E P floor) s q) hU b u hb hu p)
  rw [mul_add, Finset.mul_sum] at h
  simp_rw [normalized_incidence_mass ν hE'
    (packetAssignment_measurable hU b u hb hu p _) s hq,
    normalized_incidence_mass ν hE' hU s hq, ← selectedEvent_eq] at h
  exact h

end
end Submission.Obl.k4_horizon_chart_assembly
