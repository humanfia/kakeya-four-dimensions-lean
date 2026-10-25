import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonContext

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- Actual selected original incidences in one old label, with all finite
child-level preparations imposed only on the labeled event. -/
def selectedEvent
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (G : Set (α × ℝ)) (h : Fin c.m) : Set (α × ℝ) :=
  {p | p ∈ G ∧ p ∈ c.support.event ∧ p.1 ∈ c.AH h ∧
    ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
      choice h (cfg.j k s i) = some i}

theorem measurable_selectedEvent (lev : cfg.AssignmentLevel k s)
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (G : Set (α × ℝ)) (hG : MeasurableSet G) (h : Fin c.m) :
    MeasurableSet (c.selectedEvent choice G h) := by
  classical
  have hQ : MeasurableSet {p : α × ℝ | ∃ i, p.1 ∈ cfg.B k s i ∧
      p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧ choice h (cfg.j k s i) = some i} := by
    have hi (i : Fin (cfg.n k s)) : MeasurableSet {p : α × ℝ |
        p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
          choice h (cfg.j k s i) = some i} := by
      by_cases hh : choice h (cfg.j k s i) = some i
      · convert (lev.fitted_measurable i).prod
          (show MeasurableSet (Data.I (cfg.T k s) (cfg.j k s i)) from measurableSet_Icc) using 1
        ext p
        simp only [mem_prod, mem_setOf_eq, hh, and_true]
      · simp only [hh, and_false, Set.ofPred_false, MeasurableSet.empty]
    convert MeasurableSet.iUnion hi using 1
    ext p
    simp only [mem_iUnion, mem_setOf_eq]
  exact hG.inter (c.support.measurable.inter
    (((c.layer.1 h).preimage measurable_fst).inter hQ))

theorem selectedEvent_subset
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (G : Set (α × ℝ)) (h : Fin c.m) :
    c.selectedEvent choice G h ⊆ c.AH h ×ˢ Icc (0 : ℝ) 1 := by
  intro p hp
  exact ⟨hp.2.2.1, c.support.unit p hp.2.1⟩

/-- The selected law loses no further mass when pointwise finite-grid
certificates are placed in the labeled events. Old assignments stay whole. -/
theorem selectedEvent_conull
    (choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)))
    (G : Set (α × ℝ)) (τ : Measure (α × ℝ)) (hτ : τ ≤ σ)
    (hG : ∀ᵐ p ∂τ, p ∈ G)
    (hcover : ∀ᵐ p ∂τ, ∃ h i, p.1 ∈ c.AH h ∧ p.1 ∈ cfg.B k s i ∧
      p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧ choice h (cfg.j k s i) = some i)
    (h : Fin c.m) :
    τ ((c.AH h ×ˢ Icc (0 : ℝ) 1) \ c.selectedEvent choice G h) = 0 := by
  have hAE : ∀ᵐ p ∂τ, p ∈ c.AH h ×ˢ Icc (0 : ℝ) 1 →
      p ∈ c.selectedEvent choice G h := by
    filter_upwards [hG, ae_mono hτ c.support.conull, hcover] with p hpG hpS hp hpA
    obtain ⟨h', i, hpA', hpB, hpI, hchoice⟩ := hp
    have hh : h' = h := by
      by_contra hne
      exact Set.disjoint_left.mp (c.layer.2.1 h' h hne) hpA' hpA.1
    subst h'
    exact ⟨hpG, hpS, hpA.1, i, hpB, hpI, hchoice⟩
  have heq : {p | ¬ (p ∈ c.AH h ×ˢ Icc (0 : ℝ) 1 →
      p ∈ c.selectedEvent choice G h)} =
      (c.AH h ×ˢ Icc (0 : ℝ) 1) \ c.selectedEvent choice G h := by
    ext p
    simp only [mem_setOf_eq, not_imp, mem_diff]
  exact heq ▸ ae_iff.mp hAE

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
