/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/IncidenceNesting.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/IncidenceNesting.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.OriginalMass
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic

namespace Submission.Obl.k4_critical_switching_state_preparation

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

def labelIncidence (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Set (α × ℝ) :=
  cfg.A k s i ×ˢ I (cfg.T k s) (cfg.j k s i)

/-- Distinct true labels overlap only on a null set of original incidences.
Labels in the same time block have disjoint assignments; distinct closed
time blocks meet in a Lebesgue-null endpoint. -/
theorem AssignmentLevel.incidence_inter_null (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i i' : Fin (cfg.n k s)) (hne : i ≠ i') :
    cfg.μ k (cfg.labelIncidence k s i ∩ cfg.labelIncidence k s i') = 0 := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  by_cases hj : cfg.j k s i = cfg.j k s i'
  · have hd := a.disjoint i i' hne hj
    have hempty : cfg.labelIncidence k s i ∩ cfg.labelIncidence k s i' = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact Set.disjoint_left.mp hd hp.1.1 hp.2.1
    rw [hempty, measure_empty]
  · have hvol : volume (I (cfg.T k s) (cfg.j k s i) ∩
        I (cfg.T k s) (cfg.j k s i')) = 0 :=
      Submission.Obl.k4_scalar_angular_pair_agreement.volume_I_inter (cfg.T k s) hj
    apply le_antisymm _ zero_le
    calc
      _ ≤ (ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod volume))
          (univ ×ˢ (I (cfg.T k s) (cfg.j k s i) ∩ I (cfg.T k s) (cfg.j k s i'))) := by
        refine ((h.basic k).2.2.2.1 _).trans (measure_mono ?_)
        intro p hp
        exact ⟨Set.mem_univ _, hp.1.2, hp.2.2⟩
      _ = 0 := by simp [Measure.smul_apply, Measure.prod_prod, hvol]

/-- The original incidence law almost surely has a unique true label at a
fixed level, even though the dyadic time blocks are closed. -/
theorem AssignmentLevel.ae_unique_label (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) :
    ∀ᵐ p ∂cfg.μ k, ∀ i i', p ∈ cfg.labelIncidence k s i →
      p ∈ cfg.labelIncidence k s i' → i = i' := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro i'
  by_cases hi : i = i'
  · subst i'
    exact Eventually.of_forall (fun _ _ _ => rfl)
  · have hz := a.incidence_inter_null h i i' hi
    have hae : ∀ᵐ p ∂cfg.μ k,
        p ∉ cfg.labelIncidence k s i ∩ cfg.labelIncidence k s i' := by
      simpa [ae_iff] using hz
    filter_upwards [hae] with p hp hpi hpi'
    exact False.elim (hp ⟨hpi, hpi'⟩)

/-- A fine label meeting the current parent in a genuine original incidence
is a descendant of that same full parent, almost everywhere. -/
theorem AssignmentLevel.ae_matching_ancestor (h : cfg.Valid) {k : ℕ} {s t : ℝ}
    (parent : cfg.AssignmentLevel k s)
    (hnest : ∀ i : Fin (cfg.n k t), ∃ ip : Fin (cfg.n k s),
      cfg.A k t i ⊆ cfg.A k s ip ∧
      I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip)) :
    ∀ᵐ p ∂cfg.μ k, ∀ (ip : Fin (cfg.n k s)) (i : Fin (cfg.n k t)),
      p ∈ cfg.labelIncidence k s ip → p ∈ cfg.labelIncidence k t i →
      cfg.A k t i ⊆ cfg.A k s ip ∧
        I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) := by
  filter_upwards [parent.ae_unique_label h] with p hp ip i hparent hchild
  obtain ⟨ip', hA, hI⟩ := hnest i
  have hip : ip = ip' := hp ip ip' hparent ⟨hA hchild.1, hI hchild.2⟩
  simpa only [hip] using And.intro hA hI

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
