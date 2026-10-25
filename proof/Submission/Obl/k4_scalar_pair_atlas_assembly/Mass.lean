import Submission.Obl.k4_scalar_pair_atlas_assembly.Dyadic
set_option autoImplicit false
namespace Submission.Obl.k4_scalar_pair_atlas_assembly
open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
noncomputable section

/-- A later event in every coarse block contributes its full original mass. Endpoint trimming
makes those contributions disjoint and costs zero product measure. -/
theorem sum_coarse_mass_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (E : Set (α × ℝ)) {T : ℕ}
    (V : Fin (2 ^ T) → Set (α × ℝ)) (hV : ∀ b, MeasurableSet (V b))
    (hsub : ∀ b, V b ⊆ E ∩ {q | q.2 ∈ I T b})
    (D : Set (α × ℝ))
    (hD : ∀ b, V b ∩ {q | q.2 ∈ halfI T b} ⊆ D) :
    (∑ b : Fin (2 ^ T), ((ν.prod volume).restrict E) (V b)) ≤
      ((ν.prod volume).restrict E) D := by
  let V' := fun b => V b ∩ {q | q.2 ∈ halfI T b}
  have hm (b) : MeasurableSet (V' b) :=
    (hV b).inter ((measurable_halfI T b).preimage measurable_snd)
  have hs (b) : V' b ⊆ E := fun q hq => (hsub b hq.1).1
  have hd : Pairwise (fun b b' => Disjoint (V' b) (V' b')) := by
    intro b b' hbb
    apply disjoint_left.mpr
    rintro q hq hq'
    exact disjoint_left.mp (halfI_disjoint T hbb) hq.2 hq'.2
  have htrim (b) : ((ν.prod volume).restrict E) (V b) =
      ((ν.prod volume).restrict E) (V' b) := by
    rw [Measure.restrict_apply (hV b), Measure.restrict_apply (hm b),
      inter_eq_left.mpr (fun q hq => (hsub b hq).1), inter_eq_left.mpr (hs b)]
    exact (trim_halfI_measure ν (fun q hq => (hsub b hq).2)).symm
  calc
    (∑ b : Fin (2 ^ T), ((ν.prod volume).restrict E) (V b)) =
        ∑ b : Fin (2 ^ T), ((ν.prod volume).restrict E) (V' b) :=
      Finset.sum_congr rfl (fun b _ => htrim b)
    _ = ((ν.prod volume).restrict E) (⋃ b, V' b) := by
      rw [measure_iUnion hd hm, tsum_fintype]
    _ ≤ ((ν.prod volume).restrict E) D := by
      apply measure_mono
      exact iUnion_subset hD

end
end Submission.Obl.k4_scalar_pair_atlas_assembly
