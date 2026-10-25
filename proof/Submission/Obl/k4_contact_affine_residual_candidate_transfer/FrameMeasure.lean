import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameBlocks

/-!
# Measurability and masses on the frame

Histories are measurable up to the last grid level. A retained label lies in
the parent block and history, and its history keeps the prior floor
`θ * ν(A) / K`. The residual incidence law of a measurable set is the core
mass of its parent-time preimage divided by the parent reference.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (f : Frame D k s₀ U')

theorem left_le_right (h : ℕ) (i : Fin (f.nl h)) : f.left h i ≤ f.right h i := by
  unfold left right
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem right_eq (h : ℕ) (i : Fin (f.nl h)) : f.right h i = f.left h i + f.ql h := by
  simp only [right, left, ql, zpow_neg, zpow_natCast]
  field_simp

theorem block_eq_Icc (h : ℕ) (i : Fin (f.nl h)) :
    f.block h i = Icc (f.left h i) (f.left h i + f.ql h) := by
  rw [← right_eq]
  rfl

theorem measurableSet_entry (hb : Measurable (D.b k)) {h : ℕ} {i : Fin (f.nl h)}
    (hB : MeasurableSet (D.B k (f.depth h) i)) (u : Fin f.M) :
    MeasurableSet (f.entry h i u) :=
  measurableSet_assignedAffineEntry (D.b k) hb _ hB _ (f.left_le_right h i) u

theorem measurableSet_hist (hb : Measurable (D.b k)) :
    ∀ h, (∀ h' ≤ h, ∀ i : Fin (f.nl h'), MeasurableSet (D.A k (f.depth h') i) ∧
        MeasurableSet (D.B k (f.depth h') i)) →
      ∀ i u, MeasurableSet (f.hist h i u)
  | 0, hA, i, u => (hA 0 le_rfl i).1.inter (f.measurableSet_entry hb (hA 0 le_rfl i).2 u)
  | h + 1, hA, i, u => by
    have ih := measurableSet_hist hb h (fun h' hh' => hA h' (by omega)) (f.anc h i) u.1
    exact ((hA (h + 1) le_rfl i).1.inter ih).inter
      (f.measurableSet_entry hb (hA (h + 1) le_rfl i).2 u.2)

theorem hist_subset_A (h : ℕ) (i : Fin (f.nl h)) (u : EntryHistory f.M h) :
    f.hist h i u ⊆ D.A k (f.depth h) i :=
  historyAssignment_subset _ _ _ _ h i u

theorem hist_subset_entry : ∀ (h : ℕ) (i : Fin (f.nl h)) (u : EntryHistory f.M h),
    f.hist h i u ⊆ f.entry h i (lastEntry h u)
  | 0, _, _ => inter_subset_right
  | _ + 1, _, _ => inter_subset_right

theorem entry_subset_B (h : ℕ) (i : Fin (f.nl h)) (u : Fin f.M) :
    f.entry h i u ⊆ D.B k (f.depth h) i :=
  fun _ hl => ((assignedAffineEntry_subset _ _ _ _ _ _ u) hl).1

theorem toChart_measurable : Measurable f.toChart :=
  measurable_fst.prodMk ((measurable_snd.sub_const _).div_const _)

/-- The residual incidence law of a measurable set. -/
theorem resμ_apply {E : Set (α × ℝ)} (hE : MeasurableSet E) (hcore : MeasurableSet f.core) :
    f.resμ E = f.scale⁻¹ * D.μ k (f.toChart ⁻¹' E ∩ f.core) := by
  rw [resμ, Measure.smul_apply, Measure.map_apply f.toChart_measurable hE,
    Measure.restrict_apply (f.toChart_measurable hE), smul_eq_mul]

theorem resρ_apply {E : Set (α × ℝ)} (hE : MeasurableSet E) (hcore : MeasurableSet f.core) :
    f.resρ E = f.scale⁻¹ * D.ρ k (f.toChart ⁻¹' E ∩ f.core) := by
  rw [resρ, Measure.smul_apply, Measure.map_apply f.toChart_measurable hE,
    Measure.restrict_apply (f.toChart_measurable hE), smul_eq_mul]

/-- The node of a residual label is retained. -/
theorem node_retained (h : ℕ) (i : Fin (f.retained h).card) :
    (f.event h (f.node h i).1 (f.node h i).2 ∩ f.core).Nonempty := by
  classical
  have hmem := ((f.retained h).equivFin.symm i).2
  simp only [retained, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem

/-- The residual label of a retained node. -/
def labelOf (h : ℕ) (a : Fin (f.nl h) × EntryHistory f.M h) (ha : a ∈ f.retained h) :
    Fin (f.retained h).card :=
  (f.retained h).equivFin ⟨a, ha⟩

theorem node_labelOf (h : ℕ) (a : Fin (f.nl h) × EntryHistory f.M h)
    (ha : a ∈ f.retained h) : f.node h (f.labelOf h a ha) = a := by
  simp [node, labelOf]

theorem mem_retained {h : ℕ} {a : Fin (f.nl h) × EntryHistory f.M h}
    (ha : (f.event h a.1 a.2 ∩ f.core).Nonempty) : a ∈ f.retained h := by
  classical
  simp only [retained, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ha

end Frame

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
