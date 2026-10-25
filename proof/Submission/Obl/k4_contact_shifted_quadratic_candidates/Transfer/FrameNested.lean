/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameNested.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameAtlas

/-!
# Nesting of the residual labels

The parent node of a retained node (its original ancestor with the history
truncated) contains its incidence, hence is retained, and its residual label
contains the child's assignment and residual block.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- The parent node of a node at level `h + 1`. -/
def Frame.parentNode (f : Frame D k s₀ U') (h : ℕ)
    (a : Fin (f.nl (h + 1)) × EntryHistory f.M (h + 1)) :
    Fin (f.nl h) × EntryHistory f.M h :=
  (f.anc h a.1, a.2.1)

theorem FrameGood.hist_subset_parentNode (hg : FrameGood f Rk θ K₂ e₀') (h : ℕ)
    (a : Fin (f.nl (h + 1)) × EntryHistory f.M (h + 1)) :
    f.hist (h + 1) a.1 a.2 ⊆ f.hist h (f.parentNode h a).1 (f.parentNode h a).2 :=
  historyAssignment_subset_parent _ _ _ _ h a.1 a.2.1 a.2.2

theorem FrameGood.event_subset_parentNode (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ}
    (hh : h < f.m) (a : Fin (f.nl (h + 1)) × EntryHistory f.M (h + 1)) :
    f.event (h + 1) a.1 a.2 ⊆ f.event h (f.parentNode h a).1 (f.parentNode h a).2 :=
  prod_mono (hg.hist_subset_parentNode h a) (hg.anc_sub h hh a.1).2

theorem FrameGood.parentNode_retained (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ}
    (hh : h < f.m) {a : Fin (f.nl (h + 1)) × EntryHistory f.M (h + 1)}
    (ha : a ∈ f.retained (h + 1)) : f.parentNode h a ∈ f.retained h := by
  classical
  have hne : (f.event (h + 1) a.1 a.2 ∩ f.core).Nonempty := by
    simpa [retained] using ha
  obtain ⟨p, hp1, hp2⟩ := hne
  exact f.mem_retained ⟨p, hg.event_subset_parentNode hh a hp1, hp2⟩

/-- The residual parent label of a residual label. -/
def Frame.upLabel (f : Frame D k s₀ U') (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ}
    (hh : h < f.m) (i : Fin (f.retained (h + 1)).card) : Fin (f.retained h).card :=
  f.labelOf h (f.parentNode h (f.node (h + 1) i))
    (hg.parentNode_retained hh ((f.retained (h + 1)).equivFin.symm i).2)

theorem FrameGood.node_upLabel (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h < f.m)
    (i : Fin (f.retained (h + 1)).card) :
    f.node h (f.upLabel hg hh i) = f.parentNode h (f.node (h + 1) i) :=
  f.node_labelOf _ _ _

/-- Nesting between consecutive residual levels. -/
theorem FrameGood.res_nested (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h < f.m)
    (i : Fin (f.level (h + 1)).n) :
    ∃ i' : Fin (f.level h).n, (f.level (h + 1)).A i ⊆ (f.level h).A i' ∧
      Data.I (f.level (h + 1)).T ((f.level (h + 1)).j i) ⊆
        Data.I (f.level h).T ((f.level h).j i') := by
  refine ⟨f.upLabel hg hh i, ?_, ?_⟩
  · change f.hist (h + 1) (f.node (h + 1) i).1 (f.node (h + 1) i).2 ⊆
      f.hist h (f.node h (f.upLabel hg hh i)).1 (f.node h (f.upLabel hg hh i)).2
    rw [hg.node_upLabel hh i]
    exact hg.hist_subset_parentNode h _
  · intro τ hτ
    have h1 := (hg.mem_resBlock (show h + 1 ≤ f.m from hh) i τ).mp hτ
    refine (hg.mem_resBlock hh.le (f.upLabel hg hh i) τ).mpr ?_
    rw [hg.node_upLabel hh i]
    exact (hg.anc_sub h hh _).2 h1

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
