import Mathlib

namespace Submission.Obl.k4_pair_bin_atlas_assembly

/-- Pick a source equation with the prescribed frame and bin and with a
non-small anchor discriminant. Empty bins are allowed. -/
noncomputable def chooseRepresentative {ι Φ B : Type*}
    (frame : ι → Φ) (bins : ι → Finset B) (good : ι → Prop) (b : Φ) (β : B) : Option ι := by
  classical
  exact if h : ∃ s, frame s = b ∧ β ∈ bins s ∧ good s then
    some (Classical.choose h) else none

theorem chooseRepresentative_spec {ι Φ B : Type*}
    (frame : ι → Φ) (bins : ι → Finset B) (good : ι → Prop)
    {b : Φ} {β : B} {s : ι}
    (hs : chooseRepresentative frame bins good b β = some s) :
    frame s = b ∧ β ∈ bins s ∧ good s := by
  classical
  unfold chooseRepresentative at hs
  split_ifs at hs with h
  · obtain rfl := Option.some.inj hs
    exact Classical.choose_spec h

theorem chooseRepresentative_exists {ι Φ B : Type*}
    (frame : ι → Φ) (bins : ι → Finset B) (good : ι → Prop)
    {b : Φ} {β : B} (h : ∃ s, frame s = b ∧ β ∈ bins s ∧ good s) :
    ∃ s, chooseRepresentative frame bins good b β = some s ∧
      frame s = b ∧ β ∈ bins s ∧ good s := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp only [chooseRepresentative, dite_eq_left h]

end Submission.Obl.k4_pair_bin_atlas_assembly
