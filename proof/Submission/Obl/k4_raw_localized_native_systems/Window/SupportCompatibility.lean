import Submission.Obl.k4_raw_localized_native_systems.Window.RawTags

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Only pairs met by the original current and earlier events can receive a tag. -/
def supportCompat {p : Data} {k C : ℕ} (W : Atlas p k)
    (H : Fin W.C → Set Point) (FC : Fin C → Set Point)
    (Compat : Fin C → Fin W.C → Prop) (a : Fin C) (e : Fin W.C) : Prop :=
  Compat a e ∧ ∃ q ∈ FC a, q ∈ H e

theorem rawSupportSet_supportCompat {p : Data} {k C : ℕ} (W : Atlas p k)
    (H : Fin W.C → Set Point) (FC : Fin C → Set Point)
    (Compat : Fin C → Fin W.C → Prop) (a : Fin C) :
    rawSupportSet W H (supportCompat W H FC Compat) FC a =
      rawSupportSet W H Compat FC a := by
  ext q
  simp only [rawSupportSet, certSupport, compatEvent, mem_inter_iff,
    mem_iUnion, mem_setOf_eq, rawAtlas]
  constructor
  · rintro ⟨hq, e, ⟨hc, _⟩, he⟩
    exact ⟨hq, e, hc, he⟩
  · rintro ⟨hq, e, hc, he⟩
    exact ⟨hq, e, ⟨hc, q, hq, he⟩, he⟩

/-- A positive covered current law provides a default earlier label. -/
theorem raw_witness_nonempty {p : Data} {k C : ℕ} (W : Atlas p k)
    (H : Fin W.C → Set Point) (FC : Fin C → Set Point)
    (Compat : Fin C → Fin W.C → Prop) (a : Fin C) (law : Measure Point)
    (hpos : 0 < law univ) (hcover : law (rawSupportSet W H Compat FC a)ᶜ = 0) :
    Nonempty (Fin W.C) := by
  classical
  by_contra h
  have hs : rawSupportSet W H Compat FC a = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨_, hq⟩
    obtain ⟨e, _⟩ := mem_iUnion.mp hq
    exact h ⟨e⟩
  rw [hs, compl_empty] at hcover
  exact hpos.ne' hcover

end
end Submission.Obl.k4_raw_localized_native_systems.Window
