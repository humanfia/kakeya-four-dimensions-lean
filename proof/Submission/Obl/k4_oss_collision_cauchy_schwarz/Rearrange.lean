import Mathlib

open MeasureTheory

namespace Submission.Obl.k4_oss_collision_cauchy_schwarz

/-- Transpose a two-by-two array of independent random variables. -/
theorem measurePreserving_pair_transpose {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun q : (A × B) × (C × D) => ((q.1.1, q.2.1), (q.1.2, q.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h₁ := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h₂ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μb μc μd)
  have h₃ := (Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod
    (MeasurePreserving.id μd)
  have h₄ := measurePreserving_prodAssoc μc μb μd
  have hmid := h₄.comp (h₃.comp h₂)
  have h₅ := (MeasurePreserving.id μa).prod hmid
  have h₆ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μa μc (μb.prod μd))
  exact h₆.comp (h₅.comp h₁)

end Submission.Obl.k4_oss_collision_cauchy_schwarz
