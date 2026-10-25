-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extreme_offset_fibre_estimate.Coordinates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_extreme_offset_fibre_estimate

open MeasureTheory Set

noncomputable section

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space

/-- The twisted projection, with its unused coordinate retained. -/
def chart (f : ℝ → ℝ) (p : Space) : (ℝ × ℝ) × ℝ :=
  ((p 0 + f (p 2) * p 1, p 2), p 1)

lemma measurePreserving_translation (k : ℝ × ℝ → ℝ) (hk : Measurable k) :
    MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => (q.1, q.2 + k q.1)) := by
  exact (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).skew_product
    (measurable_snd.add (hk.comp measurable_fst))
    (ae_of_all _ fun q => (measurePreserving_add_right volume (k q)).map_eq)

lemma measurePreserving_coordinates :
    MeasurePreserving (fun p : Space => (p 0, (p 1, p 2))) := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_piFinTwo (fun _ => ℝ))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin 3)))
  convert h using 1
  funext p
  rfl

lemma measurePreserving_chart (f : ℝ → ℝ) (hf : Measurable f) :
    MeasurePreserving (chart f) := by
  have h₁ : MeasurePreserving (fun p : Space => ((p 1, p 2), p 0)) :=
    Measure.measurePreserving_swap.comp measurePreserving_coordinates
  have h₂ : MeasurePreserving (fun p : Space => ((p 1, p 2), p 0 + f (p 2) * p 1)) :=
    (measurePreserving_translation (fun q => f q.2 * q.1)
      ((hf.comp measurable_snd).mul measurable_fst)).comp h₁
  have h₃ := Measure.measurePreserving_swap.comp h₂
  have h₄ := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_swap (μ := volume) (ν := volume))).comp h₃
  have h₅ := (measurePreserving_prodAssoc volume volume volume).symm
    (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ))
  exact h₅.comp h₄

/-- A second shear centers the fibre over each projected point. -/
def centeredChart (f a : ℝ → ℝ) (p : Space) : (ℝ × ℝ) × ℝ :=
  ((chart f p).1, (chart f p).2 - ((chart f p).1.1 - a (chart f p).1.2) / f (chart f p).1.2)

lemma measurePreserving_centeredChart (f a : ℝ → ℝ)
    (hf : Measurable f) (ha : Measurable a) :
    MeasurePreserving (centeredChart f a) := by
  have hm : Measurable (fun q : ℝ × ℝ => - ((q.1 - a q.2) / f q.2)) :=
    ((measurable_fst.sub (ha.comp measurable_snd)).div (hf.comp measurable_snd)).neg
  unfold centeredChart
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_translation _ hm).comp (measurePreserving_chart f hf)

end

end WangZahlLot.Obl.wz_extreme_offset_fibre_estimate
