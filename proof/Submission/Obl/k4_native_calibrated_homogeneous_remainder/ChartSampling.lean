import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpTransport
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.RawDensities
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.GeometryParameters

/-! The exact weighted sampling identity of a normalized chart family. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable def RemainderGeometry.incidenceEquiv {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) :
    Incidence ≃ᵐ Incidence :=
  Cmp.incEquiv (a.θ k b) ((2 : ℝ) ^ (a.parent k).T)
    (((a.parent k).j (a.worlds k b) : ℝ) / (2 : ℝ) ^ (a.parent k).T) (by positivity)

noncomputable def RemainderGeometry.pullbackSelection {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) : Set Incidence :=
  a.incidenceEquiv k b ⁻¹' q.E k b

noncomputable def RemainderGeometry.pullbackLaw {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) : Measure Incidence :=
  (((p.ν (a.φ k) ((a.parent k).γ (a.worlds k b))).restrict
    ((a.parent k).A (a.worlds k b))).prod volume).restrict (a.pullbackSelection k b)

theorem RemainderGeometry.pullbackSelection_subset {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) :
    a.pullbackSelection k b ⊆ (a.parent k).F (a.worlds k b) := by
  intro z hz
  have hh := a.selected_pullback k b (a.incidenceEquiv k b z) hz
  have htime : ((a.parent k).j (a.worlds k b) : ℝ) / (2 : ℝ) ^ (a.parent k).T +
      (z.2 - ((a.parent k).j (a.worlds k b) : ℝ) / (2 : ℝ) ^ (a.parent k).T) *
        (2 : ℝ) ^ (a.parent k).T / (2 : ℝ) ^ (a.parent k).T = z.2 := by
    field_simp
    ring
  simpa only [incidenceEquiv, Cmp.incEquiv_apply, (a.θ k b).symm_apply_apply, htime] using hh

theorem RemainderGeometry.selected_law {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (hq : RawValid q)
    (k : ℕ) (b : Fin (q.W k)) :
    selected q k b =
      (ENNReal.ofReal ((2 : ℝ) ^ (a.parent k).T) / a.assignmentMass k b) •
        (a.pullbackLaw k b).map (a.incidenceEquiv k b) := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  haveI := ((hfmt (a.φ k)).2.2.2.1 ((a.parent k).γ (a.worlds k b))).1
  have hEq : MeasurableSet (q.E k b) := by
    obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hq
    exact ((hfmt k).2.2.2.1 b).2.2.2.2.2.2.2.1
  change (((q.ν k b).prod volume).restrict (q.E k b)) = _
  rw [a.conditioned_prior k b]
  exact Cmp.selected_law_transport _ _ _ (by positivity) hEq

theorem RemainderGeometry.pullbackLaw_eq {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (k : ℕ) (b : Fin (q.W k)) :
    a.pullbackLaw k b =
      (selected p (a.φ k) ((a.parent k).γ (a.worlds k b))).restrict
        (a.pullbackSelection k b) := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  haveI := ((hfmt (a.φ k)).2.2.2.1 ((a.parent k).γ (a.worlds k b))).1
  have hc := (a.parent_valid k).2.2 (a.worlds k b)
  have hsub := a.pullbackSelection_subset k b
  have hsubA : a.pullbackSelection k b ⊆ (a.parent k).A (a.worlds k b) ×ˢ univ := by
    intro z hz
    exact ⟨(hc.2.2.2.2.2.2.2.2.2.2.1 z (hsub hz)).2.1, mem_univ _⟩
  have hsubE : a.pullbackSelection k b ⊆ p.E (a.φ k) ((a.parent k).γ (a.worlds k b)) :=
    fun z hz => (hc.2.2.2.2.2.2.2.2.2.2.1 z (hsub hz)).1
  unfold pullbackLaw selected priorMass
  rw [show ((p.ν (a.φ k) ((a.parent k).γ (a.worlds k b))).restrict
      ((a.parent k).A (a.worlds k b))).prod volume =
      ((p.ν (a.φ k) ((a.parent k).γ (a.worlds k b))).prod volume).restrict
        ((a.parent k).A (a.worlds k b) ×ˢ univ) by
    rw [← Measure.prod_restrict, Measure.restrict_univ]]
  rw [Measure.restrict_restrict_of_subset hsubA, Measure.restrict_restrict_of_subset hsubE]

theorem RemainderGeometry.weighted_selected_law {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (hq : RawValid q)
    (k : ℕ) (b : Fin (q.W k)) :
    ENNReal.ofReal (q.ω k b) • selected q k b =
      (ENNReal.ofReal ((a.Z k)⁻¹) * ENNReal.ofReal
        (p.ω (a.φ k) ((a.parent k).γ (a.worlds k b)))) •
          (a.pullbackLaw k b).map (a.incidenceEquiv k b) := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  haveI := ((hfmt (a.φ k)).2.2.2.1 ((a.parent k).γ (a.worlds k b))).1
  have hmassfin : a.assignmentMass k b ≠ ∞ := measure_ne_top _ _
  have hmasspos := (a.assignmentMass_bounds hp k b).1
  have hω : 0 ≤ q.ω k b := by
    obtain ⟨-, -, -, -, -, -, -, -, M', D', hf⟩ := hq
    exact (hf k).2.1 b
  have hreal : q.ω k b * ((2 : ℝ) ^ (a.parent k).T / (a.assignmentMass k b).toReal) =
      (a.Z k)⁻¹ * p.ω (a.φ k) ((a.parent k).γ (a.worlds k b)) := by
    rw [a.world_weights k b]
    change (p.ω (a.φ k) ((a.parent k).γ (a.worlds k b)) /
      (2 : ℝ) ^ (a.parent k).T * (a.assignmentMass k b).toReal / a.Z k) *
      ((2 : ℝ) ^ (a.parent k).T / (a.assignmentMass k b).toReal) = _
    field_simp [hmasspos.ne', (a.normalizer_pos k).ne']
    <;> ring
  rw [a.selected_law hp hq k b, smul_smul]
  congr 1
  conv_lhs => arg 2; arg 2; rw [← ENNReal.ofReal_toReal hmassfin]
  rw [← ENNReal.ofReal_div_of_pos hmasspos, ← ENNReal.ofReal_mul hω, hreal,
    ENNReal.ofReal_mul (inv_nonneg.mpr (a.normalizer_pos k).le)]

theorem RemainderGeometry.weighted_selected_apply {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (hq : RawValid q)
    (k : ℕ) (b : Fin (q.W k)) (S : Set Incidence) :
    ENNReal.ofReal (q.ω k b) * selected q k b S =
      ENNReal.ofReal ((a.Z k)⁻¹) *
        ENNReal.ofReal (p.ω (a.φ k) ((a.parent k).γ (a.worlds k b))) *
          a.pullbackLaw k b (a.incidenceEquiv k b ⁻¹' S) := by
  have heq := congrArg (fun μ : Measure Incidence => μ S) (a.weighted_selected_law hp hq k b)
  simpa only [Measure.smul_apply, smul_eq_mul,
    (a.incidenceEquiv k b).measurableEmbedding.map_apply] using heq

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
