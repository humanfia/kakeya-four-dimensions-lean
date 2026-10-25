/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeData.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.Model
import Submission.Obl.k4_critical_intercept_concentration.OriginalMass

/-! Extract original native data without assuming the critical rate.
The assignment-level extraction generalizes the accepted o212 OriginalMass
lemma to the subcritical Prepared predicate; it uses only the atlas field. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Data

open Submission.Obl.k4_critical_intercept_concentration.Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem Prepared.eventually_assignment_level (h : cfg.Prepared) {s : ℝ}
    (hs : 0 < s) (hsU : s ≤ cfg.U) : ∀ᶠ k in atTop, cfg.AssignmentLevel k s := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by
    have hh : 0 < s⁻¹ := inv_pos.mpr hs
    dsimp [R]
    linarith
  have hRs : R⁻¹ ≤ s := by
    have hRpos : 0 < R := by linarith
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    exact (inv_le_comm₀ hRpos hs).mpr hle
  filter_upwards [h.atlas R hR] with k hk
  have hk := hk s hRs hsU
  refine ⟨hk.1, hk.2.1, (fun i => (hk.2.2.1 i).1), hk.2.2.2.1,
    ?_, ?_, hk.2.2.2.2.2.1, (fun i => (hk.2.2.1 i).2.2),
    (fun i => (hk.2.2.2.2.1 i).2.2.2.1), ?_,
    (fun i => (hk.2.2.2.2.1 i).2.2.2.2.2.2.1), ?_, ?_,
    (fun i => ((hk.2.2.2.2.1 i).2.2.2.2.2.2.2.2 rfl).1),
    (fun i => ((hk.2.2.2.2.1 i).2.2.2.2.2.2.2.2 rfl).2.1)⟩
  · intro i
    simpa only [timeLength, zpow_neg, zpow_natCast] using (hk.2.2.2.2.1 i).1
  · intro i
    simpa only [timeLength, zpow_neg, zpow_natCast] using (hk.2.2.2.2.1 i).2.1
  · intro i l hl t ht
    simpa only [timeLength, zpow_neg, zpow_natCast] using
      (hk.2.2.2.2.1 i).2.2.2.2.2.1 l hl t ht
  · intro i
    simpa only [timeLength, zpow_neg, zpow_natCast] using
      ((hk.2.2.2.2.1 i).2.2.2.2.2.2.2.2 rfl).2.2.1
  · intro i
    simpa only [timeLength, zpow_neg, zpow_natCast] using
      ((hk.2.2.2.2.1 i).2.2.2.2.2.2.2.2 rfl).2.2.2

/-- The lower mass is in the full original witness, prior to every
subsequent endpoint or scalar restriction. -/
theorem Prepared.eventually_native_mass (h : cfg.Prepared) {s : ℝ}
    (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ i : Fin (cfg.n k s),
      ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
        cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by
    have hh : 0 < s⁻¹ := inv_pos.mpr hs
    dsimp [R]
    linarith
  have hRs : R⁻¹ ≤ s := by
    have hRpos : 0 < R := by linarith
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    exact (inv_le_comm₀ hRpos hs).mpr hle
  filter_upwards [h.atlas R hR] with k hk
  intro i
  simpa only [timeLength, zpow_neg, zpow_natCast] using
    ((hk s hRs hsU).2.2.2.2.1 i).2.2.1

/-- The frozen nesting concerns whole trajectory assignments and time blocks. -/
theorem Prepared.eventually_nested (h : cfg.Prepared) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (htU : t ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ i : Fin (cfg.n k t), ∃ ip : Fin (cfg.n k s),
      cfg.A k t i ⊆ cfg.A k s ip ∧
        I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by
    have hh : 0 < s⁻¹ := inv_pos.mpr hs
    dsimp [R]
    linarith
  have hRs : R⁻¹ ≤ s := by
    have hRpos : 0 < R := by linarith
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    exact (inv_le_comm₀ hRpos hs).mpr hle
  filter_upwards [h.nested R hR] with k hk
  exact hk s t hRs hst htU

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
