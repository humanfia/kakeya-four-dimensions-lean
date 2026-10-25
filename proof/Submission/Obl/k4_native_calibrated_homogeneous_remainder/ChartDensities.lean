import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ChartSampling
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ValidParts
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpTerminalLower

/-! Old fine terminal densities of the actual pulled-back selections. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable def RemainderGeometry.terminalDensity {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) : Observation → ENNReal :=
  ((a.pullbackLaw k b).map (obs (p.B (a.φ k) ((a.parent k).γ (a.worlds k b)))
    (δ (p.N (a.φ k)) p.L))).rnDeriv (volume.prod Measure.count)

theorem RemainderGeometry.terminalDensity_spec {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (k : ℕ) (b : Fin (q.W k)) :
    Measurable (a.terminalDensity k b) ∧
      (a.pullbackLaw k b).map (obs (p.B (a.φ k) ((a.parent k).γ (a.worlds k b)))
        (δ (p.N (a.φ k)) p.L)) =
          (volume.prod Measure.count).withDensity (a.terminalDensity k b) := by
  let γ := (a.parent k).γ (a.worlds k b)
  have hraw := raw_of_valid hp
  haveI : IsFiniteMeasure (selected p (a.φ k) γ) :=
    ⟨(hraw.selected_mass_le_one (a.φ k) γ).trans_lt (by simp)⟩
  haveI : IsFiniteMeasure (a.pullbackLaw k b) := by
    rw [a.pullbackLaw_eq hp k b]
    infer_instance
  have hmaple := Measure.map_mono
    (show a.pullbackLaw k b ≤ selected p (a.φ k) γ by
      rw [a.pullbackLaw_eq hp k b]; exact Measure.restrict_le_self)
    (measurable_nativeObs (p.B (a.φ k) γ) (δ (p.N (a.φ k)) p.L))
  have hfull : (selected p (a.φ k) γ).map
      (obs (p.B (a.φ k) γ) (δ (p.N (a.φ k)) p.L)) ≪ volume.prod Measure.count := by
    rw [((profile_of_valid hp).pure (a.φ k) γ p.L hp.length_pos.le le_rfl).2]
    exact withDensity_absolutelyContinuous _ _
  have hac := (Measure.absolutelyContinuous_of_le hmaple).trans hfull
  exact ⟨Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _ hac).symm⟩

noncomputable def RemainderGeometry.oldTerminalObservation {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) : Incidence → Observation :=
  fun z => obs (p.B (a.φ k) ((a.parent k).γ (a.worlds k b))) (δ (p.N (a.φ k)) p.L)
    ((a.incidenceEquiv k b).symm z)

noncomputable def RemainderGeometry.oldTerminalDensity {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) : Incidence → ENNReal :=
  fun z => p.g (a.φ k) ((a.parent k).γ (a.worlds k b)) p.L (a.oldTerminalObservation k b z)

noncomputable def RemainderGeometry.restrictedTerminalDensity {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) : Incidence → ENNReal :=
  fun z => a.terminalDensity k b (a.oldTerminalObservation k b z)

theorem RemainderGeometry.ofReal_densityRatio {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (k : ℕ) (b : Fin (q.W k)) :
    ENNReal.ofReal (a.densityRatio k b) =
      ENNReal.ofReal |Matrix.det ((a.parent k).Q (a.worlds k b))| / a.assignmentMass k b := by
  have hfin : a.assignmentMass k b ≠ ∞ := by
    haveI := (raw_of_valid hp).probability (a.φ k) ((a.parent k).γ (a.worlds k b))
    exact measure_ne_top _ _
  rw [densityRatio, ENNReal.ofReal_div_of_pos (a.assignmentMass_bounds hp k b).1,
    ENNReal.ofReal_toReal hfin]

theorem RemainderGeometry.terminal_density_lower {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (hq : RawValid q)
    (hg : ∀ k b, Measurable (q.g k b q.L) ∧
      (selected q k b).map (obs (q.B k b) (δ (q.N k) q.L)) =
        (volume.prod Measure.count).withDensity (q.g k b q.L))
    (k : ℕ) (b : Fin (q.W k)) : ∀ᵐ z ∂selected q k b,
      ENNReal.ofReal (a.densityRatio k b) * a.restrictedTerminalDensity k b z ≤
        q.g k b q.L (obs (q.B k b) (δ (q.N k) q.L) z) := by
  haveI := (raw_of_valid hp).probability (a.φ k) ((a.parent k).γ (a.worlds k b))
  have hEq : MeasurableSet (q.E k b) := by
    obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hq
    exact ((hfmt k).2.2.2.1 b).2.2.2.2.2.2.2.1
  have hsum : r + q.L = p.L := by rw [a.length]; ring
  obtain ⟨n, hwidth⟩ : ∃ n : ℕ, δ (p.N (a.φ k)) r * δ (p.N (a.φ k)) q.L =
      (n : ℝ) * δ (p.N (a.φ k)) p.L := by
    rcases Cmp.delta_mul_delta (p.N (a.φ k)) r q.L with hh | hh
    · exact ⟨1, by simpa only [hsum, Nat.cast_one, one_mul] using hh⟩
    · exact ⟨2, by simpa only [hsum, Nat.cast_ofNat] using hh⟩
  have hGlaw : Measure.map
      (obs (p.B (a.φ k) ((a.parent k).γ (a.worlds k b)) / δ (p.N (a.φ k)) r)
        (δ (p.N (a.φ k)) q.L))
      (((((p.ν (a.φ k) ((a.parent k).γ (a.worlds k b)))
        ((a.parent k).A (a.worlds k b)))⁻¹ •
        Measure.map (a.θ k b) ((p.ν (a.φ k) ((a.parent k).γ (a.worlds k b))).restrict
          ((a.parent k).A (a.worlds k b)))).prod volume).restrict (q.E k b)) =
        (volume.prod Measure.count).withDensity (q.g k b q.L) := by
    rw [← a.conditioned_prior k b, ← a.derivative_unit k b, ← a.same_base k]
    exact (hg k b).2
  have hh := Cmp.chart_fine_density_lower
    (p.ν (a.φ k) ((a.parent k).γ (a.worlds k b))) ((a.parent k).A (a.worlds k b))
    (a.θ k b) (by positivity : 0 < (2 : ℝ) ^ (a.parent k).T)
    ((a.parent_valid k).2.2 (a.worlds k b)).1 (a.prior_pos k b).ne'
    (a.planar_map k b) (a.hidden_map k b) hEq
    (p.B (a.φ k) ((a.parent k).γ (a.worlds k b)))
    (by unfold δ; positivity) (by unfold δ; positivity) n hwidth
    (a.terminalDensity_spec hp k b).1 (hg k b).1 (a.terminalDensity_spec hp k b).2 hGlaw
  rw [← a.conditioned_prior k b] at hh
  simpa only [a.ofReal_densityRatio hp k b, restrictedTerminalDensity, oldTerminalObservation,
    incidenceEquiv, a.derivative_unit k b, a.same_base k, assignmentMass, selected, priorMass] using hh

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
