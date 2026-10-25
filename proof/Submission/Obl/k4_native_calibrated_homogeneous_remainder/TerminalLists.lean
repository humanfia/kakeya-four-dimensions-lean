import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ChartDensities
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WeightedLists

/-! Original terminal observation lists control normalized chart tails without
a loss proportional to the total number of charts. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable def RawRemainder.worldList {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (k : ℕ) (γ : Fin (p.W (a.φ k))) (o : Observation) :
    Finset (Fin (q.W k)) :=
  ((a.parent k).lst γ o).map (a.worlds k).symm.toEmbedding

theorem RawRemainder.worldList_card {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (k : ℕ) (γ : Fin (p.W (a.φ k))) (o : Observation) :
    ((a.worldList k γ o).card : ENNReal) ≤ ENNReal.ofReal (a.κ k) := by
  rw [worldList, Finset.card_map]
  exact_mod_cast ENNReal.ofReal_le_ofReal (a.list_bound k γ o)

theorem RawRemainder.pullback_listed {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (k : ℕ) (b : Fin (q.W k)) (z : Incidence)
    (hz : z ∈ a.toRemainderGeometry.pullbackSelection k b) :
    b ∈ a.worldList k ((a.parent k).γ (a.worlds k b))
      (obs (p.B (a.φ k) ((a.parent k).γ (a.worlds k b))) (δ (p.N (a.φ k)) p.L) z) := by
  apply Finset.mem_map.mpr
  exact ⟨a.worlds k b,
    a.listed k _ z (a.toRemainderGeometry.pullbackSelection_subset k b hz),
    (a.worlds k).symm_apply_apply b⟩

theorem RawRemainder.terminal_refinement_bound {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (hp : Valid p) (k : ℕ) (ε : ENNReal) :
    (∑ b, ENNReal.ofReal (q.ω k b) * selected q k b
      {z | a.toRemainderGeometry.restrictedTerminalDensity k b z <
        ε * a.toRemainderGeometry.oldTerminalDensity k b z}) ≤
      ε * ENNReal.ofReal (a.κ k / a.Z k) := by
  let geom := a.toRemainderGeometry
  let μ := selected p (a.φ k)
  let O : Fin (p.W (a.φ k)) → Incidence → Observation := fun γ =>
    obs (p.B (a.φ k) γ) (δ (p.N (a.φ k)) p.L)
  let γ : Fin (q.W k) → Fin (p.W (a.φ k)) := fun b => (a.parent k).γ (a.worlds k b)
  have hraw := raw_of_valid hp
  letI : ∀ γ, IsFiniteMeasure (μ γ) := fun γ =>
    ⟨(hraw.selected_mass_le_one (a.φ k) γ).trans_lt (by simp)⟩
  have hE : ∀ b, MeasurableSet (geom.pullbackSelection k b) := by
    intro b
    apply (geom.incidenceEquiv k b).measurable
    obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := a.raw_valid
    exact ((hfmt k).2.2.2.1 b).2.2.2.2.2.2.2.1
  have hres : ∀ b, ((μ (γ b)).restrict (geom.pullbackSelection k b)).map (O (γ b)) =
      (volume.prod Measure.count).withDensity (geom.terminalDensity k b) := by
    intro b
    rw [← geom.pullbackLaw_eq hp k b]
    exact (geom.terminalDensity_spec hp k b).2
  have hbound := weighted_observation_list_lowDensity_mass μ O (fun _ => measurable_nativeObs _ _)
    (volume.prod Measure.count) (fun γ => p.g (a.φ k) γ p.L)
    (fun γ => ((profile_of_valid hp).pure (a.φ k) γ p.L hp.length_pos.le le_rfl).1)
    (fun γ => ((profile_of_valid hp).pure (a.φ k) γ p.L hp.length_pos.le le_rfl).2)
    γ (geom.pullbackSelection k) hE (geom.terminalDensity k)
    (fun b => (geom.terminalDensity_spec hp k b).1) hres (a.worldList k)
    (a.pullback_listed k) (fun γ => ENNReal.ofReal (p.ω (a.φ k) γ)) ε
    (ENNReal.ofReal (a.κ k)) (a.worldList_card k)
  have hmass : (∑ γ, ENNReal.ofReal (p.ω (a.φ k) γ) * μ γ univ) ≤ 1 := by
    simpa only [familyLaw, worldLaw_univ] using hraw.family_mass_le_one (a.φ k)
  calc
    _ = ENNReal.ofReal ((a.Z k)⁻¹) * ∑ b,
        ENNReal.ofReal (p.ω (a.φ k) (γ b)) * (μ (γ b)).restrict (geom.pullbackSelection k b)
          {z | geom.terminalDensity k b (O (γ b) z) <
            ε * p.g (a.φ k) (γ b) p.L (O (γ b) z)} := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [geom.weighted_selected_apply hp a.raw_valid k b, ← geom.pullbackLaw_eq hp k b]
      rw [mul_assoc]
      congr 3
      ext z
      simp only [geom, O, γ, RemainderGeometry.restrictedTerminalDensity, RemainderGeometry.oldTerminalDensity,
        RemainderGeometry.oldTerminalObservation, mem_preimage, mem_ofPred_eq,
        MeasurableEquiv.symm_apply_apply]
    _ ≤ ENNReal.ofReal ((a.Z k)⁻¹) *
        (ε * ENNReal.ofReal (a.κ k) * 1) := mul_le_mul' le_rfl
      (hbound.trans (mul_le_mul' le_rfl hmass))
    _ = _ := by
      rw [mul_one, div_eq_mul_inv, ENNReal.ofReal_mul (by linarith [a.slack_one k])]
      ring

theorem RawRemainder.source_event_bound {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (hp : Valid p) (k : ℕ)
    (B : Fin (p.W (a.φ k)) → Set Incidence) (hB : ∀ γ, MeasurableSet (B γ)) :
    (∑ b, ENNReal.ofReal (q.ω k b) * selected q k b
      {z | (a.toRemainderGeometry.incidenceEquiv k b).symm z ∈
        B ((a.parent k).γ (a.worlds k b))}) ≤
      ENNReal.ofReal (a.κ k / a.Z k) *
        ∑ γ, ENNReal.ofReal (p.ω (a.φ k) γ) * selected p (a.φ k) γ (B γ) := by
  let geom := a.toRemainderGeometry
  let γ : Fin (q.W k) → Fin (p.W (a.φ k)) := fun b => (a.parent k).γ (a.worlds k b)
  have hE : ∀ b, MeasurableSet (geom.pullbackSelection k b) := by
    intro b
    apply (geom.incidenceEquiv k b).measurable
    obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := a.raw_valid
    exact ((hfmt k).2.2.2.1 b).2.2.2.2.2.2.2.1
  have hbound := weighted_listed_restriction_mass (selected p (a.φ k)) γ
    (geom.pullbackSelection k) hE
    (fun γ z => a.worldList k γ (obs (p.B (a.φ k) γ) (δ (p.N (a.φ k)) p.L) z))
    (a.pullback_listed k) (fun γ => ENNReal.ofReal (p.ω (a.φ k) γ))
    (ENNReal.ofReal (a.κ k)) (fun γ z => a.worldList_card k γ _) B hB
  calc
    _ = ENNReal.ofReal ((a.Z k)⁻¹) * ∑ b,
        ENNReal.ofReal (p.ω (a.φ k) (γ b)) *
          (selected p (a.φ k) (γ b)).restrict (geom.pullbackSelection k b) (B (γ b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [geom.weighted_selected_apply hp a.raw_valid k b, ← geom.pullbackLaw_eq hp k b,
        mul_assoc]
      congr 3
      ext z
      simp only [geom, γ, mem_preimage, mem_ofPred_eq, MeasurableEquiv.symm_apply_apply]
    _ ≤ ENNReal.ofReal ((a.Z k)⁻¹) *
        (ENNReal.ofReal (a.κ k) * ∑ γ, ENNReal.ofReal (p.ω (a.φ k) γ) *
          selected p (a.φ k) γ (B γ)) := mul_le_mul' le_rfl hbound
    _ = _ := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (by linarith [a.slack_one k])]
      ring

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
