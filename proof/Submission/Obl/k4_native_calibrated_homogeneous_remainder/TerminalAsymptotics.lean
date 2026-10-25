import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TerminalLists
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! The losses in terminal-list transport are subpower. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Submission.Obl.k4_scalar_grid_density_extension

theorem RemainderGeometry.normalizer_inv_le {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) : (a.Z k)⁻¹ ≤ a.κ k := by
  calc
    _ ≤ ((a.κ k)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (by linarith [a.slack_one k]))
      (a.normalizer_lower k)
    _ = a.κ k := inv_inv _

theorem RemainderGeometry.list_loss_subpower {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) :
    (∀ k, 1 ≤ a.κ k / a.Z k) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a.κ k / a.Z k ≤ q.N k ^ ε := by
  have hsub := a.slack_subpower hp
  constructor
  · intro k
    apply (le_div_iff₀ (a.normalizer_pos k)).mpr
    simpa only [one_mul] using (a.normalizer_upper k).trans (a.slack_one k)
  · intro ε hε
    have hev := Submission.Obl.k4_profile_density_bounds.eventually_subpower_pow_le
      (fun k => by rw [a.same_base k]; exact hp.scale_ge_one _) hsub.1 hsub.2 2 hε
    filter_upwards [hev] with k hk
    apply le_trans _ hk
    rw [div_eq_mul_inv, pow_two]
    exact mul_le_mul_of_nonneg_left (a.normalizer_inv_le k) (by linarith [a.slack_one k])

theorem RawRemainder.terminal_refinement_isPowerSmall {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (hp : Valid p) : ∀ ε : ℝ, 0 < ε →
    IsPowerSmall q.N (fun k => familyLaw q k {z |
      a.toRemainderGeometry.restrictedTerminalDensity k z.1 z.2 <
        ENNReal.ofReal (q.N k ^ (-ε)) * a.toRemainderGeometry.oldTerminalDensity k z.1 z.2}) := by
  have hN : ∀ k, 1 ≤ q.N k := fun k => by linarith [a.raw_valid.1 k]
  have ht := refinement_tail_isPowerSmall q.N hN (familyLaw q)
    (fun k z => a.toRemainderGeometry.oldTerminalDensity k z.1 z.2)
    (fun k z => a.toRemainderGeometry.restrictedTerminalDensity k z.1 z.2) 0
    (fun k => a.κ k / a.Z k)
    (by simpa only [zero_add] using (a.toRemainderGeometry.list_loss_subpower hp).2) ?_
  · simpa only [zero_add] using ht
  · intro ε hε k
    rw [familyLaw, worldLaw_apply]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hN k]) _)]
    simpa only [mem_ofPred_eq, zero_add] using
      a.terminal_refinement_bound hp k (ENNReal.ofReal (q.N k ^ (-ε)))

theorem RawRemainder.old_terminal_typical {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (hp : Valid p) :
    HasTypicalDensity q.N (familyLaw q)
      (fun k z => a.toRemainderGeometry.oldTerminalDensity k z.1 z.2) (p.f p.L) := by
  intro τ hτ
  obtain ⟨c, hc, hev⟩ := (profile_of_valid hp).typical p.L hp.length_pos.le le_rfl τ hτ
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [a.increasing.tendsto_atTop.eventually hev,
    (a.toRemainderGeometry.list_loss_subpower hp).2 (c / 2) (by positivity)] with k hk hloss
  let B : Fin (p.W (a.φ k)) → Set Incidence := fun γ => {z |
    p.g (a.φ k) γ p.L (obs (p.B (a.φ k) γ) (δ (p.N (a.φ k)) p.L) z) <
      ENNReal.ofReal (p.N (a.φ k) ^ (-p.f p.L - τ)) ∨
    ENNReal.ofReal (p.N (a.φ k) ^ (-p.f p.L + τ)) <
      p.g (a.φ k) γ p.L (obs (p.B (a.φ k) γ) (δ (p.N (a.φ k)) p.L) z)}
  have hB : ∀ γ, MeasurableSet (B γ) := by
    intro γ
    have hm := ((profile_of_valid hp).pure (a.φ k) γ p.L hp.length_pos.le le_rfl).1.comp
      (measurable_nativeObs (p.B (a.φ k) γ) (δ (p.N (a.φ k)) p.L))
    exact (measurableSet_lt hm measurable_const).union (measurableSet_lt measurable_const hm)
  have hbound := a.source_event_bound hp k B hB
  have hmass : (∑ γ, ENNReal.ofReal (p.ω (a.φ k) γ) * selected p (a.φ k) γ (B γ)) ≤
      ENNReal.ofReal (q.N k ^ (-c)) := by
    rw [a.same_base k]
    simpa only [familyLaw, worldLaw_apply, mem_ofPred_eq] using hk
  calc
    _ ≤ ENNReal.ofReal (a.κ k / a.Z k) *
        ∑ γ, ENNReal.ofReal (p.ω (a.φ k) γ) * selected p (a.φ k) γ (B γ) := by
      simpa only [familyLaw, worldLaw_apply, RemainderGeometry.oldTerminalDensity,
        RemainderGeometry.oldTerminalObservation, B, mem_ofPred_eq, a.same_base k] using hbound
    _ ≤ ENNReal.ofReal (q.N k ^ (c / 2)) * ENNReal.ofReal (q.N k ^ (-c)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hloss) hmass
    _ = _ := by
      rw [ofReal_rpow_mul_rpow (by linarith [a.raw_valid.1 k])]
      congr 2
      ring

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
