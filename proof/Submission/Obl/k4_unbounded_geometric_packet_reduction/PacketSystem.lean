import Submission.Obl.k4_unbounded_geometric_packet_reduction.SampleRecovery

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open Filter MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A fixed original problem has prepared packets at every positive actual
loss, with one fixed format and one fixed projected cap tolerance. -/
def ProjectedPacketSystem (p : Data) (h η d s m S U : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ loss : ℝ, 0 < loss → ∃ᶠ k in atTop,
    Nonempty (ProjectedPackets p k M D loss h η d s m S U)

/-- The all-slack limit is taken inside the same original problem.  The
scalar cap tolerance and all polynomial formats are fixed beforehand. -/
theorem ProjectedPacketSystem.to_analyticalKnownSystem
    {p : Data} {h η d s m S U c N₀ : ℝ} {Mq Dq : ℕ}
    (hp : Valid p) (hη : 0 < η)
    (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hs1 : s < 1) (hc : 0 ≤ c)
    (hrule : ∀ N : ℝ, N₀ ≤ N → ScalarRecoveryRule N η d s m S U c Mq Dq)
    (hprep : ProjectedPacketSystem p h η d s m S U) :
    AnalyticalKnownSystem p (c / 2) h := by
  obtain ⟨Mp, Dp, hprep⟩ := hprep
  refine ⟨2 * Mp + Mq + 10, max Dp (2 * Dq), fun ε hε => ?_⟩
  let loss : ℝ := min (ε / 2) (η / 2)
  have hloss : 0 < loss := lt_min (by positivity) (by positivity)
  have hleε : loss ≤ ε / 2 := min_le_left _ _
  have hleη : loss ≤ η / 2 := min_le_right _ _
  have hltε : loss < ε := by linarith
  have hltη : loss < η := by linarith
  have hN : ∀ᶠ k in atTop, N₀ ≤ p.N k :=
    hp.scale_tendsto.eventually (eventually_ge_atTop _)
  have hlist : ∀ᶠ k in atTop, p.N k ^ loss * (Mq : ℝ) ≤ p.N k ^ ε := by
    have hh := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
      hp.scale_tendsto hltε (Mq : ℝ)
    exact hh.mono (fun _ hk => by simpa only [mul_comm] using hk.le)
  have hgap : ∀ᶠ k in atTop,
      2 * p.N k ^ (-ε) + p.N k ^ (-η) ≤ p.N k ^ (-loss) :=
    eventually_recovery_mass_gap hp.scale_tendsto hltη hltε
  apply ((hprep loss hloss).and_eventually (hN.and (hlist.and hgap))).mono
  rintro k ⟨⟨a⟩, hNk, hlistk, hgapk⟩
  exact a.to_analytical hp (hrule _ hNk) hd hd1 hs hs1 hc hε.le hltε.le hlistk hgapk

theorem ProjectedPacketSystem.to_knownSystem
    {p : Data} {h η d s m S U c N₀ : ℝ} {Mq Dq : ℕ}
    (hp : Valid p) (hη : 0 < η)
    (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hs1 : s < 1) (hc : 0 ≤ c)
    (hrule : ∀ N : ℝ, N₀ ≤ N → ScalarRecoveryRule N η d s m S U c Mq Dq)
    (hprep : ProjectedPacketSystem p h η d s m S U) : KnownSystem p (c / 2) h :=
  (hprep.to_analyticalKnownSystem hp hη hd hd1 hs hs1 hc hrule).to_knownSystem hp

/-- Q0 supplies fixed scalar parameters before the original problem and its
small atlas slack are selected.  Prepared packets then imply a genuine known
atlas, with original-law formatted incidence selections and pointwise lists. -/
theorem FixedBudgetRecovery.packets_to_known (hQ : FixedBudgetRecovery)
    {d s m S U : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hs1 : s < 1)
    (hsm : s < m) (hS : 0 < S) (hU : 0 < U) (hUm : U < m) :
    ∃ c : ℝ, 0 < c ∧ c < min s 1 ∧ ∃ η : ℝ, 0 < η ∧
      ∀ (p : Data) (h : ℝ), Valid p →
        ProjectedPacketSystem p h η d s m S U → KnownSystem p (c / 2) h := by
  obtain ⟨c, hc, hcs, M, D, hM, η, hη, N₀, hN₀, hrule⟩ :=
    hQ.fixed_parameters hd hd1 hs hs1 hsm hS hU hUm
  exact ⟨c, hc, hcs, η, hη, fun p h hp hprep =>
    hprep.to_knownSystem hp hη hd hd1 hs hs1 hc.le hrule⟩

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
