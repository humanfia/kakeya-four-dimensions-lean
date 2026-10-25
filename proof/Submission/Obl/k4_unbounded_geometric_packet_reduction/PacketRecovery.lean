import Submission.Obl.k4_unbounded_geometric_packet_reduction.ProjectedPackets
import Submission.Obl.k4_unbounded_geometric_packet_reduction.ScalarRecovery
import Submission.Obl.k4_horizon_light_cell_mass.Observation

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

theorem packetObservation_measurable {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) :
    Measurable (packetObservation a b) :=
  (Submission.Obl.k4_horizon_light_cell_mass.pureMap_measurable _ _).comp
    (packetExpand_measurable a b)

/-- A scalar recovery rule at one sample.  The coefficient tolerance is fixed
at one, independently of the original atlas's actual small loss. -/
def ScalarRecoveryRule (N η d s m S U c : ℝ) (M D : ℕ) : Prop :=
  ∀ (ν : Measure (ℕ × (Fin 6 → ℝ)))
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ)
    (O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ)
    (base : (EuclideanSpace ℝ (Fin 3) × ℤ) → EuclideanSpace ℝ (Fin 2))
    (signal : (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ),
    ProjectedScalarLaw N η d s m S U ν μ b →
    ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ →
    Measurable O → Measurable base → Measurable signal →
    (∀ᵐ z ∂μ, base (O z) = WithLp.toLp 2 ![z.2, scalarY (b z.1) z.2] ∧
      |scalarX (b z.1) z.2 - signal (O z)| ≤ N ^ (-1 + η)) →
    Nonempty (ScalarRecovery N d s c 1 M D μ b O)

theorem FixedBudgetRecovery.fixed_parameters (hQ : FixedBudgetRecovery)
    {d s m S U : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hs1 : s < 1)
    (hsm : s < m) (hS : 0 < S) (hU : 0 < U) (hUm : U < m) :
    ∃ c : ℝ, 0 < c ∧ c < min s 1 ∧ ∃ M D : ℕ, 1 ≤ M ∧
      ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
        ∀ N : ℝ, N₀ ≤ N → ScalarRecoveryRule N η d s m S U c M D := by
  obtain ⟨c, hc, hcs, M, D, hM, hrec⟩ :=
    hQ.parameters hd hd1 hs hs1 hsm hS hU hUm
  obtain ⟨η, hη, N₀, hN₀, hrec⟩ := hrec 1 zero_lt_one le_rfl
  exact ⟨c, hc, hcs, M, D, hM, η, hη, N₀, hN₀, hrec⟩

/-- Apply Q0 simultaneously to all substantial packets.  Every application
uses the same fixed prior-times-block denominator. -/
theorem ProjectedPackets.recover
    {p : Data} {k Mp Dp : ℕ} {loss h η d s m S U c : ℝ} {M D : ℕ}
    (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (hrule : ScalarRecoveryRule (p.N k) η d s m S U c M D) :
    Nonempty (∀ b : {b : Fin a.atlas.C |
        ENNReal.ofReal (p.N k ^ (-η)) ≤ a.law b Set.univ},
      ScalarRecovery (p.N k) d s c 1 M D (a.law b.val)
        (packetCoeff a.atlas a.offset a.tangent b.val) (packetObservation a.atlas b.val)) := by
  classical
  have hr (b : {b : Fin a.atlas.C |
      ENNReal.ofReal (p.N k ^ (-η)) ≤ a.law b Set.univ}) :=
    hrule (a.prior b.val) (a.law b.val) (packetCoeff a.atlas a.offset a.tangent b.val)
      (packetObservation a.atlas b.val) (a.base b.val) (a.signal b.val)
      (a.projected b.val) b.property (packetObservation_measurable _ _)
      (a.base_measurable b.val) (a.signal_measurable b.val) (a.observed_signal b.val)
  exact ⟨fun b => Classical.choice (hr b)⟩

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
