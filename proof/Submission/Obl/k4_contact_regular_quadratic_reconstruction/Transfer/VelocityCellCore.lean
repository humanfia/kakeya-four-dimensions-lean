/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/VelocityCellCore.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.ReferenceFloors
import Submission.Lib.K4HorizontalCoercivity.VelocityWitnesses

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

open Set MeasureTheory

noncomputable section

/-- Delete light original cells once. Every cell met by the final source
then has its final mass floor and three actual separated velocity witnesses.
The interval ceilings are still those of the original source. -/
theorem finite_velocity_cell_core {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [DecidableEq Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Q) (hcode : Measurable code)
    (G : Set Ω) (hG : MeasurableSet G) (F : Finset Q)
    (hcover : ∀ p ∈ G, code p ∈ F) (v : Ω → ℝ)
    {θ b r : ℝ} (hθ : 0 < θ) (hb : 0 ≤ b) (hsmall : 2 * b < θ)
    (hcap : ∀ q ∈ F, ∀ c : ℝ,
      μ {p | p ∈ G ∧ code p = q ∧ |v p - c| ≤ r} ≤ ENNReal.ofReal b) :
    ∃ G' : Set Ω, MeasurableSet G' ∧ G' ⊆ G ∧
      μ.real G ≤ μ.real G' + (F.card : ℝ) * θ ∧
      ∀ q : Q, (∃ p ∈ G', code p = q) →
        ENNReal.ofReal θ ≤ μ {p | p ∈ G' ∧ code p = q} ∧
        ∃ p₀ ∈ G', ∃ p₁ ∈ G', ∃ p₂ ∈ G',
          code p₀ = q ∧ code p₁ = q ∧ code p₂ = q ∧
          r < |v p₀ - v p₁| ∧ r < |v p₀ - v p₂| ∧ r < |v p₁ - v p₂| := by
  classical
  let E : Q → Set Ω := fun q => {p | code p = q}
  have hE (q : Q) : MeasurableSet (E q) := hcode (measurableSet_singleton q)
  obtain ⟨S, G', hSF, hG', hsub, hselected, hfloor, hloss⟩ :=
    exists_simultaneous_reference_floors μ G hG E F (fun q _ => hE q)
      (fun _ => θ) (fun _ _ => hθ.le)
  refine ⟨G', hG', hsub, ?_, ?_⟩
  · simpa only [Finset.sum_const, nsmul_eq_mul] using hloss
  · intro q hq
    obtain ⟨p, hp, hpq⟩ := hq
    have hqF : q ∈ F := hpq ▸ hcover p (hsub hp)
    have hqS : q ∈ S := hselected p hp q hqF hpq
    let A : Set Ω := {p | p ∈ G' ∧ code p = q}
    have hfl : ENNReal.ofReal θ ≤ μ A := by
      have hh : θ ≤ μ.real A := by
        simpa [measureReal_def, Measure.restrict_apply (hE q), E,
          Set.inter_comm, Set.ofPred_and, A] using hfloor q hqS
      calc
        ENNReal.ofReal θ ≤ ENNReal.ofReal (μ.real A) := ENNReal.ofReal_le_ofReal hh
        _ = μ A := ENNReal.ofReal_toReal (measure_ne_top μ A)
    have hbθ : ENNReal.ofReal b + ENNReal.ofReal b < ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add hb hb]
      exact ENNReal.ofReal_lt_ofReal_iff hθ |>.mpr (by linarith)
    have hAcap (c : ℝ) : μ (A ∩ {p | |v p - c| ≤ r}) ≤ ENNReal.ofReal b := by
      refine (measure_mono ?_).trans (hcap q hqF c)
      exact fun p hp => ⟨hsub hp.1.1, hp.1.2, hp.2⟩
    obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, hs₀₁, hs₀₂, hs₁₂⟩ :=
      Submission.Lib.K4HorizontalCoercivity.exists_three_velocity_witnesses
        μ A v r (ENNReal.ofReal b) hAcap (hbθ.trans_le hfl)
    exact ⟨hfl, p₀, hp₀.1, p₁, hp₁.1, p₂, hp₂.1,
      hp₀.2, hp₁.2, hp₂.2, hs₀₁, hs₀₂, hs₁₂⟩

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
