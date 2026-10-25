import Submission.Obl.k4_contact_regular_quadratic_reconstruction.SourceCoreAssembly
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.ReturnAssembly
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.ContactAdapter

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation.Data

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α] {cfg : Model α}

/-- A measurable pointwise successful source becomes an affine candidate
without dividing its original mass by a retention factor. -/
theorem affine_candidate_of_measurable_source
    {k : ℕ} {s v ε : ℝ} {i : Fin (cfg.n k s)}
    (L : Fin 4 → ℝ) (W : Set (α × ℝ)) (hW : MeasurableSet W)
    (hsub : W ⊆ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))
    (hfit : ∀ p ∈ W, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |eval (cfg.x k p.1 t) (affineBase L) - cfg.x k p.1 t 3| ≤
        cfg.N k ^ ε * cfg.N k ^ (-s - v))
    (hmass : ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤ cfg.ρ k W) : cfg.AffineCandidate k s v ε i := by
  refine ⟨(cfg.ρ k).restrict W, L, Measure.restrict_le_self, ?_, ?_⟩
  · simpa only [Measure.restrict_apply_univ] using hmass
  · filter_upwards [ae_restrict_mem hW] with p hp
    exact ⟨(hsub hp).1, (hsub hp).2, hfit p hp⟩

/-- Pointwise form of the remaining preparation theorem. The positive input
tolerance may depend on the requested output tolerance and fixed horizon. -/
def PointwiseAffinePreparation (cfg : Model α) : Prop :=
  ∀ V : ℝ, 0 < V → cfg.κ * V ≤ cfg.e₀ / 4 → V ≤ cfg.U →
    ∀ R : ℝ, 1 < R → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ (s v : ℝ) (i : Fin (cfg.n k s)),
        R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → s + v ≤ V →
        cfg.ShiftedCandidate k s v η R i →
        ∃ (L : Fin 4 → ℝ) (W : Set (α × ℝ)), MeasurableSet W ∧
          W ⊆ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i) ∧
          (∀ p ∈ W, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
            |eval (cfg.x k p.1 t) (affineBase L) - cfg.x k p.1 t 3| ≤
              cfg.N k ^ ε * cfg.N k ^ (-s - v)) ∧
          ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
            cfg.ν k (cfg.A k s i) ≤ cfg.ρ k W

/-- The pointwise preparation supplies the source-law core on one fixed
positive contact horizon. -/
theorem Valid.second_affine_core_of_pointwise_preparation (h : cfg.Valid)
    (hprep : cfg.PointwiseAffinePreparation) : cfg.SecondAffineCore := by
  obtain ⟨V, hV, hVU, hκV⟩ := h.exists_contact_horizon
  refine ⟨V, hV, hVU, ?_⟩
  intro R hR ε hε
  obtain ⟨η, hη, hprep⟩ := hprep V hV hκV hVU R hR ε hε
  refine ⟨η, hη, hprep.mono ?_⟩
  intro k hk s v i hs hsR hv hvR hsv hshift
  obtain ⟨L, W, hW, hsub, hfit, hmass⟩ := hk s v i hs hsR hv hvR hsv hshift
  exact affine_candidate_of_measurable_source L W hW hsub hfit hmass

/-- Complete original-model reconstruction once the second pointwise affine
preparation is supplied. All geometric and coefficient losses are paid here. -/
theorem Valid.candidates_of_pointwise_preparation (h : cfg.Valid)
    {C : ℝ} (hC : 1 ≤ C) (hcal : MeshCalibration C)
    (hprep : cfg.PointwiseAffinePreparation) (hshift : cfg.ShiftedCandidates) :
    cfg.Candidates :=
  h.candidates_of_affine_candidates hC hcal
    (h.affine_candidates_of_core (h.second_affine_core_of_pointwise_preparation hprep) hshift)

/-- The frozen shifted alternatives return to the original homogeneous
coefficient budget once the second affine core is available. -/
theorem Valid.candidates_of_second_affine_core (h : cfg.Valid)
    {C : ℝ} (hC : 1 ≤ C) (hcal : MeshCalibration C)
    (hcore : cfg.SecondAffineCore) (hshift : cfg.ShiftedCandidates) :
    cfg.Candidates :=
  h.candidates_of_affine_candidates hC hcal
    (h.affine_candidates_of_core hcore hshift)

end Model

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
