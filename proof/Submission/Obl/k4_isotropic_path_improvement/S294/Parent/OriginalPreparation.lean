-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OriginalPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/OriginalPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalCoefficients
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPath

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set Filter

noncomputable section

namespace OriginalPreparation

abbrev Problem := DensityPreparation.Problem

/-- The analytical conditions imposed on an actual original incidence.
The scalar table is in original physical time. -/
structure PreparedAt (p : Problem) (S : ℝ) (R A : Finset ℝ) (τ : ℝ)
    (k : ℕ) (w : Fin (p.W k)) (z : Ev) : Prop where
  parent : z.1 ∈ ParentSignal.goodLines (p.P k w) (p.K k) (p.B k w)
  regular : z ∈ ParentSignal.regularEvents (p.P k w) (p.K k) (p.B k w)
  coefficients : ∀ i, |ParentSignal.globalCoefficients (p.P k w) z.1 i| ≤ 8 * p.K k
  planar : z.1 ∈ OriginalCoefficients.boxLines (p.K k)
  pure : ∀ r ∈ insert p.L R,
    ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ≤
      p.g k w r (obs (p.B k w) (δ (p.N k) r) z) ∧
    p.g k w r (obs (p.B k w) (δ (p.N k) r) z) ≤
      ENNReal.ofReal (p.N k ^ (-p.f r + τ))
  angular : ∀ u ∈ A,
    p.G k w u (obs (p.B k w) (δ (p.N k) p.L) z,
      fun j => ⌊v z.1 j / δ (p.N k) u⌋) ≤
        ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ)) *
          p.g k w p.L (obs (p.B k w) (δ (p.N k) p.L) z)

/-- Original density preparation, zero-loss parent regularity, and actual
old-packet selection compose without changing the prior or clock. The small
path exponent is chosen before any path and any terminal residual. -/
theorem exists_prepared_packet {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (R A : Finset ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L)
    (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L) {τ : ℝ} (hτ : 0 < τ)
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop,
      ∀ pth : OriginalPath.Data (p.W k),
      pth.Valid 0 (p.N k) p.L (p.ω k) (p.ν k) (p.E k) (p.B k) p.f
        κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (p.W k) → Set Ev,
      (∀ w, MeasurableSet (H w) ∧
        H w ⊆ {z | ∃ b, pth.lev b = m - 1 ∧ pth.world b = w ∧ z ∈ pth.counted b}) →
      ENNReal.ofReal (pth.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (p.ω k w) * ((p.ν k w).prod volume) (H w) →
      ∀ i : ℕ, i < m →
      ∃ (b : Fin pth.C) (U : Set Ev), pth.lev b = i ∧ 0 < p.ω k (pth.world b) ∧
        MeasurableSet U ∧ U ⊆ H (pth.world b) ∩ pth.counted b ∧
        0 < ENNReal.ofReal (PotentialFits.clock (pth.T i)) *
          p.ν k (pth.world b) (pth.assigned b) ∧
        ENNReal.ofReal (pth.κ⁻¹ / 8) *
          (ENNReal.ofReal (PotentialFits.clock (pth.T i)) *
            p.ν k (pth.world b) (pth.assigned b)) ≤
              ((p.ν k (pth.world b)).prod volume) U ∧
        ∀ z ∈ U, PreparedAt p S R A τ k (pth.world b) z := by
  classical
  obtain ⟨σ, hσ, hprep⟩ := DensityPreparation.fixed_masks hp R A hR hA hτ
  refine ⟨σ, hσ, hprep.mono ?_⟩
  intro k hk pth hpth H hH hmass i hi
  have hHE w : H w ⊆ p.E k w := by
    intro z hz
    obtain ⟨b, _, hw, hb⟩ := (hH w).2 hz
    simpa only [hw] using (hpth.counted_support b z hb).1
  obtain ⟨F, hFm, hFp, hFa, hmassF⟩ := hk pth.κ hpth.one_le_slack hpth.slack_le H
    (fun w => ⟨(hH w).1, hHE w⟩) hmass
  have hzero w := OriginalCoefficients.prepare_events_with_box hp k w (F w) (hFm w).1
    ((hFm w).2.trans (hHE w))
  choose F' hF'm hF'F hF'eq hF'parent using hzero
  have hmassEq w : ((p.ν k w).prod volume) (F' w) = ((p.ν k w).prod volume) (F w) := by
    simpa only [Measure.restrict_apply_univ] using congrArg
      (fun μ : Measure Ev => μ univ) (hF'eq w)
  have hprob := (DensityPreparation.valid_iff p S η).mp hp
  have hν w : IsProbabilityMeasure (p.ν k w) :=
    (ParentSignal.original_parent_bounds hprob k w).2.1
  obtain ⟨M, D, hdata⟩ := hp.2.2.2.2.2.2.2.2.1
  have hω := (hdata k).2.1
  have hωsum := (hdata k).2.2.1
  obtain ⟨b, hb, hbw, hbm⟩ := OriginalPath.exists_dense_packet hpth hν hω hωsum
    F' hF'm (fun w z hz => (hH w).2 ((hFm w).2 (hF'F w hz)))
    (by simpa only [hmassEq] using hmassF) i hi
  let U := F' (pth.world b) ∩ pth.counted b
  have hcounted : MeasurableSet (pth.counted b) := by
    rcases hpth.chart b with ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  letI : IsProbabilityMeasure (p.ν k (pth.world b)) := hν (pth.world b)
  refine ⟨b, U, hb, hbw, (hF'm _).inter hcounted,
    (fun z hz => ⟨(hFm _).2 (hF'F _ hz.1), hz.2⟩), ?_, hbm, ?_⟩
  · simpa only [hb] using OriginalPath.reference_pos hpth
      (show 0 < p.N k by linarith [hp.1 k]) b
  · intro z hz
    exact ⟨(hF'parent _ z hz.1).1, (hF'parent _ z hz.1).2.1,
      (hF'parent _ z hz.1).2.2.1, (hF'parent _ z hz.1).2.2.2,
      hFp _ z (hF'F _ hz.1), hFa _ z (hF'F _ hz.1)⟩

end OriginalPreparation

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
