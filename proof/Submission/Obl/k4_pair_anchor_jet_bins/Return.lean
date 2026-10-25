import Submission.Obl.k4_pair_anchor_jet_bins.Bins
import Submission.Obl.k4_pair_anchor_jet_bins.Powers

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Submission.Lib.K4QuadraticSheets

/-- A representative sharing the source's bin is small on the continued source sheet. -/
theorem bin_return (hC : Continuation) :
    ∃ (J : ℕ) (C₁ C₂ : ℝ), 0 < C₁ ∧ 0 < C₂ ∧
    ∀ A δ k V C w : ℝ, 1 ≤ A → 0 < δ → 2 ≤ A ^ k → 0 < w →
    (3 : ℝ) ^ J * (2 * w) ≤ δ * A ^ V → 2 ≤ k * C₁ + V →
    2 * A ^ (k * C₂ + 2 * (k * C₁ + V)) ≤ A ^ C →
    ∀ (P R : Test) (z α : R3) (σ : ℂ),
    ‖emb z‖ ≤ 1 → ‖emb z + σ • (emb α - emb z)‖ ≤ 1 → ‖emb α‖ ≤ 1 →
    (R.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 →
    ‖qc (R.map (algebraMap ℝ ℂ))‖ ≤ δ⁻¹ →
    ∀ f : E3 → ℂ,
    SimpleSheet (P.map (algebraMap ℝ ℂ)) f (Metric.thickening (A ^ k)⁻¹ (safePath z α σ)) →
    AnalyticOnNhd ℂ f (Metric.thickening (A ^ k)⁻¹ (safePath z α σ)) →
    (∀ ε : Bool,
      SimpleSheet (R.map (algebraMap ℝ ℂ))
        (canonBranch (R.map (algebraMap ℝ ℂ)) (emb α) ε) (Metric.ball (emb α) (A ^ k)⁻¹) ∧
      AnalyticOnNhd ℂ (canonBranch (R.map (algebraMap ℝ ℂ)) (emb α) ε)
        (Metric.ball (emb α) (A ^ k)⁻¹)) →
    (∀ (ε : Bool) ζ, ζ ∈ Metric.closedBall (emb α) ((8 * A ^ k)⁻¹) →
      ‖MvPolynomial.eval
        (Fin.snoc (fun i => ζ i) (canonBranch (R.map (algebraMap ℝ ℂ)) (emb α) ε ζ))
        (MvPolynomial.pderiv (Fin.last 3) (R.map (algebraMap ℝ ℂ)))‖ ≤ A ^ (2 : ℕ)) →
    flatJetBin J w f (emb α) ∈ bins J w R α →
    ∀ ζ ∈ Metric.closedBall (emb z) ((8 * A ^ k)⁻¹),
      ‖MvPolynomial.eval (Fin.snoc (fun i => ζ i) (f ζ)) (R.map (algebraMap ℝ ℂ))‖ ≤
        δ * A ^ C := by
  obtain ⟨J, C₁, C₂, _, hC₁, hC₂, hmain⟩ := anchor_return hC 0
  refine ⟨J, C₁, C₂, hC₁, hC₂, ?_⟩
  intro A δ k V C w hA hδ hT hw hmesh hE habsorb P R z α σ hz hb hα hR hqc f hfs hfa
    hcanon hder hbin ζ hζ
  obtain ⟨ε, hε⟩ := mem_bins hbin
  have hflat : flatJetBin J w f (emb α) =
      flatJetBin J w (canonBranch (R.map (algebraMap ℝ ℂ)) (emb α) ε) (emb α) := hε.symm
  have hjets : ∀ j : ℕ, j ≤ J →
      ‖iteratedFDeriv ℂ j f (emb α) -
        iteratedFDeriv ℂ j (canonBranch (R.map (algebraMap ℝ ℂ)) (emb α) ε) (emb α)‖ ≤
        δ * A ^ V := by
    intro j hj
    exact (jets_close_of_flatJetBin_eq hw hflat j hj).trans hmesh
  have hv : 0 ≤ δ * A ^ V := by positivity
  have hret := hmain (A ^ k) hT (emb z) (emb z + σ • (emb α - emb z)) (emb α)
    hz hb hα (P.map (algebraMap ℝ ℂ)) (R.map (algebraMap ℝ ℂ)) hR f
    (canonBranch (R.map (algebraMap ℝ ℂ)) (emb α) ε) hfs hfa (hcanon ε).1 (hcanon ε).2
    (A ^ (2 : ℕ)) (sq_nonneg _) (hder ε) (δ * A ^ V) hv hjets ζ hζ
  exact hret.trans (return_expression_bound hA hδ (norm_nonneg _) hqc hE habsorb)

end Submission.Obl.k4_pair_anchor_jet_bins
