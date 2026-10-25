import Submission.Obl.k4_pair_anchor_jet_bins.Scale

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Submission.Lib.K4QuadraticSheets

/-- Uniform geometric estimates needed by the analytic bin construction. -/
structure Geometry (Cs : ℕ) (k A₀ : ℝ) : Prop where
  exponent : 1 ≤ k
  scale : ∀ A : ℝ, A₀ ≤ A → 2 ≤ A ∧ 2 ≤ A ^ k ∧ (A ^ k)⁻¹ ≤ A⁻¹
  degree : ∀ P : Test, (P.map (algebraMap ℝ ℂ)).totalDegree ≤ P.totalDegree
  qc : ∀ A δ : ℝ, ∀ P : Test, ScaleTest A δ P →
    ‖Submission.Lib.K4QuadraticSheets.qc (P.map (algebraMap ℝ ℂ))‖ ≤ δ⁻¹
  real_eval : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (z : Fin n → ℝ),
    ‖MvPolynomial.eval (fun i => (z i : ℂ)) (P.map (algebraMap ℝ ℂ))‖ =
      |MvPolynomial.eval z P|
  disc : ∀ A : ℝ, A₀ ≤ A → ∀ δ : ℝ, ∀ P : Test, ScaleTest A δ P →
    ∀ ζ : E3, ‖ζ‖ ≤ 1 → ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun i => ζ i)‖ ≤ A ^ (2 : ℕ)
  root_deriv : ∀ A : ℝ, A₀ ≤ A → ∀ δ : ℝ, ∀ P : Test, ScaleTest A δ P →
    ∀ (ζ : E3) (w : ℂ), ‖ζ‖ ≤ 1 →
    MvPolynomial.eval (Fin.snoc (fun i => ζ i) w) (P.map (algebraMap ℝ ℂ)) = 0 →
    ‖MvPolynomial.eval (Fin.snoc (fun i => ζ i) w)
      (MvPolynomial.pderiv (Fin.last 3) (P.map (algebraMap ℝ ℂ)))‖ ≤ A ^ (2 : ℕ)
  anchor : ∀ A : ℝ, A₀ ≤ A → ∀ δ : ℝ, ∀ P : Test, ScaleTest A δ P →
    ∀ α : R3, α ∈ Metric.closedBall (0 : R3) (1 / 8) →
    A ^ (-(Cs : ℝ)) ≤ |MvPolynomial.eval (fun i => α i) (k4_pair_anchor_jet_bins.disc P)| →
    P.map (algebraMap ℝ ℂ) ≠ 0 ∧
    ∀ ζ ∈ Metric.ball (emb α) (A ^ k)⁻¹,
      ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun i => ζ i) -
        qdisc (P.map (algebraMap ℝ ℂ)) (fun i => emb α i)‖ <
        ‖qdisc (P.map (algebraMap ℝ ℂ)) (fun i => emb α i)‖
  sqrt : ∀ A : ℝ, A₀ ≤ A → ∀ δ : ℝ, ∀ P P' : Test,
    ScaleTest A δ P → ScaleTest A δ P' → ∀ (z α : R3) (σ : ℂ),
    SafeFor (A ^ (-(Cs : ℝ))) (k4_pair_anchor_jet_bins.disc P)
      (k4_pair_anchor_jet_bins.disc P') z α σ →
    ∃ S S' : E3 → ℂ,
      (AnalyticOnNhd ℂ S (Metric.thickening (A ^ k)⁻¹ (safePath z α σ)) ∧
        ∀ ζ ∈ Metric.thickening (A ^ k)⁻¹ (safePath z α σ),
          S ζ ^ 2 = qdisc (P.map (algebraMap ℝ ℂ)) (fun i => ζ i) ∧
          qdisc (P.map (algebraMap ℝ ℂ)) (fun i => ζ i) ≠ 0) ∧
      (AnalyticOnNhd ℂ S' (Metric.thickening (A ^ k)⁻¹ (safePath z α σ)) ∧
        ∀ ζ ∈ Metric.thickening (A ^ k)⁻¹ (safePath z α σ),
          S' ζ ^ 2 = qdisc (P'.map (algebraMap ℝ ℂ)) (fun i => ζ i) ∧
          qdisc (P'.map (algebraMap ℝ ℂ)) (fun i => ζ i) ≠ 0)

end Submission.Obl.k4_pair_anchor_jet_bins
