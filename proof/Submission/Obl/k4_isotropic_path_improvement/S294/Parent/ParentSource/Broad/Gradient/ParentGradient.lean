-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentGradient, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentGradient.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentGradient.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentRows

/-!
# Physical parent gradient from original-row renewal

The fine root error and the original parent motion are the only two errors.
The geometry is adapted from o265 session x0946, `CoreLipschitz.lean`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric MvPolynomial
open Analytic k4_stable_native_signal_oscillation
open scoped ContDiff

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)

include hp

/-- Broad long rows and the original norming law control the physical parent gradient. -/
theorem parent_core_gradient (hNk : 0 < Nk) (old b : Fin p.C) (hB : 0 < B (p.γ b))
    (P : Poly) (hP : P.totalDegree ≤ 2)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ 1)
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K) (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹)
    (center : ℝ) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (sign : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
    (hbranch : LocalNativeBranchData 5186 (packetNativeValueTest Nk B p b center)
      (fun j => c j) (K ^ R)⁻¹ sign F f)
    (U : Set Event) (hUm : MeasurableSet U)
    (hU : ∀ q ∈ U, CoreIncidence Nk B p old b K ε R center c f q)
    {M : ℝ} (hM : 0 ≤ M)
    (hparentJets : ∀ q ∈ U, |eval (xp q.1 q.2) (pderiv 3 P)| ≤ K * B (p.γ b) ∧
      |eval (xp q.1 q.2) (pderiv 3 (pderiv 3 P))| ≤ K * B (p.γ b) ^ 2)
    (hmotion : ∀ q ∈ U, ∀ q' ∈ U, q'.1 = q.1 →
      |eval (xp q'.1 q'.2) P - eval (xp q.1 q.2) P| ≤ M * |q'.2 - q.2|)
    {D J : ℕ} (hD : 578 ≤ D) (hjets : ValueJetBound D J)
    (μ₀ : Measure Event) (μc : (Fin 3 → ℤ) → Measure Event) (tests : (Fin 3 → ℤ) → Set Event)
    (E : Set Base) (hE : MeasurableSet E) (hEball : E ⊆ closedBall (0 : Base) (1 / 4))
    {Kc A δs β θ : ℝ} {qc : ℕ} (hKc : 2 ≤ Kc) (hA : 2 ≤ A) (hAK : A ≤ Kc)
    (hδs : 0 < δs) (hδfloor : (Kc ^ qc)⁻¹ ≤ δs) (hβ : 0 < β) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hmass₀ : ENNReal.ofReal (β / A) ≤ μ₀ univ)
    (hcap : ∀ V : Set Base, MeasurableSet V →
      μ₀ (packetLocalCorePoint Nk B p b K R c ⁻¹' V) ≤ ENNReal.ofReal β * volume V)
    (hsupp : ∀ᵐ q ∂μ₀, packetLocalCorePoint Nk B p b K R c q ∈ E)
    (threshold : (Fin 3 → ℤ) → ENNReal)
    (hstrip : ∀ i, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c' : ℝ,
      μc i ((fun q : Event => packetCubeVelocity p b q.1) ⁻¹'
        Submission.Lib.K4VelocityStrips.affineStrip n c' δs) ≤ threshold i)
    (hmass : ∀ x ∈ E, threshold (renewalCellCode Kc J qc x) <
      μc (renewalCellCode Kc J qc x) (tests (renewalCellCode Kc J qc x)))
    (hcode : ∀ i q, q ∈ tests i →
      renewalCellCode Kc J qc (packetLocalCorePoint Nk B p b K R c q) = i)
    (htestU : ∀ i q, q ∈ tests i → q ∈ U)
    (hlong : ∀ i q, q ∈ tests i → ENNReal.ofReal θ ≤ volume (coreRowTimes p b K R U q)) :
    ∀ x ∈ closedBall (0 : Base) 2,
      ‖fderiv ℝ (parentCorePrediction Nk B p b P K R c f) x‖ ≤
        coreGradientCoeff A δs θ J *
          (K ^ 14 * ε * δ Nk (p.r (p.lev b)) +
            M / 2 * coreRowStep p b K R) := by
  obtain ⟨-, -, hrow⟩ := coreRow_spec
  obtain ⟨⟨Δ, U', V', Wd, sq, Q, hΔ, hU', hV', hW', hroot, hrep, hQ, hreal, hWd⟩, hg, hgext⟩ :=
    parentCorePrediction_analytic Nk B p b P hP K R center c sign F f hbranch
  have hκ0 : 0 ≤ p.κ := by linarith [hp.1]
  have hεfit : 0 ≤ K ^ 14 * ε * δ Nk (p.r (p.lev b)) +
      M / 2 * coreRowStep p b K R := by
    have h1 : 0 < δ Nk (p.r (p.lev b)) := by unfold δ; positivity
    have h2 : 0 ≤ coreRowStep p b K R := by unfold coreRowStep; positivity
    have h3 : (0 : ℝ) ≤ K ^ 14 := by positivity
    positivity
  have hvel : Measurable (fun q : Event => packetCubeVelocity p b q.1) :=
    (measurable_packetCubeVelocity p b).comp measurable_fst
  have hres := hrow hjets Δ U' V' Wd hΔ hU' hV' hW' sq Q
    (parentCorePrediction Nk B p b P K R c f) hroot hrep hQ hreal hg (hgext D hD)
    μ₀ μc (fun q : Event => packetCubeVelocity p b q.1) hvel tests
    (packetLocalCorePoint Nk B p b K R c) E hE hEball Kc A (1 / 2) δs β θ
    (K ^ 14 * ε * δ Nk (p.r (p.lev b)) +
      M / 2 * coreRowStep p b K R) qc
    hKc hA hAK (by norm_num) (by linarith) hδs hδfloor hβ hθ hθ1 hεfit hmass₀ hcap hsupp
    threshold hstrip hmass hcode
    (fun i q hq => packetCubeVelocity_norm_le_half hp b q.1
      (coreIncidence_line_old (hU q (htestU i q hq)) hp).2.2)
    (fun i q hq => (hU q (htestU i q hq)).2.2.2.1)
    (fun i q hq => hWd _ (by linarith [(hU q (htestU i q hq)).2.2.2.1]))
    (fun i q hq => ⟨coreRowTimes p b K R U q, eval (xp q.1 q.2) P,
      measurableSet_coreRowTimes p b K R hUm q, hlong i q hq,
      fun t ht => (parent_core_row_fit hp hNk old b hB P hP hwidth hK hκK hε hεK center R c f U hU hM hparentJets hmotion q
        (htestU i q hq) t ht).1,
      fun t ht => (parent_core_row_fit hp hNk old b hB P hP hwidth hK hκK hε hεK center R c f U hU hM hparentJets hmotion q
        (htestU i q hq) t ht).2⟩)
  intro x hx
  refine (hres.1 x hx).trans (le_of_eq ?_)
  unfold coreGradientCoeff
  ring

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
