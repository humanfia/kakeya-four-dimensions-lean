-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.OriginalParentSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/OriginalParentSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/OriginalParentSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.OriginalParentInputs

/-!
# Global original parent gradient source

The parent polynomial, good lines, hidden jets and original-time motion are all
extracted from the literal original problem data. No polynomial-gradient input is assumed.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- **The gradient source.** -/
theorem ValueBranchData.exists_original_parent_gradient_core_source
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hHterminal : ∀ w, H₀ w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, H w ⊆ broad.residual w)
    (old : Fin p.C) (hold : p.lev old = i) (hactive : F.active old)
    (hmid : p.lev old ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    {Kc width θrow : ℝ} {qc : ℕ} (hKc : 2 * K ^ (qcore + 7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc ^ qc)⁻¹ ≤ width)
    (hstrip : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ r)
    (hdeep : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞)
    (hβ1 : δref⁻¹ * ENNReal.ofReal (8 * fraction) < 1)
    (μ : Measure Event) (hμ : μ ≤ (d.ν k (p.γ old)).prod volume)
    (hsupport : ∀ᵐ z ∂μ, z ∈ V.coreRetained cores (p.γ old) ∩ p.F old) :
    ∃ keep : Set Event, MeasurableSet keep ∧
      keep ⊆ Prod.fst ⁻¹' ParentSignal.goodLines
        (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) ∧
      μ univ ≤ (μ.restrict keep) univ +
        ENNReal.ofReal (4 * K ^ (3 * R + 28) * p.κ ^ 2) *
          (ENNReal.ofReal (θrow * (K ^ R)⁻¹) + 27 * (δref * ENNReal.ofReal (p.κ ^ 2))) *
          (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) ∧
      ∀ (v : V.ActiveValue) (ii : ↥(cores v).codes × Bool), p.γ v.1.1 = p.γ old →
        (keep ∩ (V.inner v.1.1 v.1.2 ∩ (cores v).kept ii)).Nonempty →
        ∀ z ∈ (cores v).raw ii ∩ Prod.fst ⁻¹' (ParentSignal.goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))),
        ∀ z' ∈ (cores v).raw ii ∩ Prod.fst ⁻¹' (ParentSignal.goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))),
          |MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old)) -
              MvPolynomial.eval (xp z'.1 z'.2) (d.P k (p.γ old))| ≤
            (2 + coreGradientCoeff (2 * K ^ (qcore + 7)) width θrow J / 2) *
                (K ^ 14 * (K ^ 6)⁻¹ *
                  δ (d.N k) (p.r (p.lev v.1.1))) +
              (24 * K) / 2 * coreGradientCoeff (2 * K ^ (qcore + 7)) width θrow J *
                (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
                ((2 : ℝ) ^ p.T (p.lev old))⁻¹ *
                ‖packetBase p old z - packetBase p old z'‖ := by
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hwidth : δ (d.N k) (p.r mid) ≤ 1 := physical_parent_fine_width_le_one hN hr
  have hKoriginal : d.K k ≤ K := (le_max_right _ _).trans hmax
  obtain ⟨hP, hG, hAE, hparentJets, hmotion⟩ :=
    original_parent_source_inputs hd k (p.γ old) hKoriginal (H (p.γ old)) (hHE _)
  obtain ⟨keep, hkeep, hbudget, hpair⟩ := V.exists_parent_gradient_core_source Q hpure hd hp hHE hHbase hHterminal
    hK hmax hpower hκK cores broad hHbroad old hold hactive hmid hstop hr hrL hD hjets
    (d.P k (p.γ old)) hP hwidth
    (ParentSignal.goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))) hG hAE
    (by linarith : 0 ≤ 24 * K) hparentJets hmotion
    hKc hwidthpos hwidthfloor hstrip hdeep hθrow hθrow1 hfraction δref hδ0 hδtop hβ1
    μ hμ hsupport
  let G := ParentSignal.goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))
  have hae : ∀ᵐ z ∂μ, z.1 ∈ G := (ae_mono hμ) (ae_prod_fst_mem hG hAE)
  have heq : μ.restrict (keep ∩ Prod.fst ⁻¹' G) = μ.restrict keep := by
    apply Measure.restrict_congr_set
    filter_upwards [hae] with z hz
    simp only [mem_inter_iff, mem_preimage, hz, and_true]
  refine ⟨keep ∩ Prod.fst ⁻¹' G, hkeep.inter (hG.preimage measurable_fst),
    (fun z hz => hz.2), ?_, ?_⟩
  · simpa only [heq] using hbudget
  · intro v ii hv hne
    exact hpair v ii hv (hne.mono (fun z hz => ⟨hz.1.1, hz.2⟩))

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
