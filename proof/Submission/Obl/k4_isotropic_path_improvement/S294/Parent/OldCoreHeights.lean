-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OldCoreHeights, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/OldCoreHeights.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Height sheets of a dense root source (paper tex-06, "the
Q-graph lists predict X to Ka"): at any core depth `j`, every source incidence
lies in a piece (active value, kept core/sign entry), and inside a piece the
physical parent is Lipschitz in the unsheared base of ANY target packet up to
the core-depth thickness (x1035's `CoreEntryData.parent_pairs_of_gradient`
with the source's whole-core gradients). This is the per-piece input of the
base-only row lists of the Cartesian field.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.CapturedParentPairs
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.DenseRootParentSource

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set Metric ParentSource ParentSource.Native ParentSource.Analytic

noncomputable section

/-- **Height pieces of a dense root source at one core depth.** Every
incidence of the source lies in a piece (active value of the depth, kept
core/sign entry); inside one piece the physical parent `P` is Lipschitz in
the unsheared base of ANY target packet, up to the core-depth thickness. -/
theorem ParentSource.DenseRootParentSource.height_pieces
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ}
    {K : ℝ} {e R : ℕ} {C : BroadMultiscaleCoreSource d k p original n depth K e R}
    {G fineMesh census dimension δ₀' : ℝ} {stop : ℕ}
    (S : DenseRootParentSource C G fineMesh census dimension δ₀' stop)
    (hd : d.Valid) {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ j w, C.source j w ⊆ d.E k w) (hK : 2 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hκK : 3 * p.κ ≤ K) (j : Fin n) (hr : 0 ≤ p.r (depth j)) (target : Fin p.C) :
    (∀ z ∈ S.current, ∃ (v : (C.values j).ActiveValue) (ci : ↥(C.cores j v).codes × Bool),
      p.γ v.1.1 = p.γ S.old ∧
        z ∈ S.current ∩ ((C.values j).inner v.1.1 v.1.2 ∩ (C.cores j v).kept ci)) ∧
    ∀ (v : (C.values j).ActiveValue) (ci : ↥(C.cores j v).codes × Bool),
      p.γ v.1.1 = p.γ S.old →
      ∀ z ∈ S.current ∩ ((C.values j).inner v.1.1 v.1.2 ∩ (C.cores j v).kept ci),
      ∀ z' ∈ S.current ∩ ((C.values j).inner v.1.1 v.1.2 ∩ (C.cores j v).kept ci),
        |MvPolynomial.eval (ParentSource.xp z.1 z.2) (d.P k (p.γ S.old)) -
          MvPolynomial.eval (ParentSource.xp z'.1 z'.2) (d.P k (p.γ S.old))| ≤
          (2 + G / 2) * (K ^ 14 * (K ^ 6)⁻¹ * ParentSource.δ (d.N k) (p.r (depth j))) +
            (12 * K * G * (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
              (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2)))) *
              (((2 : ℝ) ^ p.T (p.lev target))⁻¹) *
              ‖unshearedPacketBase p target z - unshearedPacketBase p target z'‖ := by
  classical
  refine ⟨?_, ?_⟩
  · intro z hz
    have hC := (S.subset hz).1
    have hret := C.current_cores j _ hC
    obtain ⟨-, hU⟩ := hret
    simp only [mem_iUnion] at hU
    obtain ⟨v, hv⟩ := hU
    by_cases hγ : p.γ v.1.1 = p.γ S.old
    · rw [ite_eq_left hγ] at hv
      obtain ⟨hin, hkept⟩ := hv
      simp only [mem_iUnion] at hkept
      obtain ⟨ci, hci⟩ := hkept
      exact ⟨v, ci, hγ, hz, hin, hci⟩
    · rw [ite_eq_right hγ] at hv
      exact absurd hv (notMem_empty z)
  · intro v ci hγ z hz z' hz'
    have hne : (S.current ∩ ((C.values j).inner v.1.1 v.1.2 ∩ (C.cores j v).kept ci)).Nonempty :=
      ⟨z, hz⟩
    have hgrad := S.gradients j v ci hγ hne
    have hpair := ParentSource.CoreEntryData.parent_pairs_of_gradient (C.values j) hd hp (hHE j)
      hK hmax hκK v.1.1 v.2.1 hr v.1.2 (C.cores j v) ci S.gradient_nonneg hgrad target
    have hgood (x : Event) (hx : x ∈ S.current) :
        x.1 ∈ ParentSignal.goodLines (d.P k (p.γ v.1.1)) (d.K k) (d.B k (p.γ v.1.1)) := by
      rw [hγ]
      exact S.goodLines hx
    have hraw (x : Event) (hx : x ∈ S.current ∩ ((C.values j).inner v.1.1 v.1.2 ∩
        (C.cores j v).kept ci)) : x ∈ (C.cores j v).raw ci ∩ Prod.fst ⁻¹' ParentSignal.goodLines
          (d.P k (p.γ v.1.1)) (d.K k) (d.B k (p.γ v.1.1)) :=
      ⟨((C.cores j v).subset ci).1 hx.2.2, hgood x hx.1⟩
    have h := hpair z (hraw z hz) z' (hraw z' hz')
    rw [hγ] at h
    exact h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
