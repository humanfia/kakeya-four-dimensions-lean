-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ValueBranchData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ValueBranchData.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ValueBranchData.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PreGeometryBranches
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceNativeCoreEntries
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.UniformBoundsPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FullDenseResidual

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open scoped ENNReal BigOperators

noncomputable section

/-- The actual value entries, before any physical-state or potential
selection. All entry laws keep their full original assignment and clock. -/
structure ValueBranchData (d : ProblemData) (k : ℕ) (p : PathData (d.W k))
    (H : Fin (d.W k) → Set Event) (mid : ℕ) (K : ℝ) (q e R : ℕ) where
  count : ℕ
  center : Fin count → ℝ
  outer : Fin p.C → Fin count → Set Event
  inner : Fin p.C → Fin count → Set Event
  residual : Fin (d.W k) → Set Event
  count_le : (count : ℝ) ≤ K ^ 10
  measurable : ∀ b a, MeasurableSet (outer b a) ∧ MeasurableSet (inner b a)
  disjoint : ∀ b, Pairwise fun a a' => Disjoint (inner b a) (inner b a')
  subset : ∀ b a, inner b a ⊆ outer b a ∧ outer b a ⊆ H (p.γ b) ∩ p.F b
  value : ∀ b a z, z ∈ outer b a → |packetSignal (d.N k) p b z - center a| ≤ (K ^ 6)⁻¹
  residual_measurable : ∀ w, MeasurableSet (residual w)
  residual_subset : ∀ w, residual w ⊆ H w
  loss : (∑ w, ENNReal.ofReal (d.ω k w) *
    ((d.ν k w).prod volume) (H w \ residual w)) ≤
      ENNReal.ofReal (K ^ 10) * ENNReal.ofReal ((K ^ q)⁻¹)
  original_floor : ∀ b, p.lev b = mid → ∀ a, (inner b a).Nonempty →
    ENNReal.ofReal ((K ^ q)⁻¹) *
      (ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹) * d.ν k (p.γ b) (p.A b)) ≤
        ((d.ν k (p.γ b)).prod volume) (outer b a)
  quarter_cover : ∀ b, p.lev b = mid → ∀ a, (inner b a).Nonempty →
    NativeQuarterBranchCover e R K (packetNativeValueTest (d.N k) (d.B k) p b (center a))
      (((d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹))⁻¹) •
        (((d.ν k (p.γ b)).prod volume).restrict (outer b a)))
      (fun z j => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc)
  cover : ∀ w z, z ∈ residual w → ∃ b a, p.lev b = mid ∧ p.γ b = w ∧ z ∈ inner b a

theorem valueBranchData_of_original_family
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (h : OriginalValueBranchFamily d k p H mid K q e R) :
    Nonempty (ValueBranchData d k p H mid K q e R) := by
  obtain ⟨M, center, U, V, J, hM, hm, hd, hs, hv, hJ, hloss, hfloor, hquarter, hcover⟩ := h
  exact ⟨⟨M, center, U, V, J, hM, hm, hd, hs, hv,
    fun w => (hJ w).1, fun w => (hJ w).2, hloss, hfloor, hquarter, hcover⟩⟩

/-- Each surviving original value entry constructs its own coherent
core/sign branches and original core floors. No later selected core mass
is supplied as an input or used as a denominator. -/
theorem ValueBranchData.core_entries
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hN : 0 < d.N k) (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid) (hB : 0 < d.B k (p.γ b))
    (a : Fin V.count) (ha : (V.inner b a).Nonempty) (θ : ENNReal) :
    NativeCoreEntryFamily e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (((d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹))⁻¹) •
        (((d.ν k (p.γ b)).prod volume).restrict (V.outer b a)))
      (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a) θ := by
  have hKpos : 0 < K := by linarith
  apply packet_value_native_core_entries hp hN b hB hK hκK
    (show 0 < (K ^ 6)⁻¹ by positivity) le_rfl (V.center a) _ (V.outer b a)
    (V.measurable b a).1
  · exact Measure.ae_smul_measure (ae_restrict_mem (V.measurable b a).1) _
  · exact fun z hz => ((V.subset b a).2 hz).2
  · exact V.value b a
  · exact V.quarter_cover b hb a ha

/-- Fixed branch exponents work on every genuine broad source. The
original pure bands produce the value entries and their covers; no source
value bin, branch, or entry floor is supplied. -/
theorem exists_broad_value_branch_data (q : ℕ) (hq : 7 ≤ q) :
    ∃ e rad : ℕ, 4 ≤ e ∧ 1 ≤ rad ∧
    ∀ {T : Type*} {d : ProblemData}, d.Valid →
    ∀ {k : ℕ} {p : PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
    ∀ {H : Fin (d.W k) → Set Event} {u : T → ℝ} {τ ε : ℝ},
    ∀ Q : PreparedAngularPath d k p m H u τ, Q.uniformPureBounds ε → 0 ≤ τ + ε →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
    ∀ {i stop : ℕ} {mesh envelope r fraction : ℝ} {θ : ENNReal}
      {F : PaletteFamily Q i stop mesh envelope θ},
      ∀ broad : BroadResidual F r fraction,
    ∀ mid : ℕ, mid < m → 0 ≤ p.r mid → p.r mid ≤ d.L →
    ∃ J : Fin (d.W k) → Set Event,
      (∀ w, MeasurableSet (J w)) ∧ (∀ w, J w ⊆ broad.residual w) ∧
      (∀ w, (((d.ν k w).prod volume).restrict (J w)) =
        (((d.ν k w).prod volume).restrict (broad.residual w))) ∧
      Nonempty (ValueBranchData d k p J mid
        (nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + ε)) q e rad) := by
  obtain ⟨e, rad, he, hrad, hfactory⟩ := exists_original_pre_geometry_value_branches q hq
  refine ⟨e, rad, he, hrad, ?_⟩
  intro T d hd k p κ₁ m s δ₀ Mp Dp σ hp H u τ ε Q hpure htol hH
    i stop mesh envelope r fraction θ F broad mid hmid hr hrL
  have hHE := hp.residual_subset_event H hH
  obtain ⟨J, hJ, hsub, heq, hfamily⟩ := hfactory hd hp Q hpure.ceiling htol
    broad.residual broad.measurable (fun w => (broad.subset_H w).trans (hHE w))
    (fun w => (broad.subset_prepared w).trans (Q.residual_subset w))
    (fun w => (broad.subset_H w).trans (hH w)) mid hmid hr hrL
  exact ⟨J, hJ, hsub, heq, valueBranchData_of_original_family hfamily⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
