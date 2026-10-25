-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.DenseRootParentSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/DenseRootParentSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 40b071c3e1be70138434c7f18ff663f9c27a6dfa,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/DenseRootParentSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.MultiscaleCoreSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentMovingBandCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedDeepMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepPhysicalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentGradient
import Submission.Lib.K4ParentSignalPreparation.Census
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

/-- Data actually produced by early original gradient pruning and dense
root selection. Every measure and denominator remains original. -/
structure DenseRootParentSource
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ}
    {K : ℝ} {e R : ℕ}
    (C : BroadMultiscaleCoreSource d k p original n depth K e R)
    (G fineMesh census dimension δ₀ : ℝ) (stop : ℕ) where
  old : Fin p.C
  level_zero : p.lev old=0
  weight_pos : 0 < d.ω k (p.γ old)
  assignment_pos : d.ν k (p.γ old) (p.A old)≠0
  current : Set Event
  measurable : MeasurableSet current
  subset : current⊆C.current (p.γ old)∩p.F old
  goodLines : current⊆Prod.fst ⁻¹' ParentSignal.goodLines
    (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))
  original_mass : ENNReal.ofReal (p.κ⁻¹/256)*
    (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)) ≤
      ((d.ν k (p.γ old)).prod volume) current
  gradients : ∀ (j : Fin n) (v : (C.values j).ActiveValue) (ci : ↥(C.cores j v).codes × Bool),
    p.γ v.1.1=p.γ old →
    (current∩((C.values j).inner v.1.1 v.1.2∩(C.cores j v).kept ci)).Nonempty →
    ∀ x∈closedBall (0 : Base) 2,
      ‖fderiv ℝ (parentCorePrediction (d.N k) (d.B k) p v.1.1 (d.P k (p.γ v.1.1)) K R
        ((C.cores j v).center ci.1.1) ((C.cores j v).sheet ci)) x‖ ≤
        G*(K^14*(K^6)⁻¹*δ (d.N k) (p.r (depth j))+12*K*coreRowStep p v.1.1 K R)
  census_bounds : ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
    census^(100:ℕ)*base ≤ (δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*hidden →
    (occupied current (fun z j => unshearedPacketBase p old z j)
      (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) base hidden).Finite ∧
    ((occupied current (fun z j => unshearedPacketBase p old z j)
      (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) base hidden).ncard:ℝ) ≤
      census/(base^3*hidden^dimension)

  one_le_census : 1 ≤ census
  height_ratio_le_census :
    δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ census
  gradient_nonneg : 0 ≤ G
  resolution_depth : Fin n
  resolution_depth_le : depth resolution_depth ≤ stop
  deep_base_resolution : ∀ deep : Fin p.C, p.lev deep=stop →
    p.unshearedDeepRadius old deep ≤ fineMesh
  deep_height_resolution : ∀ deep : Fin p.C, p.lev deep=stop →
    let aOld := δ (d.N k) (p.r (p.lev old))
    let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
    let Lip := (12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison)*
      (((2:ℝ)^p.T (p.lev old))⁻¹)/aOld
    (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r (depth resolution_depth))/aOld))+
      Lip*(6*p.unshearedDeepRadius old deep) ≤ fineMesh
  deep_core_resolution : ∀ fine deep : Fin p.C,
    p.lev fine=depth resolution_depth → p.lev deep=stop →
    p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K^R)⁻¹/12

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
