-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.DenseRootClockStages, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/DenseRootClockStages.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/DenseRootClockStages.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.DenseRootParentSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ShallowParentClockPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ShallowClockBudgets

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic Metric
open k4_stable_native_signal_oscillation
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Obl.k4_scalar_grid_cartesian_field
open Submission.Obl.k4_initial_horizon_bound
open scoped ENNReal

noncomputable section

/-- One actual clock preparation. Floors refer to its earlier original
law; duration and breadth refer to the later retained source. -/
structure OriginalParentClockStage
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (old : Fin p.C) (K census dimension precision coarse radius fraction : ℝ)
    (R steps : ℕ) (source : Set Event) where
  earlier : Set Event
  current : Set Event
  earlier_measurable : MeasurableSet earlier
  current_measurable : MeasurableSet current
  current_subset : current⊆earlier
  earlier_subset : earlier⊆source
  clock_good : current⊆Prod.fst ⁻¹' ParentSignal.clockJetGood
    (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))
  original_cost : ((d.ν k (p.γ old)).prod volume) source ≤
    ((d.ν k (p.γ old)).prod volume) current+
      ENNReal.ofReal (p.κ⁻¹/4096)*
        (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹))
  finite : (activeCodes (((d.ν k (p.γ old)).prod volume).restrict earlier)
    (clockParentCode p old (d.P k (p.γ old)) (precision*(2:ℝ)^steps))).Finite
  earlier_floor : ∀ q,
    (((d.ν k (p.γ old)).prod volume).restrict earlier)
      (clockParentCode p old (d.P k (p.γ old)) (precision*(2:ℝ)^steps) ⁻¹' {q})=0 ∨
    ENNReal.ofReal (parentClockCellRate K census ((2:ℝ)^steps)*
      (δ (d.N k) (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))^(-dimension)*
      (precision*(2:ℝ)^steps)^((3:ℝ)+dimension))*
      (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)) ≤
    (((d.ν k (p.γ old)).prod volume).restrict earlier)
      (clockParentCode p old (d.P k (p.γ old)) (precision*(2:ℝ)^steps) ⁻¹' {q})
  durations : ∀ z∈(hp.frozenPacket old).assignedSelectedEvent current,
    ENNReal.ofReal (parentClockDurationRate K*coarse) ≤ incidenceDuration
      (hp.assignedClockCellSource old (d.P k (p.γ old)) earlier coarse
        (hp.assignedClockCode old (d.P k (p.γ old)) coarse z)) z.1
  breadth : ∀ label (n center : P2), ‖n‖=1 →
    (((d.ν k (p.γ old)).prod volume).restrict current)
      {z | clockParentCode p old (d.P k (p.γ old)) (precision*(2:ℝ)^steps) z=label ∧
        |Inner.inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity old z-center)| ≤ radius} ≤
      ((ENNReal.ofReal (parentRenewalFloor K R))⁻¹*ENNReal.ofReal (8*fraction))*
        (((d.ν k (p.γ old)).prod volume).restrict current)
          (clockParentCode p old (d.P k (p.γ old)) (precision*(2:ℝ)^steps) ⁻¹' {label})

/-- Every later subset of the genuine dense source inherits all its
independent physical mesh censuses, with the same original constants. -/
theorem DenseRootParentSource.census_on_subset
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ}
    {K G fineMesh census dimension δ₀ : ℝ} {e R stop : ℕ}
    {C : BroadMultiscaleCoreSource d k p original n depth K e R}
    (S : DenseRootParentSource C G fineMesh census dimension δ₀ stop)
    {source : Set Event} (hsource : source⊆S.current)
    {precision : ℝ} (hprecision : fineMesh ≤ precision)
    (base hidden : ℝ) (hb : precision ≤ base) (hb1 : base ≤ 1)
    (hh : precision ≤ hidden) (hh1 : hidden ≤ 1)
    (hshape : census^(100:ℕ)*base ≤
      (δ (d.N k) (p.r (p.lev S.old))/(((2:ℝ)^p.T (p.lev S.old))⁻¹))*hidden) :
    (occupied source (fun z j => unshearedPacketBase p S.old z j)
      (physicalParentSignal (d.N k) p S.old (d.P k (p.γ S.old))) base hidden).Finite ∧
    ((occupied source (fun z j => unshearedPacketBase p S.old z j)
      (physicalParentSignal (d.N k) p S.old (d.P k (p.γ S.old))) base hidden).ncard:ℝ) ≤
      census/(base^3*hidden^dimension) := by
  obtain ⟨hfin,hnum⟩ := S.census_bounds base hidden (hprecision.trans hb) hb1
    (hprecision.trans hh) hh1 hshape
  have hsub : occupied source (fun z j => unshearedPacketBase p S.old z j)
      (physicalParentSignal (d.N k) p S.old (d.P k (p.γ S.old))) base hidden ⊆
      occupied S.current (fun z j => unshearedPacketBase p S.old z j)
        (physicalParentSignal (d.N k) p S.old (d.P k (p.γ S.old))) base hidden := by
    rintro q ⟨z,hz,heq⟩
    exact ⟨z,hsource hz,heq⟩
  refine ⟨hfin.subset hsub,le_trans ?_ hnum⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

/-- Prepare a new original clock at any precision above the genuine
source's finest physical precision. Deep resolution, all core gradients
and all censuses are supplied by that constructed source itself. -/
theorem DenseRootParentSource.prepare_clock_stage
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {H₀ : Fin (d.W k) → Set Event} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H₀ u τ)
    (hHterminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hio : i ≤ stop) {n : ℕ} {depth : Fin n → ℕ}
    {K G fineMesh census dimension : ℝ} {e R : ℕ}
    {C : BroadMultiscaleCoreSource d k p broad.residual n depth K e R}
    (S : DenseRootParentSource C G fineMesh census dimension δ₀ stop)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K) (hκK : 3*p.κ ≤ K)
    (hr : 0 ≤ p.r (depth S.resolution_depth)) (hfraction : 0 ≤ fraction)
    {precision radius coarse : ℝ} (hFine : 0 < precision)
    (hFine1 : precision ≤ 1) (hprecision : fineMesh ≤ precision)
    (hradius : 0 ≤ radius) (hradiusScale : radius*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (hCensus : 1 ≤ census)
    (hθCensus : δ (d.N k) (p.r (p.lev S.old))/(((2:ℝ)^p.T (p.lev S.old))⁻¹) ≤ census)
    (steps : ℕ) (hsteps : census^(100:ℕ) ≤ (2:ℝ)^steps)
    (hresolved : precision*(2:ℝ)^steps ≤
      δ (d.N k) (p.r (p.lev S.old))/(((2:ℝ)^p.T (p.lev S.old))⁻¹))
    (hcoarse : 0 < coarse) (hcoarse1 : coarse ≤ 1)
    (source : Set Event) (hsource : MeasurableSet source) (hsub : source⊆S.current) :
    Nonempty (OriginalParentClockStage hp S.old K census dimension precision coarse radius fraction
      R steps source) := by
  classical
  have hKp : 0 < K := by linarith
  let j := S.resolution_depth
  have hHE (w) : C.source j w⊆d.E k w :=
    (C.subset j w).trans ((broad.subset_H w).trans ((hp.residual_subset_event H₀ hHterminal) w))
  have hHbase (w) : C.source j w⊆Q.base w :=
    (C.subset j w).trans ((broad.subset_prepared w).trans (Q.residual_subset w))
  have hsourceCore : source⊆(C.values j).coreRetained (C.cores j) (p.γ S.old)∩
      (broad.residual (p.γ S.old)∩p.F S.old) := by
    intro z hz
    have hh := S.subset (hsub hz)
    exact ⟨C.current_cores j _ hh.1,C.current_subset _ hh.1,hh.2⟩
  have hmid : p.lev S.old ≤ depth j := by rw [S.level_zero]; exact Nat.zero_le _
  have hcell : 0 ≤ parentClockCellRate K census ((2:ℝ)^steps) := by
    unfold parentClockCellRate
    positivity
  have hduration : 0 ≤ parentClockDurationRate K := by
    unfold parentClockDurationRate
    positivity
  obtain ⟨earlier,current,hearlier,hcurrent,hcurSub,hearSub,hgood,hloss,hfinite,hfloor,hlong,hbroad⟩ :=
    (C.values j).prepare_shallow_parent_clock_velocity_source Q hd hp hHE hHbase hHterminal
      hK hmax hκK (C.cores j) broad hio S.old hmid S.resolution_depth_le hr S.gradient_nonneg hfraction
      hFine hFine1 (fun deep hdeep => (S.deep_base_resolution deep hdeep).trans hprecision)
      (fun deep hdeep => (S.deep_height_resolution deep hdeep).trans hprecision)
      S.deep_core_resolution hradius hradiusScale
      (ENNReal.ofReal (parentRenewalFloor K R))
      (ENNReal.ofReal_pos.mpr (parentRenewalFloor_pos hKp R)).ne' ENNReal.ofReal_ne_top
      hCensus hθCensus steps hsteps hresolved hcell hduration hcoarse hcoarse1
      source hsource hsourceCore
      (fun v ci hγ hne => S.gradients j v ci hγ
        (hne.mono (fun z hz => ⟨hsub hz.1,hz.2⟩)))
      (S.census_on_subset hsub hprecision)
  refine ⟨⟨earlier,current,hearlier,hcurrent,hcurSub,hearSub,hgood,?_,hfinite,hfloor,hlong,hbroad⟩⟩
  apply hloss.trans
  apply add_le_add le_rfl
  exact mul_le_mul' (shallow_parent_clock_source_cost_strong R hp.1 hK hκK
    (zero_lt_one.trans_le hCensus) (by positivity)) le_rfl

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
