-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.DenseRootDyadicClock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/DenseRootDyadicClock.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/DenseRootDyadicClock.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.DenseRootClockStages
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.DyadicClockFloors

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

/-- A later clock duration is also a duration in every larger ORIGINAL
earlier source, at the same actual coarse clock code. -/
theorem OriginalParentClockStage.durations_in_larger_source
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    {hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ}
    {old : Fin p.C} {K census dimension precision coarse radius fraction : ℝ}
    {R steps : ℕ} {source : Set Event}
    (stage : OriginalParentClockStage hp old K census dimension precision coarse radius fraction
      R steps source)
    {earlier : Set Event} (hsub : stage.earlier⊆earlier)
    {current : Set Event} (hcurrent : current⊆stage.current) :
    ∀ z∈(hp.frozenPacket old).assignedSelectedEvent current,
      ENNReal.ofReal (parentClockDurationRate K*coarse) ≤ incidenceDuration
        (hp.assignedClockCellSource old (d.P k (p.γ old)) earlier coarse
          (hp.assignedClockCode old (d.P k (p.γ old)) coarse z)) z.1 := by
  intro z hz
  have hz' : z∈(hp.frozenPacket old).assignedSelectedEvent stage.current := by
    rw [(hp.frozenPacket old).assignedSelectedEvent_originalIncidence] at hz ⊢
    exact hcurrent hz
  apply (stage.durations z hz').trans
  apply measure_mono
  intro t ht
  change (z.1,t)∈hp.assignedClockCellSource old (d.P k (p.γ old)) stage.earlier coarse
    (hp.assignedClockCode old (d.P k (p.γ old)) coarse z) at ht
  change (z.1,t)∈hp.assignedClockCellSource old (d.P k (p.γ old)) earlier coarse
    (hp.assignedClockCode old (d.P k (p.γ old)) coarse z)
  refine ⟨?_,ht.2⟩
  have hselected := ht.1
  rw [(hp.frozenPacket old).assignedSelectedEvent_originalIncidence] at hselected ⊢
  exact hsub hselected

/-- The actual shallow source prepares an exactly nested MK4 dyadic
clock pair, with coarsening bounded independently of the physical mesh. -/
theorem DenseRootParentSource.prepare_dyadic_clock_stage
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
    {precision radius ζ : ℝ} (precisionIndex : ℕ)
    (hprecisionEq : precision=Submission.Lib.K4DyadicRowScales.unit precisionIndex)
    (hprecision : fineMesh ≤ precision)
    (hradius : 0 ≤ radius) (hradiusScale : radius*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (hCensus : 1 ≤ census)
    (hθCensus : δ (d.N k) (p.r (p.lev S.old))/(((2:ℝ)^p.T (p.lev S.old))⁻¹) ≤ census)
    (hmargin : 8*census^(100:ℕ)*ζ ≤ 1)
    (hprecisionζ : precision ≤
      (δ (d.N k) (p.r (p.lev S.old))/(((2:ℝ)^p.T (p.lev S.old))⁻¹))*ζ)
    (hprecisionPlain : precision ≤ ζ)
    (source : Set Event) (hsource : MeasurableSet source) (hsub : source⊆S.current) :
    ∃ steps rowIndex : ℕ, precisionIndex=steps+3*rowIndex ∧
      census^(100:ℕ) ≤ (2:ℝ)^steps ∧ (2:ℝ)^steps ≤ 8*census^(100:ℕ) ∧
      precision ≤ precision*(2:ℝ)^steps ∧
      precision*(2:ℝ)^steps=Submission.Lib.K4DyadicRowScales.mesh rowIndex ∧
      Submission.Lib.K4DyadicRowScales.mesh rowIndex ≤
        δ (d.N k) (p.r (p.lev S.old))/(((2:ℝ)^p.T (p.lev S.old))⁻¹) ∧
      Nonempty (OriginalParentClockStage hp S.old K census dimension precision
        (Submission.Lib.K4DyadicRowScales.coarse rowIndex) radius fraction R steps source) := by
  have hθ : 0 < δ (d.N k) (p.r (p.lev S.old))/(((2:ℝ)^p.T (p.lev S.old))⁻¹) := by
    unfold δ
    positivity
  obtain ⟨steps,rowIndex,heq,hlo,hhi,hprec,hmesh,hresolved,hmesh1,_,_⟩ :=
    ClockCalibration.RowScale.exists_calibrated_steps precisionIndex hprecisionEq hθ hCensus
      hprecisionζ hprecisionPlain hmargin
  have hFine : 0 < precision := hprecisionEq ▸ Submission.Lib.K4DyadicRowScales.unit_pos _
  have hFine1 : precision ≤ 1 := hprecisionEq ▸ Submission.Lib.K4DyadicRowScales.unit_le_one _
  refine ⟨steps,rowIndex,heq,hlo,hhi,hprec,hmesh,hresolved,?_⟩
  apply S.prepare_clock_stage hd hp Q hHterminal broad hio hK hmax hκK hr hfraction hFine hFine1
    hprecision hradius hradiusScale hCensus hθCensus steps hlo
    (by simpa only [hmesh] using hresolved)
    (Submission.Lib.K4DyadicRowScales.coarse_pos rowIndex)
    (Submission.Lib.K4DyadicRowScales.coarse_le_one rowIndex) source hsource hsub

/-- Two actual clock preparations retain a fixed portion of the full
original old reference. The intermediate source is not renormalized. -/
theorem DenseRootParentSource.original_mass_after_two_clocks
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hd : d.Valid)
    {hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ}
    {K G fineMesh census dimension : ℝ} {e R stop : ℕ}
    {C : BroadMultiscaleCoreSource d k p original n depth K e R}
    (S : DenseRootParentSource C G fineMesh census dimension δ₀ stop)
    {precision₁ coarse₁ radius₁ fraction₁ precision₂ coarse₂ radius₂ fraction₂ : ℝ}
    {steps₁ steps₂ : ℕ}
    (first : OriginalParentClockStage hp S.old K census dimension precision₁ coarse₁ radius₁ fraction₁
      R steps₁ S.current)
    (second : OriginalParentClockStage hp S.old K census dimension precision₂ coarse₂ radius₂ fraction₂
      R steps₂ first.current) :
    ENNReal.ofReal (p.κ⁻¹/512)*
      (d.ν k (p.γ S.old) (p.A S.old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev S.old))⁻¹)) ≤
        ((d.ν k (p.γ S.old)).prod volume) second.current := by
  have hκp : 0 < p.κ := zero_lt_one.trans_le hp.1
  let raw : Measure Event := (d.ν k (p.γ S.old)).prod volume
  let reference := d.ν k (p.γ S.old) (p.A S.old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev S.old))⁻¹)
  let cost := ENNReal.ofReal (p.κ⁻¹/4096)*reference
  letI : IsProbabilityMeasure (d.ν k (p.γ S.old)) := (hd.weights k).2.2 _
  have hrefTop : reference≠∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hcostTop : cost≠∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hrefTop
  apply ENNReal.le_of_add_le_add_right (a:=cost+cost) (ENNReal.add_ne_top.mpr ⟨hcostTop,hcostTop⟩)
  calc
    _ = ENNReal.ofReal (p.κ⁻¹/512+p.κ⁻¹/4096+p.κ⁻¹/4096)*reference := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      dsimp only [cost]
      ring
    _ ≤ ENNReal.ofReal (p.κ⁻¹/256)*reference := by
      apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      nlinarith [inv_nonneg.mpr (zero_lt_one.trans_le hp.1).le]
    _ ≤ raw S.current := S.original_mass
    _ ≤ raw first.current+cost := first.original_cost
    _ ≤ (raw second.current+cost)+cost := add_le_add second.original_cost le_rfl
    _ = _ := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
