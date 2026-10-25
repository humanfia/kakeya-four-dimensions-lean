import Submission.Obl.k4_scalar_guarded_entropic_path.Info.ViewCanonicalRanges
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.StagePointReadouts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CoreViews
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryWidths

/-! Instantiate the canonical point-state ambiguity theorem on the
actual floored common preparation. The original charts, weights, priors,
within-world laws, and scalar readouts are all unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set
open scoped ENNReal
open PathGeometry PathGeometry.PathMeasures PathGeometry.PathPruning
open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

noncomputable section

/-- The complete canonical natural-valued observation record. Keeping
this application intact preserves all dependent finite-code indices
when replacing one equal original resolution by another. -/
def canonicalRecord (N K : ℝ) (m : ℕ) (z : Incidence) : ℕ :=
  canonY m (canonM N K m) (canonX N m (canonM N K m) z)

variable {α : Type*} [Fintype α] {root final : Code} {D S₀ η : ℝ}

/-- The common preparation supplies all geometric measure hypotheses.
Only explicit inner-scale inequalities are left to the stage numerics. -/
theorem canonical_point_ranges_from_floored_core
    (views : α → OriginalView root final D S₀ η) (hz : Exact final)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent)
    (γ : ℝ) (k : ℕ) (E : Set (Fin (W final k) × State))
    (hcore : PreparedViews.FlooredCoreProperties views ε u tests γ k E)
    (a : α) (read : (views a).Readouts) (c f : Fin (views a).count) (hcf : c ≤ f)
    (scale K : ℝ) (m : ℕ) (hscale : 0 ≤ scale) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hε : 0 ≤ ε a) (htest : (views a).depth c ∈ (tests a).pure)
    (hX : N final k ^ ε a ≤ K) (hH : N final k ^ γ ≤ K)
    (hwidth : 2 * N final k ^ (ε a + u a) ≤ K)
    (hpure : N final k ^ (tests a).tolerance ≤ K)
    (hrcm : scale * ((m : ℝ) + 1) ≤ (views a).depth c)
    (hratio : (((2 : ℝ) ^ ((views a).geometry k f).generation)⁻¹) /
        (((2 : ℝ) ^ ((views a).geometry k c).generation)⁻¹) ≤
      N final k ^ (-(scale * ((m : ℝ) + 1))))
    (hmargin : 47589120000003 * K ^ 26 ≤ N final k ^ scale) :
    FiniteRangeGiven ((normalizedWorldMixture final k).restrict E)
      (fun z => canonY m (canonM (N final k ^ scale) K m)
        (canonX (N final k ^ scale) m (canonM (N final k ^ scale) K m)
          (((views a).suffixChain.pullback k z).2)))
      (fun z => (views a).suffixChain.history k (f.val + 1) z.1)
      (4 ^ (3 * (m ^ 2 + 1))) := by
  have hNpos : 0 < N final k := by linarith [hz.1.1 k]
  let P := (normalizedWorldMixture final k).restrict E
  let view := views a
  let σ := view.suffixChain.selectedWorldLaw k E
  have hPcore : P ≤ (normalizedWorldMixture final k).restrict (PreparedViews.core views ε u tests k) :=
    Measure.restrict_mono hcore.2.1 le_rfl
  have hPac : P ≪ worldMixture final k :=
    (Measure.absolutelyContinuous_of_le (show P ≤ normalizedWorldMixture final k from
      Measure.restrict_le_self)).trans Measure.smul_absolutelyContinuous
  obtain ⟨Qc, hcChoice, hcGeom, hcFloor⟩ := hcore.2.2.2.1 a c
  obtain ⟨Qf, hfChoice, hfGeom, hfFloor⟩ := hcore.2.2.2.1 a f
  have hgeometryFloor : RootPacketFamilies.CurrentGeometryFloors view.suffixChain k
      (view.geometry k c) (N final k ^ γ) E σ :=
    chartFloors_geometry view.suffixChain k Qc _ hcGeom (N final k ^ γ) E hcFloor
  obtain ⟨Λc, hcdc⟩ := ChartGeometry.exists_chartData Qc (view.geometry k c) hcGeom
  have hpathAE : ∀ᵐ z ∂P, z ∈ view.suffixChain.pathSet k :=
    hPac.ae_le (view.suffixChain.pathSet_ae k)
  have hsel : ∀ᵐ z ∂P, (view.suffixChain.pullback k z).2 ∈
      (view.geometry k c).selected (read.row k c z.1) :=
    hpathAE.mono (fun z hz => read.selected k z hz c)
  have hworld : ∀ᵐ z ∂P, (view.geometry k c).world (read.row k c z.1) =
      (view.suffixChain.pullback k z).1 := Filter.Eventually.of_forall fun z =>
    (read.world k c z.1).trans (view.suffixChain.pullback_world k z).symm
  have hrowWidth := PreparedViews.fixed_row_width_ae views ε u tests k P hPcore a c Qc
    hcChoice hcGeom (fun z => read.row k c z.1) hworld hsel
    (fun d => ((hcdc.2.2.2.2.2.1 d).2.1).le) K
    (by simpa only [view, ← (views a).suffixChain.resolution k] using hwidth)
  have hNparentpos : 0 < N view.parent (view.suffixChain.sample k) := by
    linarith [view.parent_exact.1.1 (view.suffixChain.sample k)]
  have hcap (g : Fin (W view.parent (view.suffixChain.sample k))) :
      (σ g).map (obsL (N view.parent (view.suffixChain.sample k) ^ (-view.depth c))) ≤
        ENNReal.ofReal (K * N view.parent (view.suffixChain.sample k) ^ (-Split.f view.parent (view.depth c))) •
          (volume.prod Measure.count) := by
    have hnull : σ g (pureException view.parent (view.suffixChain.sample k) g
        (view.depth c) (tests a).tolerance) = 0 :=
      PreparedViews.current_pure_null views ε u tests k P hPcore a _ htest g
    have hbase := pure_observation_cap view.parent_exact (view.suffixChain.sample k) g
      (view.depth_bounds c).1 (view.depth_bounds c).2.le (tests a).tolerance
      (view.suffixChain.selectedWorldLaw_le hz k E g) hnull
    apply hbase.trans
    apply Measure.le_iff.mpr
    intro A hA
    simp only [Measure.smul_apply, smul_eq_mul]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = N view.parent (view.suffixChain.sample k) ^ (tests a).tolerance *
          N view.parent (view.suffixChain.sample k) ^ (-Split.f view.parent (view.depth c)) := by
        rw [← Real.rpow_add (by linarith [view.parent_exact.1.1 (view.suffixChain.sample k)])]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa only [← view.suffixChain.resolution k] using hpure) (by positivity)
  intro e
  have hrange := canonical_range_given_view_history view read k c f hcf
    (ε a) (ε a) scale K (N final k ^ γ) K m Qc Qf hcGeom hfGeom E hcore.1 P le_rfl
    σ hgeometryFloor hcap hscale (by linarith) (by positivity) hK hm hε
    (by simpa only [← view.suffixChain.resolution k] using hX)
    (by simpa only [← view.suffixChain.resolution k] using hX) le_rfl hH hrowWidth
    hrcm (by simpa only [← view.suffixChain.resolution k] using hratio)
    (by simpa only [← view.suffixChain.resolution k] using hmargin) e
  change ∃ U : Finset ℕ, U.card ≤ 4 ^ (3 * (m ^ 2 + 1)) ∧
    ∀ᵐ z ∂P, view.suffixChain.history k (f.val + 1) z.1 = e →
      canonicalRecord (N view.parent (view.suffixChain.sample k) ^ scale) K m
        ((view.suffixChain.pullback k z).2) ∈ U at hrange
  dsimp only [view, P] at hrange
  rw [← (views a).suffixChain.resolution k] at hrange
  exact hrange

/-- On the actual dense grid, a long lookahead gives the complete local
history range needed by hs. Its only block-count inputs are the same
calibrated counts required for the final guarded path. -/
theorem canonical_point_ranges_from_grid_core
    (views : α → OriginalView root final D S₀ η) (hz : Exact final)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent)
    (γ : ℝ) (k : ℕ) (E : Set (Fin (W final k) × State))
    (hcore : PreparedViews.FlooredCoreProperties views ε u tests γ k E)
    (a : α) (read : (views a).Readouts)
    (scale K κ ηgrid Δ baseLength error v Bcal : ℝ) (m : ℕ)
    (hscale : 0 ≤ scale) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hη : 0 < ηgrid)
    (herror : 0 ≤ error) (herrorScale : error ≤ scale) (hv : v ≤ scale)
    (hstep : Δ * baseLength = scale * ηgrid)
    (hcount : 2 * pointHalfWindow κ ηgrid m ≤ (views a).count)
    (hgrid : PathNodes.TrueGridPath.GridControl (views a) κ Δ baseLength error)
    (hε : 0 ≤ ε a)
    (htest : (views a).depth (pointCoarseIndex (pointHalfWindow κ ηgrid m)
      (pointHalfWindow_pos κ ηgrid m) hcount) ∈ (tests a).pure)
    (hX : N final k ^ ε a ≤ K) (hH : N final k ^ γ ≤ K)
    (hwidth : 2 * N final k ^ (ε a + u a) ≤ K)
    (hpure : N final k ^ (tests a).tolerance ≤ K)
    (hBcal : 0 < Bcal) (hBv : Bcal ≤ N final k ^ v)
    (hcoarse : (2 : ℝ) ^ ((views a).geometry k (pointCoarseIndex (pointHalfWindow κ ηgrid m)
        (pointHalfWindow_pos κ ηgrid m) hcount)).generation ≤
      Bcal * N final k ^ (κ * (views a).depth (pointCoarseIndex (pointHalfWindow κ ηgrid m)
        (pointHalfWindow_pos κ ηgrid m) hcount)))
    (hfine : N final k ^ (κ * (views a).depth (pointFineIndex (pointHalfWindow κ ηgrid m)
        (pointHalfWindow_pos κ ηgrid m) hcount)) / Bcal ≤
      (2 : ℝ) ^ ((views a).geometry k (pointFineIndex (pointHalfWindow κ ηgrid m)
        (pointHalfWindow_pos κ ηgrid m) hcount)).generation)
    (hmargin : 47589120000003 * K ^ 26 ≤ N final k ^ scale) :
    FiniteRangeGiven ((normalizedWorldMixture final k).restrict E)
      (fun z => canonY m (canonM (N final k ^ scale) K m)
        (canonX (N final k ^ scale) m (canonM (N final k ^ scale) K m)
          (((views a).suffixChain.pullback k z).2)))
      (fun z => (views a).suffixChain.history k (2 * pointHalfWindow κ ηgrid m) z.1)
      (4 ^ (3 * (m ^ 2 + 1))) := by
  let q := pointHalfWindow κ ηgrid m
  have hq : 0 < q := pointHalfWindow_pos κ ηgrid m
  let c := pointCoarseIndex q hq hcount
  let f := pointFineIndex q hq hcount
  have hg := point_grid_depth_gaps (views a) hκ hκ1 hη hscale herror herrorScale hv
    hstep hcount hgrid
  have hN : 1 ≤ N final k := (by norm_num : (1 : ℝ) ≤ 2).trans (hz.1.1 k)
  have hr := duration_ratio_of_calibrated_counts hN hBcal hBv hcoarse hfine hg.2
  have hlocal := canonical_point_ranges_from_floored_core views hz ε u tests γ k E hcore
    a read c f (point_indices_ordered hq hcount) scale K m hscale hK hm hε htest hX hH
    hwidth hpure hg.1 hr hmargin
  have hfuture : f.val + 1 = 2 * q := point_fine_future hq hcount
  simpa only [hfuture] using hlocal

/-- The precise StageLayout used by the finite-stage construction gives
constant canonical ambiguity after its actual C future worlds. -/
theorem canonical_point_ranges_from_layout_core
    (views : α → OriginalView root final D S₀ η) (hz : Exact final)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent)
    (γ : ℝ) (k : ℕ) (E : Set (Fin (W final k) × State))
    (hcore : PreparedViews.FlooredCoreProperties views ε u tests γ k E)
    (a : α) (read : (views a).Readouts)
    {stage : ℕ} {R δ κ angularRange : ℝ} (q : StageLayout stage R δ κ angularRange)
    (hc : q.C ≤ (views a).count) (K error v Bcal : ℝ)
    (hK : 1 ≤ K) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (herror : 0 ≤ error) (herrorSmall : error ≤ q.scale / 8) (hv : v ≤ q.scale / 8)
    (hgrid : PathNodes.TrueGridPath.GridControl (views a) κ (q.scale * q.mesh) 1 error)
    (hε : 0 ≤ ε a)
    (htest : (views a).depth (layoutPointCoarse q hc) ∈ (tests a).pure)
    (hX : N final k ^ ε a ≤ K) (hH : N final k ^ γ ≤ K)
    (hwidth : 2 * N final k ^ (ε a + u a) ≤ K)
    (hpure : N final k ^ (tests a).tolerance ≤ K)
    (hBcal : 0 < Bcal) (hBv : Bcal ≤ N final k ^ v)
    (hcoarse : (2 : ℝ) ^ ((views a).geometry k (layoutPointCoarse q hc)).generation ≤
      Bcal * N final k ^ (κ * (views a).depth (layoutPointCoarse q hc)))
    (hfine : N final k ^ (κ * (views a).depth (layoutPointFine q hc)) / Bcal ≤
      (2 : ℝ) ^ ((views a).geometry k (layoutPointFine q hc)).generation)
    (hmargin : 47589120000003 * K ^ 26 ≤ N final k ^ q.scale) :
    FiniteRangeGiven ((normalizedWorldMixture final k).restrict E)
      (fun z => canonY q.m (canonM (N final k ^ q.scale) K q.m)
        (canonX (N final k ^ q.scale) q.m (canonM (N final k ^ q.scale) K q.m)
          (((views a).suffixChain.pullback k z).2)))
      (fun z => (views a).suffixChain.history k q.C z.1)
      (4 ^ (3 * (q.m ^ 2 + 1))) := by
  have hg := layout_point_depth_gaps q (views a) hc hκ hκ1 herror herrorSmall hv hgrid
  have hN : 1 ≤ N final k := (by norm_num : (1 : ℝ) ≤ 2).trans (hz.1.1 k)
  have hr := duration_ratio_of_calibrated_counts hN hBcal hBv hcoarse hfine hg.2
  have hlocal := canonical_point_ranges_from_floored_core views hz ε u tests γ k E hcore
    a read (layoutPointCoarse q hc) (layoutPointFine q hc) (layoutPoint_ordered q hc)
    q.scale K q.m q.scale_pos.le hK q.m_one hε htest hX hH hwidth hpure hg.1 hr hmargin
  simpa only [layoutPoint_future] using hlocal

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
