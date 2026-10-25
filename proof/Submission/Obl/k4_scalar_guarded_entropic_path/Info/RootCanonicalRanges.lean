import Submission.Obl.k4_scalar_guarded_entropic_path.Info.CanonicalPointRanges
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootRowSupport
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootGeometryFloors
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PositiveWeights

/-! The actual later original world fixes a fine root row. Restored
coarse packet floors and the common width core then bound the complete
canonical Y record on that world class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set
open scoped ENNReal
open PathGeometry PathGeometry.PathMeasures PathGeometry.PathNodes
open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- Finite canonical ambiguity in the actual future original world,
under the unchanged common retained law. All current floor and ceiling
hypotheses concern the same original within-world measures σ. -/
theorem canonical_range_given_root_history
    (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i)
    (hl : path.forget.AllLayers i) (k : ℕ) (c f : Fin targets.length) (hcf : c ≤ f)
    (εc εf scale B H K : ℝ) (m : ℕ)
    (Qc : path.UniformRootTerminalChart i certs εc k c)
    (Qf : path.UniformRootTerminalChart i certs εf k f)
    (hQc : ChartGeometry.ofChart Qc = path.rootGeometry i certs k c)
    (hQf : ChartGeometry.ofChart Qf = path.rootGeometry i certs k f)
    (E : Set (Fin (W (path.forget.finalFamily.problem i) k) × State))
    (hE : MeasurableSet E)
    (P : Measure (Fin (W (path.forget.finalFamily.problem i) k) × State))
    (hP : P ≤ (normalizedWorldMixture (path.forget.finalFamily.problem i) k).restrict E)
    (σ : Fin (W (source.problem i) ((path.measuredChain i certs).sample k)) → Measure Incidence)
    (hfloor : RootPacketFamilies.CurrentGeometryFloors (path.measuredChain i certs) k
      (path.rootGeometry i certs k c) H E σ)
    (hcap : ∀ g, (σ g).map (obsL
        (N (source.problem i) ((path.measuredChain i certs).sample k) ^ (-path.prefixDepth i c))) ≤
      ENNReal.ofReal (B * N (source.problem i) ((path.measuredChain i certs).sample k) ^
        (-Split.f (source.problem i) (path.prefixDepth i c))) • (volume.prod Measure.count))
    (hscale : 0 ≤ scale) (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hεc : 0 ≤ εc)
    (hXc : N (source.problem i) ((path.measuredChain i certs).sample k) ^ εc ≤ K)
    (hXf : N (source.problem i) ((path.measuredChain i certs).sample k) ^ εf ≤ K)
    (hBK : B ≤ K) (hHK : H ≤ K)
    (hwidth : ∀ z ∈ E, z ∈ (path.measuredChain i certs).pathSet k →
      (K * (2 : ℝ) ^ (path.rootGeometry i certs k c).generation)⁻¹ ≤
        (path.rootGeometry i certs k c).width (path.rootRow i certs k c z.1))
    (hrcm : scale * ((m : ℝ) + 1) ≤ path.prefixDepth i c)
    (hratio : (((2 : ℝ) ^ (path.rootGeometry i certs k f).generation)⁻¹) /
        (((2 : ℝ) ^ (path.rootGeometry i certs k c).generation)⁻¹) ≤
      N (source.problem i) ((path.measuredChain i certs).sample k) ^
        (-(scale * ((m : ℝ) + 1))))
    (hmargin : 47589120000003 * K ^ 26 ≤
      N (source.problem i) ((path.measuredChain i certs).sample k) ^ scale)
    (e : ℕ) :
    ∃ U : Finset ℕ, U.card ≤ 4 ^ (3 * (m ^ 2 + 1)) ∧
      ∀ᵐ z ∂P, (path.measuredChain i certs).history k (f.val + 1) z.1 = e →
        canonY m (canonM
            (N (source.problem i) ((path.measuredChain i certs).sample k) ^ scale) K m)
          (canonX (N (source.problem i) ((path.measuredChain i certs).sample k) ^ scale) m
            (canonM (N (source.problem i) ((path.measuredChain i certs).sample k) ^ scale) K m)
            (((path.measuredChain i certs).pullback k z).2)) ∈ U := by
  classical
  let chain := path.measuredChain i certs
  let gc := path.rootGeometry i certs k c
  let gf := path.rootGeometry i certs k f
  have hPac : P ≪ worldMixture (path.forget.finalFamily.problem i) k :=
    (Measure.absolutelyContinuous_of_le (hP.trans Measure.restrict_le_self)).trans
      Measure.smul_absolutelyContinuous
  have hEae : ∀ᵐ z ∂P, z ∈ E :=
    (Measure.absolutelyContinuous_of_le hP).ae_le (ae_restrict_mem hE)
  have hpos : ∀ᵐ z ∂P, 0 < ω (source.problem i) (chain.sample k) (chain.pullback k z).1 :=
    chain.positive_weight_pullback_ae k P hPac
  have hpath : ∀ᵐ z ∂P, z ∈ chain.pathSet k := hPac.ae_le (chain.pathSet_ae k)
  by_cases hactive : ∃ z ∈ E, z ∈ chain.pathSet k ∧
      0 < ω (source.problem i) (chain.sample k) (chain.pullback k z).1 ∧
        chain.history k (f.val + 1) z.1 = e
  · obtain ⟨z₀, hz₀, hpath₀, hω₀, he₀⟩ := hactive
    obtain ⟨π, hπ, _⟩ := path.root_rowProjection_with_rootRow i certs k c f hcf
    let d := path.rootRow i certs k f z₀.1
    have hπd : π.row d = path.rootRow i certs k c z₀.1 := hπ z₀.1
    obtain ⟨Λc, hcdc⟩ := ChartGeometry.exists_chartData Qc gc hQc
    obtain ⟨Λf, hcdf⟩ := ChartGeometry.exists_chartData Qf gf hQf
    let Rc := ChartGeometry.chartOfData gc Λc hcdc
    let Rf := ChartGeometry.chartOfData gf Λf hcdf
    have hselected : (chain.pullback k z₀).2 ∈ gc.selected (π.row d) := by
      rw [hπd]
      exact path.rootRow_selected i certs k z₀ hpath₀ c
    have hworld : gc.world (π.row d) = (chain.pullback k z₀).1 := by
      rw [hπd]
      exact (path.rootRow_world i certs k c z₀.1).trans (chain.pullback_world k z₀).symm
    have hcell : E ∩ RootPacketFamilies.geometryCell chain k gc (π.row d) ≠ ∅ := by
      apply Set.nonempty_iff_ne_empty.mp
      refine ⟨z₀, hz₀, ?_⟩
      exact ⟨hworld.symm, ((hcdc.2.2.2.2.1 (π.row d)) hselected).2⟩
    have hfl : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ gc.generation)⁻¹) *
        ν (source.problem i) (chain.sample k) (gc.world (π.row d)) (gc.assignment (π.row d)) ≤
          σ (gc.world (π.row d)) (RootPacketFamilies.geometryPriorCell gc (π.row d)) := by
      have hω : 0 < ω (source.problem i) (chain.sample k) (gc.world (π.row d)) := by
        rw [hworld]
        exact hω₀
      exact (hfloor (π.row d) hω).resolve_left hcell
    have hJ : (K * (2 : ℝ) ^ gc.generation)⁻¹ ≤ gc.width (π.row d) := by
      rw [hπd]
      exact hwidth z₀ hz₀ hpath₀
    obtain ⟨U, hU, hcover⟩ := canonical_range_of_strict_actual_rows (source.angular i).1 Rc Rf
      π d scale B H K m hscale hB hH hK hm
      (path.prefixDepth_bounds i hl c).1 hεc hXc hXf hBK hHK hJ
      (σ (gc.world (π.row d))) (hcap _) hfl hrcm hratio hmargin
    refine ⟨U, hU, ?_⟩
    filter_upwards [hEae, hpath] with z hz hpz he
    have hrow : path.rootRow i certs k f z.1 = d :=
      path.rootRow_eq_of_history_eq i certs k f z.1 z₀.1 (he.trans he₀.symm)
    apply hcover _
    change (chain.pullback k z).2 ∈ gf.selected d
    rw [← hrow]
    exact path.rootRow_selected i certs k z hpz f
  · refine ⟨∅, by simp, ?_⟩
    filter_upwards [hEae, hpath, hpos] with z hz hpz hω he
    exact (hactive ⟨z, hz, hpz, hω, he⟩).elim

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
