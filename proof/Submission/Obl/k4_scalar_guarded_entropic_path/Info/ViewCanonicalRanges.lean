import Submission.Obl.k4_scalar_guarded_entropic_path.Info.RootCanonicalRanges
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewReadouts
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.FiniteRecordRanges

/-! The constant-cost canonical range certificate in every actual
original candidate frame, before the information window is chosen. -/

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

variable {root final : Code} {D S₀ η : ℝ}

/-- Finite canonical ambiguity in the actual future original world,
under the unchanged common retained law. All current floor and ceiling
hypotheses concern the same original within-world measures σ. -/
theorem canonical_range_given_view_history
    (a : OriginalView root final D S₀ η) (read : a.Readouts)
    (k : ℕ) (c f : Fin a.count) (hcf : c ≤ f)
    (εc εf scale B H K : ℝ) (m : ℕ)
    (Qc : Submission.Obl.k4_scalar_true_terminal_lifting.ChartW a.parent a.complexity
      (a.depth c) (L a.parent) (a.time c + εc) εc true (a.suffixChain.sample k))
    (Qf : Submission.Obl.k4_scalar_true_terminal_lifting.ChartW a.parent a.complexity
      (a.depth f) (L a.parent) (a.time f + εf) εf true (a.suffixChain.sample k))
    (hQc : ChartGeometry.ofChart Qc = a.geometry k c)
    (hQf : ChartGeometry.ofChart Qf = a.geometry k f)
    (E : Set (Fin (W final k) × State))
    (hE : MeasurableSet E)
    (P : Measure (Fin (W final k) × State))
    (hP : P ≤ (normalizedWorldMixture final k).restrict E)
    (σ : Fin (W a.parent (a.suffixChain.sample k)) → Measure Incidence)
    (hfloor : RootPacketFamilies.CurrentGeometryFloors a.suffixChain k
      (a.geometry k c) H E σ)
    (hcap : ∀ g, (σ g).map (obsL
        (N a.parent (a.suffixChain.sample k) ^ (-a.depth c))) ≤
      ENNReal.ofReal (B * N a.parent (a.suffixChain.sample k) ^
        (-Split.f a.parent (a.depth c))) • (volume.prod Measure.count))
    (hscale : 0 ≤ scale) (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hεc : 0 ≤ εc)
    (hXc : N a.parent (a.suffixChain.sample k) ^ εc ≤ K)
    (hXf : N a.parent (a.suffixChain.sample k) ^ εf ≤ K)
    (hBK : B ≤ K) (hHK : H ≤ K)
    (hwidth : ∀ᵐ z ∂P,
      (K * (2 : ℝ) ^ (a.geometry k c).generation)⁻¹ ≤
        (a.geometry k c).width (read.row k c z.1))
    (hrcm : scale * ((m : ℝ) + 1) ≤ a.depth c)
    (hratio : (((2 : ℝ) ^ (a.geometry k f).generation)⁻¹) /
        (((2 : ℝ) ^ (a.geometry k c).generation)⁻¹) ≤
      N a.parent (a.suffixChain.sample k) ^
        (-(scale * ((m : ℝ) + 1))))
    (hmargin : 47589120000003 * K ^ 26 ≤
      N a.parent (a.suffixChain.sample k) ^ scale)
    (e : ℕ) :
    ∃ U : Finset ℕ, U.card ≤ 4 ^ (3 * (m ^ 2 + 1)) ∧
      ∀ᵐ z ∂P, a.suffixChain.history k (f.val + 1) z.1 = e →
        canonY m (canonM
            (N a.parent (a.suffixChain.sample k) ^ scale) K m)
          (canonX (N a.parent (a.suffixChain.sample k) ^ scale) m
            (canonM (N a.parent (a.suffixChain.sample k) ^ scale) K m)
            ((a.suffixChain.pullback k z).2)) ∈ U := by
  classical
  let chain := a.suffixChain
  let gc := a.geometry k c
  let gf := a.geometry k f
  have hPac : P ≪ worldMixture final k :=
    (Measure.absolutelyContinuous_of_le (hP.trans Measure.restrict_le_self)).trans
      Measure.smul_absolutelyContinuous
  have hEae : ∀ᵐ z ∂P, z ∈ E :=
    (Measure.absolutelyContinuous_of_le hP).ae_le (ae_restrict_mem hE)
  have hpos : ∀ᵐ z ∂P, 0 < ω a.parent (chain.sample k) (chain.pullback k z).1 :=
    chain.positive_weight_pullback_ae k P hPac
  have hpath : ∀ᵐ z ∂P, z ∈ chain.pathSet k := hPac.ae_le (chain.pathSet_ae k)
  by_cases hactive : ∃ z ∈ E, z ∈ chain.pathSet k ∧
      (K * (2 : ℝ) ^ gc.generation)⁻¹ ≤ gc.width (read.row k c z.1) ∧
      0 < ω a.parent (chain.sample k) (chain.pullback k z).1 ∧
        chain.history k (f.val + 1) z.1 = e
  · obtain ⟨z₀, hz₀, hpath₀, hW₀, hω₀, he₀⟩ := hactive
    obtain ⟨π, hπ⟩ := read.projection k c f hcf
    let d := read.row k f z₀.1
    have hπd : π.row d = read.row k c z₀.1 := hπ z₀.1
    obtain ⟨Λc, hcdc⟩ := ChartGeometry.exists_chartData Qc gc hQc
    obtain ⟨Λf, hcdf⟩ := ChartGeometry.exists_chartData Qf gf hQf
    let Rc := ChartGeometry.chartOfData gc Λc hcdc
    let Rf := ChartGeometry.chartOfData gf Λf hcdf
    have hselected : (chain.pullback k z₀).2 ∈ gc.selected (π.row d) := by
      rw [hπd]
      exact read.selected k z₀ hpath₀ c
    have hworld : gc.world (π.row d) = (chain.pullback k z₀).1 := by
      rw [hπd]
      exact (read.world k c z₀.1).trans (chain.pullback_world k z₀).symm
    have hcell : E ∩ RootPacketFamilies.geometryCell chain k gc (π.row d) ≠ ∅ := by
      apply Set.nonempty_iff_ne_empty.mp
      refine ⟨z₀, hz₀, ?_⟩
      exact ⟨hworld.symm, ((hcdc.2.2.2.2.1 (π.row d)) hselected).2⟩
    have hfl : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ gc.generation)⁻¹) *
        ν a.parent (chain.sample k) (gc.world (π.row d)) (gc.assignment (π.row d)) ≤
          σ (gc.world (π.row d)) (RootPacketFamilies.geometryPriorCell gc (π.row d)) := by
      have hω : 0 < ω a.parent (chain.sample k) (gc.world (π.row d)) := by
        rw [hworld]
        exact hω₀
      exact (hfloor (π.row d) hω).resolve_left hcell
    have hJ : (K * (2 : ℝ) ^ gc.generation)⁻¹ ≤ gc.width (π.row d) := by
      rw [hπd]
      exact hW₀
    obtain ⟨U, hU, hcover⟩ := canonical_range_of_strict_actual_rows a.parent_exact Rc Rf
      π d scale B H K m hscale hB hH hK hm
      (a.depth_bounds c).1 hεc hXc hXf hBK hHK hJ
      (σ (gc.world (π.row d))) (hcap _) hfl hrcm hratio hmargin
    refine ⟨U, hU, ?_⟩
    filter_upwards [hEae, hpath] with z hz hpz he
    have hrow : read.row k f z.1 = d :=
      read.row_eq_of_history_eq k f z.1 z₀.1 (he.trans he₀.symm)
    apply hcover _
    change (chain.pullback k z).2 ∈ gf.selected d
    rw [← hrow]
    exact read.selected k z hpz f
  · refine ⟨∅, by simp, ?_⟩
    filter_upwards [hEae, hpath, hwidth, hpos] with z hz hpz hwz hω he
    exact (hactive ⟨z, hz, hpz, hwz, hω, he⟩).elim

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
