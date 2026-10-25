/-
Adapted from this LOT tree, obligation o093, session x0535, commit 62576536,
Submission/Obl/k4_scalar_critical_path_terminal/RootPrefixCharts.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootTrueCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TruePathSupport
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartGeometry

/-! Every prefix of the actual true critical path has a root TRUE chart
on the SAME final-inner tail, with coverage of the SAME pulled-back law. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open PathMeasures IntermediateTrueLift IntermediateLiftSupport TrueLiftChains RootTrueCharts

noncomputable section

def prefixDepth {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : Fin targets.length → ℝ :=
  match path with
  | .nil _ _ => Fin.elim0
  | .cons _ _ _ _ node tail =>
      Fin.cases (node.depth i) (fun j => node.depth i + tail.prefixDepth i j)

def prefixCost {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : Fin targets.length → ℝ :=
  match path with
  | .nil _ _ => Fin.elim0
  | .cons _ _ _ _ node tail =>
      Fin.cases (node.cost i) (fun j => node.cost i + tail.prefixCost i j)

def prefixBudget {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : path.Certificates i → Fin targets.length → ℕ :=
  match path with
  | .nil _ _ => fun _ => Fin.elim0
  | .cons _ _ _ _ _ tail => fun certs =>
      Fin.cases certs.1.ambientExponent
        (fun j => 2 * tail.prefixBudget i certs.2 j + 2 * certs.1.witness.exponent + 9)

/-- All original geometric fields, fixed independently of epsilon and k's
later residuals. The leaf restores full ambient TRUE C; earlier steps use
the exact selected intersections of the same literal normalizations. -/
def rootGeometry {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : TrueGridPath ctx source start targets)
    (i : ℕ) : (certs : path.Certificates i) → (k : ℕ) → Fin targets.length →
      ChartGeometry.Geometry (source.problem i) ((path.measuredChain i certs).sample k) :=
  match path with
  | .nil _ _ => fun _ _ => Fin.elim0
  | .cons _ _ _ _ _ tail => fun certs k =>
      Fin.cases
        (ChartGeometry.ofChart (ambientChart certs.1 ((tail.measuredChain i certs.2).sample k)))
        (fun j => ChartGeometry.lift certs.1.witness ((tail.measuredChain i certs.2).sample k)
          (tail.rootGeometry i certs.2 k j))

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

theorem prefixDepth_bounds (path : TrueGridPath ctx source start targets)
    (i : ℕ) (hl : path.forget.AllLayers i) (j : Fin targets.length) :
    0 ≤ path.prefixDepth i j ∧ path.prefixDepth i j < L (source.problem i) := by
  induction path with
  | nil => exact Fin.elim0 j
  | @cons source start r rs hstart hr node tail ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ⟨hl.1.depth_nonneg, hl.1.depth_lt⟩
    · have ht := ih hl.2 j
      refine ⟨add_nonneg hl.1.depth_nonneg ht.1, ?_⟩
      change node.depth i + tail.prefixDepth i j < L (source.problem i)
      linarith [hl.1.remaining_length]

theorem prefixCost_nonneg (path : TrueGridPath ctx source start targets)
    (i : ℕ) (hl : path.forget.AllLayers i) (j : Fin targets.length) :
    0 ≤ path.prefixCost i j := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases hl.1.outer_cost.1 (fun j => ?_) j
    exact add_nonneg hl.1.outer_cost.1 (ih hl.2 j)

abbrev RootChart (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (ε : ℝ) (k : ℕ) (j : Fin targets.length) :=
  ChartW (source.problem i) (path.prefixBudget i certs j)
    (path.prefixDepth i j) (path.prefixDepth i j) (path.prefixCost i j + ε) ε true
      ((path.measuredChain i certs).sample k)

/-- ALL original true prefixes are chosen on one final-inner tail. Their
complexities are fixed before the tolerance or final inner index, and every
chart covers every later AC residual on the IDENTICAL original path law. -/
theorem eventually_root_charts_with_geometry (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j : Fin targets.length,
      ∃ P : path.RootChart i certs ε k j,
        ChartGeometry.ofChart P = path.rootGeometry i certs k j ∧
        ∀ ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
          ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
          ∀ᵐ u ∂ρ.map ((path.measuredChain i certs).pullback k), u ∈ chartRegion P := by
  induction path generalizing ε with
  | nil =>
    exact Eventually.of_forall fun k j => Fin.elim0 j
  | @cons source start r rs hstart hr node tail ih =>
    let a := certs.1
    let tailChain := tail.measuredChain i certs.2
    have hquarter : 0 < ε / 4 := by positivity
    have htail := ih certs.2 hl.2 (ε / 4) hquarter
    have hloss₁ := (a.witness.loss_tendsto.comp tailChain.sample_strictMono.tendsto_atTop).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hlossε := (a.witness.loss_tendsto.comp tailChain.sample_strictMono.tendsto_atTop).eventually
      (gt_mem_nhds hquarter)
    have hsigma := (a.floorLoss_tendsto.comp tailChain.sample_strictMono.tendsto_atTop).eventually
      (gt_mem_nhds hquarter)
    have hambient := (a.ambientLoss_tendsto.comp tailChain.sample_strictMono.tendsto_atTop).eventually
      (gt_mem_nhds hε)
    have hfour : ∀ᶠ k in atTop,
        4 ≤ N (source.problem i) (a.witness.sample (tailChain.sample k)) ^ (ε / 2) :=
      ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).comp
        (a.parent_exact.1.2.1.comp
          (a.witness.sample_strictMono.comp tailChain.sample_strictMono).tendsto_atTop)).eventually_ge_atTop 4
    filter_upwards [htail, hloss₁, hlossε, hsigma, hambient, hfour]
      with k htk hl1 hlε hσε haε h4
    change a.witness.loss (tailChain.sample k) < 1 at hl1
    change a.witness.loss (tailChain.sample k) < ε / 4 at hlε
    change a.floorLoss (tailChain.sample k) < ε / 4 at hσε
    change a.ambientLoss (tailChain.sample k) < ε at haε
    have hN : 0 < N (source.problem i) (a.witness.sample (tailChain.sample k)) := by
      linarith [a.parent_exact.1.1 (a.witness.sample (tailChain.sample k))]
    have hN₁ : 1 ≤ N (source.problem i) (a.witness.sample (tailChain.sample k)) := by
      linarith [a.parent_exact.1.1 (a.witness.sample (tailChain.sample k))]
    have hfactor : 4 * N (source.problem i) (a.witness.sample (tailChain.sample k)) ^
        (a.witness.loss (tailChain.sample k) + ε / 4) ≤
      N (source.problem i) (a.witness.sample (tailChain.sample k)) ^ ε := by
      calc
        _ ≤ N (source.problem i) (a.witness.sample (tailChain.sample k)) ^ (ε / 2) *
            N (source.problem i) (a.witness.sample (tailChain.sample k)) ^ (ε / 2) :=
          mul_le_mul h4 (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith))
            (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
        _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · let P := relaxChart (ambientChart a (tailChain.sample k)) hN₁ le_rfl
        (show node.cost i + a.ambientLoss (tailChain.sample k) ≤ node.cost i + ε by linarith)
        haε.le
      refine ⟨P, rfl, ?_⟩
      intro ρ hρ
      have hac : ρ.map (tailChain.pullback k) ≪ worldMixture (node.remaining.problem i) (tailChain.sample k) :=
        (hρ.map (tailChain.measurable_pullback k)).trans (tailChain.map_absolutelyContinuous k)
      have hcovered := ambientChart_covers a (tailChain.sample k) _ hac
      apply (ae_map_iff
        ((((TrueGridPath.cons r rs hstart hr node tail).measuredChain i certs).measurable_pullback k).aemeasurable)
        (measurableSet_chartRegion P)).mpr
      exact ae_of_ae_map (tailChain.measurable_pullback k).aemeasurable
        (ae_of_ae_map (measurable_pullbackMap a.witness a.parent_exact (tailChain.sample k)).aemeasurable
          hcovered)
    · obtain ⟨Qt, hgeometry, hcover⟩ := htk j
      have hd := tail.prefixDepth_bounds i hl.2 j
      have hrel := hl.1.remaining_profile _ ⟨hd.1, hd.2.le⟩
      let P₀ := liftChartW a.witness a.parent_exact (node.remaining.angular i).1 Qt
        a.floorLoss a.saturated hrel hl.1.depth_nonneg
        (show node.depth i ≤ node.depth i + tail.prefixDepth i j by linarith [hd.1])
        hl1.le hquarter.le hσε.le hquarter.le
        (show a.witness.loss (tailChain.sample k) + ε / 4 + ε / 4 ≤ ε by linarith) hfactor
      let P := relaxChart P₀ hN₁ le_rfl
        (show node.cost i + a.witness.loss (tailChain.sample k) +
          (tail.prefixCost i j + ε / 4) ≤ node.cost i + tail.prefixCost i j + ε by linarith) le_rfl
      refine ⟨P, ?_, ?_⟩
      · change ChartGeometry.ofChart P₀ =
          ChartGeometry.lift a.witness (tailChain.sample k) (tail.rootGeometry i certs.2 k j)
        rw [ChartGeometry.of_liftChartW, hgeometry]
      intro ρ hρ
      have hac : ρ.map (tailChain.pullback k) ≪ worldMixture (node.remaining.problem i) (tailChain.sample k) :=
        (hρ.map (tailChain.measurable_pullback k)).trans (tailChain.map_absolutelyContinuous k)
      have hcovered := liftChartW_covers a.witness a.parent_exact (node.remaining.angular i).1 Qt
        a.floorLoss a.saturated hrel hl.1.depth_nonneg
        (show node.depth i ≤ node.depth i + tail.prefixDepth i j by linarith [hd.1])
        hl1.le hquarter.le hσε.le hquarter.le
        (show a.witness.loss (tailChain.sample k) + ε / 4 + ε / 4 ≤ ε by linarith) hfactor
        (ρ.map (tailChain.pullback k)) hac (hcover ρ hρ)
      apply (ae_map_iff
        ((((TrueGridPath.cons r rs hstart hr node tail).measuredChain i certs).measurable_pullback k).aemeasurable)
        (measurableSet_chartRegion P)).mpr
      exact ae_of_ae_map (tailChain.measurable_pullback k).aemeasurable
        (ae_of_ae_map (measurable_pullbackMap a.witness a.parent_exact (tailChain.sample k)).aemeasurable
          hcovered)

/-- Forgetting the additional field identities preserves the common-law
coverage theorem used by all existing original-terminal consumers. -/
theorem eventually_root_charts (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j : Fin targets.length,
      ∃ P : path.RootChart i certs ε k j,
        ∀ ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
          ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
          ∀ᵐ u ∂ρ.map ((path.measuredChain i certs).pullback k), u ∈ chartRegion P := by
  filter_upwards [path.eventually_root_charts_with_geometry i certs hl ε hε] with k hk
  intro j
  obtain ⟨P, _, hcover⟩ := hk j
  exact ⟨P, hcover⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
