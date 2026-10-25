/-
Adapted from this LOT tree, obligation o093, session x0535, commit 5d4e5637,
Submission/Obl/k4_scalar_critical_path_terminal/RootTrueCharts.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueAmbientCharts

/-! Seed the finite backward lift with the ambient TRUE chart of the
actual last normalization. The resulting original chart covers every
later residual on exactly the same composed original law. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootTrueCharts

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open PathMeasures IntermediateLiftSupport TrueLiftChains

noncomputable section

variable {p q z : Code} {r b h : ℝ}

theorem inputLoss_le (chain : Chain p q) {ε : ℝ} (hε : 0 ≤ ε) :
    chain.inputLoss ε ≤ ε := by
  induction chain generalizing ε with
  | nil => exact le_rfl
  | cons a hL hr hh hrelative tail ih =>
    exact (ih (show 0 ≤ ε / 4 by positivity)).trans (by linarith)

/-- One ambient TRUE piece for every identical retained normalized world. -/
def ambientChart (a : TrueNormalization p q r b h) (k : ℕ) :
    ChartW p a.ambientExponent r b (h + a.ambientLoss k) (a.ambientLoss k) true
      (a.witness.sample k) :=
  ⟨a.witness.T k, W q k, a.witness.world k, a.witness.block k,
    a.witness.assignment k, a.ambientSelected k, a.witness.center k, a.witness.speed k,
    a.witness.width k, a.witness.polynomial k, a.ambientLists k, a.ambient_charts k⟩

/-- The restored true piece covers every absolutely continuous later law
through the SAME retained normalization's original coordinate map. -/
theorem ambientChart_covers (a : TrueNormalization p q r b h) (k : ℕ)
    (ρ : Measure (Fin (W q k) × PathMeasures.State)) (hρ : ρ ≪ worldMixture q k) :
    ∀ᵐ u ∂ρ.map (pullbackMap a.witness a.parent_exact k), u ∈ chartRegion (ambientChart a k) := by
  apply (ae_map_iff (measurable_pullbackMap a.witness a.parent_exact k).aemeasurable
    (measurableSet_chartRegion (ambientChart a k))).mpr
  filter_upwards [hρ.ae_le (a.ambientSelected_ae k)] with u hu
  exact ⟨u.1, rfl, hu⟩

def extensionPullback (chain : Chain p q) (a : TrueNormalization q z r r h) (k : ℕ) :
    Fin (W z k) × PathMeasures.State →
      Fin (W p (chain.sample (a.witness.sample k))) × PathMeasures.State :=
  chain.pullback (a.witness.sample k) ∘ pullbackMap a.witness a.parent_exact k

/-- A genuine original TRUE chart at the last actual prefix depth, with
fixed complexity and universal coverage of every later original-law residual. -/
theorem eventually_ambient_extension (chain : Chain p q)
    (a : TrueNormalization q z r r h) (hr : 0 ≤ r) (hrL : r ≤ L q)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      ∃ P : ChartW p (chain.chartBudget a.ambientExponent) (chain.depth + r) (chain.depth + r)
          (chain.cost + h + ε) ε true (chain.sample (a.witness.sample k)),
        ∀ ρ : Measure (Fin (W z k) × PathMeasures.State), ρ ≪ worldMixture z k →
          ∀ᵐ u ∂ρ.map (extensionPullback chain a k), u ∈ chartRegion P := by
  let η := chain.inputLoss (ε / 4)
  have hε4 : 0 < ε / 4 := by positivity
  have hη : 0 < η := chain.inputLoss_pos hε4
  have hηε : η ≤ ε / 4 := inputLoss_le chain hε4.le
  have hsmall := a.ambientLoss_tendsto.eventually (gt_mem_nhds hη)
  have hchain := a.witness.sample_strictMono.tendsto_atTop.eventually
    (chain.eventually_lift a.ambientExponent r (h + η) (ε / 4) hr hrL hε4)
  filter_upwards [hsmall, hchain] with k hsk hck
  have hNq : 1 ≤ N q (a.witness.sample k) :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (a.parent_exact.1.1 (a.witness.sample k))
  let Q := relaxChart (ambientChart a k) hNq le_rfl
    (show h + a.ambientLoss k ≤ h + η from add_le_add le_rfl hsk.le) hsk.le
  obtain ⟨P₀, hcover⟩ := hck Q
  have hNp : 1 ≤ N p (chain.sample (a.witness.sample k)) :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (chain.source_exact.1.1 _)
  let P := relaxChart P₀ hNp le_rfl
    (show chain.cost + (h + η) + ε / 4 ≤ chain.cost + h + ε by linarith)
    (show ε / 4 ≤ ε by linarith)
  refine ⟨P, ?_⟩
  intro ρ hρ
  have hac : ρ.map (pullbackMap a.witness a.parent_exact k) ≪
      worldMixture q (a.witness.sample k) :=
    (hρ.map (measurable_pullbackMap a.witness a.parent_exact k)).trans
      ((PathMeasures.RefinementChain.cons a.witness a.parent_exact (.nil z)).map_absolutelyContinuous k)
  have hseed : ∀ᵐ u ∂ρ.map (pullbackMap a.witness a.parent_exact k), u ∈ chartRegion Q :=
    ambientChart_covers a k ρ hρ
  have hout := hcover _ hac hseed
  rw [Measure.map_map (chain.toRefinementChain.measurable_pullback (a.witness.sample k))
    (measurable_pullbackMap a.witness a.parent_exact k)] at hout
  exact hout

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootTrueCharts
