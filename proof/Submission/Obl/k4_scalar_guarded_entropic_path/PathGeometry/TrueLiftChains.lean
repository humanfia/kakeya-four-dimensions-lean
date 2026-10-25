/-
Adapted from this LOT tree, obligation o093, session x0535, commit 5d4e5637,
Submission/Obl/k4_scalar_critical_path_terminal/TrueLiftChains.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.IntermediateLiftSupport
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueNormalization

/-! Backward TRUE lifting on a finite chain of the actual chosen
normalizations, keeping one common original pulled-back measure. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW chartData_mono)
open PathMeasures IntermediateTrueLift IntermediateLiftSupport

noncomputable section

/-- Changing budgets preserves every actual chart field and selected region. -/
def relaxChart {p : Code} {B B' k : ℕ} {r b h h' ε ε' : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) (hN : 1 ≤ N p k) (hB : B ≤ B')
    (hh : h ≤ h') (hε : ε ≤ ε') : ChartW p B' r b h' ε' flag k :=
  ⟨Q.T, Q.n, Q.γ, Q.j, Q.A, Q.C, Q.u, Q.v, Q.J, Q.P, Q.Λ,
    chartData_mono Q.hcd hN hB hh hε⟩

inductive Chain : Code → Code → Type where
  | nil (p : Code) (hp : Exact p) : Chain p p
  | cons {p q z : Code} {r h : ℝ} (a : TrueNormalization p q r r h)
      (hL : L q = L p - r) (hr : 0 ≤ r) (hh : 0 ≤ h)
      (relative : ∀ s, 0 ≤ s → s ≤ L q → f q s - f q 0 = f p (r + s) - f p r)
      (tail : Chain q z) : Chain p z

namespace Chain

variable {p z : Code}

theorem source_exact {p z : Code} (chain : Chain p z) : Exact p :=
  match chain with
  | .nil _ hp => hp
  | .cons a _ _ _ _ _ => a.parent_exact

theorem final_exact {p z : Code} (chain : Chain p z) : Exact z :=
  match chain with
  | .nil _ hp => hp
  | .cons _ _ _ _ _ tail => tail.final_exact

def toRefinementChain {p z : Code} (chain : Chain p z) : PathMeasures.RefinementChain p z :=
  match chain with
  | .nil p _ => .nil p
  | .cons a _ _ _ _ tail => .cons a.witness a.parent_exact tail.toRefinementChain

abbrev sample (chain : Chain p z) := chain.toRefinementChain.sample
abbrev pullback (chain : Chain p z) (k : ℕ) := chain.toRefinementChain.pullback k

def depth {p z : Code} (chain : Chain p z) : ℝ :=
  match chain with
  | .nil _ _ => 0
  | @cons _ _ _ r _ _ _ _ _ _ tail => r + tail.depth

def cost {p z : Code} (chain : Chain p z) : ℝ :=
  match chain with
  | .nil _ _ => 0
  | @cons _ _ _ _ h _ _ _ _ _ tail => h + tail.cost

def chartBudget {p z : Code} (chain : Chain p z) (B : ℕ) : ℕ :=
  match chain with
  | .nil _ _ => B
  | .cons a _ _ _ _ tail => 2 * tail.chartBudget B + 2 * a.witness.exponent + 9

def inputLoss {p z : Code} (chain : Chain p z) (ε : ℝ) : ℝ :=
  match chain with
  | .nil _ _ => ε
  | .cons _ _ _ _ _ tail => tail.inputLoss (ε / 4)

theorem remaining_length (chain : Chain p z) : L z = L p - chain.depth := by
  induction chain with
  | nil => simp [depth]
  | @cons p q z r h a hL hr hh hrelative tail ih =>
    rw [depth, ih, hL]
    ring

theorem depth_nonneg (chain : Chain p z) : 0 ≤ chain.depth := by
  induction chain with
  | nil => exact le_rfl
  | cons a hL hr hh hrelative tail ih => exact add_nonneg hr ih

theorem cost_nonneg (chain : Chain p z) : 0 ≤ chain.cost := by
  induction chain with
  | nil => exact le_rfl
  | cons a hL hr hh hrelative tail ih => exact add_nonneg hh ih

theorem inputLoss_pos (chain : Chain p z) {ε : ℝ} (hε : 0 < ε) :
    0 < chain.inputLoss ε := by
  induction chain generalizing ε with
  | nil => exact hε
  | cons a hL hr hh hrelative tail ih => exact ih (by positivity)

/-- The root chart covers the IDENTICAL common pulled-back law for every
absolutely continuous later residual; it is not chosen independently of it. -/
abbrev Lifted (chain : Chain p z) (B : ℕ) (s h₂ ε : ℝ) (k : ℕ)
    (Q : ChartW z B s s h₂ (chain.inputLoss ε) true k) : Prop :=
  ∃ P : ChartW p (chain.chartBudget B) (chain.depth + s) (chain.depth + s)
      (chain.cost + h₂ + ε) ε true (chain.sample k),
    ∀ ρ : Measure (Fin (W z k) × PathMeasures.State), ρ ≪ worldMixture z k →
      (∀ᵐ u ∂ρ, u ∈ chartRegion Q) →
      ∀ᵐ u ∂ρ.map (chain.pullback k), u ∈ chartRegion P

/-- Every fixed finite chain lifts all sufficiently accurate child TRUE
charts, with one fixed complexity and one common original-measure support. -/
theorem eventually_lift (chain : Chain p z) (B : ℕ) (s h₂ ε : ℝ)
    (hs : 0 ≤ s) (hsL : s ≤ L z) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ Q : ChartW z B s s h₂ (chain.inputLoss ε) true k,
      chain.Lifted B s h₂ ε k Q := by
  induction chain generalizing B s h₂ ε with
  | nil p hp =>
    simp only [Lifted, depth, cost, inputLoss, chartBudget]
    repeat rw [zero_add]
    apply Eventually.of_forall
    intro k Q
    have hN : 1 ≤ N p k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 k)
    refine ⟨relaxChart Q hN le_rfl (by linarith) le_rfl, ?_⟩
    intro ρ hρ hQ
    change ∀ᵐ u ∂ρ.map id, u ∈ chartRegion Q
    rw [Measure.map_id]
    exact hQ
  | @cons p q z r h a hL hr hh hrelative tail ih =>
    have hquarter : 0 < ε / 4 := by positivity
    have htail := ih B s h₂ (ε / 4) hs hsL hquarter
    have hsource : Exact q := tail.source_exact
    have hs' : 0 ≤ tail.depth + s := add_nonneg tail.depth_nonneg hs
    have hsL' : tail.depth + s ≤ L q := by linarith [tail.remaining_length]
    have hrel := hrelative _ hs' hsL'
    have hloss₁ := (a.witness.loss_tendsto.comp
      tail.toRefinementChain.sample_strictMono.tendsto_atTop).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hlossε := (a.witness.loss_tendsto.comp
      tail.toRefinementChain.sample_strictMono.tendsto_atTop).eventually
        (gt_mem_nhds hquarter)
    have hsigma := (a.floorLoss_tendsto.comp
      tail.toRefinementChain.sample_strictMono.tendsto_atTop).eventually
        (gt_mem_nhds hquarter)
    have hfour : ∀ᶠ k in atTop, 4 ≤ N p (a.witness.sample (tail.sample k)) ^ (ε / 2) :=
      ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).comp
        (a.parent_exact.1.2.1.comp
          (a.witness.sample_strictMono.comp
            tail.toRefinementChain.sample_strictMono).tendsto_atTop)).eventually_ge_atTop 4
    filter_upwards [htail, hloss₁, hlossε, hsigma, hfour] with k htk hl1 hlε hσε h4
    intro Q
    change a.witness.loss (tail.sample k) < 1 at hl1
    change a.witness.loss (tail.sample k) < ε / 4 at hlε
    change a.floorLoss (tail.sample k) < ε / 4 at hσε
    obtain ⟨Qt, hcover⟩ := htk Q
    have hN : 0 < N p (a.witness.sample (tail.sample k)) := by
      linarith [a.parent_exact.1.1 (a.witness.sample (tail.sample k))]
    have hN₁ : 1 ≤ N p (a.witness.sample (tail.sample k)) := by
      linarith [a.parent_exact.1.1 (a.witness.sample (tail.sample k))]
    have hfactor : 4 * N p (a.witness.sample (tail.sample k)) ^
        (a.witness.loss (tail.sample k) + ε / 4) ≤
      N p (a.witness.sample (tail.sample k)) ^ ε := by
      calc
        _ ≤ N p (a.witness.sample (tail.sample k)) ^ (ε / 2) *
            N p (a.witness.sample (tail.sample k)) ^ (ε / 2) :=
          mul_le_mul h4 (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith))
            (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
        _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
    let P₀ := liftChartW a.witness a.parent_exact hsource Qt a.floorLoss a.saturated hrel
      hr (show r ≤ r + (tail.depth + s) by linarith) hl1.le hquarter.le
      hσε.le hquarter.le
      (show a.witness.loss (tail.sample k) + ε / 4 + ε / 4 ≤ ε by linarith) hfactor
    let P := relaxChart P₀ hN₁ le_rfl
      (show h + a.witness.loss (tail.sample k) + (tail.cost + h₂ + ε / 4) ≤
        (h + tail.cost) + h₂ + ε by linarith) le_rfl
    simp only [Lifted, depth, cost, chartBudget]
    rw [add_assoc r tail.depth s]
    refine ⟨P, ?_⟩
    intro ρ hρ hQ
    have hac : ρ.map (tail.pullback k) ≪ worldMixture q (tail.sample k) :=
      (hρ.map (tail.toRefinementChain.measurable_pullback k)).trans
        (tail.toRefinementChain.map_absolutelyContinuous k)
    have hcovered := liftChartW_covers a.witness a.parent_exact hsource Qt
      a.floorLoss a.saturated hrel hr (show r ≤ r + (tail.depth + s) by linarith)
      hl1.le hquarter.le hσε.le hquarter.le
      (show a.witness.loss (tail.sample k) + ε / 4 + ε / 4 ≤ ε by linarith) hfactor
      (ρ.map (tail.pullback k)) hac (hcover ρ hρ hQ)
    rw [Measure.map_map (measurable_pullbackMap a.witness a.parent_exact (tail.sample k))
      (tail.toRefinementChain.measurable_pullback k)] at hcovered
    exact hcovered

end Chain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains
