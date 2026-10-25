-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.FixedSourcePowers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.MultiscaleCoreBudget
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.DenseJet.Bridge

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source.FixedSourcePowers

open Parent.ParentSource

noncomputable section

/-- Fixed exponents of the genuine multiscale core factory. They precede
all problem, path, grid, front and prediction-budget choices. -/
def coreE : ℕ := Classical.choose exists_broad_multiscale_core_source_with_budget.{0}

def coreRadius : ℕ := Classical.choose
  (Classical.choose_spec exists_broad_multiscale_core_source_with_budget.{0})

theorem core_bounds : 4 ≤ coreE ∧ 1 ≤ coreRadius := by
  exact ⟨(Classical.choose_spec (Classical.choose_spec
    exists_broad_multiscale_core_source_with_budget.{0})).1,
    (Classical.choose_spec (Classical.choose_spec
      exists_broad_multiscale_core_source_with_budget.{0})).2.1⟩

/-- The actual original-law core producer at these fixed exponents. -/
def coreFactory {T : Type} {d : Native.ProblemData} :=
  (Classical.choose_spec (Classical.choose_spec
    exists_broad_multiscale_core_source_with_budget.{0})).2.2 (T := T) (d := d)

/-- The accepted sheet Remez theorem supplies the fixed dense-jet
exponent needed by the source; no extra analytic premise is required. -/
theorem exists_source_jet_exponent :
    ∃ J : ℕ, 1 ≤ J ∧ Analytic.DenseJetBound 5186 J := by
  exact Submission.Obl.k4_physical_parent_potential_candidates.Analytic.denseJetAssertion 5186

def jet : ℕ := Classical.choose exists_source_jet_exponent

theorem jet_positive : 1 ≤ jet := (Classical.choose_spec exists_source_jet_exponent).1

theorem jet_bound : Analytic.DenseJetBound 5186 jet :=
  (Classical.choose_spec exists_source_jet_exponent).2

/-- A fixed reserve for the branch and jet powers. Dividing the freely
chosen pure tolerance and grid tolerance by this constant lets their
powers stay inside a subsequently returned positive prediction budget. -/
def power : ℕ := (4*coreRadius+100)*jet+100

def slack : ℝ := 2^20*(power:ℝ)^2

/-- The fixed reserve pays the actual ancestor row-list jet exponent. -/
theorem row_list_power_le : (3*coreRadius+65)*jet+coreRadius+8 ≤ power := by
  have h := Nat.mul_le_mul_left coreRadius jet_positive
  unfold power
  nlinarith

theorem slack_large : 2^20 ≤ slack := by
  unfold slack
  have h : (1:ℝ) ≤ (power:ℝ) := by
    unfold power
    exact_mod_cast (show 1 ≤ (4*coreRadius+100)*jet+100 by omega)
  nlinarith

theorem slack_positive : 0 < slack := lt_of_lt_of_le (by norm_num) slack_large


theorem slack_pays_power : 1024*(power:ℝ) ≤ slack := by
  have h : (1:ℝ) ≤ power := by
    unfold power
    exact_mod_cast (show 1 ≤ (4*coreRadius+100)*jet+100 by omega)
  unfold slack
  nlinarith

/-- The fixed core/jet powers fit within an arbitrary later positive
prediction budget. Each freely chosen tolerance and path/source factor
uses only budget/slack. This is the actual pregeometry envelope. -/
theorem native_envelope_power {N κ source tolerance budget : ℝ}
    (hN : 1 ≤ N) (hκone : 1 ≤ κ) (hbudget : 0 < budget)
    (hκ : κ ≤ N^(budget/slack)) (hsource : source ≤ N^(budget/slack))
    (hconstant : 2304 ≤ N^(budget/slack))
    (htolerance : tolerance ≤ 2*budget/slack) :
    (Native.nativePreGeometryEnvelope κ source N tolerance)^power ≤ N^(budget/256) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have henv : Native.nativePreGeometryEnvelope κ source N tolerance ≤ N^(4*budget/slack) :=
    Native.native_pre_geometry_envelope_power hN hκ hsource hconstant (by
      calc
        budget/slack+budget/slack+tolerance ≤ budget/slack+budget/slack+2*budget/slack :=
          add_le_add_right htolerance _
        _ = 4*budget/slack := by ring)
  have hexp : (4*budget/slack)*(power:ℝ) ≤ budget/256 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ slack_positive]
    have hh := mul_le_mul_of_nonneg_left slack_pays_power hbudget.le
    nlinarith
  calc
    _ ≤ (N^(4*budget/slack))^power :=
      pow_le_pow_left₀ (by
        unfold Native.nativePreGeometryEnvelope
        have hmax : 0 ≤ max κ source := (by linarith : (0:ℝ)≤κ).trans (le_max_left _ _)
        positivity) henv power
    _ = N^((4*budget/slack)*(power:ℝ)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
    _ ≤ N^(budget/256) := Real.rpow_le_rpow_of_exponent_le hN hexp


/-- Choose a positive path tolerance before the sample and all actual
coefficients. Eventually the literal native core envelope, at every
allowed path/source factor, pays all fixed core and jet powers. -/
theorem eventually_native_envelope_power
    (N : ℕ → ℝ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    {budget : ℝ} (hbudget : 0 < budget) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in Filter.atTop,
      ∀ κ source tolerance : ℝ, 1 ≤ κ → κ ≤ N k^σ → source ≤ N k^σ →
      tolerance ≤ 2*budget/slack →
      (Native.nativePreGeometryEnvelope κ source (N k) tolerance)^power ≤ (N k)^(budget/256) := by
  let σ := min 1 (budget/slack)
  have hσ : 0 < σ := lt_min one_pos (div_pos hbudget slack_positive)
  have hNlarge : ∀ᶠ k in Filter.atTop, 1 ≤ N k := hN.eventually (Filter.eventually_ge_atTop 1)
  have hconstant : ∀ᶠ k in Filter.atTop, 2304 ≤ (N k)^(budget/slack) :=
    ((tendsto_rpow_atTop (div_pos hbudget slack_positive)).comp hN).eventually
      (Filter.eventually_ge_atTop 2304)
  refine ⟨σ,hσ,min_le_left _ _,?_⟩
  filter_upwards [hNlarge,hconstant] with k hk hc
  intro κ source tolerance hκone hκ hsource htolerance
  have hp : (N k)^σ ≤ (N k)^(budget/slack) :=
    Real.rpow_le_rpow_of_exponent_le hk (min_le_right _ _)
  exact native_envelope_power hk hκone hbudget (hκ.trans hp) (hsource.trans hp) hc htolerance

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source.FixedSourcePowers
