/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ChainBudgets.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.MeasuredPaths
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathBudgets

/-! A finite actual scalar path retains subpower original mass, and can be
normalized once to a fixed probability without changing any full-layer prior.
All budgets and all subsequence maps remain termwise actual quantities. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem worldMixture_univ (p : Code) (k : ℕ) :
    worldMixture p k univ = ∑ g, ENNReal.ofReal (ω p k g) * mu p k g univ := by
  simp only [worldMixture, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g _
  rw [Measure.map_apply
    (show Measurable (fun z : State => (g, z)) from measurable_const.prodMk measurable_id)
      MeasurableSet.univ, preimage_univ]

theorem worldMixture_mass_lower {p : Code} (hp : Exact p) (k : ℕ) :
    ENNReal.ofReal ((K p k)⁻¹) ≤ worldMixture p k univ := by
  rw [worldMixture_univ]
  exact (hp.2.1 k).2.2.2.2

theorem worldMixture_mass_le_one {p : Code} (hp : Exact p) (k : ℕ) :
    worldMixture p k univ ≤ 1 := by
  rw [worldMixture_univ]
  have hmu (g : Fin (W p k)) : mu p k g univ ≤ 1 := by
    simpa only [Submission.Obl.k4_scalar_true_atlas_terminal_lists.mu,
      Submission.Obl.k4_scalar_true_atlas_terminal_lists.prior,
      Submission.Obl.k4_scalar_true_atlas_terminal_lists.event, mu, ν, E] using
        Submission.Obl.k4_scalar_true_atlas_terminal_lists.Exact.mu_univ_le (p := p) hp k g
  calc
    _ ≤ ∑ g, ENNReal.ofReal (ω p k g) * 1 :=
      Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (hmu g)
    _ = ENNReal.ofReal (∑ g, ω p k g) := by
      simp only [mul_one]
      exact (ENNReal.ofReal_sum_of_nonneg (fun g _ => (hp.2.1 k).2.1 g)).symm
    _ = 1 := by rw [(hp.2.1 k).2.2.1]; norm_num

namespace RefinementChain

def loss {p z : Code} (chain : RefinementChain p z) (k : ℕ) : ℝ :=
  match chain with
  | .nil _ => 0
  | .cons w _ tail => w.loss (tail.sample k) + tail.loss k

theorem source_exact {p z : Code} (chain : RefinementChain p z) (hz : Exact z) : Exact p := by
  cases chain with
  | nil => exact hz
  | cons w hp tail => exact hp

theorem loss_nonneg {p z : Code} (chain : RefinementChain p z) (k : ℕ) : 0 ≤ chain.loss k := by
  induction chain with
  | nil => exact le_rfl
  | cons w hp tail ih => exact add_nonneg (w.loss_pos _).le ih

theorem loss_tendsto_zero {p z : Code} (chain : RefinementChain p z) :
    Tendsto chain.loss atTop (nhds 0) := by
  induction chain with
  | nil => exact tendsto_const_nhds
  | cons w hp tail ih =>
    simpa only [loss, Function.comp_apply, add_zero] using
      (w.loss_tendsto.comp tail.sample_strictMono.tendsto_atTop).add ih

/-- The product of actual assignment budgets pays for the sum of the actual
layer losses in the resolution of the final exact problem. -/
theorem budget_floor {p z : Code} (chain : RefinementChain p z) (hz : Exact z) (k : ℕ) :
    N z k ^ (-chain.loss k) ≤ chain.budget k := by
  induction chain with
  | nil => simp [loss, budget]
  | @cons p q z r b h w hp tail ih =>
    have hN : 0 < N z k := by linarith [hz.1.1 k]
    have hw : N z k ^ (-w.loss (tail.sample k)) ≤ normalizer w (tail.sample k) := by
      rw [tail.resolution k, (w.charts (tail.sample k)).1]
      exact normalizer_lower w hp (tail.sample k)
    change N z k ^ (-(w.loss (tail.sample k) + tail.loss k)) ≤
      normalizer w (tail.sample k) * tail.budget k
    rw [neg_add, Real.rpow_add hN]
    exact mul_le_mul hw (ih hz) (Real.rpow_nonneg hN.le _) (normalizer_pos w _).le

theorem budget_le_one {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    chain.budget k ≤ 1 := by
  induction chain with
  | nil => exact le_rfl
  | cons w hp tail ih =>
    change normalizer w (tail.sample k) * tail.budget k ≤ 1
    exact (mul_le_mul (normalizer_le_one w hp _) ih (tail.budget_pos k).le zero_le_one).trans_eq
      (one_mul 1)

theorem originalLaw_mass_pos {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) : 0 < chain.originalLaw k univ := by
  rw [chain.originalLaw_univ]
  have hK : 0 < K z k := lt_of_lt_of_le zero_lt_one (hz.1.2.2.1.1 k)
  exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (chain.budget_pos k),
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr hK)) (worldMixture_mass_lower hz k)⟩

theorem originalLaw_mass_le_one {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) : chain.originalLaw k univ ≤ 1 :=
  (chain.originalLaw_le k univ).trans (worldMixture_mass_le_one (chain.source_exact hz) _)

/-- No limiting path measure is substituted: the actual pulled-back law has
inverse-subpower original mass on the fixed exact sequence. -/
theorem originalLaw_mass_subpower {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ENNReal.ofReal (N z k ^ (-ε)) ≤ chain.originalLaw k univ := by
  have hloss : ∀ᶠ k in atTop, chain.loss k < ε / 2 :=
    chain.loss_tendsto_zero.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hloss, hz.1.2.2.1.2 (ε / 2) (half_pos hε)] with k hk hK
  have hN : 0 < N z k := by linarith [hz.1.1 k]
  have hN₁ : 1 ≤ N z k := (by norm_num : (1 : ℝ) ≤ 2).trans (hz.1.1 k)
  have hK₀ : 0 < K z k := lt_of_lt_of_le zero_lt_one (hz.1.2.2.1.1 k)
  have hbudget : N z k ^ (-(ε / 2)) ≤ chain.budget k :=
    (Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)).trans (chain.budget_floor hz k)
  have hinv : N z k ^ (-(ε / 2)) ≤ (K z k)⁻¹ := by
    rw [Real.rpow_neg hN.le]
    exact inv_anti₀ hK₀ hK
  calc
    ENNReal.ofReal (N z k ^ (-ε)) =
        ENNReal.ofReal (N z k ^ (-(ε / 2))) * ENNReal.ofReal (N z k ^ (-(ε / 2))) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
      rw [show -(ε / 2) + -(ε / 2) = -ε by ring]
    _ ≤ ENNReal.ofReal (chain.budget k) * ENNReal.ofReal ((K z k)⁻¹) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) (ENNReal.ofReal_le_ofReal hinv)
    _ ≤ ENNReal.ofReal (chain.budget k) * worldMixture z k univ :=
      mul_le_mul' le_rfl (worldMixture_mass_lower hz k)
    _ = _ := (chain.originalLaw_univ k).symm

def probability {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    Measure (Fin (W p (chain.sample k)) × State) :=
  (chain.originalLaw k univ)⁻¹ • chain.originalLaw k

/-- Normalize the surviving original path once; all later operations can
restrict this fixed probability while retaining the same reference laws. -/
theorem probability_isProbability {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) : IsProbabilityMeasure (chain.probability k) := by
  rw [isProbabilityMeasure_iff, probability, Measure.smul_apply]
  exact ENNReal.inv_mul_cancel (chain.originalLaw_mass_pos hz k).ne'
    ((chain.originalLaw_mass_le_one hz k).trans_lt (by simp)).ne

end RefinementChain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
