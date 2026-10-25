import Submission.Obl.k4_scalar_guarded_entropic_path.GuardTime
import Submission.Obl.k4_scalar_guarded_entropic_path.ReferenceLaws
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityCaps

/-! Original-unit bounds for every layer, including layers deeper than
the compact tangent range used by the selected node map. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

/-- The global original guard calibrates all block counts, with no
restriction to the final compact tangent range. -/
theorem layer_block_bounds {p : Code} {k M B : ℕ} {r t ε loss κ gain β Bs : ℝ}
    {F : Layer (p.1 k)} (hN : 1 ≤ p.N k)
    (hc : Split.ChartData p M r p.L t ε true k F.T F.n F.world F.block
      F.assignment F.witness F.u F.v F.width F.graph F.list)
    (hMB : M ≤ B) (hε : ε ≤ loss)
    (hguard : ∀ h : ℝ, h ≤ κ * r - gain → ¬Split.Chart p B r p.L h loss false k)
    (ht : t ≤ κ * r + β) (hβ : p.N k ^ β ≤ Bs) (hgain : p.N k ^ gain ≤ Bs) :
    p.N k ^ (κ * r) / Bs ≤ (2 : ℝ) ^ F.T ∧
      (2 : ℝ) ^ F.T ≤ Bs * p.N k ^ (κ * r) := by
  have hN0 : 0 < p.N k := lt_of_lt_of_le zero_lt_one hN
  have hBs : 0 < Bs := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hgain
  have hlow : p.N k ^ (κ * r - gain) < (2 : ℝ) ^ F.T := by
    by_contra! hbad
    exact hguard _ le_rfl
      ⟨F.T, F.n, F.world, F.block, F.assignment, F.witness, F.u, F.v,
        F.width, F.graph, F.list, ChartData.to_false hN hMB hε hbad hc⟩
  constructor
  · rw [div_le_iff₀ hBs]
    calc
      _ = p.N k ^ (κ * r - gain) * p.N k ^ gain := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ F.T * Bs :=
        mul_le_mul hlow.le hgain (Real.rpow_nonneg hN0.le _) (by positivity)
  · calc
      _ ≤ p.N k ^ t := hc.1
      _ ≤ p.N k ^ (κ * r + β) := Real.rpow_le_rpow_of_exponent_le hN ht
      _ = p.N k ^ β * p.N k ^ (κ * r) := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ Bs * p.N k ^ (κ * r) :=
        mul_le_mul_of_nonneg_right hβ (Real.rpow_nonneg hN0.le _)

/-- An original pure-density cap uses exactly the continuous base
observation in the frozen path conclusion. -/
theorem pureObservation_cap {p : Code} (hp : Split.Exact p) (k : ℕ)
    (g : Fin (p.1 k)) {r τ B : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L)
    {σ : Measure Incidence} (hσ : σ ≤ Split.mu p k g)
    (hnull : σ (PathGeometry.PathMeasures.pureException p k g r τ) = 0)
    (hB : p.N k ^ τ ≤ B) :
    σ.map (pureObservation (p.N k) r) ≤
      ENNReal.ofReal (B * p.N k ^ (-p.profile r)) • (volume.prod Measure.count) := by
  have hcap := PathGeometry.PathMeasures.pure_observation_cap hp k g hr hrL τ hσ hnull
  apply hcap.trans
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (exact_N_ge_two hp k)
  have hscalar : ENNReal.ofReal (p.N k ^ (-p.profile r + τ)) ≤
      ENNReal.ofReal (B * p.N k ^ (-p.profile r)) := by
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = p.N k ^ τ * p.N k ^ (-p.profile r) := by
        rw [← Real.rpow_add hN]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hN.le _)
  apply Measure.le_iff.mpr
  intro E _
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' hscalar le_rfl

end

end Submission.Obl.k4_scalar_guarded_entropic_path
