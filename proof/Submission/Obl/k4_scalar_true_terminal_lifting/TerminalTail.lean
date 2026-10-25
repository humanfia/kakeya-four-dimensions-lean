import Submission.Obl.k4_scalar_true_terminal_lifting.TerminalComparison
import Submission.Obl.k4_dyadic_crop_typicality.Assembly
import Submission.Obl.k4_scalar_grid_density_extension.GridExtension
import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity

noncomputable section

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Set Filter
open scoped ENNReal
open k4_scalar_linear_critical_extremizers.Split
open k4_native_grid_profile_extension.Profiles

namespace RefinementData

variable {p q : Code} {r b h : ℝ} (s : RefinementData p q r b h)

theorem oldLowerMass_powerSmall (hp : Exact p) (τ : ℝ) (hτ : 0 < τ) :
    IsPowerSmall (fun k => N p (s.φ k)) (s.oldLowerMass τ) := by
  have hLp : 0 ≤ L p := (hp.1.2.2.2.2.2.1).le
  obtain ⟨c, hc, ht⟩ := hp.2.2.2.2.2.1 (L p) τ hLp le_rfl hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [s.mono.tendsto_atTop.eventually ht] with k hk
  refine (Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (measure_mono ?_)).trans hk
  intro z hz
  exact Or.inl hz

theorem newUpperMass_powerSmall (hq : Exact q) (τ : ℝ) (hτ : 0 < τ) :
    IsPowerSmall (N q) (s.newUpperMass τ) := by
  have hLq : 0 ≤ L q := (hq.1.2.2.2.2.2.1).le
  obtain ⟨c, hc, ht⟩ := hq.2.2.2.2.2.1 (L q) τ hLq le_rfl hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [ht] with k hk
  refine (Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (measure_mono ?_)).trans hk
  intro z hz
  exact Or.inr hz

theorem scaleLoss_subpower (hp : Exact p) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      N p (s.φ k) ^ s.loss k ≤ N p (s.φ k) ^ ε := by
  exact (k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
    (fun k => N p (s.φ k)) s.loss
    (fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 (s.φ k)))
    (fun k => (s.loss_pos k).le) s.loss_zero).2

theorem normalizer_inv_le (hp : Exact p) (k : ℕ) :
    (ENNReal.ofReal (s.Z k))⁻¹ ≤ ENNReal.ofReal (N p (s.φ k) ^ s.loss k) := by
  have hN : 0 < N p (s.φ k) := lt_of_lt_of_le (by norm_num) (hp.1.1 (s.φ k))
  rw [← ENNReal.ofReal_inv_of_pos (s.Z_pos k)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (N p (s.φ k) ^ (-s.loss k))⁻¹ :=
      (inv_le_inv₀ (s.Z_pos k) (Real.rpow_pos_of_pos hN _)).mpr (s.normalizer_lower_bound hp k)
    _ = _ := by rw [Real.rpow_neg hN.le, inv_inv]

theorem badMass_powerSmall (hp : Exact p) (hq : Exact q) (hL : L q = L p - r)
    (hb : b ≤ L p) (δ : ℝ) (hδ : 0 < δ) :
    IsPowerSmall (N q) (badMass p q s.φ s.γ s.A s.J δ) := by
  let N₀ := fun k => N p (s.φ k)
  let D₀ := fun k => N₀ k ^ s.loss k
  let τ := δ / 4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hN₀ (k : ℕ) : 1 ≤ N₀ k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 (s.φ k))
  have hNt : Tendsto N₀ atTop atTop := hp.1.2.1.comp s.mono.tendsto_atTop
  have hNeq : N₀ = N q := (funext s.resolution).symm
  have hD : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, D₀ k ≤ N₀ k ^ ε := s.scaleLoss_subpower hp
  have hold : IsPowerSmall N₀ (s.oldLowerMass τ) := s.oldLowerMass_powerSmall hp τ hτ
  have hnew : IsPowerSmall N₀ (s.newUpperMass τ) := by
    simpa only [hNeq] using s.newUpperMass_powerSmall hq τ hτ
  have hbase : IsPowerSmall N₀ (fun k => ENNReal.ofReal (4 * N₀ k ^ (-(δ / 2)))) :=
    k4_scalar_grid_density_extension.isPowerSmall_of_le_const_mul N₀ hNt 4 (δ / 2)
      (by positivity) _ (Eventually.of_forall fun _ => le_rfl)
  have hraw₀ := k4_dyadic_crop_typicality.powerSmall_mul_subpower hN₀ hD hbase
  have hexp : -δ + 2 * τ = -(δ / 2) := by dsimp [τ]; ring
  have hraw : IsPowerSmall N₀ (fun k => ENNReal.ofReal (N₀ k ^ (-δ + 2 * τ)) *
      (4 * ENNReal.ofReal (D₀ k))) := by
    apply hraw₀.mono
    apply Eventually.of_forall
    intro k
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), hexp]
    norm_num only [ENNReal.ofReal_ofNat]
    exact le_of_eq (by ring)
  have hinner := IsPowerSmall.add hNt
    (k4_dyadic_crop_typicality.powerSmall_mul_subpower hN₀ hD hold) hraw
  have htotal := IsPowerSmall.add hNt hnew
    (k4_dyadic_crop_typicality.powerSmall_mul_subpower hN₀ hD hinner)
  have hbad : IsPowerSmall N₀ (badMass p q s.φ s.γ s.A s.J δ) := by
    apply htotal.mono
    apply Eventually.of_forall
    intro k
    exact (s.badMass_finite_bound hp hq hL hb δ τ k).trans
      (add_le_add le_rfl (mul_le_mul' (s.normalizer_inv_le hp k) le_rfl))
  simpa only [hNeq] using hbad

end RefinementData

/-- The terminal floor holds for every actual exact refinement, after discarding
only a power-small weighted family of its normalized worlds. -/
theorem badWorldsSmall : BadWorldsSmall := by
  intro p q r b h hp hq _ _ _ hb _ hL φ loss B T γ j A C u v J P Λ θ hbody δ hδ
  let s := dataOfRefBody p q r b h φ loss B T γ j A C u v J P Λ θ hbody
  exact s.badMass_powerSmall hp hq hL hb δ hδ

end Submission.Obl.k4_scalar_true_terminal_lifting
