import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Types
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.Bridge
import Submission.Obl.k4_scalar_grid_density_extension.GridExtension

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_native_grid_profile_extension.Profiles

abbrev WorldState (p : Problem) (k : ℕ) := Fin (p.1 k) × Incidence

/-- A state includes its original world, without changing any within-world law. -/
def worldLaw (p : Problem) (k : ℕ) : Measure (WorldState p k) :=
  ∑ a, ENNReal.ofReal (weight p k a) •
    (law p k a).map (fun z => (a, z))

theorem worldLaw_apply (p : Problem) (k : ℕ) {S : Set (WorldState p k)}
    (hS : MeasurableSet S) :
    worldLaw p k S = ∑ a, ENNReal.ofReal (weight p k a) *
      law p k a {z | (a, z) ∈ S} := by
  simp only [worldLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Measure.map_apply (f := fun z : Incidence => (a, z)) (by fun_prop) hS]
  rfl

theorem worldLaw_univ (p : Problem) (k : ℕ) :
    worldLaw p k univ = ∑ a, ENNReal.ofReal (weight p k a) * law p k a univ := by
  rw [worldLaw_apply p k MeasurableSet.univ]
  rfl

theorem law_le_one {p : Problem} (hp : RawScalar p) (k : ℕ) (a : Fin (p.1 k)) :
    law p k a univ ≤ 1 := by
  have h := (hp.2 k).2.2.2.1 a
  let := h.1
  exact Submission.Obl.k4_scalar_terminal_chart_packet_extraction.incLaw_univ_le
    h.2.2.2.2.1

theorem worldLaw_le_one {p : Problem} (hp : RawScalar p) (k : ℕ) :
    worldLaw p k univ ≤ 1 := by
  rw [worldLaw_univ]
  calc
    _ ≤ ∑ a, ENNReal.ofReal (weight p k a) * 1 := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul' le_rfl (law_le_one hp k a)
    _ = 1 := by
      simp only [mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (hp.2 k).2.1 a),
        (hp.2 k).2.2.1, ENNReal.ofReal_one]

theorem worldLaw_mass_lower {p : Problem} (hp : RawScalar p) (k : ℕ) :
    ENNReal.ofReal ((loss p k)⁻¹) ≤ worldLaw p k univ := by
  rw [worldLaw_univ]
  exact (hp.2 k).2.2.2.2

theorem worldLaw_inverse_subpower {p : Problem} (hp : RawScalar p) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ENNReal.ofReal (resolution p k ^ (-ε)) ≤ worldLaw p k univ := by
  intro ε hε
  filter_upwards [hp.1.2.2.1.2 ε hε] with k hk
  apply le_trans _ (worldLaw_mass_lower hp k)
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_neg (by linarith [hp.1.1 k] : 0 ≤ resolution p k)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith [hp.1.1 k]) _)
    (by linarith [hp.1.2.2.1.1 k])).2 hk

abbrev HasDensities (p : Problem) : Prop :=
  ∀ k a r, 0 ≤ r → r ≤ length p → Measurable (density p k a r) ∧
    (law p k a).map (observe (resolution p k) r) =
      reference.withDensity (density p k a r)

abbrev sampledDensity (p : Problem) (r : ℝ) (k : ℕ) (z : WorldState p k) : ENNReal :=
  density p k z.1 r (observe (resolution p k) r z.2)

theorem measurable_sampledDensity {p : Problem} (hd : HasDensities p)
    (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ length p) :
    Measurable (sampledDensity p r k) := by
  apply measurable_from_prod_countable_right
  intro a
  exact (hd k a r hr hrL).1.comp
    (Submission.Obl.k4_scalar_grid_density_extension.measurable_obs_label _ _)

/-- A common exceptional-mass factor survives summing with the original weights. -/
theorem weighted_exception_bound {ι : Type*} [Fintype ι]
    (w mass bad : ι → ENNReal) (C : ENNReal)
    (hbad : ∀ i, bad i ≤ C * mass i) (hmass : ∑ i, w i * mass i ≤ 1) :
    ∑ i, w i * bad i ≤ C := by
  calc
    _ ≤ ∑ i, w i * (C * mass i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul' le_rfl (hbad i)
    _ = C * ∑ i, w i * mass i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ C * 1 := mul_le_mul' le_rfl hmass
    _ = C := mul_one _

theorem world_coarse_low_mass {p : Problem} (hp : RawScalar p) (hd : HasDensities p)
    (k : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ length p)
    (ε : ENNReal) :
    worldLaw p k {z | sampledDensity p r k z < ε * sampledDensity p s k z} ≤ ε * 2 := by
  have hm : MeasurableSet {z : WorldState p k |
      sampledDensity p r k z < ε * sampledDensity p s k z} :=
    measurableSet_lt (measurable_sampledDensity hd k hr (hrs.trans hs))
      (measurable_const.mul (measurable_sampledDensity hd k (hr.trans hrs) hs))
  rw [worldLaw_apply p k hm]
  apply weighted_exception_bound _ _ _ (ε * 2) _ (by
    rw [← worldLaw_univ]
    exact worldLaw_le_one hp k)
  intro a
  exact Submission.Obl.k4_scalar_grid_density_extension.pure_coarse_low_mass
    (law p k a) (by linarith [hp.1.1 k]) hrs _ _
    (hd k a r hr (hrs.trans hs)).1 (hd k a s (hr.trans hrs) hs).1
    (hd k a r hr (hrs.trans hs)).2 (hd k a s (hr.trans hrs) hs).2 ε

theorem world_fine_low_mass {p : Problem} (hp : RawScalar p) (hd : HasDensities p)
    (k : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ length p)
    (ε : ENNReal) :
    worldLaw p k {z | sampledDensity p s k z < ε * sampledDensity p r k z} ≤
      ε * ENNReal.ofReal (resolution p k ^ (s - r) + 2) := by
  have hm : MeasurableSet {z : WorldState p k |
      sampledDensity p s k z < ε * sampledDensity p r k z} :=
    measurableSet_lt (measurable_sampledDensity hd k (hr.trans hrs) hs)
      (measurable_const.mul (measurable_sampledDensity hd k hr (hrs.trans hs)))
  rw [worldLaw_apply p k hm]
  apply weighted_exception_bound _ _ _ _ _ (by
    rw [← worldLaw_univ]
    exact worldLaw_le_one hp k)
  intro a
  exact Submission.Obl.k4_scalar_grid_density_extension.pure_fine_low_mass
    (law p k a) (by linarith [hp.1.1 k]) hrs _ _
    (hd k a r hr (hrs.trans hs)).1 (hd k a s (hr.trans hrs) hs).1
    (hd k a r hr (hrs.trans hs)).2 (hd k a s (hr.trans hrs) hs).2 ε

theorem world_approx_mono {p : Problem} (hp : RawScalar p) (hd : HasDensities p)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ length p)
    {ε : ℝ} (hε : 0 < ε) :
    IsPowerSmall (resolution p) (fun k => worldLaw p k
      {z | sampledDensity p r k z <
        ENNReal.ofReal (resolution p k ^ (-ε)) * sampledDensity p s k z}) := by
  apply Submission.Obl.k4_scalar_grid_density_extension.isPowerSmall_of_le_const_mul
    (resolution p) hp.1.2.1 2 ε hε
  apply Eventually.of_forall
  intro k
  calc
    _ ≤ ENNReal.ofReal (resolution p k ^ (-ε)) * 2 :=
      world_coarse_low_mass hp hd k hr hrs hs _
    _ = ENNReal.ofReal (2 * resolution p k ^ (-ε)) := by
      rw [mul_comm, ENNReal.ofReal_mul (by norm_num)]
      norm_num

theorem world_approx_tail {p : Problem} (hp : RawScalar p) (hd : HasDensities p)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ length p)
    {ε : ℝ} (hε : 0 < ε) :
    IsPowerSmall (resolution p) (fun k => worldLaw p k
      {z | sampledDensity p s k z <
        ENNReal.ofReal (resolution p k ^ (-(s - r + ε))) * sampledDensity p r k z}) := by
  apply Submission.Obl.k4_scalar_grid_density_extension.isPowerSmall_of_le_const_mul
    (resolution p) hp.1.2.1 3 ε hε
  apply Eventually.of_forall
  intro k
  have hN₁ : 1 ≤ resolution p k := by linarith [hp.1.1 k]
  have hN₀ : 0 < resolution p k := by linarith
  calc
    _ ≤ ENNReal.ofReal (resolution p k ^ (-(s - r + ε))) *
        ENNReal.ofReal (resolution p k ^ (s - r) + 2) :=
      world_fine_low_mass hp hd k hr hrs hs _
    _ = ENNReal.ofReal (resolution p k ^ (-(s - r + ε)) *
        (resolution p k ^ (s - r) + 2)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hN₀.le _)]
    _ ≤ ENNReal.ofReal (3 * resolution p k ^ (-ε)) := by
      apply ENNReal.ofReal_le_ofReal
      have hlarge : 1 ≤ resolution p k ^ (s - r) :=
        Real.one_le_rpow hN₁ (sub_nonneg.mpr hrs)
      calc
        _ ≤ resolution p k ^ (-(s - r + ε)) * (3 * resolution p k ^ (s - r)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hN₀.le _)
        _ = 3 * resolution p k ^ (-ε) := by
          rw [mul_left_comm, ← Real.rpow_add hN₀]
          congr 2
          ring

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
