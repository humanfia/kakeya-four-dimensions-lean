-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/NativeBaseCaps.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelGood
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Set MeasureTheory Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Summing only the occupied native unit bins preserves any original
numerator, including the original velocity-palette weight. -/
theorem bounded_scalar_bin_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Set Ω) (f : Ω → ℝ) {a L : ℝ}
    (ha : 0 < a) (hL : 0 ≤ L) (W : ENNReal)
    (hbound : ∀ᵐ u ∂μ, |f u| ≤ L * a)
    (hcap : ∀ j : ℤ, μ {u | u ∈ C ∧ ⌊f u / a⌋ = j} ≤ W) :
    μ C ≤ ENNReal.ofReal (2 * L + 5) * W := by
  classical
  let J : Finset ℤ := Finset.Icc (-⌈L + 1⌉) ⌈L + 1⌉
  have hsub : ∀ᵐ u ∂μ, u ∈ C →
      u ∈ ⋃ j ∈ J, {u | u ∈ C ∧ ⌊f u / a⌋ = j} := by
    filter_upwards [hbound] with u hu hC
    have hm := floor_offset_mem ha (show |f u - 0| ≤ L * a by simpa using hu)
    have hj : ⌊f u / a⌋ ∈ J := by simpa [J] using hm
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hj, hC, rfl⟩⟩
  have hcard : (J.card : ENNReal) ≤ ENNReal.ofReal (2 * L + 5) := by
    simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (card_floor_offsets_le hL)
  calc
    μ C ≤ μ (⋃ j ∈ J, {u | u ∈ C ∧ ⌊f u / a⌋ = j}) := measure_mono_ae hsub
    _ ≤ ∑ j ∈ J, μ {u | u ∈ C ∧ ⌊f u / a⌋ = j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ J, W := Finset.sum_le_sum (fun j _ => hcap j)
    _ = (J.card : ENNReal) * W := by simp
    _ ≤ ENNReal.ofReal (2 * L + 5) * W := mul_le_mul hcard le_rfl bot_le bot_le

namespace Model

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- The full original base-cell marginal has a subpower density at every
prescribed mesh. This uses the bounded ORIGINAL native signal, not a
continuous domination hypothesis on the base law. -/
theorem eventually_base_cell_caps (hp : p.Valid) (R : ℝ) (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ r v : ℝ,
      R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ v → v ≤ R →
      (∀ q : Fin 3 → ℤ, p.μ k {u | p.z k r u = q} ≤
        ENNReal.ofReal ((2 * p.K k + 5) * p.K k * p.N k ^ (-3 * r))) ∧
      (∀ (q : Fin 3 → ℤ) (j : ℤ),
        p.μ k {u | p.z k r u = q ∧ ⌊p.b k u.1 3 / (p.N k ^ (-v))⌋ = j} ≤
          ENNReal.ofReal ((2 * p.K k + 5) * p.K k * p.N k ^ (-3 * r)) *
            p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = j}) := by
  filter_upwards [hp.caps R hR] with k hk
  intro r v hr hr' hv hv'
  obtain ⟨_, hscalar, hjoint⟩ := hk r 0 v hr hr' (by norm_num) (by linarith) hv hv'
  have hbound : ∀ᵐ u ∂p.μ k,
      |MvPolynomial.eval (p.x k u.1 u.2) (p.P k)| ≤ p.K k * 1 := by
    filter_upwards [Valid.ae_good p hp k] with u hu
    simpa only [mul_one] using (hu.fit u.2 hu.time).1
  have hK : 0 ≤ p.K k := (Valid.K_pos p hp k).le
  have hrpow : 0 ≤ p.N k ^ (-3 * r) := Real.rpow_nonneg (Valid.N_pos p hp k).le _
  have hscalar' (q : Fin 3 → ℤ) (a : ℤ) :
      p.μ k {u | p.z k r u = q ∧
        ⌊MvPolynomial.eval (p.x k u.1 u.2) (p.P k) / 1⌋ = a} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * r)) := by
    simpa only [Bool.true_eq, ↓reduceIte, neg_zero, Real.rpow_zero, mul_zero, sub_zero] using
      hscalar true q a
  have hfactor : ENNReal.ofReal (2 * p.K k + 5) *
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r)) =
      ENNReal.ofReal ((2 * p.K k + 5) * p.K k * p.N k ^ (-3 * r)) := by
    rw [← ENNReal.ofReal_mul (show 0 ≤ 2 * p.K k + 5 by positivity), mul_assoc]
  constructor
  · intro q
    have h := bounded_scalar_bin_cap (p.μ k) {u | p.z k r u = q}
      (fun u => MvPolynomial.eval (p.x k u.1 u.2) (p.P k))
      (by norm_num : (0 : ℝ) < 1) hK _ hbound (hscalar' q)
    simpa only [hfactor] using h
  · intro q j
    have hcap (a : ℤ) : p.μ k {u |
        u ∈ {u | p.z k r u = q ∧ ⌊p.b k u.1 3 / (p.N k ^ (-v))⌋ = j} ∧
        ⌊MvPolynomial.eval (p.x k u.1 u.2) (p.P k) / 1⌋ = a} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * r)) *
          p.π k {w : ℝ | ⌊w / (p.N k ^ (-v))⌋ = j} := by
      simpa only [Bool.true_eq, ↓reduceIte, neg_zero, Real.rpow_zero, mul_zero, sub_zero,
        mem_ofPred_eq, and_assoc, and_left_comm, and_comm] using hjoint true q a j
    have h := bounded_scalar_bin_cap (p.μ k)
      {u | p.z k r u = q ∧ ⌊p.b k u.1 3 / (p.N k ^ (-v))⌋ = j}
      (fun u => MvPolynomial.eval (p.x k u.1 u.2) (p.P k))
      (by norm_num : (0 : ℝ) < 1) hK _ hbound hcap
    rwa [← mul_assoc, hfactor] at h

end Model

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
