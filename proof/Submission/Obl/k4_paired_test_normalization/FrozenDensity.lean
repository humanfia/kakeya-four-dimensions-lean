-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/FrozenDensity.lean. Existing attribution comments are retained below.

import Mathlib
import Submission.Obl.k4_paired_test_normalization.Interface
import Submission.Obl.k4_paired_test_normalization.BandBounds

/-! The band bound for the frozen terminal observation, and the elementary scale facts
(`δ` bounds, cap-class density comparison) used with it. -/

namespace Submission.Obl.k4_paired_test_normalization

open MeasureTheory Set

lemma measurable_x_inc : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => x p.1 p.2) := by
  unfold x
  fun_prop

lemma measurable_obs (Bγ a : ℝ) : Measurable (obs Bγ a) := by
  unfold obs
  have hx := measurable_x_inc
  have h0 : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (x p.1 p.2) 3) :=
    (measurable_pi_apply 3).comp hx
  refine Measurable.prodMk ?_ ?_
  · apply (PiLp.continuous_toLp 2 _).measurable.comp
    refine measurable_pi_iff.mpr (fun i => ?_)
    fin_cases i
    · exact measurable_snd
    · show Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => x p.1 p.2 1)
      exact (measurable_pi_apply 1).comp hx
    · show Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => x p.1 p.2 2)
      exact (measurable_pi_apply 2).comp hx
  · exact Int.measurable_floor.comp ((h0.const_mul Bγ).div_const a)

/-- The base point `(t, x₁, x₂)` of an incidence (the first component of `obs`). -/
noncomputable def incBase (p : (ℕ × (Fin 6 → ℝ)) × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (obs 1 1 p).1

lemma obs_fst (Bγ a : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) : (obs Bγ a p).1 = incBase p := rfl

lemma obs_eq (Bγ a : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    obs Bγ a p = (incBase p, ⌊Bγ * x p.1 p.2 3 / a⌋) := rfl

lemma measurable_incBase : Measurable incBase :=
  measurable_fst.comp (measurable_obs 1 1)

lemma δ_pos (N r : ℝ) : 0 < δ N r := by
  unfold δ
  positivity

/-- `N^(-r) ≤ δ N r ≤ 2 N^(-r)` for `N > 1`. -/
lemma δ_bounds {N : ℝ} (hN : 1 < N) (r : ℝ) :
    N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) := by
  have hN0 : 0 < N := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set m : ℤ := ⌊r * Real.log N / Real.log 2⌋ with hm
  have h1 : (m : ℝ) ≤ r * Real.log N / Real.log 2 := Int.floor_le _
  have h2 : r * Real.log N / Real.log 2 < m + 1 := Int.lt_floor_add_one _
  have hδ : δ N r = (2 : ℝ) ^ (-(m : ℝ)) := by
    unfold δ
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  have hNr : N ^ (-r) = (2 : ℝ) ^ (-(r * Real.log N / Real.log 2)) := by
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp
  rw [hδ, hNr]
  constructor
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  · calc (2 : ℝ) ^ (-(m : ℝ)) ≤ (2 : ℝ) ^ (1 - r * Real.log N / Real.log 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          linarith
      _ = 2 * (2 : ℝ) ^ (-(r * Real.log N / Real.log 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]

/-- **Band bound for the frozen terminal observation.** If the observation of the
selected law `(ν ⊗ dt)|_E` at bin width `a` has density `g`, then the capped part of the
band `|Bγ x₃ - G(base)| ≤ W` over a base region `Reg` has mass at most `c vol(Reg) (2W/a + 2)`. -/
theorem obs_band_le (ν : Measure (ℕ × (Fin 6 → ℝ))) (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Bγ : ℝ) {a : ℝ} (ha : 0 < a) (g : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hg : Measurable g)
    (hmap : ((ν.prod volume).restrict E).map (obs Bγ a) = (volume.prod Measure.count).withDensity g)
    (c : ENNReal) (Reg : Set (EuclideanSpace ℝ (Fin 3))) (hReg : MeasurableSet Reg)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ) (hG : Measurable G) {W : ℝ} (hW : 0 ≤ W) :
    ((ν.prod volume).restrict E) {p | g (obs Bγ a p) ≤ c ∧ incBase p ∈ Reg ∧
        |Bγ * x p.1 p.2 3 - G (incBase p)| ≤ W} ≤
      c * volume Reg * ENNReal.ofReal (2 * W / a + 2) := by
  have h := band_mass_le ((ν.prod volume).restrict E) incBase (fun p => Bγ * x p.1 p.2 3) ha
    (by simpa only [← obs_eq] using measurable_obs Bγ a) g hg
    (by simpa only [← obs_eq] using hmap) c Reg hReg G hG hW
  simpa only [← obs_eq] using h

/-- The cap-class comparison of typical densities. -/
lemma rpow_neg_f_le {N : ℝ} (hN : 1 ≤ N) {f : ℝ → ℝ} {d L r : ℝ}
    (hcap : f L - f r ≤ d * (L - r)) :
    N ^ (-f r) ≤ N ^ (-f L) * N ^ (d * (L - r)) := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end Submission.Obl.k4_paired_test_normalization
