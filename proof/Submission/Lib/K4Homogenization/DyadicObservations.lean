/-
Adapted from: here:o018
-/
import Mathlib

/-! The exact nested dyadic bins used by the frozen native observation interface. -/

open MeasureTheory Set

namespace Submission.Lib.K4Homogenization

noncomputable def observationDepth (N r : ℝ) : ℤ := ⌊r * Real.log N / Real.log 2⌋

noncomputable def observationWidth (N r : ℝ) : ℝ := (2 : ℝ) ^ (-observationDepth N r)

noncomputable def observationRefinement (N r s : ℝ) : ℕ :=
  2 ^ (observationDepth N s - observationDepth N r).toNat

theorem observationDepth_mono {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) :
    observationDepth N r ≤ observationDepth N s := by
  apply Int.floor_mono
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrs (Real.log_nonneg hN))
    (by positivity : 0 ≤ Real.log 2)

theorem observationWidth_pos (N r : ℝ) : 0 < observationWidth N r := by
  exact zpow_pos (by norm_num) _

theorem observationRefinement_pos (N r s : ℝ) : 0 < observationRefinement N r s := by
  exact pow_pos (by norm_num) _

/-- The ratio between every coarser and finer width is an exact positive integer. -/
theorem observationWidth_refinement {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) :
    observationWidth N r = observationWidth N s * observationRefinement N r s := by
  have hdepth : 0 ≤ observationDepth N s - observationDepth N r :=
    sub_nonneg.mpr (observationDepth_mono hN hrs)
  unfold observationWidth observationRefinement
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg hdepth,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-- Coarse bins are an exact function of fine bins, including at endpoints and
for negative hidden coordinates. -/
theorem observation_bin_coarsen {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) (x : ℝ) :
    ⌊x / observationWidth N r⌋ =
      ⌊x / observationWidth N s⌋ / (observationRefinement N r s : ℤ) := by
  rw [observationWidth_refinement hN hrs, div_mul_eq_div_div, Int.floor_div_natCast]

noncomputable def coarsenObservation {X : Type*} (N r s : ℝ) (p : X × ℤ) : X × ℤ :=
  (p.1, p.2 / (observationRefinement N r s : ℤ))

theorem measurable_coarsenObservation {X : Type*} [MeasurableSpace X] (N r s : ℝ) :
    Measurable (coarsenObservation (X := X) N r s) := by
  exact measurable_fst.prodMk ((measurable_of_countable
    (fun j : ℤ => j / (observationRefinement N r s : ℤ))).comp measurable_snd)

theorem observation_factorization {Ω X : Type*} (b : Ω → X) (w : Ω → ℝ)
    {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) (p : Ω) :
    (b p, ⌊w p / observationWidth N r⌋) =
      coarsenObservation N r s (b p, ⌊w p / observationWidth N s⌋) := by
  simp only [coarsenObservation, observation_bin_coarsen hN hrs]

noncomputable def refinementBins (N r s : ℝ) (k : ℤ) : Finset ℤ :=
  Finset.Ico (k * observationRefinement N r s) ((k + 1) * observationRefinement N r s)

theorem mem_refinementBins_iff (N r s : ℝ) (k j : ℤ) :
    j ∈ refinementBins N r s k ↔ j / (observationRefinement N r s : ℤ) = k := by
  have hm : 0 < (observationRefinement N r s : ℤ) :=
    Int.natCast_pos.mpr (observationRefinement_pos N r s)
  simp only [refinementBins, Finset.mem_Ico]
  rw [← Int.le_ediv_iff_mul_le hm, ← Int.ediv_lt_iff_lt_mul hm]
  omega

theorem refinementBins_card (N r s : ℝ) (k : ℤ) :
    (refinementBins N r s k).card = observationRefinement N r s := by
  rw [refinementBins, Int.card_Ico]
  have hsub : (k + 1) * (observationRefinement N r s : ℤ) -
      k * (observationRefinement N r s : ℤ) = observationRefinement N r s := by ring
  rw [hsub, Int.toNat_natCast]

theorem observation_fine_bin_mem {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) (x : ℝ) :
    ⌊x / observationWidth N s⌋ ∈
      refinementBins N r s ⌊x / observationWidth N r⌋ := by
  rw [mem_refinementBins_iff, observation_bin_coarsen hN hrs]

/-- The number of fine hidden bins above any one coarse bin has the expected
power bound, with only the fixed rounding factor two. -/
theorem observationRefinement_le {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) :
    (observationRefinement N r s : ℝ) ≤ 2 * N ^ (s - r) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hdepth : 0 ≤ observationDepth N s - observationDepth N r :=
    sub_nonneg.mpr (observationDepth_mono hN hrs)
  have hratio : (observationRefinement N r s : ℝ) =
      (2 : ℝ) ^ ((observationDepth N s - observationDepth N r : ℤ) : ℝ) := by
    unfold observationRefinement
    rw [Real.rpow_intCast, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
      Int.toNat_of_nonneg hdepth]
  have hfloor : ((observationDepth N s - observationDepth N r : ℤ) : ℝ) ≤
      (s - r) * Real.log N / Real.log 2 + 1 := by
    have hr := Int.sub_one_lt_floor (r * Real.log N / Real.log 2)
    have hs := Int.floor_le (s * Real.log N / Real.log 2)
    dsimp only [observationDepth]
    rw [Int.cast_sub]
    rw [sub_mul, sub_div]
    linarith
  have hpow : (2 : ℝ) ^ ((s - r) * Real.log N / Real.log 2) = N ^ (s - r) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hNpos]
    congr 1
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  rw [hratio]
  calc
    _ ≤ (2 : ℝ) ^ ((s - r) * Real.log N / Real.log 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
    _ = _ := by rw [Real.rpow_add (by norm_num), Real.rpow_one, hpow, mul_comm]

noncomputable def angularRefinementBins {d : ℕ} (N r s : ℝ)
    (k : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun i => refinementBins N r s (k i))

theorem angularRefinementBins_card {d : ℕ} (N r s : ℝ) (k : Fin d → ℤ) :
    (angularRefinementBins N r s k).card = (observationRefinement N r s) ^ d := by
  simp only [angularRefinementBins, Fintype.card_piFinset, refinementBins_card,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem angular_fine_bin_mem {d : ℕ} {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s)
    (v : Fin d → ℝ) :
    (fun i => ⌊v i / observationWidth N s⌋) ∈
      angularRefinementBins N r s (fun i => ⌊v i / observationWidth N r⌋) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact observation_fine_bin_mem hN hrs (v i)

theorem angularRefinementBins_card_le {d : ℕ} {N r s : ℝ}
    (hN : 1 ≤ N) (hrs : r ≤ s) (k : Fin d → ℤ) :
    ((angularRefinementBins N r s k).card : ℝ) ≤
      (2 : ℝ) ^ d * N ^ ((d : ℝ) * (s - r)) := by
  rw [angularRefinementBins_card, Nat.cast_pow]
  calc
    _ ≤ (2 * N ^ (s - r)) ^ d := pow_le_pow_left₀ (by positivity)
      (observationRefinement_le hN hrs) _
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by linarith : (0 : ℝ) ≤ N) (s - r) d,
        mul_comm (s - r) (d : ℝ)]

end Submission.Lib.K4Homogenization
