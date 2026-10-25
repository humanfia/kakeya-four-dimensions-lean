import Submission.Obl.k4_critical_switching_state_preparation.MassAccounting
import Submission.Obl.k4_critical_switching_state_preparation.ShiftedPalette

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Original reference weights live only on the actual finite state table. -/
def finiteReferenceWeights {Q : Type*} [DecidableEq Q] (F : Finset Q) (R : ℝ) : Q → ℝ≥0∞ :=
  fun q => if q ∈ F then ENNReal.ofReal R else 0

theorem tsum_finiteReferenceWeights {Q : Type*} [DecidableEq Q]
    (F : Finset Q) (R : ℝ) :
    ∑' q, finiteReferenceWeights F R q = ENNReal.ofReal ((F.card : ℝ) * R) := by
  rw [tsum_eq_sum (s := F) (fun q hq => by simp [finiteReferenceWeights, hq])]
  calc
    _ = ∑ _q ∈ F, ENNReal.ofReal R :=
      Finset.sum_congr rfl (fun q hq => by simp [finiteReferenceWeights, hq])
    _ = (F.card : ℝ≥0∞) * ENNReal.ofReal R := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg F.card), ENNReal.ofReal_natCast]

/-- Both reference losses, summed before normalization, are smaller than the
original primitive mass whenever each consumes at most a quarter of it. -/
theorem finite_reference_budget {Ω α Q : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [DecidableEq Q] (μ : Measure Ω) (m : Measure α) (E₀ : Set Ω) (F : Finset Q)
    {R τ L p W : ℝ} (hR : 0 ≤ R) (hτ : 0 ≤ τ) (hL : 0 ≤ L) (hp : 0 ≤ p)
    (hW : 0 < W) (hμ : μ E₀ = ENNReal.ofReal W) (hm : m univ = ENNReal.ofReal p)
    (hstate : 4 * ((F.card : ℝ) * R * τ) ≤ W) (hline : 4 * (L * p) ≤ W) :
    ENNReal.ofReal τ * ∑' q, finiteReferenceWeights F R q + ENNReal.ofReal L * m univ < μ E₀ := by
  rw [tsum_finiteReferenceWeights, hm, ← ENNReal.ofReal_mul hτ, ← ENNReal.ofReal_mul hL,
    ← ENNReal.ofReal_add (by positivity) (by positivity), hμ]
  apply (ENNReal.ofReal_lt_ofReal_iff hW).mpr
  nlinarith

/-- The packaged pruning law retains the desired original transport floor;
no restricted parent prior is substituted into the floor. -/
theorem surviving_mass_of_finite_reference {Ω α Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [DecidableEq Q] (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : Measure α) (E₀ E : Set Ω) (F : Finset Q)
    {R τ L p W T : ℝ} (hR : 0 ≤ R) (hτ : 0 ≤ τ) (hL : 0 ≤ L) (hp : 0 ≤ p)
    (hW : 0 < W) (hμ : μ E₀ = ENNReal.ofReal W) (hm : m univ = ENNReal.ofReal p)
    (hstate : 4 * ((F.card : ℝ) * R * τ) ≤ W) (hline : 4 * (L * p) ≤ W)
    (htransport : 2 * T ≤ W)
    (hretain : μ E₀ ≤ μ E +
      (ENNReal.ofReal τ * ∑' q, finiteReferenceWeights F R q + ENNReal.ofReal L * m univ)) :
    0 < μ E ∧ ENNReal.ofReal T ≤ μ E := by
  have hcost : ENNReal.ofReal τ * ∑' q, finiteReferenceWeights F R q +
      ENNReal.ofReal L * m univ = ENNReal.ofReal ((F.card : ℝ) * R * τ + L * p) := by
    rw [tsum_finiteReferenceWeights, hm, ← ENNReal.ofReal_mul hτ, ← ENNReal.ofReal_mul hL,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hμ, hcost] at hretain
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ E, ENNReal.ofReal_ne_top⟩) hretain
  rw [ENNReal.toReal_ofReal hW.le,
    ENNReal.toReal_add (measure_ne_top μ E) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hs := surviving_mass_of_reference_losses hW hstate hline htransport hreal
  constructor
  · rw [← ENNReal.ofReal_toReal (measure_ne_top μ E)]
    exact ENNReal.ofReal_pos.mpr hs.1
  · simpa only [ENNReal.ofReal_toReal (measure_ne_top μ E)] using
      ENNReal.ofReal_le_ofReal hs.2.2

/-- Outside the actual finite table the original state law is zero, so
uniform raw numerators become caps against finitely supported references. -/
theorem finite_reference_palette_cap {Ω Q : Type*} [MeasurableSpace Ω] [DecidableEq Q]
    (μ : Measure Ω) (key : Ω → Q) (Z : Ω → ℤ) (P : ℤ → ℝ≥0∞) (F : Finset Q)
    (hsupp : ∀ᵐ p ∂μ, key p ∈ F) {C R : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ u j, μ {p | key p = u ∧ Z p = j} ≤ ENNReal.ofReal (C * R) * P j) :
    ∀ u j, μ {p | key p = u ∧ Z p = j} ≤
      ENNReal.ofReal C * finiteReferenceWeights F R u * P j := by
  intro u j
  by_cases hu : u ∈ F
  · simpa only [finiteReferenceWeights, if_pos hu, ENNReal.ofReal_mul hC] using hcap u j
  · have hz : μ {p | key p = u ∧ Z p = j} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hsupp)
      intro p hp
      change key p ∉ F
      rw [hp.1]
      exact hu
    rw [hz]
    exact bot_le

/-- The unchanged raw palette controls the exact centered velocity bins,
with finite original state references and a factor two for translation. -/
theorem shifted_finite_reference_palette_cap {Ω Q : Type*}
    [MeasurableSpace Ω] [DecidableEq Q] (μ : Measure Ω) (key : Ω → Q)
    (vel : Ω → ℝ) (π : Measure ℝ) (F : Finset Q)
    (hsupp : ∀ᵐ p ∂μ, key p ∈ F) {h C R : ℝ} (hh : 0 < h) (hC : 0 ≤ C)
    (hcap : ∀ u j, μ {p | key p = u ∧ ⌊vel p / h⌋ = j} ≤
      ENNReal.ofReal (C * R) * π {w | ⌊w / h⌋ = j}) (c : ℝ) :
    ∀ u j, μ {p | key p = u ∧ ⌊(vel p - c) / h⌋ = j} ≤
      ENNReal.ofReal (2 * C) * finiteReferenceWeights F R u *
        shiftedPalette π h c {w | ⌊w / h⌋ = j} := by
  have hraw := finite_reference_palette_cap μ key (fun p => ⌊vel p / h⌋)
    (fun j => π {w | ⌊w / h⌋ = j}) F hsupp hC hcap
  have hshift := shifted_palette_cap μ key vel π hh c
    (fun u => ENNReal.ofReal C * finiteReferenceWeights F R u) hraw
  intro u j
  have htwo : ENNReal.ofReal (2 * C) = 2 * ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  exact (hshift u j).trans_eq (by rw [htwo]; ring)

end

end Submission.Obl.k4_critical_switching_state_preparation
