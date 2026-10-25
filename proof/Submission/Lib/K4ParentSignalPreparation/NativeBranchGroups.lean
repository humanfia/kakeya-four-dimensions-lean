/-
Adapted from: here:o265
Original native and physical-unit state coherence proofs by x1027.
-/
import Submission.Lib.K4ParentSignalPreparation.BranchGroups
import Submission.Lib.K4ParentSignalPreparation.PolynomialBounds

namespace Submission.Lib.K4ParentSignalPreparation.BranchGroups

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ChartLifting
open Submission.Lib.K4ParentSignalPreparation.PolynomialBounds

noncomputable section

variable {Ω : Type*}

/-- Native observations record the base and the old normalized quadratic signal. -/
def nativeState (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ) (ε : ℝ) (x : Ω) :
    (Fin 3 → ℤ) × ℤ := (fun i => ⌊z x i / ε⌋, ⌊X x / ε⌋)

/-- Whole-block own fits make the canonical intercept nearly constant inside a native
state, including states which contain both hidden quadratic roots. -/
theorem native_intercept_oscillation (E : Set Ω) (z : Ω → Fin 3 → ℝ)
    (X cpt : Ω → ℝ) (P : MvPolynomial (Fin 3) ℝ) {ε fitError B : ℝ}
    (hε : 0 < ε) (hB : 1 ≤ B)
    (hbox : ∀ x ∈ E, ∀ i, |z x i| ≤ B)
    (hfit : ∀ x ∈ E, |X x - eval (z x) P - cpt x| ≤ fitError)
    {x y : Ω} (hx : x ∈ E) (hy : y ∈ E)
    (hstate : nativeState z X ε x = nativeState z X ε y) :
    |cpt x - cpt y| ≤ 2 * fitError +
      (1 + 3 * (P.totalDegree * coeffL1 P * B ^ P.totalDegree)) * ε := by
  have hX : |X x - X y| ≤ ε := by
    have h := Int.abs_sub_lt_one_of_floor_eq_floor (congrArg Prod.snd hstate)
    rw [← sub_div, abs_div, abs_of_pos hε] at h
    exact ((div_lt_one hε).mp h).le
  have hz (i : Fin 3) : |z x i - z y i| ≤ ε := by
    have hcode := congrFun (congrArg Prod.fst hstate) i
    have h := Int.abs_sub_lt_one_of_floor_eq_floor hcode
    rw [← sub_div, abs_div, abs_of_pos hε] at h
    exact ((div_lt_one hε).mp h).le
  have hsum : ∑ i : Fin 3, |z x i - z y i| ≤ 3 * ε := by
    calc
      _ ≤ ∑ _i : Fin 3, ε := Finset.sum_le_sum (fun i _ => hz i)
      _ = _ := by simp
  have hcoeff := coeffL1_nonneg P
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hpoly := abs_eval_sub_eval_le_box P hB (z x) (z y) (hbox x hx) (hbox y hy)
  have hpoly' : |eval (z x) P - eval (z y) P| ≤
      (P.totalDegree * coeffL1 P * B ^ P.totalDegree) * (3 * ε) := by
    exact hpoly.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hfx := abs_le.mp (hfit x hx)
  have hfy := abs_le.mp (hfit y hy)
  have hXX := abs_le.mp hX
  have hPP := abs_le.mp hpoly'
  rw [abs_le]
  constructor <;> nlinarith

/-- The numerical fit/mesh budget supplies exactly the five-bin saturation hypothesis
of `exists_retained_branch`; no branch-purity assumption on native states is used. -/
theorem native_intercept_bins_close (E : Set Ω) (z : Ω → Fin 3 → ℝ)
    (X cpt : Ω → ℝ) (P : MvPolynomial (Fin 3) ℝ) {ε fitError B width : ℝ}
    (hε : 0 < ε) (hB : 1 ≤ B) (hwidth : 0 < width)
    (hbox : ∀ x ∈ E, ∀ i, |z x i| ≤ B)
    (hfit : ∀ x ∈ E, |X x - eval (z x) P - cpt x| ≤ fitError)
    (hbudget : 2 * fitError +
      (1 + 3 * (P.totalDegree * coeffL1 P * B ^ P.totalDegree)) * ε ≤ 2 * width)
    {x y : Ω} (hx : x ∈ E) (hy : y ∈ E)
    (hstate : nativeState z X ε x = nativeState z X ε y) :
    ⌊cpt x / width⌋ ∈ Icc (⌊cpt y / width⌋ - 2) (⌊cpt y / width⌋ + 2) :=
  floor_bin_close hwidth ((native_intercept_oscillation E z X cpt P hε hB hbox hfit
    hx hy hstate).trans hbudget)

/-- The physical-unit version uses the state height `X/a`, while the potential and
intercepts remain in the original parent signal's units. -/
theorem physical_intercept_bins_close (E : Set Ω) (z : Ω → Fin 3 → ℝ)
    (X cpt : Ω → ℝ) (P : MvPolynomial (Fin 3) ℝ) {a ε fitError B width : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hB : 1 ≤ B) (hwidth : 0 < width)
    (hbox : ∀ x ∈ E, ∀ i, |z x i| ≤ B)
    (hfit : ∀ x ∈ E, |X x - eval (z x) P - cpt x| ≤ fitError)
    (hbudget : 2 * fitError +
      (a + 3 * (P.totalDegree * coeffL1 P * B ^ P.totalDegree)) * ε ≤ 2 * width)
    {x y : Ω} (hx : x ∈ E) (hy : y ∈ E)
    (hstate : nativeState z (fun t => X t / a) ε x =
      nativeState z (fun t => X t / a) ε y) :
    ⌊cpt x / width⌋ ∈ Icc (⌊cpt y / width⌋ - 2) (⌊cpt y / width⌋ + 2) := by
  have hX : |X x - X y| ≤ a * ε := by
    have h := Int.abs_sub_lt_one_of_floor_eq_floor (congrArg Prod.snd hstate)
    have hh : |X x / a - X y / a| < ε := by
      rw [← sub_div, abs_div, abs_of_pos hε] at h
      exact (div_lt_one hε).mp h
    rw [← sub_div, abs_div, abs_of_pos ha] at hh
    have h' := ((div_lt_iff₀ ha).mp hh).le
    nlinarith
  have hz (i : Fin 3) : |z x i - z y i| ≤ ε := by
    have hcode := congrFun (congrArg Prod.fst hstate) i
    have h := Int.abs_sub_lt_one_of_floor_eq_floor hcode
    rw [← sub_div, abs_div, abs_of_pos hε] at h
    exact ((div_lt_one hε).mp h).le
  have hsum : ∑ i : Fin 3, |z x i - z y i| ≤ 3 * ε := by
    calc
      _ ≤ ∑ _i : Fin 3, ε := Finset.sum_le_sum (fun i _ => hz i)
      _ = _ := by simp
  have hcoeff := coeffL1_nonneg P
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hpoly := abs_eval_sub_eval_le_box P hB (z x) (z y) (hbox x hx) (hbox y hy)
  have hpoly' : |eval (z x) P - eval (z y) P| ≤
      (P.totalDegree * coeffL1 P * B ^ P.totalDegree) * (3 * ε) :=
    hpoly.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  apply floor_bin_close hwidth
  have hfx := abs_le.mp (hfit x hx)
  have hfy := abs_le.mp (hfit y hy)
  have hXX := abs_le.mp hX
  have hPP := abs_le.mp hpoly'
  rw [abs_le]
  constructor <;> nlinarith


/-- The small physical mesh pays the old clock ratio exactly, leaving a budget involving
only the fit accuracy and the potential's coefficient envelope. -/
theorem physical_clock_mesh_budget {a h ε ζ H Lip fitError w : ℝ}
    (ha : 0 ≤ a) (hh : 0 < h) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hfit : fitError ≤ a * ζ) (hLip : Lip ≤ H * h)
    (hεfit : ε ≤ ζ) (hεclock : ε ≤ (a / h) * ζ)
    (hsmall : (3 + 3 * H) * ζ ≤ 2 * w) :
    2 * fitError + (a + 3 * Lip) * ε ≤ 2 * (a * w) := by
  have hclock : h * ε ≤ a * ζ := by
    have hclockBound := mul_le_mul_of_nonneg_left hεclock hh.le
    have heq : h * (a / h * ζ) = a * ζ := by field_simp
    simpa only [heq] using hclockBound
  have hbase := mul_le_mul_of_nonneg_left hεfit ha
  have hvariation : Lip * ε ≤ H * (a * ζ) := by
    calc Lip * ε ≤ (H * h) * ε := mul_le_mul_of_nonneg_right hLip hε
         _ = H * (h * ε) := by ring
         _ ≤ H * (a * ζ) := mul_le_mul_of_nonneg_left hclock hH
  have htarget := mul_le_mul_of_nonneg_left hsmall ha
  nlinarith

/-- A potential with physical coefficient size `H*h` satisfies the corrected source's
state-bin coherence at a normalized intercept width `w`. -/
theorem physical_intercept_bins_close_of_clock_mesh (E : Set Ω) (z : Ω → Fin 3 → ℝ)
    (X cpt : Ω → ℝ) (P : MvPolynomial (Fin 3) ℝ) {a h ε ζ H B w : ℝ}
    (ha : 0 < a) (hh : 0 < h) (hε : 0 < ε) (hB : 1 ≤ B) (hw : 0 < w)
    (hH : 0 ≤ H) (hbox : ∀ x ∈ E, ∀ i, |z x i| ≤ B)
    (hfit : ∀ x ∈ E, |X x - eval (z x) P - cpt x| ≤ a * ζ)
    (hcoeff : P.totalDegree * coeffL1 P * B ^ P.totalDegree ≤ H * h)
    (hεfit : ε ≤ ζ) (hεclock : ε ≤ (a / h) * ζ)
    (hsmall : (3 + 3 * H) * ζ ≤ 2 * w)
    {x y : Ω} (hx : x ∈ E) (hy : y ∈ E)
    (hstate : nativeState z (fun t => X t / a) ε x =
      nativeState z (fun t => X t / a) ε y) :
    ⌊cpt x / (a * w)⌋ ∈ Icc (⌊cpt y / (a * w)⌋ - 2) (⌊cpt y / (a * w)⌋ + 2) := by
  exact physical_intercept_bins_close E z X cpt P ha hε hB (mul_pos ha hw) hbox hfit
    (physical_clock_mesh_budget ha.le hh hε.le hH le_rfl hcoeff hεfit hεclock hsmall)
    hx hy hstate


end

end Submission.Lib.K4ParentSignalPreparation.BranchGroups
