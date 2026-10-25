/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameBoxes.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameNested

/-!
# The centered box of a residual label

The incidences of a residual label lie in its centered horizontal box: the box
of size `q'` (horizontal) and `q' ^ 2` (transverse, after removing the contact
shear at the box center), centered at the block midpoint and the label's row
values there. Its box coordinates are bounded by `K_box = 50 K⁴ K₂²`.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

namespace Frame

/-- The residual base point (time, major and transverse coordinates). -/
def resBase (f : Frame D k s₀ U') (p : α × ℝ) : Fin 3 → ℝ :=
  ![p.2, point (f.coeff p.1) p.2 1, point (f.coeff p.1) p.2 2]

/-- The residual block length at a level. -/
def resq (f : Frame D k s₀ U') (h : ℕ) : ℝ := (2 : ℝ) ^ (-(f.resT h : ℤ))

/-- The residual block midpoint of a label. -/
def resMid (f : Frame D k s₀ U') (h : ℕ) (i : Fin (f.retained h).card) : ℝ :=
  (((f.level h).j i : ℕ) + (1 : ℝ) / 2) * f.resq h

/-- The box center of a label. -/
def boxZ (f : Frame D k s₀ U') (h : ℕ) (i : Fin (f.retained h).card) : ℝ :=
  (f.level h).c i 0 + f.resMid h i * (f.level h).c i 1

def boxY (f : Frame D k s₀ U') (h : ℕ) (i : Fin (f.retained h).card) : ℝ :=
  (f.level h).c i 2 + f.resMid h i * (f.level h).c i 3 + (f.level h).c i 4 * f.boxZ h i

theorem resq_pos (f : Frame D k s₀ U') (h : ℕ) : 0 < f.resq h := by unfold resq; positivity

end Frame

/-- A point of a dyadic block is within half a block of its midpoint. -/
theorem abs_sub_dyadic_mid {T j : ℕ} {τ : ℝ}
    (hτ : τ ∈ Icc ((j : ℝ) / 2 ^ T) (((j : ℝ) + 1) / 2 ^ T)) :
    |τ - ((j : ℝ) + 1 / 2) * (2 : ℝ) ^ (-(T : ℤ))| ≤ (2 : ℝ) ^ (-(T : ℤ)) / 2 := by
  have e1 : (j : ℝ) / 2 ^ T = j * (2 : ℝ) ^ (-(T : ℤ)) := by
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  have e2 : ((j : ℝ) + 1) / 2 ^ T = (j + 1) * (2 : ℝ) ^ (-(T : ℤ)) := by
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [e1, e2] at hτ
  rw [abs_le]
  constructor <;> nlinarith [hτ.1, hτ.2]

/-- A time of the residual block is within half a block of its midpoint. -/
theorem Frame.abs_sub_resMid (f : Frame D k s₀ U') (h : ℕ) (i : Fin (f.retained h).card)
    {τ : ℝ} (hτ : τ ∈ Data.I (f.level h).T ((f.level h).j i)) :
    |τ - f.resMid h i| ≤ f.resq h / 2 :=
  abs_sub_dyadic_mid hτ

/-- The residual transverse width is at most `K ^ 2` times the block length. -/
theorem FrameGood.g_le_resq (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) ≤ D.K k ^ 2 * f.resq h := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hc := (hg.res_count hh).2
  have h2 : (0 : ℝ) < 2 ^ f.resT h := by positivity
  rw [Frame.resq, zpow_neg, zpow_natCast]
  rw [← div_eq_mul_inv, le_div_iff₀ h2]
  calc D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) * 2 ^ f.resT h ≤
        D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) *
          (D.K k ^ 2 * D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m)))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = D.K k ^ 2 * (D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) *
          D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m)))) := by ring
    _ = D.K k ^ 2 := by rw [← Real.rpow_add hN]; simp

/-- The incidences of a residual label lie in its centered box. -/
theorem FrameGood.box_mem (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) (l : α) (hl : l ∈ (f.level h).B i) (τ : ℝ)
    (hτ : τ ∈ Data.I (f.level h).T ((f.level h).j i)) (e : Fin 3) :
    |boxCoord (f.resMid h i) (f.boxZ h i) (f.boxY h i) (f.resq h) (f.resBase (l, τ)) e| ≤
      13 * D.K k ^ 4 * K₂ ^ 2 := by
  have hK : 1 ≤ D.K k := hg.K_ge
  have hK₂ : 1 ≤ K₂ := hg.K₂_ge
  have hq := f.resq_pos h
  set q := f.resq h
  set m := f.resMid h i
  set c := (f.level h).c i
  set Z := point (f.coeff l) τ 1
  set Y := point (f.coeff l) τ 2
  obtain ⟨r1, r2, -⟩ := hg.res_rows hh i l hl τ hτ
  have hcen := hg.res_centered hh i
  have hcb (e : Fin 5) : |c e| ≤ 20 * D.K k ^ 2 * K₂ := hg.res_cbound hh i e
  have hτm : |τ - m| ≤ q / 2 := f.abs_sub_resMid h i hτ
  have hgq := hg.g_le_resq hh
  have hK2 : 1 ≤ D.K k ^ 2 := one_le_pow₀ hK
  have hK4 : D.K k ^ 2 ≤ D.K k ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hK₂2 : K₂ ≤ K₂ ^ 2 := le_self_pow₀ hK₂ (by norm_num)
  have hKK₂ : 1 ≤ K₂ ^ 2 := one_le_pow₀ hK₂
  -- the centering, split
  have hc3 : |c 3 + c 0 + m * c 1| ≤ K₂ * q :=
    (le_of_add_le_of_nonneg_left hcen (abs_nonneg _))
  have hc4 : |c 4 - m| ≤ K₂ * q := (le_of_add_le_of_nonneg_right hcen (abs_nonneg _))
  -- the major coordinate
  have hZ : |Z - f.boxZ h i| ≤ 11 * D.K k ^ 2 * K₂ * q := by
    have e1 : Z - f.boxZ h i = (Z - c 0 - τ * c 1) + (τ - m) * c 1 := by
      simp only [Frame.boxZ, c, m]; ring
    rw [e1]
    have h2 : |(τ - m) * c 1| ≤ q / 2 * (20 * D.K k ^ 2 * K₂) := by
      rw [abs_mul]; exact mul_le_mul hτm (hcb 1) (abs_nonneg _) (by positivity)
    have h3 : D.K k ^ 2 * q ≤ D.K k ^ 2 * K₂ * q := by
      have := mul_le_mul_of_nonneg_left hK₂ (by positivity : (0 : ℝ) ≤ D.K k ^ 2 * q)
      nlinarith
    calc _ ≤ |Z - c 0 - τ * c 1| + |(τ - m) * c 1| := abs_add_le _ _
      _ ≤ D.K k ^ 2 * q + q / 2 * (20 * D.K k ^ 2 * K₂) := add_le_add r1 h2
      _ ≤ _ := by nlinarith
  simp only [resBase]
  fin_cases e
  · -- time
    change |(τ - m) / q| ≤ _
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    have : q / 2 ≤ 13 * D.K k ^ 4 * K₂ ^ 2 * q := by
      have h1 : 1 ≤ 13 * D.K k ^ 4 * K₂ ^ 2 := by
        have := one_le_pow₀ (n := 4) hK
        nlinarith
      nlinarith
    linarith
  · -- major
    change |(Z - f.boxZ h i) / q| ≤ _
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    refine hZ.trans ?_
    have : 11 * D.K k ^ 2 * K₂ ≤ 13 * D.K k ^ 4 * K₂ ^ 2 := by nlinarith
    nlinarith
  · -- transverse
    change |(Y - f.boxY h i + f.boxZ h i * (τ - m) - m * (Z - f.boxZ h i)) / q ^ 2| ≤ _
    have hq2 : 0 < q ^ 2 := by positivity
    rw [abs_div, abs_of_pos hq2, div_le_iff₀ hq2]
    have e2 : Y - f.boxY h i + f.boxZ h i * (τ - m) - m * (Z - f.boxZ h i) =
        (Y - c 2 - τ * c 3 - c 4 * Z) + (τ - m) * (c 3 + c 0 + m * c 1) +
          (Z - f.boxZ h i) * (c 4 - m) := by
      simp only [Frame.boxY, Frame.boxZ, c, m]; ring
    rw [e2]
    have hE : |Y - c 2 - τ * c 3 - c 4 * Z| ≤ D.K k ^ 4 * q ^ 2 := by
      refine r2.trans ?_
      calc D.K k ^ 2 * q * D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) ≤
            D.K k ^ 2 * q * (D.K k ^ 2 * q) := mul_le_mul_of_nonneg_left hgq (by positivity)
        _ = D.K k ^ 4 * q ^ 2 := by ring
    have hA : |(τ - m) * (c 3 + c 0 + m * c 1)| ≤ q / 2 * (K₂ * q) := by
      rw [abs_mul]; exact mul_le_mul hτm hc3 (abs_nonneg _) (by positivity)
    have hB : |(Z - f.boxZ h i) * (c 4 - m)| ≤ 11 * D.K k ^ 2 * K₂ * q * (K₂ * q) := by
      rw [abs_mul]; exact mul_le_mul hZ hc4 (abs_nonneg _) (by positivity)
    calc _ ≤ |Y - c 2 - τ * c 3 - c 4 * Z| + |(τ - m) * (c 3 + c 0 + m * c 1)| +
          |(Z - f.boxZ h i) * (c 4 - m)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ D.K k ^ 4 * q ^ 2 + q / 2 * (K₂ * q) + 11 * D.K k ^ 2 * K₂ * q * (K₂ * q) :=
        add_le_add (add_le_add hE hA) hB
      _ = (D.K k ^ 4 + K₂ / 2 + 11 * D.K k ^ 2 * K₂ ^ 2) * q ^ 2 := by ring
      _ ≤ 13 * D.K k ^ 4 * K₂ ^ 2 * q ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hq2.le
        nlinarith

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
