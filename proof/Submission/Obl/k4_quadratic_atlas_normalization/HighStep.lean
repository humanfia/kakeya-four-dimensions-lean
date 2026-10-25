import Submission.Obl.k4_quadratic_atlas_normalization.StepInterface
import Submission.Obl.k4_quadratic_atlas_normalization.HighCurvatureChart
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat
import Submission.Obl.k4_quadratic_atlas_normalization.LowNumerics
import Submission.Obl.k4_quadratic_atlas_normalization.EmptyChart

/-!
# The high-curvature step

A late rough sample whose high-curvature charts carry half of the selected mass normalizes at
depth `L - 12a`. Each high-curvature chart is replaced by the affine critical-center test
(`high_curvature_chart`), keeping its assignment and selection; each low-curvature chart keeps
its frame and test but loses its assignment and selection. Lists, time blocks and the original
priors are unchanged, and the output slack is twice the input slack.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_quadratic_atlas_normalization

open MeasureTheory Filter Set

/-- The value and coefficient budgets of the critical-center test at depth `L - 12a`. -/
theorem high_budgets {N L a Bv : ℝ} {M Mb : ℕ} (hN2 : 2 ≤ N) (hL : 0 ≤ L)
    (ha3 : 2 ≤ N ^ (3 * a)) (hB : 0 < Bv) (hBinv : Bv⁻¹ ≤ N ^ Mb) :
    Bv ^ 2 * N ^ a / (Bv ^ 2 * N ^ (-(8 * a)) / δ N L) ≤ δ N (L - 12 * a) ∧
      2 * Bv * N ^ M / (Bv ^ 2 * N ^ (-(8 * a)) / δ N L) ≤
        N ^ (M + Mb + ⌈8 * a⌉₊ + 1) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hδ : 0 < δ N L := by unfold δ; positivity
  have h8 : 0 < N ^ (8 * a) := Real.rpow_pos_of_pos hN0 _
  constructor
  · have key : Bv ^ 2 * N ^ a / (Bv ^ 2 * N ^ (-(8 * a)) / δ N L) =
        δ N L * N ^ (9 * a) := by
      rw [Real.rpow_neg hN0.le, show 9 * a = a + 8 * a by ring, Real.rpow_add hN0]
      field_simp
    rw [key]
    have := delta_absorb_power hN0 ha3 L (9 * a)
    rwa [show L - (9 * a + 3 * a) = L - 12 * a by ring] at this
  · have key : 2 * Bv * N ^ M / (Bv ^ 2 * N ^ (-(8 * a)) / δ N L) =
        2 * N ^ M * δ N L * N ^ (8 * a) * Bv⁻¹ := by
      rw [Real.rpow_neg hN0.le]
      field_simp
    rw [key]
    have hc : N ^ (8 * a) ≤ N ^ (⌈8 * a⌉₊) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (Nat.le_ceil _)
    have hδ1 : δ N L ≤ 1 := delta_le_one hN1 hL
    have hM : (0 : ℝ) ≤ N ^ M := pow_nonneg hN0.le _
    calc 2 * N ^ M * δ N L * N ^ (8 * a) * Bv⁻¹
        ≤ N * N ^ M * 1 * N ^ (⌈8 * a⌉₊) * N ^ Mb := by
          apply mul_le_mul _ hBinv (inv_nonneg.mpr hB.le) (by positivity)
          apply mul_le_mul _ hc h8.le (by positivity)
          apply mul_le_mul _ hδ1 hδ.le (by positivity)
          exact mul_le_mul_of_nonneg_right hN2 hM
      _ = N ^ (M + Mb + ⌈8 * a⌉₊ + 1) := by ring

/-- The high-curvature step. -/
theorem highStep (L a h : ℝ) (M D Mb : ℕ) (hL : 0 < L) (ha : 0 < a) (h20 : 20 * a < L) :
    HighStep L a h M D Mb := by
  refine ⟨M + Mb + ⌈8 * a⌉₊ + 1, D, fun ε hε => ⟨ε / 2, by positivity, ?_⟩⟩
  have hev : ∀ᶠ N : ℝ in atTop, 2 ≤ N ^ (ε / 2) ∧ 2 ≤ N ^ (3 * a) :=
    ((tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2).and
      ((tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨N₀, fun Nk Wk ωk νk Ek Bk hNk hN2 hω0 hω1 hν hB hR => ?_⟩
  obtain ⟨hε2, ha3⟩ := hN₀ Nk hNk
  obtain ⟨κ, hκ1, hκε, T, C', γ, j, c, u, Q, R, A, F, lst, hT, hC, hdisj, hlst, hch,
    hmass⟩ := hR
  have hN1 : (1 : ℝ) ≤ Nk := by linarith
  have hN0 : (0 : ℝ) < Nk := by linarith
  have hδL : 0 < δ Nk L := by unfold δ; positivity
  classical
  refine ⟨2 * κ, by linarith, ?_, T, C', γ, j, c, u, Q,
    fun b => if ¬ lowCase Nk L a (Bk (γ b)) (R b) then
      criticalCenterTest (R b) 3 (Bk (γ b)) else R b,
    fun b => A b ∩ {_l | ¬ lowCase Nk L a (Bk (γ b)) (R b)},
    fun b => F b ∩ {_p | ¬ lowCase Nk L a (Bk (γ b)) (R b)}, lst,
    hT.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)),
    hC.trans (pow_le_pow_right₀ hN1 (by omega)), ?_, ?_, ?_, ?_⟩
  · calc 2 * κ ≤ Nk ^ (ε / 2) * Nk ^ (ε / 2) :=
          mul_le_mul hε2 hκε (by linarith) (by positivity)
      _ = Nk ^ ε := by rw [← Real.rpow_add hN0]; ring_nf
  · intro b b' hbb' hγ hj
    exact (hdisj b b' hbb' hγ hj).mono inter_subset_left inter_subset_left
  · intro γ₁ o
    exact (hlst γ₁ o).trans (by linarith)
  · intro b
    beta_reduce
    by_cases hb : ¬ lowCase Nk L a (Bk (γ b)) (R b)
    · have hA : A b ∩ {_l | ¬ lowCase Nk L a (Bk (γ b)) (R b)} = A b :=
        inter_eq_left.mpr fun _ _ => hb
      have hF : F b ∩ {_p | ¬ lowCase Nk L a (Bk (γ b)) (R b)} = F b :=
        inter_eq_left.mpr fun _ _ => hb
      rw [ite_eq_left hb, hA, hF]
      obtain ⟨hB0, -, hBinv⟩ := hB (γ b)
      have hc₀ : 0 < Bk (γ b) ^ 2 * Nk ^ (-(8 * a)) / δ Nk L := by positivity
      have hc : Bk (γ b) ^ 2 * Nk ^ (-(8 * a)) / δ Nk L ≤ |curvature (R b) 3| := by
        rw [← curv_eq_curvature]
        exact (not_le.mp hb).le
      obtain ⟨hthick, hcoef⟩ := high_budgets (M := M) hN2 hL.le ha3 hB0 hBinv
      exact high_curvature_chart hN1 (by omega) hκ1 (by linarith) hB0 hc₀ hc hthick hcoef
        (hch b)
    · have hA : A b ∩ {_l | ¬ lowCase Nk L a (Bk (γ b)) (R b)} = ∅ :=
        eq_empty_of_forall_notMem fun l hl => hb hl.2
      have hF : F b ∩ {_p | ¬ lowCase Nk L a (Bk (γ b)) (R b)} = ∅ :=
        eq_empty_of_forall_notMem fun p hp => hb hp.2
      rw [ite_eq_right hb, hA, hF]
      exact chart_empty_of_rough hN1 (by omega) (by linarith) (hch b)
        (fun p hp => absurd hp (notMem_empty p))
  · rw [show (2 * κ)⁻¹ = κ⁻¹ / 2 by ring]
    exact hmass

end Submission.Obl.k4_quadratic_atlas_normalization
