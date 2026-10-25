-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/SourceCoordinates.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.Cut
import Submission.Obl.k4_finite_affine_candidate_return.AffineHiddenReturn

namespace Submission.Obl.k4_finite_affine_candidate_return

open MvPolynomial
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open Submission.Lib.K4ContactNormalization

noncomputable section

def affineSourceFrame (t₀ q₀ scale : ℝ) (c₀ u₀ : EuclideanSpace ℝ (Fin 2))
    (D₀ : Matrix (Fin 2) (Fin 2) ℝ) : PFrame :=
  ⟨⟨t₀, q₀, c₀, u₀, D₀⟩, scale⟩

/-- The concrete source interface is precisely the already checked
parent normalization followed by the accepted affine hidden shear. -/
lemma affineCoefficients_eq_hiddenShear
    (t₀ q₀ scale : ℝ) (c₀ u₀ : EuclideanSpace ℝ (Fin 2))
    (D₀ : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 4 → ℝ) :
    AffineCoefficients t₀ q₀ scale c₀ u₀ D₀ a =
      hiddenShear (affineSourceFrame t₀ q₀ scale c₀ u₀ D₀).eb a := by
  funext l e
  fin_cases e <;>
    simp [AffineCoefficients, affineSourceFrame, hiddenShear, residualCoeff, PFrame.eb, Frame.normCoeff]

/-- All affine substitutions in an explicit source have one fixed
polynomial budget. No eventual loss or candidate exponent occurs here. -/
lemma PFrame.source_substBudget_le
    (Φ : PFrame) (H : ℝ) (hH : 1 ≤ H)
    (hsize : |Φ.F.q⁻¹| + |Φ.F.t₀| + ‖Φ.F.c‖ + ‖Φ.F.u‖ +
      (∑ e : Fin 2, ∑ f : Fin 2, |Φ.F.D⁻¹ e f|) ≤ H)
    (hsc : |Φ.sc| ≤ H ^ 2) : Φ.substBudget ≤ 6 * H ^ 2 := by
  have hsum : 0 ≤ ∑ e : Fin 2, ∑ f : Fin 2, |Φ.F.D⁻¹ e f| := by positivity
  have hq : |Φ.F.q⁻¹| ≤ H := by linarith [abs_nonneg Φ.F.t₀, norm_nonneg Φ.F.c, norm_nonneg Φ.F.u]
  have ht : |Φ.F.t₀| ≤ H := by linarith [abs_nonneg Φ.F.q⁻¹, norm_nonneg Φ.F.c, norm_nonneg Φ.F.u]
  have hcu : ‖Φ.F.c‖ + ‖Φ.F.u‖ ≤ H := by linarith [abs_nonneg Φ.F.q⁻¹, abs_nonneg Φ.F.t₀]
  have hD : (∑ e : Fin 2, ∑ f : Fin 2, |Φ.F.D⁻¹ e f|) ≤ H := by
    linarith [abs_nonneg Φ.F.q⁻¹, abs_nonneg Φ.F.t₀, norm_nonneg Φ.F.c, norm_nonneg Φ.F.u]
  apply max_le
  · unfold Frame.substBound
    calc
      _ ≤ 1 + H * (1 + H) + H * (1 + H) := by
        apply add_le_add
        · exact add_le_add le_rfl
            (mul_le_mul hq (by linarith : 1 + |Φ.F.t₀| ≤ 1 + H) (by positivity) (by linarith))
        · exact mul_le_mul hD (by linarith : 1 + ‖Φ.F.c‖ + ‖Φ.F.u‖ ≤ 1 + H)
            (by positivity) (by linarith)
      _ ≤ 6 * H ^ 2 := by nlinarith
  · exact hsc.trans (by nlinarith [sq_nonneg H])

lemma residualBudget_one_le (a : Fin 4 → ℝ) (H : ℝ) (hH : 1 ≤ H)
    (ha : (∑ e : Fin 4, |a e|) ≤ H) : residualBudget a 1 ≤ 3 * H := by
  simp only [residualBudget, inv_one, abs_one, one_mul]
  simp only [Fin.sum_univ_four] at ha
  linarith

/-- After the source format is bounded by H, affine candidate lifting
costs at most a fixed constant times H^7 times its native coefficient
ceiling. This will be absorbed into an exponent depending only on M,n. -/
lemma source_affine_coefficient_bound
    (Φ : PFrame) (a : Fin 4 → ℝ) (δ H Hq : ℝ)
    (hH : 1 ≤ H) (hδ : |δ| ≤ H) (ha : (∑ e : Fin 4, |a e|) ≤ H)
    (hsubst : Φ.substBudget ≤ 6 * H ^ 2)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (hcoeff : ∀ e, |Q.coeff e| ≤ Hq) (e : Fin 4 →₀ ℕ) :
    |(Φ.affineLift a δ Q).coeff e| ≤ 26244 * H ^ 7 * Hq := by
  have hHq : 0 ≤ Hq := (abs_nonneg _).trans (hcoeff 0)
  have hbudget := residualBudget_one_le a H hH ha
  have hbudget₀ : 0 ≤ residualBudget a 1 := zero_le_one.trans (one_le_residualBudget a 1)
  have hsubst₀ : 0 ≤ Φ.substBudget := zero_le_one.trans Φ.one_le_substBudget
  calc
    _ ≤ 81 * |δ| * Hq * residualBudget a 1 ^ 2 * Φ.substBudget ^ 2 :=
      Φ.coeff_affineLift_quadratic_le a δ Q hQ Hq hcoeff e
    _ ≤ 81 * H * Hq * (3 * H) ^ 2 * (6 * H ^ 2) ^ 2 := by
      gcongr
    _ = _ := by ring

lemma native_candidate_ceiling_bound
    (N H R F P : ℝ) (n : ℕ) (hN : 1 ≤ N) (hH : 1 ≤ H) (hNH : N ≤ H)
    (hR : R ≤ n) (hF₀ : 0 ≤ F) (hP₀ : 0 ≤ P) (hF : F ≤ H) (hP : P ≤ H) :
    N ^ R * (1 + F + P) ^ R ≤ 3 ^ n * H ^ (2 * n) := by
  have hright : 1 ≤ 1 + F + P := by linarith
  have hleft : N ^ R ≤ H ^ n := by
    calc
      _ ≤ N ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hR
      _ = N ^ n := Real.rpow_natCast N n
      _ ≤ H ^ n := pow_le_pow_left₀ (by linarith) hNH n
  have hright' : (1 + F + P) ^ R ≤ (3 * H) ^ n := by
    calc
      _ ≤ (1 + F + P) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hright hR
      _ = (1 + F + P) ^ n := Real.rpow_natCast _ n
      _ ≤ (3 * H) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
  apply (mul_le_mul hleft hright' (by positivity) (by positivity)).trans_eq
  rw [mul_pow]
  rw [show 2 * n = n + n by omega, pow_add]
  ring

def sourceOutputExponent (n M : ℕ) : ℕ := M * (2 * n + 20) + 2 * n + 20

lemma sourceOutputExponent_ge (n M : ℕ) : M + 1 ≤ sourceOutputExponent n M := by
  have h := Nat.mul_le_mul_left M (by omega : 1 ≤ 2 * n + 20)
  simp only [mul_one] at h
  dsimp only [sourceOutputExponent]
  omega

/-- The entire quadratic output budget is fixed by the source format M
and the tested range n, before the actual loss epsilon is chosen. -/
lemma source_output_coefficient_bound
    (N : ℝ) (hN : 2 ≤ N) (n M : ℕ)
    (Φ : PFrame) (a : Fin 4 → ℝ) (δ Nt R F P : ℝ)
    (hδ : |δ| ≤ N ^ M) (ha : (∑ e : Fin 4, |a e|) ≤ N ^ M)
    (hsubst : Φ.substBudget ≤ 6 * (N ^ M) ^ 2)
    (hNt : 1 ≤ Nt) (hNtN : Nt ≤ N ^ M) (hRn : R ≤ n)
    (hF₀ : 0 ≤ F) (hP₀ : 0 ≤ P) (hF : F ≤ N ^ M) (hP : P ≤ N ^ M)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (hcoeff : ∀ e, |Q.coeff e| ≤ Nt ^ R * (1 + F + P) ^ R) :
    ∀ e, |(Φ.affineLift a δ Q).coeff e| ≤ N ^ sourceOutputExponent n M := by
  have hN1 : 1 ≤ N := by linarith
  have hNM : 1 ≤ N ^ M := one_le_pow₀ hN1
  have hceil := native_candidate_ceiling_bound Nt (N ^ M) R F P n hNt hNM hNtN hRn hF₀ hP₀ hF hP
  have hcoeff' (e) : |Q.coeff e| ≤ 3 ^ n * (N ^ M) ^ (2 * n) := (hcoeff e).trans hceil
  have hconst : (26244 : ℝ) ≤ N ^ (15 : ℕ) := by
    calc
      _ ≤ (2 : ℝ) ^ (15 : ℕ) := by norm_num
      _ ≤ N ^ (15 : ℕ) := pow_le_pow_left₀ (by norm_num) hN 15
  have hthree : (3 : ℝ) ^ n ≤ N ^ (2 * n) := by
    calc
      _ ≤ (N ^ (2 : ℕ)) ^ n := pow_le_pow_left₀ (by norm_num) (by nlinarith) n
      _ = _ := (pow_mul N 2 n).symm
  have hsmall : M * (2 * n + 7) + 2 * n + 15 ≤ sourceOutputExponent n M := by
    have h := Nat.mul_le_mul_left M (by omega : 2 * n + 7 ≤ 2 * n + 20)
    dsimp only [sourceOutputExponent]
    omega
  intro e
  apply (source_affine_coefficient_bound Φ a δ (N ^ M) _ hNM hδ ha hsubst Q hQ hcoeff' e).trans
  calc
    26244 * (N ^ M) ^ 7 * (3 ^ n * (N ^ M) ^ (2 * n)) =
        26244 * 3 ^ n * N ^ (M * (2 * n + 7)) := by
      rw [pow_mul N M (2 * n + 7), pow_add]
      ring
    _ ≤ N ^ (15 : ℕ) * N ^ (2 * n) * N ^ (M * (2 * n + 7)) := by
      gcongr
    _ = N ^ (M * (2 * n + 7) + 2 * n + 15) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ _ := pow_le_pow_right₀ hN1 hsmall

end

end Submission.Obl.k4_finite_affine_candidate_return
