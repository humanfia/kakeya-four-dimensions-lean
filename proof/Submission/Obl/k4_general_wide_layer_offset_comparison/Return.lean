import Submission.Obl.k4_general_wide_layer_offset_comparison.Model
import Submission.Obl.k4_critical_intercept_concentration.CandidateRestore
import Submission.Lib.K4ContactNormalization.HomogeneousCorrection
import Submission.Obl.k4_balanced_native_packet_transport.Pullback

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/Return.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory MvPolynomial Set Filter
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting
open scoped ENNReal BigOperators

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Native observable predicted by a quadratic in the original full base.
The error is tested on the entire original true block. -/
def PredictorEvent (k : ℕ) (s v ε : ℝ) (i : Fin (p.n k s))
    (G : MvPolynomial (Fin 3) ℝ) : Set (α × ℝ) :=
  {ω | ω.1 ∈ p.B k s i ∧ ω.2 ∈ block (p.T k s) (p.j k s i) ∧
    ∀ t ∈ block (p.T k s) (p.j k s i),
      |eval (p.x k ω.1 t) (p.P k) - eval (p.x k ω.1 t ∘ Fin.castSucc) G| ≤
        p.N k ^ ε * p.N k ^ (-s - v)}

/-- The homogeneous size in the frozen conclusion uses only the two native tests. -/
def nativeSize (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) : ℝ :=
  (1 + coeffL1 (p.F k s i)) + coeffL1 (p.P k)

theorem nativeSize_ge_one (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) :
    1 ≤ p.nativeSize k s i := by
  have hF : 0 ≤ coeffL1 (p.F k s i) := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP : 0 ≤ coeffL1 (p.P k) := Finset.sum_nonneg fun _ _ => abs_nonneg _
  dsimp [nativeSize]
  linarith

/-- This return uses the original native signal's bounds. No derivative of
the full-base predictor is paid in the hidden coordinate. -/
theorem native_polynomial_candidate (hbase : p.Basic)
    {k : ℕ} {s v ε R : ℝ} (i : Fin (p.n k s))
    (G : MvPolynomial (Fin 3) ℝ)
    (hN : 2 ≤ p.N k) (hKpos : 0 < p.K k)
    (hK : p.K k ≤ p.N k ^ ε) (hsv : 0 ≤ s + v)
    (hG : G.totalDegree ≤ 2)
    (hcoeff : ∀ e, |(baseCalibratedTest (p.P k) G).coeff e| ≤
      p.N k ^ R * p.nativeSize k s i ^ R)
    (hmass : ENNReal.ofReal (p.N k ^ (-p.d * v - ε) / (2 : ℝ) ^ p.T k s) *
      p.ν k (p.A k s i) ≤ p.ρ k (p.PredictorEvent k s v ε i G)) :
    p.QuadraticCandidate k s v ε R i := by
  have hNpos : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := by linarith
  have hscale : 0 < p.N k ^ (-s - v) := Real.rpow_pos_of_pos hNpos _
  have hscale1 : p.N k ^ (-s - v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hpowpos : 0 < p.N k ^ ε := Real.rpow_pos_of_pos hNpos _
  have hsecond : p.K k ≤ p.N k ^ ε / p.N k ^ (-s - v) := by
    apply hK.trans
    exact le_div_self hpowpos.le hscale hscale1
  have hsmall : p.N k ^ (-ε) ≤ (p.K k)⁻¹ := by
    rw [Real.rpow_neg hNpos.le]
    exact (inv_le_inv₀ hpowpos hKpos).mpr hK
  have hg := hbase k
  have hρμ : p.ρ k ≤ p.μ k := hg.2.2.2.2.1
  have hP : (p.P k).totalDegree ≤ 2 := hg.2.2.2.2.2.2.2.1
  have hgood : ∀ᵐ ω ∂p.ρ k,
      (∀ t ∈ Icc (0 : ℝ) 1,
        |eval (p.x k ω.1 t) (p.P k)| ≤ p.K k ∧
        |eval (p.x k ω.1 t) (pderiv (3 : Fin 4) (p.P k))| ≤ p.K k ∧
        |eval (p.x k ω.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (p.P k)))| ≤ p.K k) ∧
      (p.K k)⁻¹ ≤ |eval (p.x k ω.1 ω.2) (pderiv (3 : Fin 4) (p.P k))| :=
    ae_mono hρμ hg.2.2.2.2.2.2.2.2.2
  refine ⟨baseCalibratedTest (p.P k) G, baseCalibratedTest_degree hP hG, hcoeff, ?_⟩
  apply hmass.trans
  apply measure_mono_ae
  filter_upwards [hgood] with ω hω
  rintro ⟨hb, ht, hfit⟩
  refine ⟨hb, ht, ?_, ?_⟩
  · intro t ht'
    have ht1 : t ∈ Icc (0 : ℝ) 1 :=
      Submission.Obl.k4_balanced_native_packet_transport.Pullback.block_subset_unit (p.j k s i) ht'
    obtain ⟨_, hd, hdd⟩ := hω.1 t ht1
    simp only [eval_baseCalibratedTest, pderiv_baseCalibratedTest]
    exact ⟨hfit t ht', hd.trans hK, hdd.trans hsecond⟩
  · rw [pderiv_baseCalibratedTest]
    exact hsmall.trans hω.2

/-- A coefficient ceiling on the base predictor gives the needed ceiling
on its subtraction from the native polynomial. -/
theorem residual_coefficients (k : ℕ) (G : MvPolynomial (Fin 3) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hG : ∀ e, |G.coeff e| ≤ B) :
    ∀ e, |(baseCalibratedTest (p.P k) G).coeff e| ≤ coeffL1 (p.P k) + B := by
  intro e
  calc
    _ ≤ |(p.P k).coeff e| + |(rename Fin.castSucc G).coeff e| := by
      simpa only [baseCalibratedTest, coeff_sub] using
        abs_sub ((p.P k).coeff e) ((rename Fin.castSucc G).coeff e)
    _ ≤ coeffL1 (p.P k) + B :=
      add_le_add (abs_coeff_le_coeffL1 _ _) (coeff_rename_base_le G hB hG e)

/-- Only the scale lower bound is needed to enlarge the coefficient exponent. -/
theorem polynomial_candidate_mono_exponent
    (hN : ∀ k, 2 ≤ p.N k) {k : ℕ} {s v ε R R' : ℝ}
    {i : Fin (p.n k s)} (h : p.QuadraticCandidate k s v ε R i) (hRR' : R ≤ R') :
    p.QuadraticCandidate k s v ε R' i := by
  obtain ⟨Q, hQ, hc, hm⟩ := h
  refine ⟨Q, hQ, ?_, hm⟩
  have hN1 : 1 ≤ p.N k := by linarith [hN k]
  have hsize := p.nativeSize_ge_one k s i
  intro e
  change |Q.coeff e| ≤ p.N k ^ R' * p.nativeSize k s i ^ R'
  apply (hc e).trans
  change p.N k ^ R * p.nativeSize k s i ^ R ≤ _
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hN1 hRR')
    (Real.rpow_le_rpow_of_exponent_le hsize hRR')
    (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)

/-- Fixed positive depths and one fixed coefficient bound give the exact
cofinal quantifier order. The original assignment mass is kept. -/
theorem candidates_of_fixed_gain (hN : ∀ k, 2 ≤ p.N k) {s v R₀ : ℝ}
    (hs : 0 < s) (hv : 0 < v) (hsU : s + v ≤ p.U)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ i : Fin (p.n k s), p.QuadraticCandidate k s v ε R₀ i) : p.Candidates := by
  let R := 2 + |R₀| + s + v + s⁻¹ + v⁻¹
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hvi : 0 < v⁻¹ := inv_pos.mpr hv
  have hR : 1 < R := by dsimp [R]; linarith [abs_nonneg R₀]
  have hRs : s ≤ R := by dsimp [R]; linarith [abs_nonneg R₀]
  have hRv : v ≤ R := by dsimp [R]; linarith [abs_nonneg R₀]
  have hR₀ : R₀ ≤ R := by dsimp [R]; linarith [le_abs_self R₀]
  have hsiR : R⁻¹ ≤ s := (inv_le_comm₀ (by linarith) hs).mpr (by dsimp [R]; linarith [abs_nonneg R₀])
  have hviR : R⁻¹ ≤ v := (inv_le_comm₀ (by linarith) hv).mpr (by dsimp [R]; linarith [abs_nonneg R₀])
  refine ⟨R, hR, ?_⟩
  intro ε hε
  apply (hc ε hε).mono
  rintro k ⟨i, hi⟩
  exact ⟨s, v, i, hsiR, hRs, hviR, hRv, hsU,
    Or.inl (p.polynomial_candidate_mono_exponent hN hi hR₀)⟩

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
