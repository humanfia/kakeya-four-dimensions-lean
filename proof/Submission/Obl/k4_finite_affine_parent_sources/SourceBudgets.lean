-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceRates
import Submission.Obl.k4_finite_affine_parent_sources.PolynomialBudgets
import Submission.Obl.k4_quadratic_finite_greedy_cover.PathFacts

/-!
# Coefficient and size budgets of a source stage

Polynomial-in-`Nk` bounds for the frozen `NativeSource` size budget and for the coefficients
of the normalized parent and label tests, from the chart format of the supplied path and the
problem's derivative units.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

/-- The derivative units of the exact problem are polynomially bounded. -/
theorem prob_B_power {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Trajectory}
    {E : (k : ℕ) → Fin (W k) → Set Incidence} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G) :
    ∃ Mb : ℕ, ∀ k w, B k w ≤ N k ^ Mb ∧ (B k w)⁻¹ ≤ N k ^ Mb := by
  rcases hp with ⟨-, -, -, -, -, -, -, -, hrest⟩
  obtain ⟨M, D, hdata⟩ := hrest.1
  exact ⟨M, fun k w => ⟨((hdata k).2.2.2.1 w).2.2.1, ((hdata k).2.2.2.1 w).2.2.2.1⟩⟩

/-- Absorb a fixed constant: `c * Nk^A ≤ Nk^(A + e)` once `c ≤ 2^e` and `2 ≤ Nk`. -/
theorem const_mul_pow_le {Nk c : ℝ} (hNk : 2 ≤ Nk) (A e : ℕ) (hc : c ≤ 2 ^ e) :
    c * Nk ^ A ≤ Nk ^ (A + e) := by
  have h1 : (2 : ℝ) ^ e ≤ Nk ^ e := pow_le_pow_left₀ (by norm_num) hNk e
  have hA : 0 ≤ Nk ^ A := by positivity
  calc c * Nk ^ A ≤ 2 ^ e * Nk ^ A := mul_le_mul_of_nonneg_right hc hA
    _ ≤ Nk ^ e * Nk ^ A := mul_le_mul_of_nonneg_right h1 hA
    _ = Nk ^ (A + e) := by rw [pow_add, mul_comm]

/-- A real power of `Nk` below a natural one. -/
theorem rpow_le_npow {Nk : ℝ} (hNk : 1 ≤ Nk) {a : ℝ} {A : ℕ} (ha : a ≤ A) :
    Nk ^ a ≤ Nk ^ A := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hNk ha

/-- Coefficient budget of a normalized test. -/
theorem coeffL1_normTest_budget (Φ : PFrame) (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ)
    (hR : R.totalDegree ≤ 2) (H U : ℝ) (hcoeff : ∀ e, |R.coeff e| ≤ H)
    (hU : Φ.unsubstBudget ≤ U) :
    coeffL1 (Φ.normTest δ R) ≤ |δ⁻¹| * (81 * H * U ^ 2) := by
  have hL : coeffL1 R ≤ 81 * H := by
    simpa using coeffL1_le_of_coeff_le R hR H hcoeff
  have hU1 : 1 ≤ U := Φ.one_le_unsubstBudget.trans hU
  have hpow : Φ.unsubstBudget ^ R.totalDegree ≤ U ^ 2 :=
    (pow_le_pow_left₀ (zero_le_one.trans Φ.one_le_unsubstBudget) hU _).trans
      (pow_le_pow_right₀ hU1 hR)
  calc coeffL1 (Φ.normTest δ R) ≤ |δ⁻¹| * (coeffL1 R * Φ.unsubstBudget ^ R.totalDegree) :=
        Φ.coeffL1_normTest_le δ R
    _ ≤ |δ⁻¹| * (81 * H * U ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact mul_le_mul hL hpow (pow_nonneg (zero_le_one.trans Φ.one_le_unsubstBudget) _)
          (by have := coeffL1_nonneg R; linarith)

/-- The inverse substitution budget of an explicit frame. -/
theorem unsubstBudget_le (Φ : PFrame) (X : ℝ)
    (ht : |Φ.F.t₀| ≤ 1) (hq : |Φ.F.q| ≤ 1) (hcu : ‖Φ.F.c‖ + ‖Φ.F.u‖ ≤ X)
    (hD : (∑ e : Fin 2, ∑ e' : Fin 2, |Φ.F.D e e'|) ≤ X) (hsc : |Φ.sc⁻¹| ≤ X) (hX : 0 ≤ X) :
    Φ.unsubstBudget ≤ 3 * (1 + X) ^ 2 + X := by
  unfold PFrame.unsubstBudget Frame.unsubstBound
  apply max_le
  · have h1 : 1 + |Φ.F.t₀| + |Φ.F.q| ≤ 3 := by linarith
    have h2 : 1 + ‖Φ.F.c‖ + ‖Φ.F.u‖ ≤ 1 + X := by linarith
    have h3 : 1 + ∑ e : Fin 2, ∑ e' : Fin 2, |Φ.F.D e e'| ≤ 1 + X := by linarith
    have h0 : (0 : ℝ) ≤ 1 + ‖Φ.F.c‖ + ‖Φ.F.u‖ := by positivity
    have h0' : (0 : ℝ) ≤ 1 + ∑ e : Fin 2, ∑ e' : Fin 2, |Φ.F.D e e'| := by positivity
    calc (1 + |Φ.F.t₀| + |Φ.F.q|) * (1 + ‖Φ.F.c‖ + ‖Φ.F.u‖) *
          (1 + ∑ e : Fin 2, ∑ e' : Fin 2, |Φ.F.D e e'|)
        ≤ 3 * (1 + X) * (1 + X) := by gcongr
      _ ≤ 3 * (1 + X) ^ 2 + X := by nlinarith
  · nlinarith [sq_nonneg (1 + X)]

/-- The coefficient exponent of a source stage. -/
def budgetExp (L ℓ : ℝ) (Mp Mb : ℕ) : ℕ :=
  ⌈L⌉₊ * (3 + ⌈ℓ⌉₊) + 5 * Mp + 4 * Mb + 40

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The inverse substitution budget of the source frame. -/
theorem source_unsubstBudget (D : SourceData p) (hNk : 2 ≤ Nk) {Mb : ℕ}
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hBw : 0 < B D.w₀) (hBinv : (B D.w₀)⁻¹ ≤ Nk ^ Mb) (hr₀ : 0 ≤ p.r D.i₀) :
    (D.frame Nk B).unsubstBudget ≤ Nk ^ (2 * (Mp + Mb) + 8) := by
  have hc := hp.chart D.parent
  have hN1 : (1 : ℝ) ≤ Nk := by linarith
  have hN0 : 0 < Nk := by linarith
  have hMp : 1 ≤ Nk ^ Mp := one_le_pow₀ hN1
  have hMb : 1 ≤ Nk ^ Mb := one_le_pow₀ hN1
  set X := 6 * Nk ^ (Mp + Mb)
  have hX0 : 0 ≤ X := by positivity
  have hprod : Nk ^ Mp ≤ Nk ^ (Mp + Mb) := pow_le_pow_right₀ hN1 (by omega)
  have hprod' : Nk ^ Mb ≤ Nk ^ (Mp + Mb) := pow_le_pow_right₀ hN1 (by omega)
  have hbin := hp.label_bin D.parent
  have ht : |(D.frame Nk B).F.t₀| ≤ 1 := by
    rw [D.frame_F]
    show |(p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T D.i₀| ≤ 1
    rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
    have : ((p.bin D.parent : ℕ) : ℝ) < ((2 ^ p.T D.i₀ : ℕ) : ℝ) := by exact_mod_cast hbin
    push_cast at this; exact this.le
  have hq : |(D.frame Nk B).F.q| ≤ 1 := by
    rw [D.frame_F]
    show |((2 : ℝ) ^ p.T D.i₀)⁻¹| ≤ 1
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hcu : ‖(D.frame Nk B).F.c‖ + ‖(D.frame Nk B).F.u‖ ≤ X := by
    rw [D.frame_F]
    show ‖p.center D.parent‖ + ‖p.velocity D.parent‖ ≤ X
    linarith [hc.2.1]
  have hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |(D.frame Nk B).F.D e e'|) ≤ X := by
    rw [D.frame_F]
    show (∑ e : Fin 2, ∑ e' : Fin 2, |D.D₀ e e'|) ≤ X
    rw [hD₀]
    have h1 := MajorFrame.entries_le hc.1
    have h2 : (∑ i : Fin 2, ∑ j : Fin 2, |p.frame D.parent i j|) ≤ Nk ^ Mp := by
      have := hc.2.2.1
      have hpos : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, |(p.frame D.parent)⁻¹ i j| := by positivity
      calc _ ≤ ∑ e : Fin 2, ∑ e' : Fin 2, (|p.frame D.parent e e'| + |(p.frame D.parent)⁻¹ e e'|) := by
            apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
            linarith [abs_nonneg ((p.frame D.parent)⁻¹ i j)]
        _ ≤ _ := this
    linarith
  have hsc : |(D.frame Nk B).sc⁻¹| ≤ X := by
    show |(B D.w₀ / δ Nk (p.r D.i₀))⁻¹| ≤ X
    obtain ⟨hδ1, hδ2⟩ := delta_two_sided hN0 (p.r D.i₀)
    have hδ0 : 0 < δ Nk (p.r D.i₀) := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hδ1
    have hδle : δ Nk (p.r D.i₀) ≤ 2 := by
      have : Nk ^ (-p.r D.i₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      linarith
    rw [inv_div, abs_of_nonneg (div_nonneg hδ0.le hBw.le), div_eq_mul_inv]
    calc δ Nk (p.r D.i₀) * (B D.w₀)⁻¹ ≤ 2 * Nk ^ Mb := by
          apply mul_le_mul hδle hBinv (inv_nonneg.mpr hBw.le) (by norm_num)
      _ ≤ X := by linarith
  have hU := unsubstBudget_le (D.frame Nk B) X ht hq hcu hDs hsc hX0
  have hX1 : 1 + X ≤ 7 * Nk ^ (Mp + Mb) := by
    have : 1 ≤ Nk ^ (Mp + Mb) := one_le_pow₀ hN1
    linarith
  calc (D.frame Nk B).unsubstBudget ≤ 3 * (1 + X) ^ 2 + X := hU
    _ ≤ 3 * (7 * Nk ^ (Mp + Mb)) ^ 2 + 7 * Nk ^ (Mp + Mb) := by gcongr; linarith
    _ ≤ 154 * Nk ^ (2 * (Mp + Mb)) := by
        have h1 : 1 ≤ Nk ^ (Mp + Mb) := one_le_pow₀ hN1
        have hY : Nk ^ (2 * (Mp + Mb)) = (Nk ^ (Mp + Mb)) ^ 2 := by
          rw [← pow_mul, mul_comm]
        rw [hY]
        set Y := Nk ^ (Mp + Mb)
        nlinarith
    _ ≤ Nk ^ (2 * (Mp + Mb) + 8) := const_mul_pow_le hNk _ 8 (by norm_num)

/-- **Coefficient budget of a normalized original test.** -/
theorem source_test_coeff (D : SourceData p) (hNk : 2 ≤ Nk) {Mb : ℕ}
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hBw : 0 < B D.w₀) (hBinv : (B D.w₀)⁻¹ ≤ Nk ^ Mb) (hr₀ : 0 ≤ p.r D.i₀)
    (hr₀L : p.r D.i₀ ≤ L) (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (hcoeff : ∀ e, |R.coeff e| ≤ Nk ^ Mp) :
    coeffL1 ((D.frame Nk B).normTest (δ Nk (p.r D.i₀)) R) ≤ Nk ^ budgetExp L ℓ Mp Mb := by
  have hN1 : (1 : ℝ) ≤ Nk := by linarith
  have hN0 : 0 < Nk := by linarith
  have hU := source_unsubstBudget hp D hNk hD₀ hBw hBinv hr₀
  have hc := coeffL1_normTest_budget (D.frame Nk B) (δ Nk (p.r D.i₀)) R hR (Nk ^ Mp) _
    hcoeff hU
  obtain ⟨hδ1, -⟩ := delta_two_sided hN0 (p.r D.i₀)
  have hδ0 : 0 < δ Nk (p.r D.i₀) := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hδ1
  have hδinv : |(δ Nk (p.r D.i₀))⁻¹| ≤ Nk ^ ⌈L⌉₊ := by
    rw [abs_of_nonneg (inv_nonneg.mpr hδ0.le)]
    calc (δ Nk (p.r D.i₀))⁻¹ ≤ (Nk ^ (-p.r D.i₀))⁻¹ := inv_anti₀ (by positivity) hδ1
      _ = Nk ^ p.r D.i₀ := by rw [Real.rpow_neg hN0.le, inv_inv]
      _ ≤ Nk ^ ⌈L⌉₊ := rpow_le_npow hN1 (hr₀L.trans (Nat.le_ceil L))
  calc coeffL1 ((D.frame Nk B).normTest (δ Nk (p.r D.i₀)) R)
      ≤ |(δ Nk (p.r D.i₀))⁻¹| * (81 * Nk ^ Mp * (Nk ^ (2 * (Mp + Mb) + 8)) ^ 2) := hc
    _ ≤ Nk ^ ⌈L⌉₊ * (81 * Nk ^ Mp * (Nk ^ (2 * (Mp + Mb) + 8)) ^ 2) := by gcongr
    _ = 81 * Nk ^ (⌈L⌉₊ + 5 * Mp + 4 * Mb + 16) := by
        rw [← pow_mul]; rw [show ⌈L⌉₊ + 5 * Mp + 4 * Mb + 16 =
          ⌈L⌉₊ + Mp + (2 * (Mp + Mb) + 8) * 2 by ring, pow_add, pow_add]; ring
    _ ≤ Nk ^ (⌈L⌉₊ + 5 * Mp + 4 * Mb + 16 + 7) := const_mul_pow_le hNk _ 7 (by norm_num)
    _ ≤ Nk ^ budgetExp L ℓ Mp Mb := by
        apply pow_le_pow_right₀ hN1
        unfold budgetExp
        have : ⌈L⌉₊ ≤ ⌈L⌉₊ * (3 + ⌈ℓ⌉₊) := Nat.le_mul_of_pos_right _ (by omega)
        omega

/-- **The `size` field.** -/
theorem source_size (D : SourceData p) (hNk : 2 ≤ Nk) {Mb : ℕ} {u J : ℝ}
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hB : B D.w₀ ≤ Nk ^ Mb) (hBw : 0 < B D.w₀) (hBinv : (B D.w₀)⁻¹ ≤ Nk ^ Mb)
    (hr₀ : 0 ≤ p.r D.i₀) (hr₀L : p.r D.i₀ ≤ L) (hL : 0 ≤ L) (hℓ : 0 ≤ ℓ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hJ0 : 0 ≤ J) (hJ : J ≤ Nk)
    (hT₀ : (2 : ℝ) ^ p.T D.i₀ ≤ Nk ^ (2 * ⌈L⌉₊)) :
    J + Nk ^ (u * L) + (Nk ^ (u * L)) ^ ℓ + |δ Nk (p.r D.i₀)| +
      |(δ Nk (p.r D.i₀))⁻¹| + |B D.w₀| + |(B D.w₀)⁻¹| +
      |D.t₀| + |D.q₀| + |D.q₀⁻¹| + ‖p.center D.parent‖ + ‖p.velocity D.parent‖ +
      (∑ e : Fin 4, |(fun _ : Fin 4 => (0 : ℝ)) e|) +
      (∑ e : Fin 2, ∑ e' : Fin 2, (|D.D₀ e e'| + |D.D₀⁻¹ e e'|)) ≤
        Nk ^ budgetExp L ℓ Mp Mb := by
  have hc := hp.chart D.parent
  have hN1 : (1 : ℝ) ≤ Nk := by linarith
  have hN0 : 0 < Nk := by linarith
  set A := ⌈L⌉₊ * (3 + ⌈ℓ⌉₊) + Mp + Mb + 1
  have hNA : 1 ≤ Nk ^ A := one_le_pow₀ hN1
  have h3L : 3 * ⌈L⌉₊ ≤ ⌈L⌉₊ * (3 + ⌈ℓ⌉₊) := by
    nlinarith [Nat.zero_le ⌈ℓ⌉₊, Nat.zero_le ⌈L⌉₊]
  have hle : ∀ a : ℕ, a ≤ A → Nk ^ a ≤ Nk ^ A := fun a ha => pow_le_pow_right₀ hN1 ha
  have hLc : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hLA : ⌈L⌉₊ ≤ A := by omega
  -- individual terms
  have t1 : J ≤ Nk ^ A := hJ.trans (by simpa using hle 1 (by omega))
  have t2 : Nk ^ (u * L) ≤ Nk ^ A :=
    (rpow_le_npow hN1 (show u * L ≤ (⌈L⌉₊ : ℝ) by nlinarith)).trans (hle _ hLA)
  have t3 : (Nk ^ (u * L)) ^ ℓ ≤ Nk ^ A := by
    rw [← Real.rpow_mul hN0.le]
    have hlc : ℓ ≤ (⌈ℓ⌉₊ : ℝ) := Nat.le_ceil ℓ
    have : u * L * ℓ ≤ ((⌈L⌉₊ * (3 + ⌈ℓ⌉₊) : ℕ) : ℝ) := by
      push_cast
      have h1 : u * L ≤ (⌈L⌉₊ : ℝ) := by nlinarith
      have h2 : (0 : ℝ) ≤ ⌈L⌉₊ := Nat.cast_nonneg _
      nlinarith
    exact (rpow_le_npow hN1 this).trans (hle _ (by omega))
  obtain ⟨hδ1, hδ2⟩ := delta_two_sided hN0 (p.r D.i₀)
  have hδ0 : 0 < δ Nk (p.r D.i₀) := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hδ1
  have t4 : |δ Nk (p.r D.i₀)| ≤ 2 * Nk ^ A := by
    rw [abs_of_pos hδ0]
    have : Nk ^ (-p.r D.i₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    nlinarith
  have t5 : |(δ Nk (p.r D.i₀))⁻¹| ≤ Nk ^ A := by
    rw [abs_of_nonneg (inv_nonneg.mpr hδ0.le)]
    calc (δ Nk (p.r D.i₀))⁻¹ ≤ (Nk ^ (-p.r D.i₀))⁻¹ := inv_anti₀ (by positivity) hδ1
      _ = Nk ^ p.r D.i₀ := by rw [Real.rpow_neg hN0.le, inv_inv]
      _ ≤ Nk ^ ⌈L⌉₊ := rpow_le_npow hN1 (hr₀L.trans hLc)
      _ ≤ Nk ^ A := hle _ hLA
  have t6 : |B D.w₀| ≤ Nk ^ A := by rw [abs_of_pos hBw]; exact hB.trans (hle _ (by omega))
  have t7 : |(B D.w₀)⁻¹| ≤ Nk ^ A := by
    rw [abs_of_pos (inv_pos.mpr hBw)]; exact hBinv.trans (hle _ (by omega))
  have hbin := hp.label_bin D.parent
  have t8 : |D.t₀| ≤ Nk ^ A := by
    have : |D.t₀| ≤ 1 := by
      show |(p.bin D.parent : ℝ) / (2 : ℝ) ^ p.T D.i₀| ≤ 1
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      have : ((p.bin D.parent : ℕ) : ℝ) < ((2 ^ p.T D.i₀ : ℕ) : ℝ) := by exact_mod_cast hbin
      push_cast at this; exact this.le
    linarith
  have t9 : |D.q₀| ≤ Nk ^ A := by
    have : |D.q₀| ≤ 1 := by
      show |((2 : ℝ) ^ p.T D.i₀)⁻¹| ≤ 1
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    linarith
  have t10 : |D.q₀⁻¹| ≤ Nk ^ A := by
    show |(((2 : ℝ) ^ p.T D.i₀)⁻¹)⁻¹| ≤ Nk ^ A
    rw [inv_inv, abs_of_pos (by positivity)]
    exact hT₀.trans (hle _ (by omega))
  have t11 : ‖p.center D.parent‖ + ‖p.velocity D.parent‖ ≤ Nk ^ A :=
    hc.2.1.trans (hle _ (by omega))
  have t12 : (∑ e : Fin 2, ∑ e' : Fin 2, (|D.D₀ e e'| + |D.D₀⁻¹ e e'|)) ≤ 8 * Nk ^ A := by
    rw [hD₀]
    have h1 := MajorFrame.entries_le hc.1
    have h2 := MajorFrame.inverse_entries_le hc.1
    have h3 := hc.2.2.1
    have hsplit : (∑ e : Fin 2, ∑ e' : Fin 2, (|MajorFrame.frame (p.frame D.parent) e e'| +
        |(MajorFrame.frame (p.frame D.parent))⁻¹ e e'|)) =
        (∑ e : Fin 2, ∑ e' : Fin 2, |MajorFrame.frame (p.frame D.parent) e e'|) +
        (∑ e : Fin 2, ∑ e' : Fin 2, |(MajorFrame.frame (p.frame D.parent))⁻¹ e e'|) := by
      simp only [Fin.sum_univ_two]; ring
    have hsplit2 : (∑ e : Fin 2, ∑ e' : Fin 2, (|p.frame D.parent e e'| +
        |(p.frame D.parent)⁻¹ e e'|)) =
        (∑ e : Fin 2, ∑ e' : Fin 2, |p.frame D.parent e e'|) +
        (∑ e : Fin 2, ∑ e' : Fin 2, |(p.frame D.parent)⁻¹ e e'|) := by
      simp only [Fin.sum_univ_two]; ring
    rw [hsplit]
    rw [hsplit2] at h3
    have : Nk ^ Mp ≤ Nk ^ A := hle _ (by omega)
    have hp1 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |p.frame D.parent e e'| := by positivity
    have hp2 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |(p.frame D.parent)⁻¹ e e'| := by positivity
    linarith
  have t13 : (∑ e : Fin 4, |(fun _ : Fin 4 => (0 : ℝ)) e|) = 0 := by simp
  rw [t13]
  calc _ ≤ 20 * Nk ^ A := by linarith
    _ ≤ Nk ^ (A + 5) := const_mul_pow_le hNk A 5 (by norm_num)
    _ ≤ Nk ^ budgetExp L ℓ Mp Mb := by
        apply pow_le_pow_right₀ hN1
        unfold budgetExp; omega

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
