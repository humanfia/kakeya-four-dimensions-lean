-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.AncestorFullPrior, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/AncestorFullPrior.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorCoefficients
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.Interface

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set

noncomputable section

namespace AncestorSource

open ParentSource Native ParentSource.ParentSignal

/-- At the left endpoint, the entire original assignment lies in the
unsheared ancestor frame. No successful occurrence is needed. -/
theorem assigned_left_base_bound {W : ℕ} {p : ParentSource.Native.PathData W}
    {N L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
    {B : Fin W → ℝ} {f : ℝ → ℝ} {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) {l : Ln} (hl : l ∈ p.A b) :
    let h := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
    let t0 := (p.j b : ℝ) * h
    ‖h⁻¹ • (y l t0 - p.c b - t0 • p.u b)‖ ≤ p.κ ^ 2 := by
  let clock : ℝ := (2 : ℝ) ^ p.T (p.lev b)
  let h := clock⁻¹
  let t0 := (p.j b : ℝ) * h
  have hc : 0 < clock := by dsimp [clock]; positivity
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  let residual := y l t0 - p.c b - t0 • p.u b
  rcases hp.2.2.2.2.2.2.2 b with ⟨_, _, _, _, _, _, _, _, _, _, _, hfit, _⟩
  have ht0 : t0 ∈ Icc ((p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
      (((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) := by
    dsimp [t0, h, clock]
    constructor
    · exact le_of_eq (by ring)
    · rw [div_eq_mul_inv]
      nlinarith [inv_pos.mpr hc]
  have hpos : ‖Matrix.toEuclideanLin (p.Q b)⁻¹ residual‖ ≤ p.κ :=
    ((hfit l hl).2.2 t0 ht0).1
  have hbound := hp.denormalized_frame_operator_bound b
    (Matrix.toEuclideanLin (p.Q b)⁻¹ residual)
  change ‖clock • Matrix.toEuclideanLin (p.Q b)
    (Matrix.toEuclideanLin (p.Q b)⁻¹ residual)‖ ≤ _ at hbound
  rw [Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel _
    (hp.2.2.2.2.2.2.2 b).2.2.1, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hbound
  change ‖h⁻¹ • residual‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, show h⁻¹ = clock by simp [h], abs_of_pos hc]
  exact hbound.trans ((mul_le_mul_of_nonneg_left hpos hκ).trans_eq (pow_two _).symm)

/-- All seven unit-clock physical coefficients are bounded on every
assigned trajectory satisfying the original whole-parent and velocity bounds. -/
theorem assigned_clock_coefficients_bound {W : ℕ} {p : ParentSource.Native.PathData W}
    {N L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
    {B : Fin W → ℝ} {f : ℝ → ℝ} {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) {P : Po} (hP : P.totalDegree ≤ 2)
    {K Korig Borig : ℝ} (hK : 24 ≤ K) (hκ : p.κ ≤ K) (hOrig : Korig ≤ K)
    {l : Ln} (hl : l ∈ p.A b) (hgood : l ∈ ParentSignal.goodLines P Korig Borig)
    (hvel : ‖v l‖ ≤ Korig) :
    ∀ i, |clockPacketCoefficients P p b l i| ≤ K ^ 4 * (2 : ℝ) ^ p.T (p.lev b) := by
  let clock : ℝ := (2 : ℝ) ^ p.T (p.lev b)
  let h := clock⁻¹
  let t0 := (p.j b : ℝ) * h
  have hc : 0 < clock := by dsimp [clock]; positivity
  have hc1 : 1 ≤ clock := one_le_pow₀ (by norm_num)
  have hh : 0 < h := inv_pos.mpr hc
  have hh1 : h ≤ 1 := by simpa only [h, inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hc1
  have hj : (p.j b : ℝ) ≤ clock := by
    dsimp [clock]
    exact_mod_cast Nat.le_of_lt (hp.2.2.2.2.2.2.2 b).2.1
  have ht0 : t0 ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by dsimp [t0]; positivity, ?_⟩
    simpa only [t0, h, div_eq_mul_inv] using (div_le_one hc).mpr hj
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hOrig0 : 0 ≤ Korig := (norm_nonneg _).trans hvel
  have hκ0 : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hs := oldBlock_signal_coefficient_bounds hP hgood ht0 hh.le (p.c b) (p.u b)
  let C := oldPacketCoefficients P p b l
  have h0 : |C 0| ≤ K := hs.1.trans hOrig
  have h1 : |C 1| ≤ 24 * K := by
    refine hs.2.1.trans ?_
    calc
      _ ≤ 24 * K * 1 := by gcongr
      _ = _ := mul_one _
  have h2 : |C 2| ≤ 8 * K := by
    refine hs.2.2.trans ?_
    have hh2 : h ^ 2 ≤ 1 := by nlinarith
    calc
      _ ≤ 8 * K * 1 := by gcongr
      _ = _ := mul_one _
  let Y := h⁻¹ • (y l t0 - p.c b - t0 • p.u b)
  have hY : ‖Y‖ ≤ p.κ ^ 2 := assigned_left_base_bound hp b hl
  have h3 : |C 3| ≤ K ^ 2 := by
    have heq : C 3 = Y 0 := by
      simp [C, oldPacketCoefficients, oldBlockCoefficients, Y, y, x, t0, h, clock, div_eq_mul_inv]
      ring
    rw [heq]
    exact ((PiLp.norm_apply_le Y 0).trans hY).trans (by nlinarith)
  have h5 : |C 5| ≤ K ^ 2 := by
    have heq : C 5 = Y 1 := by
      simp [C, oldPacketCoefficients, oldBlockCoefficients, Y, y, x, t0, h, clock, div_eq_mul_inv]
      ring
    rw [heq]
    exact ((PiLp.norm_apply_le Y 1).trans hY).trans (by nlinarith)
  have h4 : |C 4| ≤ K := (PiLp.norm_apply_le (v l) 0).trans (hvel.trans hOrig)
  have h6 : |C 6| ≤ K := (PiLp.norm_apply_le (v l) 1).trans (hvel.trans hOrig)
  have hK4 : K ≤ K ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK1 (by norm_num : (1 : ℕ) ≤ 4)
  have hK24 : 24 * K ≤ K ^ 4 := by
    have hsq : 24 * K ≤ K ^ 2 := by nlinarith
    exact hsq.trans (pow_le_pow_right₀ hK1 (by norm_num : (2 : ℕ) ≤ 4))
  have hcoeff : ∀ i, |C i| ≤ K ^ 4 := by
    intro i
    fin_cases i
    · exact h0.trans hK4
    · exact h1.trans hK24
    · exact h2.trans ((by nlinarith : 8 * K ≤ 24 * K).trans hK24)
    · exact h3.trans (pow_le_pow_right₀ hK1 (by norm_num : (2 : ℕ) ≤ 4))
    · exact h4.trans hK4
    · exact h5.trans (pow_le_pow_right₀ hK1 (by norm_num : (2 : ℕ) ≤ 4))
    · exact h6.trans hK4
  exact scaleSignal_uniform_bound hc1 C hcoeff

end AncestorSource

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
