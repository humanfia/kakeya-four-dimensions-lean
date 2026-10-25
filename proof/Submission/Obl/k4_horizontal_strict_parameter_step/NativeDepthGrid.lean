import Submission.Obl.k4_horizontal_strict_parameter_step.NativeWidthCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.ScalarSupportGrid

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set

noncomputable section

/-- A finite grid of original native depths covers all normalized widths
above the requested floor. Every depth stays in the same compact interval. -/
structure NativeDepthGrid (N s E : ℝ) where
  J : ℕ
  depth : Fin (J + 1) → ℝ
  depth_mem : ∀ i, s ≤ depth i ∧ depth i ≤ s + E
  width_eq : ∀ i, N ^ (-depth i) / N ^ (-s) = (1 / 2 : ℝ) ^ (i : ℕ)
  approx : ∀ w : ℝ, N ^ (-E) ≤ w → w ≤ 1 →
    ∃ i, w ≤ N ^ (-depth i) / N ^ (-s) ∧ N ^ (-depth i) / N ^ (-s) ≤ 2 * w

theorem exists_native_depth_grid {N s E : ℝ} (hN : 1 < N) (hE : 0 ≤ E) :
    Nonempty (NativeDepthGrid N s E) := by
  have hNp : 0 < N := by linarith
  have hζ : 0 < N ^ (-E) := Real.rpow_pos_of_pos hNp _
  have hζ1 : N ^ (-E) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
  obtain ⟨J, hJ, hJ'⟩ := exists_nat_pow_near_of_lt_one hζ hζ1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hgrid (i : Fin (J + 1)) : N ^ (-E) ≤ (1 / 2 : ℝ) ^ (i : ℕ) ∧
      (1 / 2 : ℝ) ^ (i : ℕ) ≤ 1 := by
    refine ⟨hJ'.trans ?_, pow_le_one₀ (by norm_num) (by norm_num)⟩
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hex (i : Fin (J + 1)) : ∃ e : ℝ, 0 ≤ e ∧ e ≤ E ∧
      N ^ (-e) = (1 / 2 : ℝ) ^ (i : ℕ) :=
    exists_bounded_width_exponent hN (hgrid i).1 (hgrid i).2
  choose e he0 heE heq using hex
  have hwidth (i : Fin (J + 1)) : N ^ (-(s + e i)) / N ^ (-s) =
      (1 / 2 : ℝ) ^ (i : ℕ) := by
    rw [neg_add, Real.rpow_add hNp]
    have ha : N ^ (-s) ≠ 0 := (Real.rpow_pos_of_pos hNp _).ne'
    rw [mul_div_cancel_left₀ _ ha, heq i]
  refine ⟨{
    J := J
    depth := fun i => s + e i
    depth_mem := fun i => ⟨by linarith [he0 i], by linarith [heE i]⟩
    width_eq := hwidth
    approx := ?_ }⟩
  intro w hw hw1
  obtain ⟨i, hi, hwi⟩ := exists_nat_pow_near_of_lt_one (hζ.trans_le hw) hw1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hiJ : i ≤ J := by
    by_contra hn
    have hpow : (1 / 2 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ (J + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  refine ⟨⟨i, by omega⟩, ?_, ?_⟩
  · simpa only [hwidth] using hwi
  · rw [hwidth]
    rw [pow_succ] at hi
    linarith

namespace NativeDepthGrid

/-- The unit normalized width is the unchanged parent depth. -/
theorem depth_zero {N s E : ℝ} (g : NativeDepthGrid N s E) (hN : 1 < N) :
    g.depth 0 = s := by
  have hNp : 0 < N := by linarith
  have hw := g.width_eq 0
  simp only [Fin.val_zero, pow_zero] at hw
  have heq : N ^ (-g.depth 0) = N ^ (-s) := by
    simpa only [one_mul] using (div_eq_iff (Real.rpow_pos_of_pos hNp (-s)).ne').mp hw
  have hleft := (Real.rpow_le_rpow_left_iff hN).mp heq.le
  have hright := (Real.rpow_le_rpow_left_iff hN).mp heq.symm.le
  linarith

/-- Once the finite native levels have support, the full real width range
costs only the fixed comparable-bin factor. -/
theorem scalar_support {Ω : Type*} {N s E K d : ℝ}
    (g : NativeDepthGrid N s E) (hN : 0 < N) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (A : Set (Ω × ℝ)) (value : Ω → ℝ → ℝ)
    (hsupport : ∀ t : ℝ, ∀ i : Fin (g.J + 1), ∃ C : Finset ℤ,
      (C.card : ℝ) ≤ K * (N ^ (-g.depth i) / N ^ (-s)) ^ (-d) ∧
      ∀ l, (l, t) ∈ A → ⌊value l t / (N ^ (-g.depth i) / N ^ (-s))⌋ ∈ C) :
    ∀ t w : ℝ, N ^ (-E) ≤ w → w ≤ 1 → ∃ C : Finset ℤ,
      (C.card : ℝ) ≤ 6 * K * w ^ (-d) ∧
      ∀ l, (l, t) ∈ A → ⌊value l t / w⌋ ∈ C := by
  exact scalar_support_from_comparable_grid A value
    (fun i => N ^ (-g.depth i) / N ^ (-s))
    (Real.rpow_pos_of_pos hN _) hK hd
    (fun i => div_pos (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _))
    g.approx hsupport

end NativeDepthGrid

end

end Submission.Obl.k4_horizontal_strict_parameter_step
