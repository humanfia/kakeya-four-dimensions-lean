/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameChain.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FramePasses

/-!
# Telescoping the fine passes along ancestor chains

A residual label's affine part is its root ancestor's affine part plus the
differences along its ancestor chain. The crude pass bounds the root, the fine
passes bound the differences; box membership turns the box-adapted bounds into
the pointwise sheared bounds of the atlas.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

theorem Frame.resq_zero (f : Frame D k s₀ U') : f.resq 0 = 1 := by
  simp [Frame.resq, Frame.resT, Frame.T₀]

/-- Box-adapted slope bounds give the pointwise sheared bounds at a point of
the box. -/
theorem sheared_of_box {q Zc tc Z t X Bx : ℝ} {L : Fin 4 → ℝ} (hq : 0 < q) (hBx : 0 ≤ Bx)
    (h1 : q * |L 1 - Zc * L 3| ≤ X) (h2 : q * |L 2 + tc * L 3| ≤ X) (h3 : q ^ 2 * |L 3| ≤ X)
    (hZ : |Z - Zc| ≤ Bx * q) (ht : |t - tc| ≤ q) :
    |L 1 - Z * L 3| + |L 2 + t * L 3| ≤ (3 + Bx) * X / q := by
  rw [le_div_iff₀ hq]
  have a1 : |L 1 - Z * L 3| ≤ |L 1 - Zc * L 3| + |Z - Zc| * |L 3| := by
    have := abs_add_le (L 1 - Zc * L 3) (-((Z - Zc) * L 3))
    rw [abs_neg, abs_mul] at this
    calc |L 1 - Z * L 3| = |(L 1 - Zc * L 3) + -((Z - Zc) * L 3)| := by congr 1; ring
      _ ≤ _ := this
  have a2 : |L 2 + t * L 3| ≤ |L 2 + tc * L 3| + |t - tc| * |L 3| := by
    have := abs_add_le (L 2 + tc * L 3) ((t - tc) * L 3)
    rw [abs_mul] at this
    calc |L 2 + t * L 3| = |(L 2 + tc * L 3) + (t - tc) * L 3| := by congr 1; ring
      _ ≤ _ := this
  have b1 : q * (|Z - Zc| * |L 3|) ≤ Bx * X := by
    calc q * (|Z - Zc| * |L 3|) ≤ q * (Bx * q * |L 3|) := by gcongr
      _ = Bx * (q ^ 2 * |L 3|) := by ring
      _ ≤ Bx * X := by gcongr
  have b2 : q * (|t - tc| * |L 3|) ≤ X := by
    calc q * (|t - tc| * |L 3|) ≤ q * (q * |L 3|) := by gcongr
      _ = q ^ 2 * |L 3| := by ring
      _ ≤ X := h3
  have c1 := mul_le_mul_of_nonneg_left a1 hq.le
  have c2 := mul_le_mul_of_nonneg_left a2 hq.le
  nlinarith

/-- Box-adapted slope bounds bound the coefficients. -/
theorem coeff_sum_le_of_box {q Zc tc B X : ℝ} {L : Fin 4 → ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hZ : |Zc| ≤ B) (ht : |tc| ≤ B) (hX : 0 ≤ X)
    (h1 : q * |L 1 - Zc * L 3| ≤ X) (h2 : q * |L 2 + tc * L 3| ≤ X) (h3 : q ^ 2 * |L 3| ≤ X) :
    |L 1| + |L 2| + |L 3| ≤ 3 * (1 + B) * X / q ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) hZ
  have a1 : |L 1| ≤ |L 1 - Zc * L 3| + |Zc| * |L 3| := by
    have := abs_add_le (L 1 - Zc * L 3) (Zc * L 3)
    rw [abs_mul] at this
    calc |L 1| = |(L 1 - Zc * L 3) + Zc * L 3| := by congr 1; ring
      _ ≤ _ := this
  have a2 : |L 2| ≤ |L 2 + tc * L 3| + |tc| * |L 3| := by
    have := abs_add_le (L 2 + tc * L 3) (-(tc * L 3))
    rw [abs_neg, abs_mul] at this
    calc |L 2| = |(L 2 + tc * L 3) + -(tc * L 3)| := by congr 1; ring
      _ ≤ _ := this
  have b1 : q ^ 2 * |L 1 - Zc * L 3| ≤ X := by
    calc q ^ 2 * |L 1 - Zc * L 3| = q * (q * |L 1 - Zc * L 3|) := by ring
      _ ≤ 1 * X := mul_le_mul hq1 h1 (by positivity) zero_le_one
      _ = X := one_mul _
  have b2 : q ^ 2 * |L 2 + tc * L 3| ≤ X := by
    calc q ^ 2 * |L 2 + tc * L 3| = q * (q * |L 2 + tc * L 3|) := by ring
      _ ≤ 1 * X := mul_le_mul hq1 h2 (by positivity) zero_le_one
      _ = X := one_mul _
  have b3 : q ^ 2 * (|Zc| * |L 3|) ≤ B * X := by
    calc q ^ 2 * (|Zc| * |L 3|) = |Zc| * (q ^ 2 * |L 3|) := by ring
      _ ≤ B * X := mul_le_mul hZ h3 (by positivity) hB
  have b4 : q ^ 2 * (|tc| * |L 3|) ≤ B * X := by
    calc q ^ 2 * (|tc| * |L 3|) = |tc| * (q ^ 2 * |L 3|) := by ring
      _ ≤ B * X := mul_le_mul ht h3 (by positivity) hB
  have c1 := mul_le_mul_of_nonneg_left a1 (sq_nonneg q)
  have c2 := mul_le_mul_of_nonneg_left a2 (sq_nonneg q)
  nlinarith

theorem FrameGood.abs_Z_sub_boxZ (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) {p : α × ℝ} (hp : p ∈ f.labelSet h i) :
    |f.resBase p 1 - f.boxZ h i| ≤ 13 * D.K k ^ 4 * K₂ ^ 2 * f.resq h := by
  have hb := hg.box_mem hh i p.1 hp.1 p.2 hp.2 1
  have hq := f.resq_pos h
  change |(f.resBase p 1 - f.boxZ h i) / f.resq h| ≤ _ at hb
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq] at hb
  exact hb

theorem FrameGood.abs_t_sub_resMid (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ}
    (i : Fin (f.retained h).card) {p : α × ℝ} (hp : p ∈ f.labelSet h i) :
    |f.resBase p 0 - f.resMid h i| ≤ f.resq h := by
  have := f.abs_sub_resMid h i hp.2
  have hq := f.resq_pos h
  exact this.trans (by linarith)

theorem FrameGood.abs_boxZ (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) : |f.boxZ h i| ≤ boxK (D.K k) K₂ := by
  have hK : 1 ≤ D.K k := hg.K_ge
  have hK₂ : 1 ≤ K₂ := hg.K₂_ge
  have hmid := f.resMid_mem h i
  have hK4 : D.K k ^ 2 ≤ D.K k ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hK₂2 : K₂ ≤ K₂ ^ 2 := le_self_pow₀ hK₂ (by norm_num)
  have h0 := hg.res_cbound hh i 0
  have h1 := hg.res_cbound hh i 1
  calc |f.boxZ h i| ≤ |(f.level h).c i 0| + |f.resMid h i| * |(f.level h).c i 1| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ 20 * D.K k ^ 2 * K₂ + 1 * (20 * D.K k ^ 2 * K₂) := by
        gcongr
        · rw [abs_of_nonneg hmid.1]; exact hmid.2
    _ ≤ boxK (D.K k) K₂ := by
        unfold boxK
        have : D.K k ^ 2 * K₂ ≤ D.K k ^ 4 * K₂ ^ 2 :=
          mul_le_mul hK4 hK₂2 (by linarith) (by positivity)
        nlinarith

theorem FrameGood.abs_resMid (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ}
    (i : Fin (f.retained h).card) : |f.resMid h i| ≤ boxK (D.K k) K₂ := by
  have hmid := f.resMid_mem h i
  have := one_le_boxK hg.K_ge hg.K₂_ge
  rw [abs_of_nonneg hmid.1]
  linarith [hmid.2]

/-- The chain of fine passes. -/
theorem FrameGood.slope_chain (hg : FrameGood f Rk θ K₂ e₀') {X₀ A₂ W1 W3 : ℝ}
    (hX₀ : 0 ≤ X₀) (hA₂ : 0 ≤ A₂)
    (h0 : ∀ i : Fin (f.retained 0).card,
      f.resq 0 * |f.labelL 0 i 1 - f.boxZ 0 i * f.labelL 0 i 3| ≤ X₀ ∧
      f.resq 0 * |f.labelL 0 i 2 + f.resMid 0 i * f.labelL 0 i 3| ≤ X₀ ∧
      f.resq 0 ^ 2 * |f.labelL 0 i 3| ≤ X₀)
    (hstep : ∀ (h : ℕ) (hh : h < f.m) (i : Fin (f.retained (h + 1)).card),
      f.resq (h + 1) * |(f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 1 -
          f.boxZ (h + 1) i * (f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 3| ≤
          A₂ * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m)))) ∧
        f.resq (h + 1) * |(f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 2 +
          f.resMid (h + 1) i * (f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 3| ≤
          A₂ * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m)))) ∧
        f.resq (h + 1) ^ 2 * |(f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 3| ≤
          A₂ * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m)))))
    {h' : ℕ} (hh' : h' ≤ f.m)
    (hW3 : ∀ h < h', A₂ * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m)))) /
      f.resq (h + 1) ^ 2 ≤ W3)
    (hW1 : ∀ h < h', (3 + 13 * D.K k ^ 4 * K₂ ^ 2) *
      (A₂ * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m))))) / f.resq (h + 1) ≤ W1) :
    ∀ h ≤ h', ∀ i : Fin (f.retained h).card,
      |f.labelL h i 3| ≤ X₀ + h * W3 ∧
      ∀ p ∈ f.labelSet h i, |f.labelL h i 1 - f.resBase p 1 * f.labelL h i 3| +
        |f.labelL h i 2 + f.resBase p 0 * f.labelL h i 3| ≤
          (3 + 13 * D.K k ^ 4 * K₂ ^ 2) * X₀ + h * W1 := by
  have hK : 1 ≤ D.K k := hg.K_ge
  have hBx : 0 ≤ 13 * D.K k ^ 4 * K₂ ^ 2 := by positivity
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  intro h
  induction h with
  | zero =>
    intro _ i
    obtain ⟨h1, h2, h3⟩ := h0 i
    rw [Frame.resq_zero] at h1 h2 h3
    refine ⟨by simpa using h3, fun p hp => ?_⟩
    have hs := sheared_of_box (q := 1) one_pos hBx (by simpa using h1) (by simpa using h2)
      (by simpa using h3) (by simpa [Frame.resq_zero] using hg.abs_Z_sub_boxZ (Nat.zero_le _) i hp)
      (by simpa [Frame.resq_zero] using hg.abs_t_sub_resMid i hp)
    simpa using hs
  | succ h ih =>
    intro hh i
    have hlt : h < h' := hh
    have hm : h < f.m := lt_of_lt_of_le hlt hh'
    set u := f.upLabel hg hm i
    set Δ := f.labelL (h + 1) i - f.labelL h u with hΔ
    have hsplit : f.labelL (h + 1) i = f.labelL h u + Δ := by rw [hΔ]; abel
    obtain ⟨d1, d2, d3⟩ := hstep h hm i
    obtain ⟨ih3, ih1⟩ := ih hlt.le u
    have hq := f.resq_pos (h + 1)
    set X := A₂ * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m)))) with hX
    have hX0 : 0 ≤ X := by have := hg.H_ge; positivity
    have hΔ3 : |Δ 3| ≤ X / f.resq (h + 1) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have e3 : f.labelL (h + 1) i 3 = f.labelL h u 3 + Δ 3 := by rw [hsplit]; rfl
    have e1 : f.labelL (h + 1) i 1 = f.labelL h u 1 + Δ 1 := by rw [hsplit]; rfl
    have e2 : f.labelL (h + 1) i 2 = f.labelL h u 2 + Δ 2 := by rw [hsplit]; rfl
    refine ⟨?_, fun p hp => ?_⟩
    · rw [e3]
      have := hW3 h hlt
      calc |f.labelL h u 3 + Δ 3| ≤ |f.labelL h u 3| + |Δ 3| := abs_add_le _ _
        _ ≤ X₀ + h * W3 + W3 := by linarith
        _ = X₀ + ((h + 1 : ℕ) : ℝ) * W3 := by push_cast; ring
    · have hpu : p ∈ f.labelSet h u := hg.labelSet_sub_up hm i hp
      have ihp := ih1 p hpu
      have hs := sheared_of_box hq hBx d1 d2 d3 (hg.abs_Z_sub_boxZ hm i hp)
        (hg.abs_t_sub_resMid i hp)
      have hw := hW1 h hlt
      have hs' : |Δ 1 - f.resBase p 1 * Δ 3| + |Δ 2 + f.resBase p 0 * Δ 3| ≤ W1 := by
        refine hs.trans (le_of_eq_of_le ?_ hw)
        ring
      rw [e1, e2, e3]
      have t1 : |f.labelL h u 1 + Δ 1 - f.resBase p 1 * (f.labelL h u 3 + Δ 3)| ≤
          |f.labelL h u 1 - f.resBase p 1 * f.labelL h u 3| +
            |Δ 1 - f.resBase p 1 * Δ 3| := by
        calc _ = |(f.labelL h u 1 - f.resBase p 1 * f.labelL h u 3) +
              (Δ 1 - f.resBase p 1 * Δ 3)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      have t2 : |f.labelL h u 2 + Δ 2 + f.resBase p 0 * (f.labelL h u 3 + Δ 3)| ≤
          |f.labelL h u 2 + f.resBase p 0 * f.labelL h u 3| +
            |Δ 2 + f.resBase p 0 * Δ 3| := by
        calc _ = |(f.labelL h u 2 + f.resBase p 0 * f.labelL h u 3) +
              (Δ 2 + f.resBase p 0 * Δ 3)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      have : (3 + 13 * D.K k ^ 4 * K₂ ^ 2) * X₀ + (h : ℝ) * W1 + W1 =
          (3 + 13 * D.K k ^ 4 * K₂ ^ 2) * X₀ + ((h + 1 : ℕ) : ℝ) * W1 := by push_cast; ring
      linarith

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
