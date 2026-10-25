import Mathlib
import Submission.Obl.k4_finite_narrowness_path_improvement.PathFacts

/-!
# Velocity cells of narrow charts

A chart frame confines the velocities of its lines to an ellipse (`gchart_velocity`); with
narrowness `|det Q| 4^T ≤ θ` the ellipse meets at most `(4 κ² / ε + 2)(4 κ √θ / ε + 4)` velocity
cells of side `ε` (`gchart_cells`), the count used with the angular cap in paper Lemma
a01:largest-axis and for the vacuity of X when `l > 0` and `S > 1`.
`exists_cells_tilted` counts cells met by a tilted box, `frame_cells` by a frame.
-/

namespace Submission.Obl.k4_finite_narrowness_path_improvement

/-- Integers between two reals. -/
theorem card_Icc_floor_le (x y : ℝ) (h : x ≤ y) :
    ((Finset.Icc ⌊x⌋ ⌊y⌋).card : ℝ) ≤ y - x + 2 := by
  rw [Int.card_Icc]
  have h1 : (⌊y⌋ + 1 - ⌊x⌋ : ℤ) ≥ 0 := by
    have := Int.floor_le_floor h
    omega
  have hc : (((⌊y⌋ + 1 - ⌊x⌋).toNat : ℕ) : ℝ) = ((⌊y⌋ + 1 - ⌊x⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
  rw [hc]
  push_cast
  have := Int.floor_le y
  have := Int.lt_floor_add_one x
  linarith

/-- Cells of side `ε` met by a tilted box `|w₀ - a| ≤ R`, `|w₁ - b - λ (w₀ - a)| ≤ W`. -/
theorem exists_cells_tilted (a b lam R W ε : ℝ) (hε : 0 < ε) (hR : 0 ≤ R) (hW : 0 ≤ W) :
    ∃ V : Finset (Fin 2 → ℤ),
      (V.card : ℝ) ≤ (2 * R / ε + 2) * (2 * W / ε + 2 * |lam| + 2) ∧
      ∀ w₀ w₁ : ℝ, |w₀ - a| ≤ R → |w₁ - b - lam * (w₀ - a)| ≤ W →
        (![⌊w₀ / ε⌋, ⌊w₁ / ε⌋] : Fin 2 → ℤ) ∈ V := by
  classical
  set lo : ℤ → ℝ := fun i => (b + lam * (i * ε - a) - W - |lam| * ε) / ε with hlo
  set hi : ℤ → ℝ := fun i => (b + lam * (i * ε - a) + W + |lam| * ε) / ε with hhi
  refine ⟨(Finset.Icc ⌊(a - R) / ε⌋ ⌊(a + R) / ε⌋).biUnion
    (fun i => (Finset.Icc ⌊lo i⌋ ⌊hi i⌋).image (fun k => (![i, k] : Fin 2 → ℤ))), ?_, ?_⟩
  · have hlohi : ∀ i, lo i ≤ hi i := by
      intro i
      simp only [hlo, hhi]
      apply div_le_div_of_nonneg_right _ hε.le
      nlinarith [abs_nonneg lam]
    have hfib : ∀ i, ((Finset.Icc ⌊lo i⌋ ⌊hi i⌋).card : ℝ) ≤ 2 * W / ε + 2 * |lam| + 2 := by
      intro i
      refine (card_Icc_floor_le _ _ (hlohi i)).trans (le_of_eq ?_)
      simp only [hlo, hhi]
      field_simp
      ring
    calc (((Finset.Icc ⌊(a - R) / ε⌋ ⌊(a + R) / ε⌋).biUnion _).card : ℝ)
        ≤ ((∑ i ∈ Finset.Icc ⌊(a - R) / ε⌋ ⌊(a + R) / ε⌋,
            ((Finset.Icc ⌊lo i⌋ ⌊hi i⌋).image (fun k => (![i, k] : Fin 2 → ℤ))).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ i ∈ Finset.Icc ⌊(a - R) / ε⌋ ⌊(a + R) / ε⌋,
            (((Finset.Icc ⌊lo i⌋ ⌊hi i⌋).image (fun k => (![i, k] : Fin 2 → ℤ))).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ i ∈ Finset.Icc ⌊(a - R) / ε⌋ ⌊(a + R) / ε⌋, (2 * W / ε + 2 * |lam| + 2) := by
          apply Finset.sum_le_sum
          intro i _
          have hci : (((Finset.Icc ⌊lo i⌋ ⌊hi i⌋).image
              (fun k => (![i, k] : Fin 2 → ℤ))).card : ℝ) ≤ (Finset.Icc ⌊lo i⌋ ⌊hi i⌋).card := by
            exact_mod_cast Finset.card_image_le
          exact hci.trans (hfib i)
      _ = ((Finset.Icc ⌊(a - R) / ε⌋ ⌊(a + R) / ε⌋).card : ℝ) * (2 * W / ε + 2 * |lam| + 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * R / ε + 2) * (2 * W / ε + 2 * |lam| + 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          refine (card_Icc_floor_le _ _ ?_).trans (le_of_eq ?_)
          · apply div_le_div_of_nonneg_right _ hε.le; linarith
          · field_simp; ring
  · intro w₀ w₁ h0 h1
    rw [Finset.mem_biUnion]
    refine ⟨⌊w₀ / ε⌋, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor <;> apply Int.floor_le_floor <;> apply div_le_div_of_nonneg_right _ hε.le <;>
        linarith [abs_le.mp h0]
    · rw [Finset.mem_image]
      refine ⟨⌊w₁ / ε⌋, ?_, rfl⟩
      rw [Finset.mem_Icc]
      have hi1 := Int.floor_le (w₀ / ε)
      have hi2 := Int.lt_floor_add_one (w₀ / ε)
      have hw0lo : (⌊w₀ / ε⌋ : ℝ) * ε ≤ w₀ := by
        have := mul_le_mul_of_nonneg_right hi1 hε.le
        rwa [div_mul_cancel₀ _ hε.ne'] at this
      have hw0hi : w₀ < ((⌊w₀ / ε⌋ : ℝ) + 1) * ε := by
        have := mul_lt_mul_of_pos_right hi2 hε
        rwa [div_mul_cancel₀ _ hε.ne'] at this
      have hlamdiff : |lam * (w₀ - a) - lam * ((⌊w₀ / ε⌋ : ℝ) * ε - a)| ≤ |lam| * ε := by
        rw [← mul_sub, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith
      have h1' := abs_le.mp h1
      have hd' := abs_le.mp hlamdiff
      constructor <;> apply Int.floor_le_floor <;> simp only [hlo, hhi] <;>
        apply div_le_div_of_nonneg_right _ hε.le <;> linarith

/-- Swapping the coordinates of the plane. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem swap2_mul_swap2 : swap2 * swap2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_swap2 : swap2.det = -1 := by simp [swap2, Matrix.det_fin_two]

/-- The frame bound in swapped coordinates. -/
theorem toEuclideanLin_swap_frame (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin (swap2 * Q)⁻¹ (Matrix.toEuclideanLin swap2 w) =
      Matrix.toEuclideanLin Q⁻¹ w := by
  have hs : swap2.det ≠ 0 := by rw [det_swap2]; norm_num
  rw [Matrix.mul_inv_rev, Matrix.toLpLin_mul_same, LinearMap.comp_apply, ← LinearMap.comp_apply
    (Matrix.toEuclideanLin swap2⁻¹), ← Matrix.toLpLin_mul_same,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs)]
  simp

end Submission.Obl.k4_finite_narrowness_path_improvement

namespace Submission.Obl.k4_finite_narrowness_path_improvement

theorem sqrt_sq_add_sq_le (x y : ℝ) : Real.sqrt (x ^ 2 + y ^ 2) ≤ |x| + |y| := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg x, abs_nonneg y, sq_abs x, sq_abs y, abs_mul_abs_self x,
    abs_mul_abs_self y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]

/-- Velocity cells of a frame when its first row is the larger one. -/
theorem frame_cells_major (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (hrow : Q 1 0 ^ 2 + Q 1 1 ^ 2 ≤ Q 0 0 ^ 2 + Q 0 1 ^ 2) (u : EuclideanSpace ℝ (Fin 2))
    {ρ σ₁ θ ε : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hsum : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ σ₁) (hdet : |Q.det| ≤ θ) :
    ∃ V : Finset (Fin 2 → ℤ),
      (V.card : ℝ) ≤ (2 * (ρ * σ₁) / ε + 2) * (2 * (ρ * Real.sqrt θ) / ε + 4) ∧
      ∀ w : EuclideanSpace ℝ (Fin 2), ‖Matrix.toEuclideanLin Q⁻¹ (w - u)‖ ≤ ρ →
        (fun j => ⌊w j / ε⌋) ∈ V := by
  set s₀ := Q 0 0 ^ 2 + Q 0 1 ^ 2 with hs₀
  set s₁ := Q 1 0 ^ 2 + Q 1 1 ^ 2 with hs₁
  have hdetf : Q.det = Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0 := Matrix.det_fin_two Q
  have hs0pos : 0 < s₀ := by
    rcases (add_nonneg (sq_nonneg (Q 0 0)) (sq_nonneg (Q 0 1))).lt_or_eq with h | h
    · exact h
    · exfalso
      have h00 : Q 0 0 = 0 := by nlinarith [sq_nonneg (Q 0 0), sq_nonneg (Q 0 1)]
      have h01 : Q 0 1 = 0 := by nlinarith [sq_nonneg (Q 0 0), sq_nonneg (Q 0 1)]
      exact hQ (by rw [hdetf, h00, h01]; ring)
  set lam := (Q 1 0 * Q 0 0 + Q 1 1 * Q 0 1) / s₀ with hlam
  have hR : Real.sqrt s₀ ≤ σ₁ := by
    refine (sqrt_sq_add_sq_le _ _).trans (le_trans ?_ hsum)
    simp only [Fin.sum_univ_two]
    linarith [abs_nonneg (Q 1 0), abs_nonneg (Q 1 1)]
  have hdet_le : |Q.det| ≤ s₀ := by
    rw [hdetf, abs_le]
    constructor <;> nlinarith [sq_nonneg (Q 0 0 - Q 1 1), sq_nonneg (Q 0 1 + Q 1 0),
      sq_nonneg (Q 0 0 + Q 1 1), sq_nonneg (Q 0 1 - Q 1 0)]
  have hW : Real.sqrt (Q.det ^ 2 / s₀) ≤ Real.sqrt θ := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hs0pos, ← sq_abs]
    calc |Q.det| ^ 2 = |Q.det| * |Q.det| := sq _
      _ ≤ θ * s₀ := mul_le_mul hdet hdet_le (abs_nonneg _) ((abs_nonneg _).trans hdet)
  have hlam1 : |lam| ≤ 1 := by
    rw [hlam, abs_div, abs_of_pos hs0pos, div_le_one hs0pos, abs_le]
    constructor <;> nlinarith [sq_nonneg (Q 1 0 * Q 0 1 - Q 1 1 * Q 0 0),
      sq_nonneg (Q 1 0 - Q 0 0), sq_nonneg (Q 1 1 - Q 0 1), sq_nonneg (Q 1 0 + Q 0 0),
      sq_nonneg (Q 1 1 + Q 0 1)]
  obtain ⟨V, hVcard, hVmem⟩ := exists_cells_tilted (u 0) (u 1) lam (ρ * σ₁)
    (ρ * Real.sqrt θ) ε hε (mul_nonneg hρ ((Real.sqrt_nonneg _).trans hR))
    (mul_nonneg hρ (Real.sqrt_nonneg _))
  refine ⟨V, hVcard.trans ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (by
      have := mul_nonneg hρ ((Real.sqrt_nonneg _).trans hR)
      positivity)
    linarith
  · intro w hw
    obtain ⟨h0, h1⟩ := tilted_box_of_frame Q hQ (w - u) hw hs0pos
    have hcell : (fun j => ⌊w j / ε⌋) = (![⌊w 0 / ε⌋, ⌊w 1 / ε⌋] : Fin 2 → ℤ) := by
      funext j; fin_cases j <;> rfl
    rw [hcell]
    apply hVmem
    · simp only [PiLp.sub_apply] at h0
      exact h0.trans (mul_le_mul_of_nonneg_left hR hρ)
    · simp only [PiLp.sub_apply] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hW hρ)

end Submission.Obl.k4_finite_narrowness_path_improvement

namespace Submission.Obl.k4_finite_narrowness_path_improvement

/-- Velocity cells of a frame: `‖Q⁻¹ (w - u)‖ ≤ ρ` meets at most
`(2 ρ σ₁ / ε + 2)(2 ρ √θ / ε + 4)` cells of side `ε`, where `Σ|Q| ≤ σ₁` and `|det Q| ≤ θ`. -/
theorem frame_cells (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (u : EuclideanSpace ℝ (Fin 2))
    {ρ σ₁ θ ε : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hsum : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ σ₁) (hdet : |Q.det| ≤ θ) :
    ∃ V : Finset (Fin 2 → ℤ),
      (V.card : ℝ) ≤ (2 * (ρ * σ₁) / ε + 2) * (2 * (ρ * Real.sqrt θ) / ε + 4) ∧
      ∀ w : EuclideanSpace ℝ (Fin 2), ‖Matrix.toEuclideanLin Q⁻¹ (w - u)‖ ≤ ρ →
        (fun j => ⌊w j / ε⌋) ∈ V := by
  by_cases hrow : Q 1 0 ^ 2 + Q 1 1 ^ 2 ≤ Q 0 0 ^ 2 + Q 0 1 ^ 2
  · exact frame_cells_major Q hQ hrow u hε hρ hsum hdet
  · set Q' := swap2 * Q with hQ'
    have e00 : Q' 0 0 = Q 1 0 := by
      rw [hQ', Matrix.mul_apply, Fin.sum_univ_two]; simp [swap2]
    have e01 : Q' 0 1 = Q 1 1 := by
      rw [hQ', Matrix.mul_apply, Fin.sum_univ_two]; simp [swap2]
    have e10 : Q' 1 0 = Q 0 0 := by
      rw [hQ', Matrix.mul_apply, Fin.sum_univ_two]; simp [swap2]
    have e11 : Q' 1 1 = Q 0 1 := by
      rw [hQ', Matrix.mul_apply, Fin.sum_univ_two]; simp [swap2]
    have hdet' : Q'.det = -Q.det := by rw [hQ', Matrix.det_mul, det_swap2]; ring
    have hQ'0 : Q'.det ≠ 0 := by rw [hdet']; exact neg_ne_zero.mpr hQ
    have hrow' : Q' 1 0 ^ 2 + Q' 1 1 ^ 2 ≤ Q' 0 0 ^ 2 + Q' 0 1 ^ 2 := by
      rw [e00, e01, e10, e11]; linarith
    have hsum' : (∑ e : Fin 2, ∑ e' : Fin 2, |Q' e e'|) ≤ σ₁ := by
      refine le_trans (le_of_eq ?_) hsum
      simp only [Fin.sum_univ_two, e00, e01, e10, e11]
      ring
    have hdetQ' : |Q'.det| ≤ θ := by rw [hdet', abs_neg]; exact hdet
    obtain ⟨V', hV'card, hV'mem⟩ := frame_cells_major Q' hQ'0 hrow'
      (Matrix.toEuclideanLin swap2 u) hε hρ hsum' hdetQ'
    refine ⟨V'.image (fun c => (![c 1, c 0] : Fin 2 → ℤ)), ?_, ?_⟩
    · have hci : ((V'.image (fun c => (![c 1, c 0] : Fin 2 → ℤ))).card : ℝ) ≤ V'.card := by
        exact_mod_cast Finset.card_image_le
      exact hci.trans hV'card
    · intro w hw
      have hw' : ‖Matrix.toEuclideanLin Q'⁻¹ (Matrix.toEuclideanLin swap2 w -
          Matrix.toEuclideanLin swap2 u)‖ ≤ ρ := by
        rw [← map_sub, hQ', toEuclideanLin_swap_frame]
        exact hw
      have hmem := hV'mem _ hw'
      rw [Finset.mem_image]
      refine ⟨_, hmem, ?_⟩
      funext j
      fin_cases j <;> simp [swap2, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two]

/-- Velocity cells of a chart: with narrowness `|det Q| 4^T ≤ θ`, the velocities of the assigned
lines meet at most `(4 κ² / ε + 2)(4 κ √θ / ε + 4)` cells of side `ε`. -/
theorem gchart_cells {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex) {θ ε : ℝ}
    (hθ : |Q.det| * (4 : ℝ) ^ T ≤ θ) (hε : 0 < ε) (hκ : 0 ≤ κ) :
    ∃ V : Finset (Fin 2 → ℤ),
      (V.card : ℝ) ≤ (4 * κ ^ 2 / ε + 2) * (4 * κ * Real.sqrt θ / ε + 4) ∧
      ∀ l ∈ A, (fun j => ⌊(gv l) j / ε⌋) ∈ V := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have h4 : (4 : ℝ) ^ T = ((2 : ℝ) ^ T) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hQ := h.1
  have hQs := h.2.2.2.1
  have hdet : |Q.det| ≤ θ / (4 : ℝ) ^ T := by rw [le_div_iff₀ (by positivity)]; exact hθ
  obtain ⟨V, hV, hmem⟩ := frame_cells Q hQ u (ρ := 2 * κ * (2 : ℝ) ^ T) hε (by positivity)
    hQs hdet
  refine ⟨V, hV.trans (le_of_eq ?_), fun l hl => hmem _ (gchart_velocity h hl)⟩
  have hθ0 : 0 ≤ θ := (mul_nonneg (abs_nonneg _) (by positivity)).trans hθ
  rw [h4, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq h2.le]
  field_simp
  ring

end Submission.Obl.k4_finite_narrowness_path_improvement
