import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

/-!
# One native decoder for a whole fine observation cell

Adapted from this LOT tree, o049, session x0147, commit 49f1ee1,
`Submission/Obl/k4_cap_class_terminal_charts/QuadraticCoefficientBounds.lean` and
`Submission/Obl/k4_cap_class_terminal_charts/NativeCellDecoder.lean`.
Changed here: the observation cells are anisotropic (time width `ρ₁`, planar width `ρ₂`), as
in the light-cell statement, instead of one common width.

Every midpoint group `(⌊y(s)/q⌋, ⌊P(x(s))/a⌋)` of an eligible trajectory with an incidence in a
fixed fine cell lies in one finite list depending only on the cell, of size `O(K³)`.
-/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set
open scoped BigOperators
open Submission.Obl.k4_scalar_coefficient_clustering (floor_scaled_error)

/-- A quadratic in four variables has at most 81 possibly nonzero monomials. -/
theorem quadratic_support_card_le (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) : P.support.card ≤ 81 := by
  classical
  let S : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ => Finset.range 3)
  have hcard : P.support.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun e : Fin 4 →₀ ℕ => fun i => e i)
    · intro e he
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Finset.mem_range.mpr
      change e i < 3
      have hi := (MvPolynomial.le_degreeOf_of_mem_support i he).trans
        ((MvPolynomial.degreeOf_le_totalDegree P i).trans hP)
      omega
    · intro e he f hf hef
      ext i
      exact congrFun hef i
  apply hcard.trans_eq
  simp [S, Fintype.card_piFinset]

/-- Bounded coefficients of a quadratic give a height bound on a bounded box. -/
theorem quadratic_eval_coefficient_bound (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hcoeff : ∀ e, |P.coeff e| ≤ C) (v : Fin 4 → ℝ) (hv : ∀ i, |v i| ≤ R) :
    |MvPolynomial.eval v P| ≤ 81 * C * R ^ 2 := by
  classical
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  rw [MvPolynomial.eval_eq']
  calc
    _ ≤ ∑ e ∈ P.support, |P.coeff e * ∏ i : Fin 4, v i ^ e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ P.support, C * R ^ 2 := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul (hcoeff e) _ (by positivity) hC
      have hdegree : ∑ i : Fin 4, e i ≤ 2 := by
        have hd := (MvPolynomial.le_totalDegree he).trans hP
        rw [Finsupp.sum_fintype e (fun _ n => n) (fun _ => rfl)] at hd
        exact hd
      calc
        (∏ i : Fin 4, |v i ^ e i|) = ∏ i : Fin 4, |v i| ^ e i := by simp only [abs_pow]
        _ ≤ ∏ i : Fin 4, R ^ e i := Finset.prod_le_prod₀
          (fun i _ => pow_nonneg (abs_nonneg _) _)
          (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hv i) _)
        _ = R ^ (∑ i : Fin 4, e i) := by rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ R ^ 2 := pow_le_pow_right₀ hR hdegree
    _ = (P.support.card : ℝ) * (C * R ^ 2) := by simp
    _ ≤ 81 * C * R ^ 2 := by
      have hc : (P.support.card : ℝ) ≤ 81 := by exact_mod_cast quadratic_support_card_le P hP
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ C * R ^ 2 by positivity)]

/-- The coefficient height gives an explicit variation bound on a small box. -/
theorem quadratic_coefficient_variation (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) {C R σ : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hcoeff : ∀ e, |P.coeff e| ≤ C)
    (v w : Fin 4 → ℝ) (hv : ∀ i, |v i| ≤ R) (hdist : ∀ i, |w i - v i| ≤ σ) :
    |MvPolynomial.eval w P - MvPolynomial.eval v P| ≤ 4131 * C * (R + 1) ^ 2 * σ := by
  let d : Fin 4 → ℝ := fun i => (w i - v i) / σ
  let f : ℝ → ℝ := fun t => MvPolynomial.eval (fun i => v i + t * d i) P
  have hd (i : Fin 4) : |d i| ≤ 1 := by
    dsimp [d]
    rw [abs_div, abs_of_pos hσ]
    exact (div_le_one hσ).mpr (hdist i)
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ 81 * C * (R + 1) ^ 2 := by
    intro t ht
    apply quadratic_eval_coefficient_bound P hP hC (by linarith) hcoeff
    intro i
    calc
      |v i + t * d i| ≤ |v i| + |t| * |d i| := by
        simpa only [abs_mul] using abs_add_le (v i) (t * d i)
      _ ≤ R + 1 * 1 := add_le_add (hv i)
        (mul_le_mul (by simpa only [abs_of_nonneg ht.1] using ht.2) (hd i)
          (abs_nonneg _) (by norm_num))
      _ = R + 1 := by ring
  have hquad := Submission.Obl.k4_eligibility_sign_description.Quadratic.mv_line P hP v d
  have hvar := bounded_quadratic_variation hquad hbound
    (show σ ∈ Icc (0 : ℝ) 1 from ⟨hσ.le, hσ1⟩) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have he : (fun i => v i + σ * d i) = w := by
    funext i
    dsimp [d]
    field_simp [hσ.ne']
    ring
  have hfσ : f σ = MvPolynomial.eval w P := by dsimp [f]; rw [he]
  have hf0 : f 0 = MvPolynomial.eval v P := by simp only [f, zero_mul, add_zero]
  calc
    _ ≤ 51 * (81 * C * (R + 1) ^ 2) * |σ - 0| := by
      simpa only [← hfσ, ← hf0] using hvar
    _ = _ := by rw [sub_zero, abs_of_pos hσ]; ring

/-- The widths of an anisotropic observation cell: time `ρ₁`, both planar coordinates `ρ₂`. -/
def cellScale (ρ₁ ρ₂ : ℝ) : Fin 3 → ℝ := ![ρ₁, ρ₂, ρ₂]

theorem cellScale_pos {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂) (i : Fin 3) :
    0 < cellScale ρ₁ ρ₂ i := by
  fin_cases i <;> simpa [cellScale]

theorem cellScale_le {ρ₁ ρ₂ : ℝ} (h₁₂ : ρ₁ ≤ ρ₂) (i : Fin 3) : cellScale ρ₁ ρ₂ i ≤ ρ₂ := by
  fin_cases i <;> simp [cellScale, h₁₂]

/-- The corner prediction of the native signal on a fine cell with a fixed hidden bin. -/
noncomputable def cellPrediction (P : MvPolynomial (Fin 4) ℝ) (B δ ρ₁ ρ₂ : ℝ)
    (c : Fin 3 → ℤ) (j : ℤ) : ℝ :=
  MvPolynomial.eval ![ρ₁ * (c 0 : ℝ), ρ₂ * (c 1 : ℝ), ρ₂ * (c 2 : ℝ), δ * (j : ℝ) / B] P

/-- Moving the exact observed base to its cell corner has a fixed polynomial cost. -/
theorem cell_prediction_variation (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (B δ : ℝ) {C R ρ₁ ρ₂ : ℝ}
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂1 : ρ₂ ≤ 1)
    (hcoeff : ∀ e, |P.coeff e| ≤ C) (v : Fin 4 → ℝ)
    (hv : ∀ i, |(Function.update v (3 : Fin 4) (δ * (⌊B * v 3 / δ⌋ : ℝ) / B)) i| ≤ R) :
    |hiddenSignalPrediction P B δ v - cellPrediction P B δ ρ₁ ρ₂
      (fun i : Fin 3 => ⌊v i.castSucc / cellScale ρ₁ ρ₂ i⌋) ⌊B * v 3 / δ⌋| ≤
      4131 * C * (R + 1) ^ 2 * ρ₂ := by
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le hρ₁₂
  have hd : ∀ i : Fin 4,
      |(![ρ₁ * (⌊v 0 / ρ₁⌋ : ℝ), ρ₂ * (⌊v 1 / ρ₂⌋ : ℝ), ρ₂ * (⌊v 2 / ρ₂⌋ : ℝ),
          δ * (⌊B * v 3 / δ⌋ : ℝ) / B] i) -
        (Function.update v (3 : Fin 4) (δ * (⌊B * v 3 / δ⌋ : ℝ) / B)) i| ≤ ρ₂ := by
    intro i
    fin_cases i
    · have h := floor_scaled_error hρ₁ (v 0)
      have h' : |ρ₁ * (⌊v 0 / ρ₁⌋ : ℝ) - v 0| ≤ ρ₂ := by
        rw [abs_sub_comm]; exact h.trans hρ₁₂
      simpa [Function.update] using h'
    · simpa [Function.update, abs_sub_comm] using floor_scaled_error hρ₂ (v 1)
    · simpa [Function.update, abs_sub_comm] using floor_scaled_error hρ₂ (v 2)
    · simpa using hρ₂.le
  have h := quadratic_coefficient_variation P hP hC hR hρ₂ hρ₂1 hcoeff _ _ hv hd
  have hpred : cellPrediction P B δ ρ₁ ρ₂
      (fun i : Fin 3 => ⌊v i.castSucc / cellScale ρ₁ ρ₂ i⌋) ⌊B * v 3 / δ⌋ =
      MvPolynomial.eval ![ρ₁ * (⌊v 0 / ρ₁⌋ : ℝ), ρ₂ * (⌊v 1 / ρ₂⌋ : ℝ),
        ρ₂ * (⌊v 2 / ρ₂⌋ : ℝ), δ * (⌊B * v 3 / δ⌋ : ℝ) / B] P := by
    simp [cellPrediction, cellScale]
  rw [hpred, hiddenSignalPrediction, abs_sub_comm]
  exact h

/-- One decoder for an entire fine cell, enlarged from the exact-observation decoder by one
spatial and one signal error unit. -/
noncomputable def cellDecoder (P : MvPolynomial (Fin 4) ℝ)
    (B δ q ρ₁ ρ₂ K : ℝ) (c : Fin 3 → ℤ) (j : ℤ) : Finset ((Fin 2 → ℤ) × ℤ) :=
  positionBinList (WithLp.toLp 2 ![ρ₂ * (c 1 : ℝ), ρ₂ * (c 2 : ℝ)]) q (K + 1) ×ˢ
    signalBinList (cellPrediction P B δ ρ₁ ρ₂ c j) δ ((53 * K + 1) + 1)

theorem cellDecoder_card (P : MvPolynomial (Fin 4) ℝ)
    (B δ q ρ₁ ρ₂ : ℝ) {K : ℝ} (hK : 0 ≤ K) (c : Fin 3 → ℤ) (j : ℤ) :
    ((cellDecoder P B δ q ρ₁ ρ₂ K c j).card : ℝ) ≤ (2 * K + 7) ^ 2 * (106 * K + 7) := by
  rw [cellDecoder, Finset.card_product, Nat.cast_mul]
  have hp := positionBinList_card
    (WithLp.toLp 2 ![ρ₂ * (c 1 : ℝ), ρ₂ * (c 2 : ℝ)]) q (show 0 ≤ K + 1 by positivity)
  have hs := signalBinList_card (cellPrediction P B δ ρ₁ ρ₂ c j) δ
    (show 0 ≤ (53 * K + 1) + 1 by positivity)
  have hp' : ((positionBinList
      (WithLp.toLp 2 ![ρ₂ * (c 1 : ℝ), ρ₂ * (c 2 : ℝ)]) q (K + 1)).card : ℝ) ≤
      (2 * K + 7) ^ 2 := by convert hp using 1 <;> congr 1 <;> ring
  have hs' : ((signalBinList (cellPrediction P B δ ρ₁ ρ₂ c j) δ
      ((53 * K + 1) + 1)).card : ℝ) ≤ 106 * K + 7 := by convert hs using 1 <;> ring
  exact mul_le_mul hp' hs' (Nat.cast_nonneg _) (sq_nonneg _)

/-- Every midpoint group compatible with an observation inside the fine cell lies in the
cell's one decoder. -/
theorem code_mem_cellDecoder (P : MvPolynomial (Fin 4) ℝ)
    (B : ℝ) {δ q ρ₁ ρ₂ K : ℝ} (hδ : 0 < δ) (hq : 0 < q) (hρ₂ : 0 < ρ₂)
    (hρ₂q : ρ₂ ≤ q) (hK : 0 ≤ K) (c : Fin 3 → ℤ) (j : ℤ)
    (base : Fin 3 → ℝ) (hcell : ∀ i : Fin 2, ⌊base i.succ / ρ₂⌋ = c i.succ)
    (y : Plane) (X pred : ℝ) (hy : ∀ i : Fin 2, |y i - base i.succ| ≤ K * q)
    (hX : |X - pred| ≤ 53 * K * δ)
    (hpred : |pred - cellPrediction P B δ ρ₁ ρ₂ c j| ≤ δ) :
    ((fun i : Fin 2 => ⌊y i / q⌋), ⌊X / δ⌋) ∈ cellDecoder P B δ q ρ₁ ρ₂ K c j := by
  apply Finset.mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro i
    apply floor_mem_signalBinList hq (show 0 ≤ K + 1 by positivity)
    have he := floor_scaled_error hρ₂ (base i.succ)
    rw [hcell i] at he
    have hc : (WithLp.toLp 2 ![ρ₂ * (c 1 : ℝ), ρ₂ * (c 2 : ℝ)] : Plane) i =
        ρ₂ * (c i.succ : ℝ) := by fin_cases i <;> rfl
    rw [hc]
    nlinarith [abs_sub_le (y i) (base i.succ) (ρ₂ * (c i.succ : ℝ)), hy i]
  · apply floor_mem_signalBinList hδ (show 0 ≤ 53 * K + 1 by positivity)
    nlinarith [abs_sub_le X pred (cellPrediction P B δ ρ₁ ρ₂ c j)]

/-- The native bounds imply the whole-cell decoder assertion once the fixed polynomial mesh is
fine enough for the coefficient bounds. -/
theorem native_midpoint_cell_list (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (l : Trajectory) {K B δ q ρ₁ ρ₂ s t C R : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hq : 0 < q) (hqδ : q ≤ δ) (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂q : ρ₂ ≤ q)
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hcoeff : ∀ e, |P.coeff e| ≤ C)
    (hrep : ∀ i, |(Function.update (graphPoint l t) (3 : Fin 4)
      (δ * (⌊B * graphPoint l t 3 / δ⌋ : ℝ) / B)) i| ≤ R)
    (hmesh : 4131 * C * (R + 1) ^ 2 * ρ₂ ≤ δ)
    (hV : ‖planarVelocity l‖ ≤ K)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (graphPoint l u) P| ≤ K)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hdt : |s - t| ≤ q)
    (hfirst : |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B)
    (hsecond : |MvPolynomial.eval (graphPoint l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2) :
    midpointGroupCode P s q δ l.2 ∈ cellDecoder P B δ q ρ₁ ρ₂ K
      (fun i : Fin 3 => ⌊graphPoint l t i.castSucc / cellScale ρ₁ ρ₂ i⌋)
      ⌊B * graphPoint l t 3 / δ⌋ := by
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le hρ₁₂
  have hp := (cell_prediction_variation P hP B δ hC hR hρ₁ hρ₁₂
    (hρ₂q.trans (hqδ.trans hδ1)) hcoeff (graphPoint l t) hrep).trans hmesh
  have hsecond' : |MvPolynomial.eval (graphPoint l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤
        K * B ^ 2 / δ := by
    apply hsecond.trans
    apply (le_div_iff₀ hδ).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1 (mul_nonneg hK (sq_nonneg B))
  have hX := native_midpoint_prediction_error P hP l hK hB hδ hbound hs ht hdt hfirst hsecond'
  have hX' : |MvPolynomial.eval (graphPoint l s) P -
      hiddenSignalPrediction P B δ (graphPoint l t)| ≤ 53 * K * δ := by
    apply hX.trans
    nlinarith [mul_le_mul_of_nonneg_left hqδ (show 0 ≤ 51 * K by positivity)]
  have hy : ∀ i : Fin 2, |planarPoint l s i - graphPoint l t i.succ.castSucc| ≤ K * q := by
    intro i
    have he : graphPoint l t i.succ.castSucc = planarPoint l t i := by fin_cases i <;> rfl
    rw [he]
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (planarPoint l s - planarPoint l t) i).trans
        (planarPoint_variation hV hdt)
  have hcell : ∀ i : Fin 2, ⌊graphPoint l t i.succ.castSucc / ρ₂⌋ =
      ⌊graphPoint l t i.succ.castSucc / cellScale ρ₁ ρ₂ i.succ⌋ := by
    intro i
    fin_cases i <;> rfl
  exact code_mem_cellDecoder P B hδ hq hρ₂ hρ₂q hK _ _
    (fun i : Fin 3 => graphPoint l t i.castSucc) hcell
    (planarPoint l s) (MvPolynomial.eval (graphPoint l s) P)
    (hiddenSignalPrediction P B δ (graphPoint l t)) hy hX' hp

end Submission.Obl.k4_horizon_chart_assembly

namespace Submission.Obl.k4_horizon_chart_assembly

open Set

/-- The hidden-bin representative has the support bound plus the reciprocal scale.
(Adapted from x0147, o049, 49f1ee1, `NativeCellDecoder.lean`.) -/
theorem hidden_representative_coord_bound (v : Fin 4 → ℝ) {B δ R : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hv : ∀ i, |v i| ≤ R) :
    ∀ i, |(Function.update v (3 : Fin 4) (δ * (⌊B * v 3 / δ⌋ : ℝ) / B)) i| ≤ R + B⁻¹ := by
  intro i
  by_cases hi : i = 3
  · subst i
    simp only [Function.update_self]
    have hs : |B * v 3| ≤ B * R := by
      rw [abs_mul, abs_of_pos hB]
      exact mul_le_mul_of_nonneg_left (hv 3) hB.le
    have hc := signal_bin_center_bound hs hδ
    rw [abs_div, abs_of_pos hB]
    apply (div_le_div_of_nonneg_right hc hB.le).trans
    apply (div_le_iff₀ hB).mpr
    field_simp
    linarith
  · rw [Function.update_of_ne hi]
    exact (hv i).trans (le_add_of_nonneg_right (inv_nonneg.mpr hB.le))

/-- Graph points of a trajectory with bounded coefficients, at times in `[0,1]`.
(Adapted from x0147, o049, 49f1ee1, `NativeCellDecoder.lean`.) -/
theorem graphPoint_coord_bound {S : ℝ} (hS : 1 ≤ S) (l : Trajectory)
    (hl : ∀ i, |l.2 i| ≤ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ i, |graphPoint l t i| ≤ 2 * S := by
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hp (i j : Fin 6) : |l.2 i + t * l.2 j| ≤ 2 * S := by
    calc
      _ ≤ |l.2 i| + |t| * |l.2 j| := by
        simpa only [abs_mul] using abs_add_le (l.2 i) (t * l.2 j)
      _ ≤ S + 1 * S := add_le_add (hl i)
        (mul_le_mul ht' (hl j) (abs_nonneg _) (by norm_num))
      _ = 2 * S := by ring
  intro i
  fin_cases i
  · change |t| ≤ 2 * S
    exact ht'.trans (by linarith)
  · exact hp 0 3
  · exact hp 1 4
  · exact hp 2 5

end Submission.Obl.k4_horizon_chart_assembly
