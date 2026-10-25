-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TrilinearKakeya.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TransversalKakeya

/-!
# The trilinear Kakeya inequality for a family of tubes

For a single family of `δ`-tubes `thickening δ (segment x (x + v))` in `ℝ³` with unit directions,
`trilinear_kakeya` bounds the integral over the unit ball of the square root of the number of
triples of tubes through a point whose directions are `θ`-transversal
(`θ ≤ |det (v i, v j, v k)|`) by `C θ^(-8) δ^(3-ε) n^(3/2)`.

The directions are sorted into cells of side `θ / (12 K)`.  For each triple of cells containing a
`θ`-transversal triple of directions, the explicit inverse `invMap` of the matrix of a
representative triple makes the three subfamilies nearly axis-parallel, so `capTriple` applies.
Cauchy–Schwarz over the cells finishes the proof.  This is the form of the multilinear Kakeya
theorem (with `δ^(-ε)` loss) used to find plane maps for extremal families.
-/

open MeasureTheory Set
open scoped ENNReal

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains.MK

/-- Determinant of the three vectors (rows) `a, b, c`. -/
def det3 (a b c : Fin 3 → ℝ) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- The matrix whose rows are the cross products `b × c`, `c × a`, `a × b`, divided by
`det3 a b c`; it is the inverse of the matrix with columns `a, b, c`. -/
noncomputable def invMat (a b c : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (det3 a b c)⁻¹ • !![b 1 * c 2 - b 2 * c 1, b 2 * c 0 - b 0 * c 2, b 0 * c 1 - b 1 * c 0;
    c 1 * a 2 - c 2 * a 1, c 2 * a 0 - c 0 * a 2, c 0 * a 1 - c 1 * a 0;
    a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- The corresponding continuous linear map. -/
noncomputable def invMap (a b c : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (invMat a b c))

lemma invMap_apply (a b c q : Fin 3 → ℝ) : invMap a b c q = (invMat a b c).mulVec q := rfl

lemma invMap_0 (a b c q : Fin 3 → ℝ) : invMap a b c q 0 = (det3 a b c)⁻¹ *
    ((b 1 * c 2 - b 2 * c 1) * q 0 + (b 2 * c 0 - b 0 * c 2) * q 1 + (b 0 * c 1 - b 1 * c 0) * q 2) := by
  rw [invMap_apply]; simp [invMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

lemma invMap_1 (a b c q : Fin 3 → ℝ) : invMap a b c q 1 = (det3 a b c)⁻¹ *
    ((c 1 * a 2 - c 2 * a 1) * q 0 + (c 2 * a 0 - c 0 * a 2) * q 1 + (c 0 * a 1 - c 1 * a 0) * q 2) := by
  rw [invMap_apply]; simp [invMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

lemma invMap_2 (a b c q : Fin 3 → ℝ) : invMap a b c q 2 = (det3 a b c)⁻¹ *
    ((a 1 * b 2 - a 2 * b 1) * q 0 + (a 2 * b 0 - a 0 * b 2) * q 1 + (a 0 * b 1 - a 1 * b 0) * q 2) := by
  rw [invMap_apply]; simp [invMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

lemma invMap_a {a b c : Fin 3 → ℝ} (hd : det3 a b c ≠ 0) : invMap a b c a = Pi.single 0 1 := by
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, invMap_0, Pi.single_eq_same]
    rw [show (b 1 * c 2 - b 2 * c 1) * a 0 + (b 2 * c 0 - b 0 * c 2) * a 1 +
      (b 0 * c 1 - b 1 * c 0) * a 2 = det3 a b c by unfold det3; ring, inv_mul_cancel₀ hd]
  · simp only [Fin.mk_one, Fin.isValue, invMap_1]
    rw [show (c 1 * a 2 - c 2 * a 1) * a 0 + (c 2 * a 0 - c 0 * a 2) * a 1 +
      (c 0 * a 1 - c 1 * a 0) * a 2 = 0 by ring]
    simp
  · simp only [Fin.reduceFinMk, Fin.isValue, invMap_2]
    rw [show (a 1 * b 2 - a 2 * b 1) * a 0 + (a 2 * b 0 - a 0 * b 2) * a 1 +
      (a 0 * b 1 - a 1 * b 0) * a 2 = 0 by ring]
    simp

lemma invMap_b {a b c : Fin 3 → ℝ} (hd : det3 a b c ≠ 0) : invMap a b c b = Pi.single 1 1 := by
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, invMap_0]
    rw [show (b 1 * c 2 - b 2 * c 1) * b 0 + (b 2 * c 0 - b 0 * c 2) * b 1 +
      (b 0 * c 1 - b 1 * c 0) * b 2 = 0 by ring]
    simp
  · simp only [Fin.mk_one, Fin.isValue, invMap_1, Pi.single_eq_same]
    rw [show (c 1 * a 2 - c 2 * a 1) * b 0 + (c 2 * a 0 - c 0 * a 2) * b 1 +
      (c 0 * a 1 - c 1 * a 0) * b 2 = det3 a b c by unfold det3; ring, inv_mul_cancel₀ hd]
  · simp only [Fin.reduceFinMk, Fin.isValue, invMap_2]
    rw [show (a 1 * b 2 - a 2 * b 1) * b 0 + (a 2 * b 0 - a 0 * b 2) * b 1 +
      (a 0 * b 1 - a 1 * b 0) * b 2 = 0 by ring]
    simp

lemma invMap_c {a b c : Fin 3 → ℝ} (hd : det3 a b c ≠ 0) : invMap a b c c = Pi.single 2 1 := by
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, invMap_0]
    rw [show (b 1 * c 2 - b 2 * c 1) * c 0 + (b 2 * c 0 - b 0 * c 2) * c 1 +
      (b 0 * c 1 - b 1 * c 0) * c 2 = 0 by ring]
    simp
  · simp only [Fin.mk_one, Fin.isValue, invMap_1]
    rw [show (c 1 * a 2 - c 2 * a 1) * c 0 + (c 2 * a 0 - c 0 * a 2) * c 1 +
      (c 0 * a 1 - c 1 * a 0) * c 2 = 0 by ring]
    simp
  · simp only [Fin.reduceFinMk, Fin.isValue, invMap_2, Pi.single_eq_same]
    rw [show (a 1 * b 2 - a 2 * b 1) * c 0 + (a 2 * b 0 - a 0 * b 2) * c 1 +
      (a 0 * b 1 - a 1 * b 0) * c 2 = det3 a b c by unfold det3; ring, inv_mul_cancel₀ hd]

lemma det_invMap {a b c : Fin 3 → ℝ} (hd : det3 a b c ≠ 0) :
    (invMap a b c).det = (det3 a b c)⁻¹ := by
  show LinearMap.det (Matrix.toLin' (invMat a b c)) = _
  rw [LinearMap.det_toLin', invMat, Matrix.det_smul]
  have h : Matrix.det !![b 1 * c 2 - b 2 * c 1, b 2 * c 0 - b 0 * c 2, b 0 * c 1 - b 1 * c 0;
      c 1 * a 2 - c 2 * a 1, c 2 * a 0 - c 0 * a 2, c 0 * a 1 - c 1 * a 0;
      a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] = det3 a b c ^ 2 := by
    simp [Matrix.det_fin_three]
    unfold det3
    ring
  rw [h, Fintype.card_fin]
  field_simp

lemma abs_entry_le {x y z w : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (hw : |w| ≤ 1) :
    |x * y - z * w| ≤ 2 := by
  calc |x * y - z * w| ≤ |x * y| + |z * w| := abs_sub _ _
    _ = |x| * |y| + |z| * |w| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * 1 + 1 * 1 := by gcongr
    _ = 2 := by norm_num

lemma abs_lin_le {e₀ e₁ e₂ : ℝ} (h₀ : |e₀| ≤ 2) (h₁ : |e₁| ≤ 2) (h₂ : |e₂| ≤ 2)
    (q : Fin 3 → ℝ) : |e₀ * q 0 + e₁ * q 1 + e₂ * q 2| ≤ 6 * ‖q‖ := by
  have hq : ∀ l, |q l| ≤ ‖q‖ := fun l => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm q l
  calc |e₀ * q 0 + e₁ * q 1 + e₂ * q 2| ≤ |e₀ * q 0| + |e₁ * q 1| + |e₂ * q 2| :=
        abs_add_three _ _ _
    _ = |e₀| * |q 0| + |e₁| * |q 1| + |e₂| * |q 2| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ 2 * ‖q‖ + 2 * ‖q‖ + 2 * ‖q‖ := by
        gcongr <;> exact hq _
    _ = 6 * ‖q‖ := by ring

/-- Norm bound for the inverse map of three bounded vectors with `|det| ≥ θ`. -/
lemma norm_invMap_le {a b c : Fin 3 → ℝ} (ha : ∀ k, |a k| ≤ 1) (hb : ∀ k, |b k| ≤ 1)
    (hc : ∀ k, |c k| ≤ 1) {θ : ℝ} (hθ : 0 < θ) (hd : θ ≤ |det3 a b c|) (q : Fin 3 → ℝ) :
    ‖invMap a b c q‖ ≤ (6 / θ) * ‖q‖ := by
  have hd0 : 0 < |det3 a b c| := lt_of_lt_of_le hθ hd
  have key : ∀ X : ℝ, |X| ≤ 6 * ‖q‖ → |(det3 a b c)⁻¹ * X| ≤ (6 / θ) * ‖q‖ := by
    intro X hX
    rw [abs_mul, abs_inv]
    calc |det3 a b c|⁻¹ * |X| ≤ θ⁻¹ * (6 * ‖q‖) := by
          apply mul_le_mul (inv_anti₀ hθ hd) hX (abs_nonneg _) (by positivity)
      _ = (6 / θ) * ‖q‖ := by ring
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  rw [Real.norm_eq_abs]
  fin_cases k
  · rw [Fin.zero_eta, invMap_0]
    exact key _ (abs_lin_le (abs_entry_le (hb _) (hc _) (hb _) (hc _))
      (abs_entry_le (hb _) (hc _) (hb _) (hc _)) (abs_entry_le (hb _) (hc _) (hb _) (hc _)) q)
  · rw [Fin.mk_one, invMap_1]
    exact key _ (abs_lin_le (abs_entry_le (hc _) (ha _) (hc _) (ha _))
      (abs_entry_le (hc _) (ha _) (hc _) (ha _)) (abs_entry_le (hc _) (ha _) (hc _) (ha _)) q)
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [invMap_2]
    exact key _ (abs_lin_le (abs_entry_le (ha _) (hb _) (ha _) (hb _))
      (abs_entry_le (ha _) (hb _) (ha _) (hb _)) (abs_entry_le (ha _) (hb _) (ha _) (hb _)) q)

lemma abs_det3_le {a b c : Fin 3 → ℝ} (ha : ∀ k, |a k| ≤ 1) (hb : ∀ k, |b k| ≤ 1)
    (hc : ∀ k, |c k| ≤ 1) : |det3 a b c| ≤ 6 := by
  unfold det3
  have h1 := abs_entry_le (hb 1) (hc 2) (hb 2) (hc 1)
  have h2 := abs_entry_le (hb 0) (hc 2) (hb 2) (hc 0)
  have h3 := abs_entry_le (hb 0) (hc 1) (hb 1) (hc 0)
  calc |a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) +
        a 2 * (b 0 * c 1 - b 1 * c 0)|
      ≤ |a 0 * (b 1 * c 2 - b 2 * c 1)| + |a 1 * (b 0 * c 2 - b 2 * c 0)| +
          |a 2 * (b 0 * c 1 - b 1 * c 0)| := by
        have := abs_add_three (a 0 * (b 1 * c 2 - b 2 * c 1)) (-(a 1 * (b 0 * c 2 - b 2 * c 0)))
          (a 2 * (b 0 * c 1 - b 1 * c 0))
        rw [abs_neg] at this
        convert this using 2
    _ = |a 0| * |b 1 * c 2 - b 2 * c 1| + |a 1| * |b 0 * c 2 - b 2 * c 0| +
          |a 2| * |b 0 * c 1 - b 1 * c 0| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ 1 * 2 + 1 * 2 + 1 * 2 := by gcongr <;> exact ha _
    _ = 6 := by norm_num


/-! ### Direction cells -/

/-- The cell of a direction for the mesh `h`. -/
noncomputable def cell (h : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℤ := fun k => ⌊v k / h⌋

lemma norm_sub_le_of_cell_eq {h : ℝ} (hh : 0 < h) {u v : Fin 3 → ℝ}
    (huv : cell h u = cell h v) : ‖u - v‖ ≤ h := by
  refine (pi_norm_le_iff_of_nonneg hh.le).2 fun k => ?_
  have hk := congrFun huv k
  simp only [cell] at hk
  have := Int.abs_sub_lt_one_of_floor_eq_floor hk
  rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh] at this
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact this.le

lemma cell_mem {h : ℝ} (hh : 0 < h) {v : Fin 3 → ℝ} (hv : ∀ k, |v k| ≤ 1) :
    cell h v ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉) := by
  rw [Fintype.mem_piFinset]
  intro k
  rw [Finset.mem_Icc]
  have h1 := (abs_le.1 (hv k))
  simp only [cell]
  constructor
  · have : -(1 / h) ≤ v k / h := by
      rw [neg_div', div_le_div_iff_of_pos_right hh]; linarith
    have h2 : -(⌈1 / h⌉ : ℝ) ≤ v k / h := le_trans (neg_le_neg (Int.le_ceil _)) this
    rw [Int.le_floor]; push_cast; exact h2
  · have : v k / h ≤ 1 / h := div_le_div_of_nonneg_right h1.2 hh.le
    exact (Int.floor_mono this).trans (Int.floor_le_ceil _)

lemma tr_single_self (j : Fin 3) : tr j (Pi.single j (1 : ℝ)) = 0 := by
  simp [tr, Pi.single_apply, Fin.succAbove_ne]

/-- A direction close to a cell representative is nearly axis-parallel after the inverse map. -/
lemma slope_cond_of_near {A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)} {j : Fin 3} {u w : Fin 3 → ℝ}
    {K : ℝ} (hK : 1 ≤ K) (hu : A u = Pi.single j 1) (hw : ‖A (w - u)‖ ≤ 1 / (2 * K)) :
    ‖tr j (A w)‖ * K ≤ |A w j| ∧ A w j ≠ 0 := by
  have hAw : A w = Pi.single j 1 + A (w - u) := by rw [map_sub, hu]; abel
  have hK0 : 0 < K := by linarith
  have hsmall : 1 / (2 * K) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hj : |A (w - u) j| ≤ 1 / (2 * K) := by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm _ j).trans hw
  have hAwj : A w j = 1 + A (w - u) j := by rw [hAw]; simp
  have hlow : 1 / 2 ≤ |A w j| := by
    rw [hAwj]
    have := abs_le.1 hj
    rw [abs_of_pos (by linarith)]; linarith
  refine ⟨?_, fun h0 => by rw [h0, abs_zero] at hlow; norm_num at hlow⟩
  have htr : tr j (A w) = tr j (A (w - u)) := by rw [hAw, tr_add, tr_single_self, zero_add]
  rw [htr]
  calc ‖tr j (A (w - u))‖ * K ≤ 1 / (2 * K) * K :=
        mul_le_mul_of_nonneg_right ((norm_tr_le j _).trans hw) hK0.le
    _ = 1 / 2 := by field_simp
    _ ≤ |A w j| := hlow


lemma rpow_half_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ (1/2:ℝ) ≤ ∑ i ∈ s, f i ^ (1/2:ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add_right ih _)

/-- Cauchy–Schwarz for square roots of counts. -/
lemma sum_sqrt_cube_le {α : Type*} (s : Finset α) (N : α → ℕ) :
    (∑ a ∈ s, Real.sqrt (N a)) ^ 3 ≤ ((s.card : ℝ) * ∑ a ∈ s, (N a : ℝ)) ^ (3/2:ℝ) := by
  have hcs : (∑ a ∈ s, Real.sqrt (N a)) ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, (N a : ℝ) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun a => Real.sqrt (N a))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    simpa [Real.sq_sqrt (Nat.cast_nonneg _)] using this
  have h0 : 0 ≤ ∑ a ∈ s, Real.sqrt (N a) := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  calc (∑ a ∈ s, Real.sqrt (N a)) ^ 3 = ((∑ a ∈ s, Real.sqrt (N a)) ^ 2) ^ (3/2:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hcs (by norm_num)

lemma sum3_eq {α : Type*} (C : Finset α) (X : ℝ≥0∞) (s : α → ℝ≥0∞) :
    ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, X * s a * s b * s c = X * (∑ a ∈ C, s a) ^ 3 := by
  have e : X * (∑ a ∈ C, s a) ^ 3 = ∑ a ∈ C, X * (s a * ((∑ b ∈ C, s b) * (∑ c ∈ C, s c))) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, pow_three]
  rw [e]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- Contribution of a triple of line neighbourhoods with transversality at least `θ`. -/
noncomputable def triTerm {n : ℕ} (θ δ : ℝ) (x v : Fin n → Fin 3 → ℝ) (i j k : Fin n)
    (q : Fin 3 → ℝ) : ℝ≥0∞ :=
  if θ ≤ |det3 (v i) (v j) (v k)| then
    (nearLine δ (x i) (v i)).indicator 1 q * (nearLine δ (x j) (v j)).indicator 1 q *
      (nearLine δ (x k) (v k)).indicator 1 q
  else 0


lemma measurable_triTerm {n : ℕ} (θ δ : ℝ) (x v : Fin n → Fin 3 → ℝ) (i j k : Fin n) :
    Measurable (triTerm θ δ x v i j k) := by
  unfold triTerm
  split_ifs
  · exact ((measurable_one.indicator (isOpen_nearLine _ _ _).measurableSet).mul
      (measurable_one.indicator (isOpen_nearLine _ _ _).measurableSet)).mul
      (measurable_one.indicator (isOpen_nearLine _ _ _).measurableSet)
  · exact measurable_const

/-- Regrouping the transversal triples by direction cells. -/
lemma triTerm_sum_le {n : ℕ} (θ δ : ℝ) (x v : Fin n → Fin 3 → ℝ) (cl : Fin n → Fin 3 → ℤ)
    (q : Fin 3 → ℝ) [DecidableEq (Fin 3 → ℤ)] :
    ∑ i, ∑ j, ∑ k, triTerm θ δ x v i j k q ≤
      ∑ a ∈ Finset.univ.image cl, ∑ b ∈ Finset.univ.image cl, ∑ c ∈ Finset.univ.image cl,
        if (∃ i j k, cl i = a ∧ cl j = b ∧ cl k = c ∧ θ ≤ |det3 (v i) (v j) (v k)|) then
          (∑ i, if cl i = a then (nearLine δ (x i) (v i)).indicator 1 q else 0) *
          (∑ j, if cl j = b then (nearLine δ (x j) (v j)).indicator 1 q else 0) *
          (∑ k, if cl k = c then (nearLine δ (x k) (v k)).indicator 1 q else 0)
        else 0 := by
  classical
  set C := Finset.univ.image cl with hC
  set G : (Fin 3 → ℤ) → (Fin 3 → ℤ) → (Fin 3 → ℤ) → Prop :=
    fun a b c => ∃ i j k, cl i = a ∧ cl j = b ∧ cl k = c ∧ θ ≤ |det3 (v i) (v j) (v k)| with hG
  set f : (Fin 3 → ℤ) → Fin n → ℝ≥0∞ :=
    fun a i => if cl i = a then (nearLine δ (x i) (v i)).indicator 1 q else 0 with hf
  set F : (Fin 3 → ℤ) → (Fin 3 → ℤ) → (Fin 3 → ℤ) → Fin n → Fin n → Fin n → ℝ≥0∞ :=
    fun a b c i j k => if G a b c then f a i * f b j * f c k else 0 with hF
  have hmem : ∀ i, cl i ∈ C := fun i => Finset.mem_image_of_mem cl (Finset.mem_univ i)
  -- each transversal triple is counted in the term of its own cells
  have hA : ∀ i j k, triTerm θ δ x v i j k q ≤ ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, F a b c i j k := by
    intro i j k
    unfold triTerm
    split_ifs with hθ
    · have hGi : G (cl i) (cl j) (cl k) := ⟨i, j, k, rfl, rfl, rfl, hθ⟩
      have e : F (cl i) (cl j) (cl k) i j k = (nearLine δ (x i) (v i)).indicator 1 q *
          (nearLine δ (x j) (v j)).indicator 1 q * (nearLine δ (x k) (v k)).indicator 1 q := by
        simp [hF, hf, hGi]
      rw [← e]
      calc F (cl i) (cl j) (cl k) i j k ≤ ∑ c ∈ C, F (cl i) (cl j) c i j k :=
            Finset.single_le_sum (f := fun c => F (cl i) (cl j) c i j k)
              (fun _ _ => zero_le) (hmem k)
        _ ≤ ∑ b ∈ C, ∑ c ∈ C, F (cl i) b c i j k :=
            Finset.single_le_sum (f := fun b => ∑ c ∈ C, F (cl i) b c i j k)
              (fun _ _ => zero_le) (hmem j)
        _ ≤ ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, F a b c i j k :=
            Finset.single_le_sum (f := fun a => ∑ b ∈ C, ∑ c ∈ C, F a b c i j k)
              (fun _ _ => zero_le) (hmem i)
    · exact zero_le
  -- each cell triple factors
  have hfac : ∀ a b c, ∑ i, ∑ j, ∑ k, F a b c i j k = if G a b c then
      (∑ i, f a i) * (∑ j, f b j) * (∑ k, f c k) else 0 := by
    intro a b c
    have e3 : ∀ (A B D : Fin n → ℝ≥0∞), (∑ i, A i) * (∑ j, B j) * (∑ k, D k) =
        ∑ i, ∑ j, ∑ k, A i * B j * D k := by
      intro A B D
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    by_cases hg : G a b c
    · simp only [hF, if_pos hg]
      rw [e3]
    · simp only [hF, if_neg hg, Finset.sum_const_zero]
  calc ∑ i, ∑ j, ∑ k, triTerm θ δ x v i j k q
      ≤ ∑ i, ∑ j, ∑ k, ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, F a b c i j k := by
        gcongr with i _ j _ k _
        exact hA i j k
    _ = ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, ∑ i, ∑ j, ∑ k, F a b c i j k := by
        simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin n))) (t := C)]
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => ?_
        rw [hfac]


lemma sum_ite_eq_ncount {n : ℕ} (δ : ℝ) (x v : Fin n → Fin 3 → ℝ) (cl : Fin n → Fin 3 → ℤ)
    (a : Fin 3 → ℤ) (q : Fin 3 → ℝ) :
    (∑ i, if cl i = a then (nearLine δ (x i) (v i)).indicator 1 q else 0) =
      ncount δ (fun i : {i // cl i = a} => x i) (fun i => v i) q := by
  classical
  rw [← Finset.sum_filter, ncount]
  refine Finset.sum_subtype _ (fun i => ?_) (fun i => (nearLine δ (x i) (v i)).indicator 1 q)
  simp

/-- Trilinear Kakeya with a transversality threshold, in the sup norm of `Fin 3 → ℝ`. -/
theorem trilinearSup (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ θ δ : ℝ, 0 < θ → θ ≤ 1 → 0 < δ → δ ≤ 1 →
    ∀ (n : ℕ) (x v : Fin n → Fin 3 → ℝ), (∀ i k, |v i k| ≤ 1) →
    ∫⁻ q in Metric.closedBall 0 1, (∑ i, ∑ j, ∑ k, triTerm θ δ x v i j k q) ^ (1/2:ℝ)
      ≤ ENNReal.ofReal (C * θ ^ (-8:ℝ) * δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ)) := by
  obtain ⟨K, Ccap, hK2, hCcap, hcap⟩ := capTriple ε hε
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  refine ⟨Ccap * 1296 * 27 ^ (9/2:ℝ) * (K : ℝ) ^ (9/2:ℝ), by positivity, ?_⟩
  intro θ δ hθ hθ1 hδ hδ1 n x v hv
  classical
  set h : ℝ := θ / (12 * K) with hhdef
  have hh : 0 < h := by positivity
  set cl : Fin n → Fin 3 → ℤ := fun i => cell h (v i) with hcl
  set C := Finset.univ.image cl with hC
  set B : ℝ := Ccap * (6 / θ) ^ 3 * 6 * δ ^ (3 - ε) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the bound for one cell triple
  have hone : ∀ a b c, (∃ i j k, cl i = a ∧ cl j = b ∧ cl k = c ∧
      θ ≤ |det3 (v i) (v j) (v k)|) →
      ∫⁻ q in Metric.closedBall 0 1,
        ((∑ i, if cl i = a then (nearLine δ (x i) (v i)).indicator 1 q else 0) *
          (∑ j, if cl j = b then (nearLine δ (x j) (v j)).indicator 1 q else 0) *
          (∑ k, if cl k = c then (nearLine δ (x k) (v k)).indicator 1 q else 0)) ^ (1/2:ℝ)
        ≤ ENNReal.ofReal B * (Fintype.card {i // cl i = a} : ℝ≥0∞) ^ (1/2:ℝ) *
          (Fintype.card {i // cl i = b} : ℝ≥0∞) ^ (1/2:ℝ) *
          (Fintype.card {i // cl i = c} : ℝ≥0∞) ^ (1/2:ℝ) := by
    rintro a b c ⟨i₀, j₀, k₀, ha, hb, hc, hθd⟩
    have hd0 : det3 (v i₀) (v j₀) (v k₀) ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hθd; linarith
    set A := invMap (v i₀) (v j₀) (v k₀) with hAdef
    have hAn : ∀ q, ‖A q‖ ≤ (6 / θ) * ‖q‖ :=
      norm_invMap_le (hv i₀) (hv j₀) (hv k₀) hθ hθd
    have hAdet : A.det ≠ 0 := by rw [hAdef, det_invMap hd0]; exact inv_ne_zero hd0
    have hnear : ∀ i i₁, cl i = cl i₁ → ‖A (v i - v i₁)‖ ≤ 1 / (2 * K) := by
      intro i i₁ hii
      have h1 := norm_sub_le_of_cell_eq hh hii
      calc ‖A (v i - v i₁)‖ ≤ (6 / θ) * ‖v i - v i₁‖ := hAn _
        _ ≤ (6 / θ) * h := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 / (2 * K) := by rw [hhdef]; field_simp; ring
    have s0 : ∀ i : {i // cl i = a}, ‖tr 0 (A (v i))‖ * K ≤ |A (v i) 0| ∧ A (v i) 0 ≠ 0 :=
      fun i => slope_cond_of_near hK1 (invMap_a hd0) (hnear i.1 i₀ (i.2.trans ha.symm))
    have s1 : ∀ i : {i // cl i = b}, ‖tr 1 (A (v i))‖ * K ≤ |A (v i) 1| ∧ A (v i) 1 ≠ 0 :=
      fun i => slope_cond_of_near hK1 (invMap_b hd0) (hnear i.1 j₀ (i.2.trans hb.symm))
    have s2 : ∀ i : {i // cl i = c}, ‖tr 2 (A (v i))‖ * K ≤ |A (v i) 2| ∧ A (v i) 2 ≠ 0 :=
      fun i => slope_cond_of_near hK1 (invMap_c hd0) (hnear i.1 k₀ (i.2.trans hc.symm))
    have hcap' := hcap A (6 / θ) (by positivity) hAn hAdet δ hδ hδ1
      (fun i : {i // cl i = a} => x i) (fun i => v i) (fun i : {i // cl i = b} => x i)
      (fun i => v i) (fun i : {i // cl i = c} => x i) (fun i => v i)
      (fun i => (s0 i).1) (fun i => (s0 i).2) (fun i => (s1 i).1) (fun i => (s1 i).2)
      (fun i => (s2 i).1) (fun i => (s2 i).2)
    have hdetA : |A.det|⁻¹ ≤ 6 := by
      rw [hAdef, det_invMap hd0, abs_inv, inv_inv]
      exact abs_det3_le (hv i₀) (hv j₀) (hv k₀)
    simp only [sum_ite_eq_ncount]
    refine le_trans (le_of_eq ?_) (hcap'.trans ?_)
    · congr 1; ext q
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    · gcongr
      rw [hB]
      have : Ccap * (6 / θ) ^ 3 * |A.det|⁻¹ ≤ Ccap * (6 / θ) ^ 3 * 6 :=
        mul_le_mul_of_nonneg_left hdetA (by positivity)
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hδ.le _)
  -- notation for the cell counts
  set na : (Fin 3 → ℤ) → (Fin 3 → ℝ) → ℝ≥0∞ :=
    fun a q => ∑ i, if cl i = a then (nearLine δ (x i) (v i)).indicator 1 q else 0 with hna
  set G : (Fin 3 → ℤ) → (Fin 3 → ℤ) → (Fin 3 → ℤ) → Prop :=
    fun a b c => ∃ i j k, cl i = a ∧ cl j = b ∧ cl k = c ∧ θ ≤ |det3 (v i) (v j) (v k)| with hG
  set N : (Fin 3 → ℤ) → ℕ := fun a => Fintype.card {i // cl i = a} with hN
  have hna_meas : ∀ a, Measurable (na a) := fun a =>
    Finset.measurable_sum _ fun i _ => by
      split_ifs
      · exact measurable_one.indicator (isOpen_nearLine _ _ _).measurableSet
      · exact measurable_const
  -- pointwise bound
  have hpt : ∀ q, (∑ i, ∑ j, ∑ k, triTerm θ δ x v i j k q) ^ (1/2:ℝ) ≤
      ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, if G a b c then (na a q * na b q * na c q) ^ (1/2:ℝ) else 0 := by
    intro q
    refine (ENNReal.rpow_le_rpow (triTerm_sum_le θ δ x v cl q) (by norm_num)).trans ?_
    refine (rpow_half_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (rpow_half_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (rpow_half_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    split_ifs
    · exact le_rfl
    · rw [ENNReal.zero_rpow_of_pos (by norm_num)]
  -- integrate
  have hint : ∫⁻ q in Metric.closedBall 0 1, (∑ i, ∑ j, ∑ k, triTerm θ δ x v i j k q) ^ (1/2:ℝ)
      ≤ ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, ENNReal.ofReal B * (N a : ℝ≥0∞) ^ (1/2:ℝ) *
          (N b : ℝ≥0∞) ^ (1/2:ℝ) * (N c : ℝ≥0∞) ^ (1/2:ℝ) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_finsetSum _ (fun a _ => Finset.measurable_sum _ fun b _ =>
      Finset.measurable_sum _ fun c _ => by
        split_ifs
        · exact (((hna_meas a).mul (hna_meas b)).mul (hna_meas c)).pow_const _
        · exact measurable_const)]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [lintegral_finsetSum _ (fun b _ => Finset.measurable_sum _ fun c _ => by
        split_ifs
        · exact (((hna_meas a).mul (hna_meas b)).mul (hna_meas c)).pow_const _
        · exact measurable_const)]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [lintegral_finsetSum _ (fun c _ => by
        split_ifs
        · exact (((hna_meas a).mul (hna_meas b)).mul (hna_meas c)).pow_const _
        · exact measurable_const)]
    refine Finset.sum_le_sum fun c _ => ?_
    by_cases hg : G a b c
    · simp only [if_pos hg]
      exact hone a b c hg
    · simp only [if_neg hg, lintegral_const, zero_mul]
      exact zero_le
  -- sum the cell bounds
  have hsq : ∀ a, (N a : ℝ≥0∞) ^ (1/2:ℝ) = ENNReal.ofReal (Real.sqrt (N a)) := by
    intro a
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by norm_num),
      Real.sqrt_eq_rpow]
  set S : ℝ := ∑ a ∈ C, Real.sqrt (N a) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hfac : ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, ENNReal.ofReal B * (N a : ℝ≥0∞) ^ (1/2:ℝ) *
      (N b : ℝ≥0∞) ^ (1/2:ℝ) * (N c : ℝ≥0∞) ^ (1/2:ℝ) = ENNReal.ofReal (B * S ^ 3) := by
    simp only [hsq]
    rw [ENNReal.ofReal_mul hB0, ENNReal.ofReal_pow hS0, hS,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
    exact sum3_eq C _ _
  have hNsum : ∑ a ∈ C, (N a : ℝ) = n := by
    have h1 := Finset.card_eq_sum_card_image cl (Finset.univ : Finset (Fin n))
    rw [Finset.card_univ, Fintype.card_fin] at h1
    simp only [hN, Fintype.card_subtype]
    exact_mod_cast h1.symm
  have hCcard : (C.card : ℝ) ≤ (27 * K / θ) ^ 3 := by
    have hsub : C ⊆ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉) := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact cell_mem hh (hv i)
    have h1 := Finset.card_le_card hsub
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc] at h1
    have hc0 : 0 ≤ ⌈1 / h⌉ := Int.ceil_nonneg (by positivity)
    have h2 : ((⌈1 / h⌉ + 1 - -⌈1 / h⌉).toNat : ℝ) ≤ 27 * K / θ := by
      have e : ⌈1 / h⌉ + 1 - -⌈1 / h⌉ = 2 * ⌈1 / h⌉ + 1 := by ring
      rw [e]
      have : ((2 * ⌈1 / h⌉ + 1).toNat : ℝ) = 2 * (⌈1 / h⌉ : ℝ) + 1 := by
        have h' : ((2 * ⌈1 / h⌉ + 1).toNat : ℤ) = 2 * ⌈1 / h⌉ + 1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast h'
      rw [this]
      have hih : 1 / h = 12 * K / θ := by rw [hhdef]; field_simp
      have hceil : (⌈1 / h⌉ : ℝ) ≤ 12 * K / θ + 1 :=
        calc (⌈1 / h⌉ : ℝ) ≤ 1 / h + 1 := (Int.ceil_lt_add_one _).le
          _ = 12 * K / θ + 1 := by rw [hih]
      have h3 : (3 : ℝ) ≤ 3 * K / θ := by rw [le_div_iff₀ hθ]; nlinarith
      have h4 : 27 * (K : ℝ) / θ = 24 * K / θ + 3 * K / θ := by ring
      have h5 : 2 * (12 * (K : ℝ) / θ + 1) + 1 = 24 * K / θ + 3 := by ring
      linarith
    calc (C.card : ℝ) ≤ (((⌈1 / h⌉ + 1 - -⌈1 / h⌉).toNat ^ 3 : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((⌈1 / h⌉ + 1 - -⌈1 / h⌉).toNat : ℝ) ^ 3 := by push_cast; ring
      _ ≤ (27 * K / θ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 3
  have hS3 : S ^ 3 ≤ ((C.card : ℝ) * n) ^ (3/2:ℝ) := by
    have := sum_sqrt_cube_le C N
    rwa [hNsum] at this
  have e1 : ((27 * K / θ) ^ 3 * (n : ℝ)) ^ (3/2:ℝ) =
      27 ^ (9/2:ℝ) * (K : ℝ) ^ (9/2:ℝ) * θ ^ (-(9/2):ℝ) * (n : ℝ) ^ (3/2:ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) hθ.le,
      Real.mul_rpow (by norm_num) hK0.le, Real.rpow_neg hθ.le]
    norm_num
    ring
  have e2 : (6 / θ) ^ 3 = 216 * θ ^ (-(3:ℝ)) := by
    rw [Real.rpow_neg hθ.le, show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
    norm_num
  have e3 : θ ^ (-(3:ℝ)) * θ ^ (-(9/2):ℝ) = θ ^ (-(15/2):ℝ) := by
    rw [← Real.rpow_add hθ]; norm_num
  have hθ8 : θ ^ (-(15/2):ℝ) ≤ θ ^ (-8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by norm_num)
  have hfinal : B * S ^ 3 ≤ Ccap * 1296 * 27 ^ (9/2:ℝ) * (K : ℝ) ^ (9/2:ℝ) * θ ^ (-8:ℝ) *
      δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ) := by
    calc B * S ^ 3 ≤ B * ((C.card : ℝ) * n) ^ (3/2:ℝ) := mul_le_mul_of_nonneg_left hS3 hB0
      _ ≤ B * ((27 * K / θ) ^ 3 * n) ^ (3/2:ℝ) := by
          gcongr
      _ = Ccap * 1296 * 27 ^ (9/2:ℝ) * (K : ℝ) ^ (9/2:ℝ) * (θ ^ (-(3:ℝ)) * θ ^ (-(9/2):ℝ)) *
            δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ) := by
          rw [e1, hB, e2]; ring
      _ = Ccap * 1296 * 27 ^ (9/2:ℝ) * (K : ℝ) ^ (9/2:ℝ) * θ ^ (-(15/2):ℝ) *
            δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ) := by rw [e3]
      _ ≤ _ := by gcongr
  calc _ ≤ _ := hint
    _ = ENNReal.ofReal (B * S ^ 3) := hfac
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal

open WangZahlLot.Obl.wz_extremal_lipschitz_grains (tube Space)

lemma abs_ofLp_le (u : Space) (k : Fin 3) : |WithLp.ofLp u k| ≤ ‖u‖ := by
  rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le u k

lemma norm_ofLp_le (u : Space) : ‖WithLp.ofLp u‖ ≤ ‖u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => by
    rw [Real.norm_eq_abs]; exact abs_ofLp_le u k

lemma ofLp_mem_nearLine {δ : ℝ} {x v p : Space} (hp : p ∈ tube δ x v) :
    WithLp.ofLp p ∈ nearLine δ (WithLp.ofLp x) (WithLp.ofLp v) := by
  rw [tube, Metric.mem_thickening_iff] at hp
  obtain ⟨y, hy, hpy⟩ := hp
  rw [segment_eq_image'] at hy
  obtain ⟨t, _, rfl⟩ := hy
  refine ⟨t, ?_⟩
  have e : WithLp.ofLp p - (WithLp.ofLp x + t • WithLp.ofLp v) =
      WithLp.ofLp (p - (x + t • (x + v - x))) := by
    simp only [add_sub_cancel_left, WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_smul]
  rw [e]
  exact lt_of_le_of_lt (norm_ofLp_le _) (by rwa [dist_eq_norm] at hpy)

/-- **Trilinear Kakeya inequality with a transversality threshold.**  For every `ε > 0` there is
`C` such that for all `0 < θ ≤ 1`, `0 < δ ≤ 1` and every family of `n` tubes
`thickening δ (segment x (x + v))` with unit directions, the integral over the unit ball of the
square root of the number of triples of tubes through a point whose directions span a
parallelepiped of volume at least `θ` is at most `C θ^(-8) δ^(3-ε) n^(3/2)`
(that is, `C θ^(-8) δ^(-ε) (δ² n)^(3/2)`). -/
theorem trilinear_kakeya (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ θ δ : ℝ, 0 < θ → θ ≤ 1 → 0 < δ → δ ≤ 1 →
    ∀ (n : ℕ) (x v : Fin n → Space), (∀ i, ‖v i‖ = 1) →
    ∫⁻ p in Metric.ball (0 : Space) 1, (∑ i, ∑ j, ∑ k,
      if θ ≤ |det3 (WithLp.ofLp (v i)) (WithLp.ofLp (v j)) (WithLp.ofLp (v k))| then
        (tube δ (x i) (v i)).indicator 1 p * (tube δ (x j) (v j)).indicator 1 p *
          (tube δ (x k) (v k)).indicator 1 p
      else 0) ^ (1/2:ℝ)
      ≤ ENNReal.ofReal (C * θ ^ (-8:ℝ) * δ ^ (3 - ε) * (n : ℝ) ^ (3/2:ℝ)) := by
  obtain ⟨C, hC, hmain⟩ := trilinearSup ε hε
  refine ⟨C, hC, ?_⟩
  intro θ δ hθ hθ1 hδ hδ1 n x v hv
  have hv' : ∀ i k, |WithLp.ofLp (v i) k| ≤ 1 := fun i k => (abs_ofLp_le _ k).trans (hv i).le
  have key := hmain θ δ hθ hθ1 hδ hδ1 n (fun i => WithLp.ofLp (x i)) (fun i => WithLp.ofLp (v i)) hv'
  set F : (Fin 3 → ℝ) → ℝ≥0∞ := fun q => (∑ i, ∑ j, ∑ k, triTerm θ δ (fun i => WithLp.ofLp (x i))
    (fun i => WithLp.ofLp (v i)) i j k q) ^ (1/2:ℝ) with hF
  have hFm : Measurable F := by
    refine Measurable.pow_const ?_ _
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => measurable_triTerm _ _ _ _ _ _ _
  have hball : MeasurableSet (Metric.closedBall (0 : Fin 3 → ℝ) 1) := Metric.isClosed_closedBall.measurableSet
  have hpt : ∀ p ∈ Metric.ball (0 : Space) 1, (∑ i, ∑ j, ∑ k,
      if θ ≤ |det3 (WithLp.ofLp (v i)) (WithLp.ofLp (v j)) (WithLp.ofLp (v k))| then
        (tube δ (x i) (v i)).indicator 1 p * (tube δ (x j) (v j)).indicator 1 p *
          (tube δ (x k) (v k)).indicator 1 p
      else 0) ^ (1/2:ℝ) ≤ (Metric.closedBall (0 : Fin 3 → ℝ) 1).indicator F (WithLp.ofLp p) := by
    intro p hp
    have hq : WithLp.ofLp p ∈ Metric.closedBall (0 : Fin 3 → ℝ) 1 := by
      rw [mem_closedBall_zero_iff]
      rw [mem_ball_zero_iff] at hp
      exact (norm_ofLp_le p).trans hp.le
    rw [indicator_of_mem hq]
    simp only [hF]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
    unfold triTerm
    split_ifs
    · have hind : ∀ y w : Space, (tube δ y w).indicator (1 : Space → ℝ≥0∞) p ≤
          (nearLine δ (WithLp.ofLp y) (WithLp.ofLp w)).indicator 1 (WithLp.ofLp p) := by
        intro y w
        by_cases hpt : p ∈ tube δ y w
        · rw [indicator_of_mem hpt, indicator_of_mem (ofLp_mem_nearLine hpt)]
          simp
        · rw [indicator_of_notMem hpt]; exact zero_le
      gcongr
      · exact hind _ _
      · exact hind _ _
      · exact hind _ _
    · exact le_rfl
  calc _ ≤ ∫⁻ p in Metric.ball (0 : Space) 1,
        (Metric.closedBall (0 : Fin 3 → ℝ) 1).indicator F (WithLp.ofLp p) :=
        setLIntegral_mono ((hFm.indicator hball).comp (PiLp.volume_preserving_ofLp (Fin 3)).measurable) hpt
    _ ≤ ∫⁻ p : Space, (Metric.closedBall (0 : Fin 3 → ℝ) 1).indicator F (WithLp.ofLp p) :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ q : Fin 3 → ℝ, (Metric.closedBall (0 : Fin 3 → ℝ) 1).indicator F q :=
        (PiLp.volume_preserving_ofLp (Fin 3)).lintegral_comp (hFm.indicator hball)
    _ = ∫⁻ q in Metric.closedBall (0 : Fin 3 → ℝ) 1, F q := lintegral_indicator hball F
    _ ≤ _ := key

end WangZahlLot.Obl.wz_extremal_lipschitz_grains.MK
