-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/SatBins.lean
import Submission.Obl.k4_terminal_label_saturation.Curvature
import Submission.Obl.k4_terminal_label_saturation.QuadraticRoots

/-!
# Hidden bins compatible with a quadratic chart test

Saturation (paper Lemma 2.8) lists, for every terminal observation, the charts
compatible with it.  An observation records the hidden coordinate only through
its bin `⌊w / h⌋`; we test a chart at the left end `n * h` of the bin:

* the value is at most `ε`;
* when the curvature is small, `|c₀| * h ≤ β`, also the hidden derivative is at
  least `β`.

At a fixed base point, at most `14 + 8 * ε / (β * h)` bins pass this test.
In the low-curvature case this is the quadratic sublevel bound; with large
curvature the derivative moves by more than `β` across one bin, so the bins
where it is below `β` are at most six.
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MvPolynomial

/-- The bin test at the left end of bin `n` for a univariate quadratic. -/
def binTest (p : Polynomial ℝ) (c₀ ε β h : ℝ) (n : ℤ) : Prop :=
  |p.eval (n * h)| ≤ ε ∧ (|c₀| * h ≤ β → β ≤ |p.derivative.eval (n * h)|)

/-- The bin index of the left end of bin `n` is `n`. -/
theorem floor_mul_div (h : ℝ) (hh : 0 < h) (n : ℤ) : ⌊((n : ℝ) * h - 0) / h⌋ = n := by
  rw [sub_zero, mul_div_assoc, div_self hh.ne', mul_one, Int.floor_intCast]

/-- Counting bins passing the bin test of a univariate quadratic. -/
theorem binTest_card_le (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {c₀ ε β h : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hh : 0 < h)
    (hc₀ : ∀ x, p.derivative.derivative.eval x = c₀) :
    {n : ℤ | binTest p c₀ ε β h n}.Finite ∧
      (({n : ℤ | binTest p c₀ ε β h n}.ncard : ℕ) : ℝ) ≤ 14 + 8 * ε / (β * h) := by
  classical
  -- bins meeting the regular sublevel set
  obtain ⟨hfin₁, hcard₁⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_quadratic_sublevel
    p hp hε hβ hh 0
  set Z₁ := (fun x : ℝ => ⌊(x - 0) / h⌋) ''
    {x : ℝ | |p.eval x| ≤ ε ∧ β ≤ |p.derivative.eval x|} with hZ₁
  -- integers whose left end has small derivative
  set Z₂ := {n : ℤ | |p.derivative.eval ((n : ℝ) * h)| < β ∧ β < |c₀| * h} with hZ₂
  have hsub : {n : ℤ | binTest p c₀ ε β h n} ⊆ Z₁ ∪ Z₂ := by
    intro n hn
    obtain ⟨hv, hd⟩ := hn
    by_cases hlow : |c₀| * h ≤ β
    · left
      exact ⟨(n : ℝ) * h, ⟨hv, hd hlow⟩, floor_mul_div h hh n⟩
    · by_cases hder : β ≤ |p.derivative.eval ((n : ℝ) * h)|
      · left
        exact ⟨(n : ℝ) * h, ⟨hv, hder⟩, floor_mul_div h hh n⟩
      · right
        exact ⟨lt_of_not_ge hder, lt_of_not_ge hlow⟩
  -- the second set has at most six elements
  have hZ₂fin : Z₂.Finite ∧ ((Z₂.ncard : ℕ) : ℝ) ≤ 6 := by
    by_cases hlarge : β < |c₀| * h
    · have hc₀ne : c₀ ≠ 0 := by
        intro h0
        rw [h0, abs_zero, zero_mul] at hlarge
        exact absurd hlarge (not_lt.mpr hβ.le)
      have hcpos : 0 < |c₀| := abs_pos.mpr hc₀ne
      -- the derivative is affine with slope `c₀`
      have haff : ∀ x, p.derivative.eval x = p.derivative.eval 0 + c₀ * x := by
        intro x
        have hh2 := quadratic_derivative_taylor p hp 0 x
        rw [zero_add, hc₀ 0] at hh2
        exact hh2
      set s : Set ℝ := {x : ℝ | |p.derivative.eval x| < β} with hs
      have hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 2 * h := by
        intro x hx y hy
        have hx' : |p.derivative.eval 0 + c₀ * x| < β := by rw [← haff]; exact hx
        have hy' : |p.derivative.eval 0 + c₀ * y| < β := by rw [← haff]; exact hy
        have hxy : |c₀ * (x - y)| < 2 * β := by
          have e : c₀ * (x - y) = (p.derivative.eval 0 + c₀ * x) -
              (p.derivative.eval 0 + c₀ * y) := by ring
          rw [e]
          obtain ⟨hx1, hx2⟩ := abs_lt.mp hx'
          obtain ⟨hy1, hy2⟩ := abs_lt.mp hy'
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
        rw [abs_mul] at hxy
        rw [Real.dist_eq]
        have hlt : |c₀| * |x - y| < |c₀| * (2 * h) := by nlinarith
        exact (lt_of_mul_lt_mul_left hlt hcpos.le).le
      obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
        s (by positivity) hh 0 hdiam
      have hsub2 : Z₂ ⊆ (fun x : ℝ => ⌊(x - 0) / h⌋) '' s := by
        intro n hn
        exact ⟨(n : ℝ) * h, hn.1, floor_mul_div h hh n⟩
      refine ⟨hfin.subset hsub2, ?_⟩
      calc ((Z₂.ncard : ℕ) : ℝ) ≤ (((fun x : ℝ => ⌊(x - 0) / h⌋) '' s).ncard : ℝ) := by
            exact_mod_cast Set.ncard_le_ncard hsub2 hfin
        _ ≤ 2 * (2 * h) / h + 2 := hcard
        _ = 6 := by field_simp; ring
    · have hempty : Z₂ = ∅ := by
        ext n
        simp only [hZ₂, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hlt
        exact hlarge hlt
      rw [hempty]
      simp
  have hfin : (Z₁ ∪ Z₂).Finite := hfin₁.union hZ₂fin.1
  refine ⟨hfin.subset hsub, ?_⟩
  calc (({n : ℤ | binTest p c₀ ε β h n}.ncard : ℕ) : ℝ)
      ≤ (((Z₁ ∪ Z₂).ncard : ℕ) : ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub hfin
    _ ≤ ((Z₁.ncard + Z₂.ncard : ℕ) : ℝ) := by exact_mod_cast Set.ncard_union_le Z₁ Z₂
    _ ≤ 8 * (1 + ε / (β * h)) + 6 := by
        push_cast
        linarith [hcard₁, hZ₂fin.2]
    _ = 14 + 8 * ε / (β * h) := by ring

/-- The univariate restriction of a four-variable polynomial to the hidden
(last) coordinate, at a fixed base point. -/
noncomputable def hiddenSlice (R : MvPolynomial (Fin 4) ℝ) (t y₁ y₂ : ℝ) : Polynomial ℝ :=
  Submission.Obl.k4_quadratic_slope_volume.coordinatePolynomialHom ![t, y₁, y₂, 0] 3 R

theorem hiddenSlice_eval (R : MvPolynomial (Fin 4) ℝ) (t y₁ y₂ w : ℝ) :
    (hiddenSlice R t y₁ y₂).eval w = eval ![t, y₁, y₂, w] R := by
  unfold hiddenSlice
  rw [Submission.Obl.k4_quadratic_slope_volume.eval_coordinatePolynomialHom]
  have hv : Function.update ![t, y₁, y₂, (0 : ℝ)] (3 : Fin 4) w = ![t, y₁, y₂, w] := by
    funext i
    fin_cases i <;> simp
  rw [hv]

theorem hiddenSlice_derivative (R : MvPolynomial (Fin 4) ℝ) (t y₁ y₂ : ℝ) :
    (hiddenSlice R t y₁ y₂).derivative = hiddenSlice (pderiv 3 R) t y₁ y₂ := by
  unfold hiddenSlice
  exact Submission.Obl.k4_quadratic_slope_volume.derivative_coordinatePolynomialHom _ _ _

theorem hiddenSlice_natDegree (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (t y₁ y₂ : ℝ) : (hiddenSlice R t y₁ y₂).natDegree ≤ 2 := by
  unfold hiddenSlice Submission.Obl.k4_quadratic_slope_volume.coordinatePolynomialHom
  refine (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le R _ ?_).trans hR
  intro j
  split_ifs
  · simp
  · simp

/-- The hidden bin test of a chart test `R` at base point `(t, y₁, y₂)`. -/
def hiddenBinTest (R : MvPolynomial (Fin 4) ℝ) (t y₁ y₂ ε β h : ℝ) (n : ℤ) : Prop :=
  |eval ![t, y₁, y₂, (n : ℝ) * h] R| ≤ ε ∧
    (|curvature R 3| * h ≤ β → β ≤ |eval ![t, y₁, y₂, (n : ℝ) * h] (pderiv 3 R)|)

/-- At most `14 + 8 ε / (β h)` hidden bins pass the test at any base point. -/
theorem hiddenBinTest_card_le (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (t y₁ y₂ : ℝ) {ε β h : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hh : 0 < h) :
    {n : ℤ | hiddenBinTest R t y₁ y₂ ε β h n}.Finite ∧
      (({n : ℤ | hiddenBinTest R t y₁ y₂ ε β h n}.ncard : ℕ) : ℝ) ≤
        14 + 8 * ε / (β * h) := by
  have hc₀ : ∀ w, (hiddenSlice R t y₁ y₂).derivative.derivative.eval w = curvature R 3 := by
    intro w
    rw [hiddenSlice_derivative, hiddenSlice_derivative, hiddenSlice_eval,
      second_pderiv_eq_curvature R hR 3, eval_C]
  have hset : {n : ℤ | hiddenBinTest R t y₁ y₂ ε β h n} =
      {n : ℤ | binTest (hiddenSlice R t y₁ y₂) (curvature R 3) ε β h n} := by
    ext n
    simp only [Set.mem_ofPred_eq, hiddenBinTest, binTest, hiddenSlice_eval,
      hiddenSlice_derivative]
  rw [hset]
  exact binTest_card_le _ (hiddenSlice_natDegree R hR t y₁ y₂) hε hβ hh hc₀

/-- A point of a chart passes the test of its own bin: the value moves by at most
`K δ` plus a curvature term across one bin, and in the low-curvature case the
derivative moves by at most `β`.  Here `h = δ / B` is the bin width. -/
theorem hiddenBinTest_of_point (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (t y₁ y₂ w : ℝ) {κ δ B : ℝ} (hκ : 1 ≤ κ) (hδ : 0 < δ) (hB : 0 < B)
    (hval : |eval ![t, y₁, y₂, w] R| ≤ κ * δ)
    (hder : |eval ![t, y₁, y₂, w] (pderiv 3 R)| ≤ κ * B)
    (hcurv : |curvature R 3| ≤ κ * B ^ 2 / δ)
    (hfloor : B / κ ≤ |eval ![t, y₁, y₂, w] (pderiv 3 R)|) :
    hiddenBinTest R t y₁ y₂ (3 * κ * δ) (B / (2 * κ)) (δ / B) ⌊B * w / δ⌋ := by
  set h := δ / B with hhdef
  have hh : 0 < h := div_pos hδ hB
  set n : ℤ := ⌊B * w / δ⌋ with hn
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ
  -- the offset from the point to the left end of its bin
  set s : ℝ := (n : ℝ) * h - w with hs
  have hBw : B * w / δ = w / h := by rw [hhdef]; field_simp
  have hs_le : s ≤ 0 := by
    have h1 : (n : ℝ) ≤ w / h := by rw [← hBw]; exact Int.floor_le _
    have h2 : (n : ℝ) * h ≤ w := by
      calc (n : ℝ) * h ≤ (w / h) * h := mul_le_mul_of_nonneg_right h1 hh.le
        _ = w := by field_simp
    linarith
  have hs_ge : -h < s := by
    have h1 : w / h - 1 < (n : ℝ) := by rw [← hBw]; exact Int.sub_one_lt_floor _
    have h2 : w - h < (n : ℝ) * h := by
      have := mul_lt_mul_of_pos_right h1 hh
      calc w - h = (w / h - 1) * h := by field_simp
        _ < (n : ℝ) * h := this
    linarith
  have habs_s : |s| ≤ h := by
    rw [abs_le]; constructor <;> linarith
  -- univariate Taylor expansions in the hidden coordinate
  set p := hiddenSlice R t y₁ y₂ with hp
  have hpdeg : p.natDegree ≤ 2 := hiddenSlice_natDegree R hR t y₁ y₂
  have hc₀ : ∀ v, p.derivative.derivative.eval v = curvature R 3 := by
    intro v
    rw [hp, hiddenSlice_derivative, hiddenSlice_derivative, hiddenSlice_eval,
      second_pderiv_eq_curvature R hR 3, eval_C]
  have hpw : p.eval w = eval ![t, y₁, y₂, w] R := hiddenSlice_eval R t y₁ y₂ w
  have hdw : p.derivative.eval w = eval ![t, y₁, y₂, w] (pderiv 3 R) := by
    rw [hp, hiddenSlice_derivative, hiddenSlice_eval]
  have hpn : p.eval ((n : ℝ) * h) = eval ![t, y₁, y₂, (n : ℝ) * h] R :=
    hiddenSlice_eval R t y₁ y₂ _
  have hdn : p.derivative.eval ((n : ℝ) * h) =
      eval ![t, y₁, y₂, (n : ℝ) * h] (pderiv 3 R) := by
    rw [hp, hiddenSlice_derivative, hiddenSlice_eval]
  have htay := quadratic_taylor p hpdeg w s
  have htay' := quadratic_derivative_taylor p hpdeg w s
  rw [show w + s = (n : ℝ) * h by rw [hs]; ring, hc₀] at htay htay'
  -- curvature times the bin width
  have hch : |curvature R 3| * h ≤ κ * B := by
    calc |curvature R 3| * h ≤ (κ * B ^ 2 / δ) * h :=
          mul_le_mul_of_nonneg_right hcurv hh.le
      _ = κ * B := by rw [hhdef]; field_simp
  refine ⟨?_, ?_⟩
  · rw [← hpn, htay, hpw, hdw]
    have h1 : |eval ![t, y₁, y₂, w] (pderiv 3 R) * s| ≤ κ * δ := by
      rw [abs_mul]
      calc _ ≤ (κ * B) * h := mul_le_mul hder habs_s (abs_nonneg _) (by positivity)
        _ = κ * δ := by rw [hhdef]; field_simp
    have h2 : |curvature R 3 / 2 * s ^ 2| ≤ κ * δ := by
      rw [abs_mul, abs_div, abs_two, abs_pow]
      have hs2 : |s| ^ 2 ≤ h * h := by nlinarith [abs_nonneg s]
      calc |curvature R 3| / 2 * |s| ^ 2 ≤ |curvature R 3| / 2 * (h * h) :=
            mul_le_mul_of_nonneg_left hs2 (by positivity)
        _ = (|curvature R 3| * h) * h / 2 := by ring
        _ ≤ (κ * B) * h / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_right hch hh.le
        _ ≤ κ * δ := by
            rw [hhdef]; field_simp; nlinarith [hκpos, hδ]
    calc |eval ![t, y₁, y₂, w] R + eval ![t, y₁, y₂, w] (pderiv 3 R) * s +
          curvature R 3 / 2 * s ^ 2|
        ≤ |eval ![t, y₁, y₂, w] R| + |eval ![t, y₁, y₂, w] (pderiv 3 R) * s| +
          |curvature R 3 / 2 * s ^ 2| := abs_add_three _ _ _
      _ ≤ κ * δ + κ * δ + κ * δ := by linarith
      _ = 3 * κ * δ := by ring
  · intro hlow
    rw [← hdn, htay', hdw]
    have hβ2 : B / (2 * κ) = B / κ - B / (2 * κ) := by field_simp; ring
    have hcs : |curvature R 3 * s| ≤ B / (2 * κ) := by
      rw [abs_mul]
      calc |curvature R 3| * |s| ≤ |curvature R 3| * h :=
            mul_le_mul_of_nonneg_left habs_s (abs_nonneg _)
        _ ≤ B / (2 * κ) := hlow
    have := abs_sub_abs_le_abs_sub (eval ![t, y₁, y₂, w] (pderiv 3 R))
      (-(curvature R 3 * s))
    rw [sub_neg_eq_add, abs_neg] at this
    linarith

end Submission.Obl.k4_terminal_label_saturation
