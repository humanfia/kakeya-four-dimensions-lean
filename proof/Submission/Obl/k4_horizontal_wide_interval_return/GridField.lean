import Submission.Obl.k4_horizontal_wide_interval_return.AnchorRows
import Submission.Obl.k4_horizontal_wide_interval_return.MixedTerm

namespace Submission.Obl.k4_horizontal_wide_interval_return

open Finset

noncomputable section

def bilinearValue (β : Fin 4 → ℝ) (x y : ℝ) : ℝ :=
  β 0 + β 1 * x + β 2 * y + β 3 * x * y

def anchorCoefficients (r₁ r₂ : ℝ × ℝ) (y₁ y₂ : ℝ) : Fin 4 → ℝ :=
  ![(r₁.1 * y₂ - r₂.1 * y₁) / (y₂ - y₁),
    (r₁.2 * y₂ - r₂.2 * y₁) / (y₂ - y₁),
    (r₂.1 - r₁.1) / (y₂ - y₁), (r₂.2 - r₁.2) / (y₂ - y₁)]

theorem bilinearValue_anchorCoefficients (r₁ r₂ : ℝ × ℝ) (y₁ y₂ x y : ℝ) :
    bilinearValue (anchorCoefficients r₁ r₂ y₁ y₂) x y =
      anchorBilinear r₁ r₂ y₁ y₂ x y := by
  simp only [bilinearValue, anchorCoefficients, Matrix.cons_val]
  unfold anchorBilinear
  ring

theorem anchorCoefficients_bound {r₁ r₂ : ℝ × ℝ} {y₁ y₂ K γ : ℝ}
    (hK : 1 ≤ K) (hγ : 0 < γ) (hgap : γ ≤ |y₁ - y₂|)
    (hr₁ : |r₁.1| ≤ K ∧ |r₁.2| ≤ K) (hr₂ : |r₂.1| ≤ K ∧ |r₂.2| ≤ K)
    (hy₁ : |y₁| ≤ K) (hy₂ : |y₂| ≤ K) :
    ∀ i, |anchorCoefficients r₁ r₂ y₁ y₂ i| ≤ 2 * K ^ 2 / γ := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hgap' : γ ≤ |y₂ - y₁| := by rwa [abs_sub_comm]
  have hquot (n : ℝ) (hn : |n| ≤ 2 * K ^ 2) :
      |n / (y₂ - y₁)| ≤ 2 * K ^ 2 / γ := by
    rw [abs_div]
    exact (div_le_div_of_nonneg_right hn (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) hγ hgap')
  have hprod (a b c d : ℝ) (ha : |a| ≤ K) (hb : |b| ≤ K)
      (hc : |c| ≤ K) (hd : |d| ≤ K) : |a * b - c * d| ≤ 2 * K ^ 2 := by
    calc |a * b - c * d| ≤ |a * b| + |c * d| := abs_sub _ _
      _ ≤ K * K + K * K := by simp only [abs_mul]; gcongr
      _ = 2 * K ^ 2 := by ring
  have hdiff (a b : ℝ) (ha : |a| ≤ K) (hb : |b| ≤ K) :
      |a - b| ≤ 2 * K ^ 2 :=
    (abs_sub a b).trans ((add_le_add ha hb).trans (by linarith))
  intro i
  fin_cases i <;> simp only [anchorCoefficients, Matrix.cons_val]
  · exact hquot _ (hprod _ _ _ _ hr₁.1 hy₂ hr₂.1 hy₁)
  · exact hquot _ (hprod _ _ _ _ hr₁.2 hy₂ hr₂.2 hy₁)
  · exact hquot _ (hdiff _ _ hr₂.1 hr₁.1)
  · exact hquot _ (hdiff _ _ hr₂.2 hr₁.2)

/-- Row and column fits on a dense weighted grid give one bilinear first
coefficient and one constant second coefficient on dense original weight. -/
theorem exists_grid_field {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (w f g : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (row : κ → ℝ × ℝ) (column : ι → ℝ × ℝ)
    (rowConst : κ → ℝ) (columnConst : ι → ℝ)
    {M K γ e : ℝ} {G : ℕ}
    (hw : ∀ i j, 0 ≤ w i j) (hM : 0 < M) (hcap : ∀ i j, w i j ≤ M)
    (hK : 1 ≤ K) (hγ : 0 < γ) (he : 0 ≤ e)
    (hy : ∀ j, |y j| ≤ K)
    (hrow : ∀ j, |(row j).1| ≤ K ∧ |(row j).2| ≤ K)
    (hrowConst : ∀ j, |rowConst j| ≤ K)
    (hrowFit : ∀ i j, 0 < w i j →
      |f i j - ((row j).1 + (row j).2 * x i)| ≤ e ∧ |g i j - rowConst j| ≤ e)
    (hcolFit : ∀ i j, 0 < w i j →
      |f i j - ((column i).1 + (column i).2 * y j)| ≤ e ∧
        |g i j - columnConst i| ≤ e)
    (hnear : ∀ j, (univ.filter fun j' => |y j - y j'| < γ).card ≤ G)
    (hpos : 0 < (∑ i, ∑ j, w i j) ^ 3 / (M ^ 2 * (Fintype.card ι : ℝ) ^ 2) -
      G * Fintype.card κ * ∑ i, ∑ j, w i j) :
    ∃ (β : Fin 4 → ℝ) (c : ℝ),
      (∀ i, |β i| ≤ 2 * K ^ 2 / γ) ∧ |c| ≤ K ∧
      ((∑ i, ∑ j, w i j) ^ 3 / (M ^ 2 * (Fintype.card ι : ℝ) ^ 2) -
        G * Fintype.card κ * ∑ i, ∑ j, w i j) / (Fintype.card κ : ℝ) ^ 2 ≤
        ∑ i, ∑ j, if |f i j - bilinearValue β (x i) (y j)| ≤ e + 8 * e * K / γ ∧
          |g i j - c| ≤ 3 * e then w i j else 0 := by
  classical
  obtain ⟨j₁, j₂, hgap, hmass⟩ :=
    exists_dense_anchor_rows w hw hM hcap y hnear hpos
  have hne : y j₁ ≠ y j₂ := by
    intro heq
    rw [heq, sub_self, abs_zero] at hgap
    linarith
  let β := anchorCoefficients (row j₁) (row j₂) (y j₁) (y j₂)
  refine ⟨β, rowConst j₁,
    anchorCoefficients_bound hK hγ hgap (hrow j₁) (hrow j₂) (hy j₁) (hy j₂),
    hrowConst j₁, hmass.trans ?_⟩
  have hfit (i : ι) (j : κ) (h₁ : 0 < w i j₁) (h₂ : 0 < w i j₂)
      (hj : 0 < w i j) :
      |f i j - bilinearValue β (x i) (y j)| ≤ e + 8 * e * K / γ ∧
        |g i j - rowConst j₁| ≤ 3 * e := by
    obtain ⟨hr₁, hrc₁⟩ := hrowFit i j₁ h₁
    obtain ⟨hr₂, _⟩ := hrowFit i j₂ h₂
    obtain ⟨hc₁, hcc₁⟩ := hcolFit i j₁ h₁
    obtain ⟨hc₂, _⟩ := hcolFit i j₂ h₂
    obtain ⟨hc, hcc⟩ := hcolFit i j hj
    constructor
    · rw [bilinearValue_anchorCoefficients]
      apply (column_fit_of_anchors hne hr₁ hr₂ hc₁ hc₂ hc).trans
      have hdist (a b : κ) : |y a - y b| ≤ 2 * K :=
        (abs_sub _ _).trans (by linarith [hy a, hy b])
      have hgap' : γ ≤ |y j₂ - y j₁| := by rwa [abs_sub_comm]
      calc e + 2 * e * (|y j - y j₁| + |y j - y j₂|) / |y j₂ - y j₁|
          ≤ e + 2 * e * (4 * K) / |y j₂ - y j₁| := by
            gcongr
            linarith [hdist j j₁, hdist j j₂]
        _ ≤ e + 2 * e * (4 * K) / γ := by gcongr
        _ = e + 8 * e * K / γ := by ring
    · calc |g i j - rowConst j₁|
          ≤ |g i j - columnConst i| + |columnConst i - rowConst j₁| :=
            abs_sub_le _ _ _
        _ ≤ |g i j - columnConst i| +
            (|columnConst i - g i j₁| + |g i j₁ - rowConst j₁|) :=
            add_le_add le_rfl (abs_sub_le (columnConst i) (g i j₁) (rowConst j₁))
        _ ≤ e + (e + e) := add_le_add hcc
          (add_le_add (by simpa only [abs_sub_comm] using hcc₁) hrc₁)
        _ = 3 * e := by ring
  unfold pairWeight
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : 0 < w i j₁ ∧ 0 < w i j₂
  · rw [if_pos hi]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : 0 < w i j
    · rw [if_pos (hfit i j hi.1 hi.2 hj)]
    · have hz : w i j = 0 := le_antisymm (le_of_not_gt hj) (hw i j)
      simp [hz]
  · rw [if_neg hi]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> [exact hw i j; rfl])

/-- Agreement on a retained third-direction line controls the mixed term.
The duration floor is supplied by the original restricted trajectory prior. -/
theorem mixed_coefficient_bound (β : Fin 4 → ℝ)
    {x₀ y₀ a₁ a₂ φ₀ φ₁ E η sep : ℝ} (S : Set ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E) (hsep : 0 < sep)
    (ha₁ : sep ≤ |a₁|) (ha₂ : sep ≤ |a₂|)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ MeasureTheory.volume S)
    (hfit : ∀ t ∈ S,
      |bilinearValue β (x₀ + t * a₁) (y₀ + t * a₂) - (φ₀ + φ₁ * t)| ≤ E) :
    |β 3| ≤ 8 * ((24 / η) ^ 2 * E) / sep ^ 2 := by
  have hmix := mixed_term_le S hη hη1 hE hS hmass hfit
  have hprod : sep ^ 2 ≤ |a₁| * |a₂| := by
    simpa only [sq] using mul_le_mul ha₁ ha₂ hsep.le (abs_nonneg _)
  rw [le_div_iff₀ (sq_pos_of_pos hsep)]
  calc |β 3| * sep ^ 2 ≤ |β 3| * (|a₁| * |a₂|) :=
      mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ = |β 3 * a₁ * a₂| := by rw [abs_mul, abs_mul]; ring
    _ ≤ 8 * ((24 / η) ^ 2 * E) := hmix

/-- Removing a small mixed term preserves every fitted occurrence, with no
additional loss of original mass. -/
theorem affine_error_of_bilinear {β : Fin 4 → ℝ} {f x y K E B : ℝ}
    (hfit : |f - bilinearValue β x y| ≤ E) (hcoeff : |β 3| ≤ B)
    (hx : |x| ≤ K) (hy : |y| ≤ K) :
    |f - (β 0 + β 1 * x + β 2 * y)| ≤ E + B * K ^ 2 := by
  have hK : 0 ≤ K := (abs_nonneg x).trans hx
  have hB : 0 ≤ B := (abs_nonneg (β 3)).trans hcoeff
  calc |f - (β 0 + β 1 * x + β 2 * y)|
      ≤ |f - bilinearValue β x y| +
          |bilinearValue β x y - (β 0 + β 1 * x + β 2 * y)| := abs_sub_le _ _ _
    _ ≤ E + B * K ^ 2 := add_le_add hfit (by
      have heq : bilinearValue β x y - (β 0 + β 1 * x + β 2 * y) = β 3 * x * y := by
        unfold bilinearValue; ring
      rw [heq, abs_mul, abs_mul]
      calc |β 3| * |x| * |y| ≤ B * K * K :=
          mul_le_mul (mul_le_mul hcoeff hx (abs_nonneg _) hB) hy
            (abs_nonneg _) (mul_nonneg hB hK)
        _ = B * K ^ 2 := by ring)

end

end Submission.Obl.k4_horizontal_wide_interval_return
