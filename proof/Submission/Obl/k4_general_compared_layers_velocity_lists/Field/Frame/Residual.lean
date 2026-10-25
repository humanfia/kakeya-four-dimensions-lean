-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Frame.Residual; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Interfaces
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Frame.Algebra
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Frame.Lists

/-!
# Residual velocity lists of a common field

On one original block `Q` with normalized time `u`, normalized major coordinate `ζ` and
transverse coordinate `U`, the native signal of an incidence of a fine color-one label `j`
of the coarse label `i` is, by the fine layer fit, the offset fit on the true fiber box and
the exact transverse Taylor identity,

  `P(x) = A_i(t, Z) + offset(i, j) + B_i U + D_i U² ± 2 H N^(-(r+v))`,

and the common field replaces `B_i U + D_i U²` by the background `C₁(τ, ζ) U + C₃ U²` up to
`(K + K²) N^ε E`. Inside one scalar cell the coarse value `A_i` varies by the variation of a
bounded quadratic over a physical step `q σ`. So the floor of the residual at the mesh
`N^(-(r+v))` is a bounded shift of the floor of a value determined by the cell, the coarse
label and the fine label; the coarse label has the velocity bin of the line and an
intercept bin within `O(K)` bins of the one predicted by the cell.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent.FieldFrame

/-- Reference time of a scalar cell. -/
def cellTime (t₀ q σ : ℝ) (x : ℤ × ℤ) : ℝ := t₀ + q * (x.1 * σ)

/-- Reference major coordinate of a scalar cell. -/
def cellMajor (t₀ q σ : ℝ) (c : Fin 5 → ℝ) (x : ℤ × ℤ) : ℝ :=
  c 0 + c 1 * cellTime t₀ q σ x + q * (x.2 * σ)

/-- Reference intercept of a scalar cell at a velocity bin. -/
def cellIntercept (t₀ q σ : ℝ) (c : Fin 5 → ℝ) (x : ℤ × ℤ) (a : ℤ) : ℝ :=
  cellMajor t₀ q σ c x - cellTime t₀ q σ x * (a * σ)

/-- A real number lies in the mesh cell named by its floor. -/
theorem floor_mul_near {y σ : ℝ} (hσ : 0 < σ) :
    (⌊y / σ⌋ : ℝ) * σ ≤ y ∧ y < (⌊y / σ⌋ : ℝ) * σ + σ := by
  have h1 := Int.floor_le (y / σ)
  have h2 := Int.lt_floor_add_one (y / σ)
  constructor
  · calc (⌊y / σ⌋ : ℝ) * σ ≤ y / σ * σ := mul_le_mul_of_nonneg_right h1 hσ.le
      _ = y := div_mul_cancel₀ y hσ.ne'
  · calc y = y / σ * σ := (div_mul_cancel₀ y hσ.ne').symm
      _ < ((⌊y / σ⌋ : ℝ) + 1) * σ := mul_lt_mul_of_pos_right h2 hσ
      _ = (⌊y / σ⌋ : ℝ) * σ + σ := by ring

theorem abs_sub_floor_mul_le {y σ : ℝ} (hσ : 0 < σ) : |y - (⌊y / σ⌋ : ℝ) * σ| ≤ σ := by
  obtain ⟨h1, h2⟩ := floor_mul_near (y := y) hσ
  rw [abs_le]
  constructor <;> linarith

/-- The residual identity, as an inequality of real numbers. -/
theorem residual_bound {S Gj G0 off A B D U C₁ C₃ bg H a₂ η K : ℝ}
    (h1 : |S - Gj| ≤ H * a₂) (h2 : |Gj - G0 - off| ≤ H * a₂)
    (h3 : G0 = A + U * B + U ^ 2 * D) (h4 : bg = C₁ * U + C₃ * U ^ 2)
    (hB : |B - C₁| ≤ η) (hD : |D - C₃| ≤ η) (hU : |U| ≤ K) :
    |S - bg - A - off| ≤ 2 * H * a₂ + (K + K ^ 2) * η := by
  have hη : 0 ≤ η := (abs_nonneg _).trans hB
  have heq : S - bg - A - off =
      (S - Gj) + (Gj - G0 - off) + U * (B - C₁) + U ^ 2 * (D - C₃) := by
    rw [h3, h4]
    ring
  have e1 : |U * (B - C₁)| ≤ K * η := by
    rw [abs_mul]
    exact mul_le_mul hU hB (abs_nonneg _) ((abs_nonneg _).trans hU)
  have e2 : |U ^ 2 * (D - C₃)| ≤ K ^ 2 * η := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hU 2) hD (abs_nonneg _)
      (by positivity)
  rw [heq]
  calc |(S - Gj) + (Gj - G0 - off) + U * (B - C₁) + U ^ 2 * (D - C₃)|
      ≤ |S - Gj| + |Gj - G0 - off| + |U * (B - C₁)| + |U ^ 2 * (D - C₃)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ H * a₂ + H * a₂ + K * η + K ^ 2 * η := by gcongr
    _ = 2 * H * a₂ + (K + K ^ 2) * η := by ring

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem block_eq_Icc (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    block (p.T k r) (p.j k r Q) =
      Icc (p.blockStart k r Q) (p.blockStart k r Q + p.blockLen k r) := by
  simp only [block, Submission.Obl.k4_critical_intercept_concentration.Data.I, Parent.blockStart,
    Parent.blockLen]
  congr 1
  rw [add_div, one_div]

theorem blockLen_pos (k : ℕ) (r : ℝ) : 0 < p.blockLen k r := by
  unfold Parent.blockLen
  positivity

theorem blockLen_le_one (k : ℕ) (r : ℝ) : p.blockLen k r ≤ 1 := by
  unfold Parent.blockLen
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- The residual lists of a common field on one block. -/
def frameLists (k : ℕ) {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (Q : Fin (p.n k r)) : ℤ → Finset ((Fin 2 → ℤ) × ℤ) :=
  listBuild
    ((Finset.Icc 0 ⌈(p.N k ^ (-m))⁻¹⌉) ×ˢ
      (Finset.Icc (-⌈p.K k * (p.N k ^ (-m))⁻¹⌉) ⌈p.K k * (p.N k ^ (-m))⁻¹⌉))
    (fun x a => Finset.Icc
      (⌊cellIntercept (p.blockStart k r Q) (p.blockLen k r) (p.N k ^ (-m)) (p.c k r Q) x a /
          p.N k ^ (-m)⌋ - (⌈2 * p.K k + 4⌉ + 1))
      (⌊cellIntercept (p.blockStart k r Q) (p.blockLen k r) (p.N k ^ (-m)) (p.c k r Q) x a /
          p.N k ^ (-m)⌋ + (⌈2 * p.K k + 4⌉ + 1)))
    (s.coarseChoices Q) (s.fineChoices 1 Q)
    (fun x i j => ⌊(transA ((s.layers 0).G i) (p.tiltY k r Q)
        (cellTime (p.blockStart k r Q) (p.blockLen k r) (p.N k ^ (-m)) x)
        (cellMajor (p.blockStart k r Q) (p.blockLen k r) (p.N k ^ (-m)) (p.c k r Q) x) +
        s.offset 1 Q i j) / p.N k ^ (-r - v)⌋)
    (⌈4 * H⌉ + 1)

theorem frameLists_card (k : ℕ) {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (Q : Fin (p.n k r)) (hN : 0 < p.N k) (hK1 : 1 ≤ p.K k) (hKH : p.K k ≤ H)
    (hσ1 : p.N k ^ (-m) ≤ 1) (a : ℤ) :
    ((frameLists p k s Q a).card : ℝ) * (p.N k ^ (-m)) ^ 2 ≤
      2000 * H ^ 11 * p.N k ^ (p.d * v) := by
  have hH2 := s.loss_one
  have hσ0 : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  set σ := p.N k ^ (-m) with hσ_def
  set K := p.K k with hK_def
  have hNdv : 0 < p.N k ^ (p.d * v) := Real.rpow_pos_of_pos hN _
  have hσi : 0 < σ⁻¹ := inv_pos.mpr hσ0
  -- the cells
  have hn0 : (0 : ℤ) ≤ ⌈σ⁻¹⌉ := Int.ceil_nonneg hσi.le
  have hn1 : (0 : ℤ) ≤ ⌈K * σ⁻¹⌉ := Int.ceil_nonneg (by positivity)
  have hc0 : ((⌈σ⁻¹⌉ : ℤ) : ℝ) < σ⁻¹ + 1 := Int.ceil_lt_add_one _
  have hc1 : ((⌈K * σ⁻¹⌉ : ℤ) : ℝ) < K * σ⁻¹ + 1 := Int.ceil_lt_add_one _
  have hcells : ((Finset.Icc 0 ⌈σ⁻¹⌉ ×ˢ Finset.Icc (-⌈K * σ⁻¹⌉) ⌈K * σ⁻¹⌉).card : ℝ) *
      σ ^ 2 ≤ 15 * K := by
    rw [Finset.card_product, Nat.cast_mul, card_Icc_real (by omega), card_Icc_real (by omega)]
    push_cast
    have e1 : (⌈σ⁻¹⌉ + 1 - 0 : ℝ) * σ ≤ 1 + 2 * σ := by
      have : (⌈σ⁻¹⌉ + 1 - 0 : ℝ) ≤ σ⁻¹ + 2 := by linarith
      calc (⌈σ⁻¹⌉ + 1 - 0 : ℝ) * σ ≤ (σ⁻¹ + 2) * σ := mul_le_mul_of_nonneg_right this hσ0.le
        _ = 1 + 2 * σ := by field_simp
    have e2 : (⌈K * σ⁻¹⌉ + 1 - -⌈K * σ⁻¹⌉ : ℝ) * σ ≤ 2 * K + 3 * σ := by
      have : (⌈K * σ⁻¹⌉ + 1 - -⌈K * σ⁻¹⌉ : ℝ) ≤ 2 * (K * σ⁻¹) + 3 := by linarith
      calc (⌈K * σ⁻¹⌉ + 1 - -⌈K * σ⁻¹⌉ : ℝ) * σ ≤ (2 * (K * σ⁻¹) + 3) * σ :=
            mul_le_mul_of_nonneg_right this hσ0.le
        _ = 2 * K + 3 * σ := by field_simp
    calc (⌈σ⁻¹⌉ + 1 - 0 : ℝ) * (⌈K * σ⁻¹⌉ + 1 - -⌈K * σ⁻¹⌉) * σ ^ 2
        = ((⌈σ⁻¹⌉ + 1 - 0 : ℝ) * σ) * ((⌈K * σ⁻¹⌉ + 1 - -⌈K * σ⁻¹⌉ : ℝ) * σ) := by ring
      _ ≤ (1 + 2 * σ) * (2 * K + 3 * σ) := by
          apply mul_le_mul e1 e2 _ (by linarith)
          have : (0 : ℝ) ≤ (⌈K * σ⁻¹⌉ : ℝ) := by exact_mod_cast hn1
          have : (0 : ℝ) ≤ (⌈K * σ⁻¹⌉ + 1 - -⌈K * σ⁻¹⌉ : ℝ) := by linarith
          exact mul_nonneg this hσ0.le
      _ ≤ 3 * (5 * K) := by
          apply mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
      _ = 15 * K := by ring
  have hL : (0 : ℤ) ≤ ⌈4 * H⌉ + 1 := by
    have : (0 : ℤ) ≤ ⌈4 * H⌉ := Int.ceil_nonneg (by linarith)
    omega
  have hb : ∀ x, ((Finset.Icc
      (⌊cellIntercept (p.blockStart k r Q) (p.blockLen k r) σ (p.c k r Q) x a / σ⌋ -
        (⌈2 * K + 4⌉ + 1))
      (⌊cellIntercept (p.blockStart k r Q) (p.blockLen k r) σ (p.c k r Q) x a / σ⌋ +
        (⌈2 * K + 4⌉ + 1))).card : ℝ) ≤ 4 * K + 13 := by
    intro x
    have hM : (0 : ℤ) ≤ ⌈2 * K + 4⌉ := Int.ceil_nonneg (by linarith)
    rw [card_Icc_real (by omega)]
    push_cast
    have := Int.ceil_lt_add_one (2 * K + 4)
    linarith
  have hc : ∀ τ, ((s.coarseChoices Q τ).card : ℝ) ≤ H ^ 4 := fun τ => s.coarse_card Q τ
  have hf : ∀ i, ((s.fineChoices 1 Q i).card : ℝ) ≤ H ^ 4 * p.N k ^ (p.d * v) := by
    intro i
    have := s.fine_card 1 Q i
    simpa using this
  have hmain := card_listBuild_le
    ((Finset.Icc 0 ⌈σ⁻¹⌉) ×ˢ (Finset.Icc (-⌈K * σ⁻¹⌉) ⌈K * σ⁻¹⌉))
    (fun x a => Finset.Icc
      (⌊cellIntercept (p.blockStart k r Q) (p.blockLen k r) σ (p.c k r Q) x a / σ⌋ -
        (⌈2 * K + 4⌉ + 1))
      (⌊cellIntercept (p.blockStart k r Q) (p.blockLen k r) σ (p.c k r Q) x a / σ⌋ +
        (⌈2 * K + 4⌉ + 1)))
    (s.coarseChoices Q) (s.fineChoices 1 Q)
    (fun x i j => ⌊(transA ((s.layers 0).G i) (p.tiltY k r Q)
        (cellTime (p.blockStart k r Q) (p.blockLen k r) σ x)
        (cellMajor (p.blockStart k r Q) (p.blockLen k r) σ (p.c k r Q) x) +
        s.offset 1 Q i j) / p.N k ^ (-r - v)⌋)
    hL a (by positivity) (by positivity) hb hc hf
  have hL' : ((⌈4 * H⌉ + 1 : ℤ) : ℝ) < 4 * H + 2 := by
    push_cast
    have := Int.ceil_lt_add_one (4 * H)
    linarith
  have hH4 : 0 ≤ H ^ 4 := by positivity
  have hLnn : (0 : ℝ) ≤ 2 * ((⌈4 * H⌉ + 1 : ℤ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((⌈4 * H⌉ + 1 : ℤ) : ℝ) := by exact_mod_cast hL
    linarith
  have hcardnn : (0 : ℝ) ≤
      ((Finset.Icc 0 ⌈σ⁻¹⌉ ×ˢ Finset.Icc (-⌈K * σ⁻¹⌉) ⌈K * σ⁻¹⌉).card : ℝ) * σ ^ 2 := by
    positivity
  unfold Parent.FieldFrame.frameLists
  calc _ ≤ ((Finset.Icc 0 ⌈σ⁻¹⌉ ×ˢ Finset.Icc (-⌈K * σ⁻¹⌉) ⌈K * σ⁻¹⌉).card : ℝ) *
          ((4 * K + 13) * (H ^ 4 * (H ^ 4 * p.N k ^ (p.d * v) *
            (2 * ((⌈4 * H⌉ + 1 : ℤ) : ℝ) + 1)))) * σ ^ 2 :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = (((Finset.Icc 0 ⌈σ⁻¹⌉ ×ˢ Finset.Icc (-⌈K * σ⁻¹⌉) ⌈K * σ⁻¹⌉).card : ℝ) * σ ^ 2) *
          ((4 * K + 13) * (H ^ 4 * (H ^ 4 * p.N k ^ (p.d * v) *
            (2 * ((⌈4 * H⌉ + 1 : ℤ) : ℝ) + 1)))) := by ring
    _ ≤ (15 * H) * ((11 * H) * (H ^ 4 * (H ^ 4 * p.N k ^ (p.d * v) * (11 * H)))) := by
        apply mul_le_mul (hcells.trans (by linarith)) _ (by positivity) (by positivity)
        apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
        apply mul_le_mul le_rfl _ (by positivity) hH4
        apply mul_le_mul le_rfl (by linarith) hLnn (by positivity)
    _ = 1815 * H ^ 11 * p.N k ^ (p.d * v) := by ring
    _ ≤ 2000 * H ^ 11 * p.N k ^ (p.d * v) := by
        apply mul_le_mul_of_nonneg_right _ hNdv.le
        apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end Parent.FieldFrame

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
