-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_separated_full_subtree.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_separated_full_subtree.Selection
import Submission.WZ.Obl.wz_tower_convex_count_composition.Arithmetic
import Submission.WZ.Obl.wz_tower_balanced_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_nsp_separated_full_subtree

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

/-- Choose the fullness loss after the height, and absorb every coloring and
regularization loss into one quarter of the requested exponent. -/
theorem parameters (ε : ℝ) (hε : 0 < ε) (B : ℕ) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ b ≤ ε / 4 ∧
    ∃ q : ℕ, 0 < q ∧ 4 < (ε / 4) * q ∧
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∃ P : ℕ, 0 < P ∧
      200000000000000000000 * δ ^ (-b) / δ ^ b < (P : ℝ) ∧
      ∀ J : ℕ, J ≤ B → (P : ℝ) ^ (J + 1) * (q : ℝ) ^ J ≤ δ ^ (-(ε / 4)) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (max (16 / ε) 0)
  have hqpos : 0 < q := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hq)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hqε : 4 < (ε / 4) * q := by
    have h := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_left _ _) hq)
    nlinarith
  let C : ℝ := 200000000000000000002 * q
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  obtain ⟨θ, hθ, hθε, d, hd, hbudget⟩ :=
    WangZahlLot.Obl.wz_tower_convex_count_composition.power_budget C hC (B + 1) (ε / 4) (by positivity)
  let b := min 1 (θ / 2)
  have hb : 0 < b := lt_min zero_lt_one (by positivity)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbθ : 2 * b ≤ θ := by dsimp [b]; linarith [min_le_right (1 : ℝ) (θ / 2)]
  have hbε : b ≤ ε / 4 := by linarith
  refine ⟨b, hb, hb1, hbε, q, hqpos, hqε, min d (1 / 100),
    lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδd
  have hδ1 : δ ≤ 1 := (hδd.trans (min_le_right _ _)).trans (by norm_num)
  let D := 200000000000000000000 * δ ^ (-b) / δ ^ b
  let P := ⌈D⌉₊ + 1
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDP : D < (P : ℝ) := by
    dsimp [P]
    push_cast
    linarith [Nat.le_ceil D]
  have hp1 : 1 ≤ δ ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hDb : D ≤ 200000000000000000000 * δ ^ (-θ) := by
    dsimp [D]
    rw [mul_div_assoc, ← Real.rpow_sub hδ]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hP : (P : ℝ) ≤ 200000000000000000002 * δ ^ (-θ) := by
    have hceil := Nat.ceil_lt_add_one hD0
    dsimp [P]
    push_cast
    nlinarith
  refine ⟨P, by dsimp [P]; omega, hDP, ?_⟩
  intro J hJB
  calc
    (P : ℝ) ^ (J + 1) * (q : ℝ) ^ J ≤
        (200000000000000000002 * δ ^ (-θ)) ^ (J + 1) * (q : ℝ) ^ (J + 1) := by
      gcongr
      omega
    _ = (C * δ ^ (-θ)) ^ (J + 1) := by
      rw [← mul_pow]
      dsimp [C]
      congr 1
      ring
    _ ≤ δ ^ (-(ε / 4)) :=
      hbudget δ hδ hδ1 (hδd.trans (min_le_left _ _)) (J + 1) (by omega)

lemma retained_card {δ ε : ℝ} {m J P q : ℕ} (hδ : 0 < δ)
    (U S : Finset (Fin m))
    (hU : (m : ℝ) ≤ (P : ℝ) ^ (J + 1) * U.card)
    (hS : (U.card : ℝ) ≤ (q : ℝ) ^ J * S.card)
    (hbudget : (P : ℝ) ^ (J + 1) * (q : ℝ) ^ J ≤ δ ^ (-(ε / 4))) :
    δ ^ (ε / 4) * m ≤ (S.card : ℝ) := by
  have h : (m : ℝ) ≤ δ ^ (-(ε / 4)) * S.card := by
    calc
      _ ≤ (P : ℝ) ^ (J + 1) * U.card := hU
      _ ≤ (P : ℝ) ^ (J + 1) * ((q : ℝ) ^ J * S.card) := by gcongr
      _ = ((P : ℝ) ^ (J + 1) * (q : ℝ) ^ J) * S.card := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)
  have hcancel : δ ^ (ε / 4) * δ ^ (-(ε / 4)) = 1 := by
    rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hδ.le (ε / 4))
  simpa only [← mul_assoc, hcancel, one_mul] using hh

/-- The retained fullness is enough to pay for the global convex-count loss. -/
lemma fullness_exponents {δ ε b A r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbε : b ≤ ε / 4)
    (h : δ ^ (ε / 4) * δ ^ b * r ^ 2 ≤ δ ^ (-(ε / 4)) * A) :
    δ ^ (3 * ε / 4) * r ^ 2 ≤ A := by
  have hleft : δ ^ (3 * ε / 4) ≤ δ ^ (ε / 4) * (δ ^ (ε / 4) * δ ^ b) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hh := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hδ.le (ε / 4))
  have hcancel : δ ^ (ε / 4) * δ ^ (-(ε / 4)) = 1 := by
    rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
  calc
    _ ≤ (δ ^ (ε / 4) * (δ ^ (ε / 4) * δ ^ b)) * r ^ 2 :=
      mul_le_mul_of_nonneg_right hleft (sq_nonneg r)
    _ = δ ^ (ε / 4) * (δ ^ (ε / 4) * δ ^ b * r ^ 2) := by ring
    _ ≤ δ ^ (ε / 4) * (δ ^ (-(ε / 4)) * A) := hh
    _ = A := by rw [← mul_assoc, hcancel, one_mul]

end WangZahlLot.Obl.wz_nsp_separated_full_subtree
