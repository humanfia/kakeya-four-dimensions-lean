-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.BlockCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityRich

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset

/-- The bounded transverse coordinate limits the number of coarse row blocks. -/
lemma card_blocks_le {ρ : ℝ} {M : ℕ} (hρ : 0 < ρ) (hM : 0 < M)
    (hs : (M : ℝ) * ρ ≤ 1) (P : Finset (ℤ × ℤ × ℤ))
    (hy : ∀ q ∈ P, |ρ * (q.2.1 : ℝ)| ≤ 1) :
    ((P.image (blockOf M)).card : ℝ) ≤ 4 / ((M : ℝ) * ρ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  have hspos : 0 < (M : ℝ) * ρ := mul_pos hMR hρ
  have hj : ∀ j ∈ P.image (blockOf M),
      -1 / ((M : ℝ) * ρ) - 1 ≤ (j : ℝ) ∧
      (j : ℝ) ≤ (-1 / ((M : ℝ) * ρ) - 1) + (2 / ((M : ℝ) * ρ) + 1) := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    have hrem0 : (0 : ℝ) ≤ ((q.2.1 % (M : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast Int.emod_nonneg q.2.1 hMZ.ne'
    have hrem1 : ((q.2.1 % (M : ℤ) : ℤ) : ℝ) < M := by
      exact_mod_cast Int.emod_lt_of_pos q.2.1 hMZ
    have he : (q.2.1 : ℝ) = (M : ℝ) * (blockOf M q : ℝ) +
        ((q.2.1 % (M : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast (Int.mul_ediv_add_emod q.2.1 (M : ℤ)).symm
    have hyq := abs_le.mp (hy q hq)
    have hremR0 := mul_nonneg hρ.le hrem0
    have hremR1 := mul_lt_mul_of_pos_left hrem1 hρ
    constructor
    · have hjlo : -1 - (M : ℝ) * ρ ≤ (M : ℝ) * ρ * (blockOf M q : ℝ) := by
        nlinarith [he]
      have hdiv : (-1 - (M : ℝ) * ρ) / ((M : ℝ) * ρ) ≤ (blockOf M q : ℝ) :=
        (div_le_iff₀ hspos).mpr (by nlinarith)
      convert hdiv using 1
      field_simp
    · have hjhi : (M : ℝ) * ρ * (blockOf M q : ℝ) ≤ 1 := by nlinarith [he]
      have hdiv : (blockOf M q : ℝ) ≤ 1 / ((M : ℝ) * ρ) :=
        (le_div_iff₀ hspos).mpr (by nlinarith)
      convert hdiv using 1
      ring
  have hc := card_le_of_subset_Icc_int (show 0 ≤ 2 / ((M : ℝ) * ρ) + 1 by positivity)
    (P.image (blockOf M)) hj
  have h1 : 1 ≤ 1 / ((M : ℝ) * ρ) := (one_le_div hspos).mpr hs
  calc ((P.image (blockOf M)).card : ℝ) ≤ (2 / ((M : ℝ) * ρ) + 1) + 1 := hc
    _ ≤ 4 / ((M : ℝ) * ρ) := by
      simp only [div_eq_mul_inv, one_mul] at h1 ⊢
      linarith

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
