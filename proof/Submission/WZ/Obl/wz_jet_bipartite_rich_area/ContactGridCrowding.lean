-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactGridCrowding.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGrid

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

def contactCrowdingSteps (δ D s : ℝ) : ℕ := ⌈20002 * (s ^ 2 / (δ * D))⌉₊

def contactCrowding (δ D s : ℝ) : ℕ := (4 * 42 + 1) ^ 2 * (4 * contactCrowdingSteps δ D s + 1)

/-- Above the natural slope scale, the number of cells in the geometric
separation window is at most a constant times `s²/(δD)`. -/
theorem contactCrowding_bounds {δ D s ℓ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hs : 0 < s) (hℓ : 0 ≤ ℓ)
    (hnat : δ * D ≤ s ^ 2) (hmesh : δ ≤ 2 * s * ℓ) (hlin : s * ℓ ≤ δ) :
    1 ≤ contactCrowding δ D s ∧
      10000 * s / D + ℓ ≤ (contactCrowdingSteps δ D s : ℝ) * ℓ ∧
      (contactCrowding δ D s : ℝ) * δ * D ≤ 3000000000 * s ^ 2 := by
  let r := s ^ 2 / (δ * D)
  have hr : 1 ≤ r := (one_le_div (mul_pos hδ hD)).mpr hnat
  have hr0 : 0 ≤ r := by linarith
  have hlow : δ / (2 * s) ≤ ℓ := (div_le_iff₀ (by positivity)).mpr (by nlinarith [hmesh])
  have hLlo : 20002 * r ≤ (contactCrowdingSteps δ D s : ℝ) := Nat.le_ceil _
  have hLhi : (contactCrowdingSteps δ D s : ℝ) ≤ 20003 * r := by
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 20002 * r)
    change (⌈20002 * r⌉₊ : ℝ) ≤ _
    linarith
  have hsep : 10000 * s / D ≤ 20000 * r * ℓ := by
    have heq : 10000 * s / D = 20000 * r * (δ / (2 * s)) := by
      dsimp [r]
      field_simp [hδ.ne', hD.ne', hs.ne']
      <;> ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hstep : ℓ ≤ r * ℓ := by nlinarith
  have hscale : 10000 * s / D + ℓ ≤ (contactCrowdingSteps δ D s : ℝ) * ℓ := by
    have hh := mul_le_mul_of_nonneg_right hLlo hℓ
    nlinarith
  have hcrowd : (contactCrowding δ D s : ℝ) ≤ 3000000000 * r := by
    norm_num [contactCrowding]
    nlinarith
  have hproduct : r * (δ * D) = s ^ 2 := div_mul_cancel₀ _ (mul_pos hδ hD).ne'
  refine ⟨by unfold contactCrowding; omega, hscale, ?_⟩
  have hh := mul_le_mul_of_nonneg_right hcrowd (mul_pos hδ hD).le
  nlinarith [hproduct]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
