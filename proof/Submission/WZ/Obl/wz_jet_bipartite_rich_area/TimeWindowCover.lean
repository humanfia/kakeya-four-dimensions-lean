-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.TimeWindowCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- Fixed short windows on the parameter interval. -/
noncomputable def timeWindowLeft (j : Fin 20000) : ℝ := -1+(j:ℝ)/10000

noncomputable def timeWindowRight (j : Fin 20000) : ℝ := -1+((j:ℝ)+1)/10000

theorem timeWindow_bounds (j : Fin 20000) :
    -1 ≤ timeWindowLeft j ∧ timeWindowLeft j < timeWindowRight j ∧
      timeWindowRight j ≤ 1 ∧ timeWindowRight j-timeWindowLeft j=1/10000 := by
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hj1 : (j:ℝ) ≤ 19999 := by exact_mod_cast (by omega : j.val ≤ 19999)
  dsimp [timeWindowLeft, timeWindowRight]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · ring

/-- Every time in the original parameter interval belongs to a fixed
short window; endpoint times are included. -/
theorem exists_mem_timeWindow {x : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    ∃ j : Fin 20000, x ∈ Set.Icc (timeWindowLeft j) (timeWindowRight j) := by
  by_cases hx1 : x=1
  · subst x
    refine ⟨⟨19999, by norm_num⟩, ?_⟩
    norm_num [timeWindowLeft, timeWindowRight]
  have hxlt : x<1 := lt_of_le_of_ne hx.2 hx1
  let k : ℕ := ⌊(x+1)*10000⌋₊
  have hv : 0 ≤ (x+1)*10000 := by nlinarith [hx.1]
  have hlo : (k:ℝ) ≤ (x+1)*10000 := Nat.floor_le hv
  have hhi : (x+1)*10000 < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hklt : k<20000 := by
    have hkr : (k:ℝ)<20000 := by linarith
    exact_mod_cast hkr
  refine ⟨⟨k,hklt⟩, ?_⟩
  change -1+(k:ℝ)/10000 ≤ x ∧ x ≤ -1+((k:ℝ)+1)/10000
  constructor <;> linarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
