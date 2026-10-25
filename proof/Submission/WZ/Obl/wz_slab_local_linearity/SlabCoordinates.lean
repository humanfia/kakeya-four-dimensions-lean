-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.SlabCoordinates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellCoordinates
import Submission.WZ.Obl.wz_slab_local_linearity.CellScaleBounds

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set

noncomputable def slabBase (ρ z₀ : ℝ) : ℤ := ⌊z₀ / ρ⌋
noncomputable def slabLayers (ρ : ℝ) : ℕ := ⌈1 / Real.sqrt ρ⌉₊ + 2

lemma slabLayers_pos (ρ : ℝ) : 0 < slabLayers ρ := by unfold slabLayers; omega

lemma slabLayers_bounds {ρ : ℝ} (hρ : 0 < ρ) (hsmall : ρ ≤ 1 / 100) :
    1 / Real.sqrt ρ ≤ (slabLayers ρ : ℝ) ∧
    (slabLayers ρ : ℝ) ≤ 2 / Real.sqrt ρ ∧ (slabLayers ρ : ℝ) * ρ ≤ 1 := by
  have hs := Real.sqrt_pos.mpr hρ
  have hs2 := Real.sq_sqrt hρ.le
  have hs10 : Real.sqrt ρ ≤ 1 / 10 := by nlinarith
  have h10 : 10 ≤ 1 / Real.sqrt ρ := (le_div_iff₀ hs).mpr (by linarith)
  have hlo := Nat.le_ceil (1 / Real.sqrt ρ)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 1 / Real.sqrt ρ by positivity)
  have hMlo : 1 / Real.sqrt ρ ≤ (slabLayers ρ : ℝ) := by simp only [slabLayers, Nat.cast_add, Nat.cast_ofNat]; linarith
  have hMhi : (slabLayers ρ : ℝ) ≤ 2 / Real.sqrt ρ := by
    simp only [slabLayers, Nat.cast_add, Nat.cast_ofNat]
    have he : 2 / Real.sqrt ρ = 2 * (1 / Real.sqrt ρ) := by ring
    rw [he]
    linarith
  refine ⟨hMlo, hMhi, ?_⟩
  have hh := (cell_layer_scale hρ hMlo hMhi).2
  linarith

lemma slabLayers_lower {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt ρ + 2 * ρ ≤ (slabLayers ρ : ℝ) * ρ := by
  have hs := Real.sqrt_pos.mpr hρ
  have he : (1 / Real.sqrt ρ) * ρ = Real.sqrt ρ := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff hs.ne', Real.mul_self_sqrt hρ.le]
  have hh := mul_le_mul_of_nonneg_right (Nat.le_ceil (1 / Real.sqrt ρ)) hρ.le
  rw [he] at hh
  simp only [slabLayers, Nat.cast_add, Nat.cast_ofNat]
  nlinarith

lemma slabBase_bounds {ρ : ℝ} (hρ : 0 < ρ) (z₀ : ℝ) :
    ρ * (slabBase ρ z₀ : ℝ) ≤ z₀ ∧ z₀ < ρ * ((slabBase ρ z₀ : ℝ) + 1) := by
  have hlo := Int.floor_le (z₀ / ρ)
  have hhi := Int.lt_floor_add_one (z₀ / ρ)
  simp only [slabBase]
  constructor
  · have hh := (le_div_iff₀ hρ).mp hlo
    linarith
  · have hh := (div_lt_iff₀ hρ).mp hhi
    linarith

lemma shifted_corner_zero (ρ : ℝ) (k₀ : ℤ) (q : ℤ × ℤ × ℤ) :
    (CellProofs.cellPos ρ q + heightShift ρ k₀) 0 = ρ * (q.1 : ℝ) := by
  simp [CellProofs.cellPos, heightShift]

lemma shifted_corner_one (ρ : ℝ) (k₀ : ℤ) (q : ℤ × ℤ × ℤ) :
    (CellProofs.cellPos ρ q + heightShift ρ k₀) 1 = ρ * (q.2.1 : ℝ) := by
  simp [CellProofs.cellPos, heightShift]

lemma shifted_corner_two (ρ : ℝ) (k₀ : ℤ) (q : ℤ × ℤ × ℤ) :
    (CellProofs.cellPos ρ q + heightShift ρ k₀) 2 = ρ * (q.2.2 : ℝ) + ρ * (k₀ : ℝ) := by
  simp [CellProofs.cellPos, heightShift]

lemma shifted_layer_mem {ρ z₀ : ℝ} (hρ : 0 < ρ) {K : Finset (Fin 3 → ℤ)}
    (hheight : ∀ p ∈ gridCubes ρ K, p 2 ∈ Icc z₀ (z₀ + Real.sqrt ρ))
    {q : ℤ × ℤ × ℤ} (hq : q ∈ shiftCells (slabBase ρ z₀) K) :
    0 ≤ q.2.2 ∧ q.2.2 < slabLayers ρ := by
  have hz := hheight _ (shifted_corner_mem hρ hq)
  have hb := slabBase_bounds hρ z₀
  have hM := slabLayers_lower hρ
  rw [shifted_corner_two] at hz
  have hqlo : (0 : ℝ) ≤ q.2.2 := by nlinarith [hz.1, hb.1]
  have hqhi : (q.2.2 : ℝ) < slabLayers ρ := by nlinarith [hz.2, hb.2]
  exact ⟨by exact_mod_cast hqlo, by exact_mod_cast hqhi⟩

end WangZahlLot.Obl.wz_slab_local_linearity
