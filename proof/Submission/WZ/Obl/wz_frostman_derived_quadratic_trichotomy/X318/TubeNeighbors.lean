-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.TubeNeighbors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FactorScale
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ExactContainment

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file TubeNeighbors.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

lemma tube_volume_upper_bounded_radius {δ B : ℝ} (hδ : 0 < δ) (hB : 1 ≤ B)
    (hδB : δ ≤ B) (x v : Space) (hv : ‖v‖ = 1) :
    volume (Tube δ x v) ≤ ENNReal.ofReal (384 * B * δ ^ 2) := by
  have hh := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
    (T := Icc 0 1) Subset.rfl (r := δ) (A := 1) hδ zero_le_one (by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have he : (fun t : ℝ => x + t • v) '' Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  rw [he] at hh
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hb : 128 * (2 * 1 + δ) ≤ 384 * B := by linarith
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg δ)

/-- Endpoint packing bounds the number of distinct tubes whose midpoints and
unoriented axes lie near those of a fixed unit segment. -/
theorem tube_parameter_neighbor_packing {δ r : ℝ}
    (hδ : 0 < δ) (hr : 0 ≤ r) (hR : δ + 2 * r ≤ 1)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (z w : Space) (hw : ‖w‖ = 1) :
    (ncard {i | ‖center (x i) (v i) - center z w‖ ≤ r ∧
      (‖v i - w‖ ≤ 2 * r ∨ ‖v i + w‖ ≤ 2 * r)} : ℝ) * δ ^ 4 ≤
        147456000000 * (δ + 2 * r) ^ 4 := by
  let W := Tube (δ + 2 * r) z w
  have hRpos : 0 < δ + 2 * r := by linarith
  have hvol : volume W ≤ ENNReal.ofReal (384 * (δ + 2 * r) ^ 2) :=
    tube_volume_upper hRpos hR z w hw
  have hfinite : volume W ≠ ⊤ := (lt_of_le_of_lt hvol ENNReal.ofReal_lt_top).ne
  have hp := packing_contained_in_enclosure hδ x v hv hsep W W hfinite (fun _ h => h)
  have hp' : ENNReal.ofReal ((contained (fun i => Tube δ (x i) (v i)) W : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal (147456000000 * (δ + 2 * r) ^ 4) := by
    calc
      _ ≤ ENNReal.ofReal 1000000 * (volume W) ^ 2 := hp
      _ ≤ ENNReal.ofReal 1000000 * ENNReal.ofReal (384 * (δ + 2 * r) ^ 2) ^ 2 := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
  have hpreal : (contained (fun i => Tube δ (x i) (v i)) W : ℝ) * δ ^ 4 ≤
      147456000000 * (δ + 2 * r) ^ 4 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hp'
  have hcount : ncard {i | ‖center (x i) (v i) - center z w‖ ≤ r ∧
      (‖v i - w‖ ≤ 2 * r ∨ ‖v i + w‖ ≤ 2 * r)} ≤
      contained (fun i => Tube δ (x i) (v i)) W :=
    Set.ncard_le_ncard fun i hi => tube_subset_of_center_unoriented_axis_near hi.1 hi.2
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) (by positivity)).trans hpreal

/-- At a fixed multiple of the tube radius the parameter-neighbor degree is
bounded independently of the radius. -/
theorem tube_parameter_neighbor_card {δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hR : (1 + 2 * C) * δ ≤ 1)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (z w : Space) (hw : ‖w‖ = 1) :
    (ncard {i | ‖center (x i) (v i) - center z w‖ ≤ C * δ ∧
      (‖v i - w‖ ≤ 2 * (C * δ) ∨ ‖v i + w‖ ≤ 2 * (C * δ))} : ℝ) ≤
        147456000000 * (1 + 2 * C) ^ 4 := by
  apply (mul_le_mul_iff_left₀ (pow_pos hδ 4)).mp
  calc
    _ ≤ 147456000000 * (δ + 2 * (C * δ)) ^ 4 :=
      tube_parameter_neighbor_packing hδ (mul_nonneg hC hδ.le) (by nlinarith) x v hv hsep z w hw
    _ = (147456000000 * (1 + 2 * C) ^ 4) * δ ^ 4 := by ring

/-- The same count for every radius at most one, allowing a larger fixed
power of the parameter-neighborhood constant. -/
theorem tube_parameter_neighbor_card_unit {δ C : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (z w : Space) (hw : ‖w‖ = 1) :
    (ncard {i | ‖center (x i) (v i) - center z w‖ ≤ C * δ ∧
      (‖v i - w‖ ≤ 2 * (C * δ) ∨ ‖v i + w‖ ≤ 2 * (C * δ))} : ℝ) ≤
        147456000000 * (1 + 2 * C) ^ 6 := by
  let B := 1 + 2 * C
  let W := Tube (B * δ) z w
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hvol : volume W ≤ ENNReal.ofReal (384 * B * (B * δ) ^ 2) :=
    tube_volume_upper_bounded_radius (mul_pos hBpos hδ) hB
      (by nlinarith) z w hw
  have hfinite : volume W ≠ ⊤ := (lt_of_le_of_lt hvol ENNReal.ofReal_lt_top).ne
  have hp := packing_contained_in_enclosure hδ x v hv hsep W W hfinite (fun _ h => h)
  have hp' : ENNReal.ofReal ((contained (fun i => Tube δ (x i) (v i)) W : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal ((147456000000 * B ^ 6) * δ ^ 4) := by
    calc
      _ ≤ ENNReal.ofReal 1000000 * (volume W) ^ 2 := hp
      _ ≤ ENNReal.ofReal 1000000 * ENNReal.ofReal (384 * B * (B * δ) ^ 2) ^ 2 := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
  have hpreal : (contained (fun i => Tube δ (x i) (v i)) W : ℝ) * δ ^ 4 ≤
      (147456000000 * B ^ 6) * δ ^ 4 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hp'
  have hcount : ncard {i | ‖center (x i) (v i) - center z w‖ ≤ C * δ ∧
      (‖v i - w‖ ≤ 2 * (C * δ) ∨ ‖v i + w‖ ≤ 2 * (C * δ))} ≤
      contained (fun i => Tube δ (x i) (v i)) W := by
    apply Set.ncard_le_ncard
    · intro i hi
      have hrad : B * δ = δ + 2 * (C * δ) := by dsimp [B]; ring
      change Tube δ (x i) (v i) ⊆ Tube (B * δ) z w
      rw [hrad]
      exact tube_subset_of_center_unoriented_axis_near hi.1 hi.2
    · exact Set.toFinite _
  apply (mul_le_mul_iff_left₀ (pow_pos hδ 4)).mp
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) (by positivity)).trans hpreal

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
