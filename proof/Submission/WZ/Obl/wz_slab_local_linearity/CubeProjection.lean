-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CubeProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CubeHeights
import Submission.WZ.Obl.wz_slab_local_linearity.IntervalPacking

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric MeasureTheory

noncomputable def cubeAxisPoint (ρ : ℝ) (k : Fin 3 → ℤ) (i : Fin 3) (t : ℝ) : Space3 :=
  WithLp.toLp 2 (fun j => ρ * (k j : ℝ) + if j = i then t else 0)

lemma cubeAxisPoint_mem {ρ t : ℝ} (hρ : 0 < ρ) (ht : t ∈ Ico 0 ρ)
    (k : Fin 3 → ℤ) (i : Fin 3) : cubeAxisPoint ρ k i t ∈ gridCube ρ k := by
  intro j
  change ρ * (k j : ℝ) ≤ ρ * (k j : ℝ) + (if j = i then t else 0) ∧
    ρ * (k j : ℝ) + (if j = i then t else 0) < ρ * ((k j : ℝ) + 1)
  split_ifs <;> constructor <;> linarith [ht.1, ht.2]

lemma inner_cubeAxisPoint (w : Space3) (ρ : ℝ) (k : Fin 3 → ℤ) (i : Fin 3) (t : ℝ) :
    inner ℝ w (cubeAxisPoint ρ k i t) = inner ℝ w (gridCorner ρ k) + w i * t := by
  fin_cases i <;> simp [PiLp.inner_apply, Fin.sum_univ_three, cubeAxisPoint, gridCorner] <;> ring

lemma exists_unit_large_coordinate {w : Space3} (hw : ‖w‖ = 1) :
    ∃ i : Fin 3, 1 / 2 ≤ |w i| := by
  have hn : (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq w
    simpa [hw, Fin.sum_univ_three] using h.symm
  by_contra h
  push Not at h
  have hs (i : Fin 3) : (w i) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w i)) (h i).le (2 : ℕ)
  nlinarith [hs 0, hs 1, hs 2]

/-- A fixed unit projection maps each full cube onto a set containing a uniformly
oriented interval of length half its side. -/
theorem cube_projection_interval {ρ : ℝ} (hρ : 0 < ρ) {w : Space3} (hw : ‖w‖ = 1) :
    ∃ c : ℝ, ∀ k : Fin 3 → ℤ,
      Ioo (inner ℝ w (gridCorner ρ k) + c) (inner ℝ w (gridCorner ρ k) + c + ρ / 2) ⊆
        (fun q : Space3 => inner ℝ w q) '' gridCube ρ k := by
  obtain ⟨i, hi⟩ := exists_unit_large_coordinate hw
  by_cases hwi : 0 ≤ w i
  · rw [abs_of_nonneg hwi] at hi
    have hpos : 0 < w i := by linarith
    refine ⟨0, ?_⟩
    intro k u hu
    let v := inner ℝ w (gridCorner ρ k)
    have hut : 0 < u - v ∧ u - v < ρ / 2 := by
      change v + 0 < u ∧ u < v + 0 + ρ / 2 at hu
      constructor <;> linarith [hu.1, hu.2]
    have ht : (u - v) / w i ∈ Ico 0 ρ := by
      constructor
      · exact div_nonneg hut.1.le hpos.le
      · rw [div_lt_iff₀ hpos]
        nlinarith
    refine ⟨cubeAxisPoint ρ k i ((u - v) / w i), cubeAxisPoint_mem hρ ht k i, ?_⟩
    dsimp only
    rw [inner_cubeAxisPoint]
    change v + w i * ((u - v) / w i) = u
    field_simp
    ring
  · have hneg : w i < 0 := lt_of_not_ge hwi
    rw [abs_of_neg hneg] at hi
    have hpos : 0 < -w i := neg_pos.mpr hneg
    refine ⟨-ρ / 2, ?_⟩
    intro k u hu
    let v := inner ℝ w (gridCorner ρ k)
    have hut : 0 < v - u ∧ v - u < ρ / 2 := by
      change v + -ρ / 2 < u ∧ u < v + -ρ / 2 + ρ / 2 at hu
      constructor <;> linarith [hu.1, hu.2]
    have ht : (v - u) / (-w i) ∈ Ico 0 ρ := by
      constructor
      · exact div_nonneg hut.1.le hpos.le
      · rw [div_lt_iff₀ hpos]
        nlinarith
    refine ⟨cubeAxisPoint ρ k i ((v - u) / (-w i)), cubeAxisPoint_mem hρ ht k i, ?_⟩
    dsimp only
    rw [inner_cubeAxisPoint]
    change v + w i * ((v - u) / (-w i)) = u
    field_simp [hneg.ne]
    ring

/-- Full cubes turn a projection-volume bound into a bottom-scale cover of the
projected lattice corners. -/
theorem cover_projected_corners {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 ≤ B)
    (K : Finset (Fin 3 → ℤ)) {w : Space3} (hw : ‖w‖ = 1) {D : Set ℝ}
    (hD : (fun q : Space3 => inner ℝ w q) '' gridCubes ρ K ⊆ D)
    (hvol : volume D ≤ ENNReal.ofReal B) :
    ∃ (m : ℕ) (c : Fin m → ℝ),
      (fun k => inner ℝ w (gridCorner ρ k)) '' (K : Set (Fin 3 → ℤ)) ⊆
        ⋃ j, closedBall (c j) ρ ∧ (m : ℝ) ≤ 2 * B / ρ := by
  classical
  obtain ⟨c, hc⟩ := cube_projection_interval hρ hw
  let S := K.image (fun k => inner ℝ w (gridCorner ρ k))
  have hsub : ∀ a ∈ S, Ioo (a + c) (a + c + ρ / 2) ⊆ D := by
    intro a ha u hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := hc k hu
    exact hD ⟨q, mem_iUnion₂.mpr ⟨k, hk, hq⟩, rfl⟩
  obtain ⟨m, cc, hcover, hm⟩ := cover_of_intervals_in_set S (by positivity : 0 < ρ / 2)
    (by linarith : ρ / 2 ≤ ρ) hB hsub hvol
  refine ⟨m, cc, ?_, ?_⟩
  · simpa only [S, Finset.coe_image] using hcover
  · calc (m : ℝ) ≤ B / (ρ / 2) := hm
      _ = 2 * B / ρ := by ring

end WangZahlLot.Obl.wz_slab_local_linearity
