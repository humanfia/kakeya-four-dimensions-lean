import Submission.Obl.k4_adapted_oscillation_tests.Frame

/-!
# Tiling a unit ball by small affine cubes

Given an invertible `L` with `‖L w‖ ≤ η ∑ |w j|` and `η n ≤ 1/8`, consider the lattice of
cells `c + L (2 z + [0,2]^n)`, `z ∈ ℤ^n`, and their middle halves
`c + L (2 z + 1/2 + [0,1]^n)` (the tiles). Keep the cells whose corner `c + L (2 z)` lies in
`B(c,1/2)`. The kept tiles are pairwise disjoint and lie in `B(c,1)`; hence there are finitely
many, at most `volume (B(c,1)) / |det L|`. The kept cells cover `B(c,1/4)`, so their number is
at least `volume (B(c,1/4)) / (2^n |det L|)`.
-/

namespace Submission.Obl.k4_adapted_oscillation_tests

open MeasureTheory Metric Set

variable {n : ℕ}

/-- The integer point `z` of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def latticePt (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (z i : ℝ)

/-- The constant vector with all coordinates `1/2`. -/
noncomputable def halfVec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun _ => (1 / 2 : ℝ)

theorem volume_affine_image_equiv
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n)) (s : Set (EuclideanSpace ℝ (Fin n))) :
    volume ((fun x => p + L x) '' s) =
      ENNReal.ofReal |(L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).det| *
        volume s :=
  volume_affine_image (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) p s

theorem det_equiv_ne_zero (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).det ≠ 0 :=
  (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero

theorem volume_box01 :
    volume (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1 : Set (EuclideanSpace ℝ (Fin n))) = 1 := by
  rw [volume_box]
  simp

theorem isCompact_affine_cube (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin n)) :
    IsCompact ((fun x => p + L x) '' (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1)) := by
  refine IsCompact.image (IsCompact.image isCompact_Icc (PiLp.continuous_toLp 2 _)) ?_
  exact continuous_const.add L.continuous

theorem tiling (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (η : ℝ)
    (hη : 0 < η) (hηn : η * n ≤ 1 / 8)
    (hL : ∀ w : EuclideanSpace ℝ (Fin n), ‖L w‖ ≤ η * ∑ j, |w j|)
    (c : EuclideanSpace ℝ (Fin n)) :
    ∃ (k : ℕ) (a : Fin k → EuclideanSpace ℝ (Fin n)),
      (∀ h, (fun x => a h + L x) '' (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1) ⊆
        ball c 1) ∧
      Pairwise (fun h h' =>
        Disjoint ((fun x => a h + L x) '' (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1))
          ((fun x => a h' + L x) '' (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1))) ∧
      (k : ENNReal) *
          ENNReal.ofReal |(L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).det| ≤
        volume (ball c 1) ∧
      volume (ball c (1 / 4)) ≤ 2 ^ n * ((k : ENNReal) *
        ENNReal.ofReal |(L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).det|) := by
  classical
  set cube : Set (EuclideanSpace ℝ (Fin n)) := WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1
    with hcube
  set D : ENNReal :=
    ENNReal.ofReal |(L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).det| with hD
  have hDpos : 0 < D := by
    rw [hD]
    exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (det_equiv_ne_zero L))
  -- corners, tiles and cells
  let a : (Fin n → ℤ) → EuclideanSpace ℝ (Fin n) :=
    fun z => c + L ((2 : ℝ) • latticePt z + halfVec n)
  let tile : (Fin n → ℤ) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun z => (fun x => a z + L x) '' cube
  let cell : (Fin n → ℤ) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun z => (fun x => (c + L ((2 : ℝ) • latticePt z)) + L x) ''
      (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 2)
  let S : Set (Fin n → ℤ) := {z | ‖L ((2 : ℝ) • latticePt z)‖ < 1 / 2}
  have hn8 : (η : ℝ) * n ≤ 1 / 8 := hηn
  -- tiles of kept cells lie in `B(c,1)`
  have hsub : ∀ z ∈ S, tile z ⊆ ball c 1 := by
    intro z hz y hy
    obtain ⟨x, ⟨x', hx', rfl⟩, rfl⟩ := hy
    have hb : ‖L (halfVec n + WithLp.toLp 2 x')‖ ≤ 3 / 16 := by
      refine (hL _).trans ?_
      have : ∑ j, |(halfVec n + WithLp.toLp 2 x') j| ≤ ∑ _j : Fin n, (3 / 2 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h0 := hx'.1 j
        have h1 := hx'.2 j
        simp only [Pi.zero_apply, Pi.one_apply] at h0 h1
        simp only [halfVec, PiLp.add_apply]
        rw [abs_le]
        constructor <;> simp <;> linarith
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      nlinarith
    rw [mem_ball, dist_eq_norm]
    have heq : a z + L (WithLp.toLp 2 x') - c =
        L ((2 : ℝ) • latticePt z) + L (halfVec n + WithLp.toLp 2 x') := by
      simp only [a, map_add]
      abel
    rw [heq]
    calc ‖L ((2 : ℝ) • latticePt z) + L (halfVec n + WithLp.toLp 2 x')‖
        ≤ ‖L ((2 : ℝ) • latticePt z)‖ + ‖L (halfVec n + WithLp.toLp 2 x')‖ := norm_add_le _ _
      _ < 1 / 2 + 3 / 16 := add_lt_add_of_lt_of_le hz hb
      _ < 1 := by norm_num
  -- tiles of distinct lattice points are disjoint
  have hdisj : ∀ z z' : Fin n → ℤ, z ≠ z' → Disjoint (tile z) (tile z') := by
    intro z z' hzz'
    rw [Set.disjoint_left]
    rintro y ⟨x, ⟨x', hx', rfl⟩, rfl⟩ ⟨u, ⟨u', hu', hu⟩, hyu⟩
    apply hzz'
    have h2 : (2 : ℝ) • latticePt z + halfVec n + WithLp.toLp 2 x' =
        (2 : ℝ) • latticePt z' + halfVec n + WithLp.toLp 2 u' := by
      subst hu
      have h := hyu
      simp only [a, add_assoc] at h
      apply L.injective
      rw [map_add L ((2 : ℝ) • latticePt z + halfVec n) (WithLp.toLp 2 x'),
        map_add L ((2 : ℝ) • latticePt z' + halfVec n) (WithLp.toLp 2 u')]
      exact (add_left_cancel h).symm
    funext j
    have h3 := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) h2
    simp [latticePt, halfVec] at h3
    have hx0 := hx'.1 j
    have hx1 := hx'.2 j
    have hu0 := hu'.1 j
    have hu1 := hu'.2 j
    simp only [Pi.zero_apply, Pi.one_apply] at hx0 hx1 hu0 hu1
    have hlt : ((z j : ℝ) - z' j) < 1 := by linarith
    have hgt : -1 < ((z j : ℝ) - z' j) := by linarith
    have hlt' : z j - z' j < 1 := by exact_mod_cast hlt
    have hgt' : -1 < z j - z' j := by exact_mod_cast hgt
    omega
  -- measure of a tile and of a cell
  have hvol_tile : ∀ z, volume (tile z) = D := by
    intro z
    simp only [tile]
    rw [volume_affine_image_equiv, hcube, volume_box01, mul_one]
  have hvol_cell : ∀ z, volume (cell z) = D * 2 ^ n := by
    intro z
    simp only [cell]
    rw [volume_affine_image_equiv, volume_box, hD]
    simp
  have hmeas_tile : ∀ z, MeasurableSet (tile z) := fun z =>
    (isCompact_affine_cube L (a z)).isClosed.measurableSet
  -- finiteness of the kept lattice points
  have hSfin : S.Finite := by
    have hU : volume (⋃ z : S, tile z.1) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (measure_ball_lt_top (x := c) (r := 1)))
      exact Set.iUnion_subset fun z => hsub z.1 z.2
    have hfin := Measure.finite_const_le_meas_of_disjoint_iUnion (volume) hDpos
      (As := fun z : S => tile z.1) (fun z => hmeas_tile z.1)
      (fun z z' hzz' => hdisj z.1 z'.1 fun h => hzz' (Subtype.ext h)) hU
    have huniv : {i : S | D ≤ volume (tile i.1)} = Set.univ := by
      ext i
      simp [hvol_tile]
    rw [huniv] at hfin
    exact Set.finite_coe_iff.mp (Set.finite_univ_iff.mp hfin)
  set F : Finset (Fin n → ℤ) := hSfin.toFinset with hF
  have hmemF : ∀ z, z ∈ F ↔ z ∈ S := fun z => Set.Finite.mem_toFinset hSfin
  -- the count
  have hcount : (F.card : ENNReal) * D ≤ volume (ball c 1) := by
    have h1 : volume (⋃ z ∈ F, tile z) = ∑ z ∈ F, volume (tile z) := by
      refine measure_biUnion_finset ?_ fun z _ => hmeas_tile z
      intro z _ z' _ hzz'
      exact hdisj z z' hzz'
    have h2 : ∑ z ∈ F, volume (tile z) = (F.card : ENNReal) * D := by
      simp [hvol_tile, Finset.sum_const, nsmul_eq_mul]
    rw [← h2, ← h1]
    refine measure_mono ?_
    exact Set.iUnion₂_subset fun z hz => hsub z ((hmemF z).mp hz)
  -- the covering
  have hcover : ball c (1 / 4) ⊆ ⋃ z ∈ F, cell z := by
    intro x hx
    set y := L.symm (x - c) with hy
    let z : Fin n → ℤ := fun j => ⌊y j / 2⌋
    let w : Fin n → ℝ := fun j => y j - 2 * (z j : ℝ)
    have hw0 : ∀ j, 0 ≤ w j := by
      intro j
      have := Int.floor_le (y j / 2)
      simp only [w, z]
      linarith
    have hw2 : ∀ j, w j ≤ 2 := by
      intro j
      have := Int.lt_floor_add_one (y j / 2)
      simp only [w, z]
      linarith
    have hyw : y = (2 : ℝ) • latticePt z + WithLp.toLp 2 w := by
      ext j
      simp [latticePt, w]
    have hxeq : x = c + L ((2 : ℝ) • latticePt z) + L (WithLp.toLp 2 w) := by
      have : x = c + L y := by
        rw [hy, ContinuousLinearEquiv.apply_symm_apply]
        abel
      rw [this, hyw, map_add]
      abel
    have hLw : ‖L (WithLp.toLp 2 w)‖ ≤ 1 / 4 := by
      refine (hL _).trans ?_
      have : ∑ j, |(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n)) j| ≤ ∑ _j : Fin n, (2 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_of_nonneg (hw0 j)]
        exact hw2 j
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      nlinarith
    have hzS : z ∈ S := by
      show ‖L ((2 : ℝ) • latticePt z)‖ < 1 / 2
      have h1 : L ((2 : ℝ) • latticePt z) = (x - c) - L (WithLp.toLp 2 w) := by
        rw [hxeq]
        abel
      rw [h1]
      have hxc : ‖x - c‖ < 1 / 4 := by
        rw [← dist_eq_norm]
        exact hx
      calc ‖x - c - L (WithLp.toLp 2 w)‖ ≤ ‖x - c‖ + ‖L (WithLp.toLp 2 w)‖ := norm_sub_le _ _
        _ < 1 / 4 + 1 / 4 := add_lt_add_of_lt_of_le hxc hLw
        _ = 1 / 2 := by norm_num
    refine Set.mem_iUnion₂.mpr ⟨z, (hmemF z).mpr hzS, ?_⟩
    exact ⟨WithLp.toLp 2 w, ⟨w, ⟨hw0, hw2⟩, rfl⟩, hxeq.symm⟩
  have hcover_vol : volume (ball c (1 / 4)) ≤ 2 ^ n * ((F.card : ENNReal) * D) := by
    refine (measure_mono hcover).trans ((measure_biUnion_finset_le F cell).trans (le_of_eq ?_))
    simp only [hvol_cell, Finset.sum_const, nsmul_eq_mul]
    ring
  -- reindex by `Fin F.card`
  let e := F.equivFin
  refine ⟨F.card, fun h => a (e.symm h).1, ?_, ?_, hcount, hcover_vol⟩
  · intro h
    exact hsub _ ((hmemF _).mp (e.symm h).2)
  · intro h h' hhh'
    refine hdisj _ _ fun heq => hhh' ?_
    exact e.symm.injective (Subtype.ext heq)

end Submission.Obl.k4_adapted_oscillation_tests
