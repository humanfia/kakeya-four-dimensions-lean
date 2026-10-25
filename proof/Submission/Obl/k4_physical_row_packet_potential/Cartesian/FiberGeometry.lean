-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/FiberGeometry.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/FiberGeometry.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.QualWitness

/-!
# Witness trajectories run along the grid fibers

In the grid coordinates `u = A⁻¹ z` of a spanning velocity triple, a witness
trajectory of velocity close to `J axis`, through a state whose grid point is
`g`, is at normalized time `t` close to the fiber point
`fiberPoint axis key t`, where `key` consists of the two other coordinates of
`g`.  This is the geometric input of the fiber-time lists (paper tex-06
l. 966-977: "Such a line stays within `Kξ` of the fiber throughout the block").
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open Matrix

noncomputable section

/-- The key of the `axis`-fiber through a real grid point. -/
def realFiberKey (axis : Fin 3) (g : Fin 3 → ℝ) : ℝ × ℝ :=
  ![(g 1, g 2), (g 0, g 2), (g 0, g 1)] axis

theorem abs_sub_fiberPoint_le (axis : Fin 3) (g y : Fin 3 → ℝ) (t c : ℝ)
    (hothers : ∀ i, i ≠ axis → |y i - g i| ≤ c)
    (haxis : |y axis - (t - (g 0 + g 1 + g 2) + g axis)| ≤ c) (i : Fin 3) :
    |y i - fiberPoint axis (realFiberKey axis g) t i| ≤ c := by
  fin_cases axis <;> fin_cases i <;>
    first
    | (simpa [fiberPoint, realFiberKey] using hothers _ (by decide))
    | (convert haxis using 2; simp [fiberPoint, realFiberKey]; ring)

/-- **A witness trajectory near its fiber.**  `u = Ainv cz` are the grid
coordinates of the state center `cz`, `g` its grid point, `zw` the witness
position at normalized time `sw = zw 0`, and `vw` the witness velocity, within
`η` of `J axis`.  At any normalized time `t ∈ [0, 1]` the witness position
`zw + (t - sw) (1, vw)` lies within `27 K² ξ` of the frame image of the fiber
point. -/
theorem witness_near_fiber {J : Fin 3 → Fin 2 → ℝ} {Ainv : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : liftMatrix J * Ainv = 1) {K ξ ε η : ℝ} (hK : 1 ≤ K) (hξ : 0 ≤ ξ)
    (hε : 0 ≤ ε) (hεξ : ε ≤ ξ) (hη : 0 ≤ η) (hηξ : η ≤ ξ)
    (hJ : ∀ i k, |J i k| ≤ K) (hAinv : ∀ i k, |Ainv i k| ≤ K)
    (cz g zw : Fin 3 → ℝ) (hg : ∀ i, |(Ainv *ᵥ cz) i - g i| ≤ ξ / 2)
    (hzw : ∀ i, |zw i - cz i| ≤ ε) (axis : Fin 3) (vw : Fin 2 → ℝ)
    (hvw : ∀ k, |vw k - J axis k| ≤ η) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hsw : zw 0 ∈ Set.Icc (0 : ℝ) 1) (i : Fin 3) :
    |(zw + (t - zw 0) • lift vw) i -
        (liftMatrix J *ᵥ fiberPoint axis (realFiberKey axis g) t) i| ≤ 27 * K ^ 2 * ξ := by
  set u := Ainv *ᵥ cz with hu
  set y := Ainv *ᵥ (zw + (t - zw 0) • lift vw) with hy
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  -- decomposition of the grid coordinates of the witness position
  have hdecomp : y = u + Ainv *ᵥ (zw - cz) + (t - zw 0) • (Pi.single axis 1 : Fin 3 → ℝ) +
      (t - zw 0) • (Ainv *ᵥ (lift vw - lift (J axis))) := by
    rw [hy, hu, mulVec_add, mulVec_smul, mulVec_sub, mulVec_sub, inv_mulVec_lift hA axis]
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have htw : |t - zw 0| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hsw.1, hsw.2]
  have h1 : ∀ k, |(Ainv *ᵥ (zw - cz)) k| ≤ 3 * K * ε := fun k =>
    abs_mulVec_le Ainv (zw - cz) hAinv (fun j => by simpa using hzw j) k
  have h2 : ∀ k, |((t - zw 0) • (Ainv *ᵥ (lift vw - lift (J axis)))) k| ≤ 3 * K * η := by
    intro k
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    have := abs_mulVec_le Ainv (lift vw - lift (J axis)) hAinv
      (fun j => by simpa using abs_lift_sub_le hη hvw j) k
    calc |t - zw 0| * |(Ainv *ᵥ (lift vw - lift (J axis))) k| ≤ 1 * (3 * K * η) :=
          mul_le_mul htw this (abs_nonneg _) zero_le_one
      _ = 3 * K * η := one_mul _
  -- the normalized time of the witness and the sum of the grid coordinates
  have hsum : |zw 0 - (g 0 + g 1 + g 2)| ≤ ε + 3 * (ξ / 2) := by
    have hcz0 : cz 0 = u 0 + u 1 + u 2 := by
      have := liftMatrix_mulVec_zero J u
      rw [hu, frame_mulVec_inv hA] at this
      simpa [Fin.sum_univ_three] using this
    have e0 := hzw 0
    have g0 := hg 0
    have g1 := hg 1
    have g2 := hg 2
    rw [abs_le] at e0 g0 g1 g2 ⊢
    constructor <;> linarith [e0.1, e0.2, g0.1, g0.2, g1.1, g1.2, g2.1, g2.2]
  -- closeness in grid coordinates
  have hclose : ∀ k, |y k - fiberPoint axis (realFiberKey axis g) t k| ≤ 9 * K * ξ := by
    apply abs_sub_fiberPoint_le axis g y t (9 * K * ξ)
    · intro k hk
      have hsingle : (Pi.single axis (1 : ℝ) : Fin 3 → ℝ) k = 0 := Pi.single_eq_of_ne hk 1
      have hyk : y k = u k + (Ainv *ᵥ (zw - cz)) k +
          ((t - zw 0) • (Ainv *ᵥ (lift vw - lift (J axis)))) k := by
        rw [hdecomp]; simp [hsingle]
      have a1 := h1 k
      have a2 := h2 k
      have a3 := hg k
      rw [hyk]
      rw [abs_le] at a1 a2 a3 ⊢
      constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
    · have hyk : y axis = u axis + (Ainv *ᵥ (zw - cz)) axis + (t - zw 0) +
          ((t - zw 0) • (Ainv *ᵥ (lift vw - lift (J axis)))) axis := by
        rw [hdecomp]; simp
      have a1 := h1 axis
      have a2 := h2 axis
      have a3 := hg axis
      rw [hyk]
      rw [abs_le] at a1 a2 a3 hsum ⊢
      constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, hsum.1, hsum.2]
  -- back to normalized base coordinates
  have hframe : zw + (t - zw 0) • lift vw = liftMatrix J *ᵥ y := by
    rw [hy, frame_mulVec_inv hA]
  rw [hframe, ← Pi.sub_apply, ← mulVec_sub]
  have := abs_mulVec_le (liftMatrix J) (y - fiberPoint axis (realFiberKey axis g) t)
    (abs_liftMatrix_le hK hJ) (fun k => by simpa using hclose k) i
  calc _ ≤ 3 * K * (9 * K * ξ) := this
    _ = 27 * K ^ 2 * ξ := by ring

/-- A state whose grid coordinates are within `ξ / 2` of the grid point `g`
has all its incidences within `3 K ξ` of the frame image of `g`. -/
theorem state_near_grid {J : Fin 3 → Fin 2 → ℝ} {Ainv : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : liftMatrix J * Ainv = 1) {K ξ ε : ℝ} (hK : 1 ≤ K) (hξ : 0 ≤ ξ)
    (hεξ : ε ≤ ξ) (hJ : ∀ i k, |J i k| ≤ K)
    (cz g z : Fin 3 → ℝ) (hg : ∀ i, |(Ainv *ᵥ cz) i - g i| ≤ ξ / 2)
    (hz : ∀ i, |z i - cz i| ≤ ε) (i : Fin 3) :
    |z i - (liftMatrix J *ᵥ g) i| ≤ 3 * K * ξ := by
  have hcz : cz = liftMatrix J *ᵥ (Ainv *ᵥ cz) := (frame_mulVec_inv hA cz).symm
  have h1 : |cz i - (liftMatrix J *ᵥ g) i| ≤ 3 * K * (ξ / 2) := by
    rw [hcz, ← Pi.sub_apply, ← mulVec_sub]
    exact abs_mulVec_le _ _ (abs_liftMatrix_le hK hJ) (fun k => by simpa using hg k) i
  have h2 := hz i
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
