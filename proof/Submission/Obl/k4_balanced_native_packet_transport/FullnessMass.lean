import Submission.Obl.k4_balanced_native_packet_transport.UWE.DensityPreparedLaw

/-!
# Velocity pinning and angular charging of pinned packets

**Geometry.** A trajectory that stays in a packet ellipse `c + t u + Q(ball κ)` for a time
window of length `q` has its velocity pinned near `u`:
`norm_v_sub_le` gives `‖v l - u‖ ≤ 2 κ (a + a') / q` whenever `(e, n)` is an orthonormal
frame with `‖Qᵀ e‖ ≤ a`, `‖Qᵀ n‖ ≤ a'`. For the rotation-scaling frame
`D = !![e 0, -g * e 1; e 1, g * e 0]` the two frame norms of `D * Q'` are the row norms of `Q'`
(`norm_frame_transpose_self`, `norm_frame_transpose_perp`), which are bounded by the entrywise
`ℓ¹` norm (`norm_toEuclideanLin_transpose_le`); `norm_v_sub_le_frame` packages the three.

**Angular charging.** Fix a world `γ` of a valid problem and an angular depth
`0 < u ≤ η L`. Off the angular mask and the terminal pure mask the joint density of
(terminal observation, angular bin) is at most `N ^ (-S u + 2 τ)` times the terminal density.
If the packets `F i` have velocities in balls `B(w i, ρ)` and each terminal observation lies
in at most `Λ` packet lists (measurable in the observation), then at most
`Λ (2 ρ / δ + 2) ^ 2` angular bins are permitted above each terminal observation, and
(`angular_charge_le`, through UWE's `angular_list_mass_le`)

  `μ((⋃ i, F i) ∩ Good) ≤ N ^ (-S u + 2 τ) * Λ * (2 ρ / δ(N, u) + 2) ^ 2 * μ(univ)`.

`angular_charge_le_one` is the same estimate in the normalization `p.L = 1`, and
`weighted_angular_charge_le` (`weighted_angular_charge_le'` for any `L`) sums it over the
worlds with the prior weights. `prepared_angular_charge_le` and
`weighted_prepared_angular_charge_le` are the same bounds off a finite density preparation
`densityPreparationBad p S R A τ k γ` with `u ∈ A`.
-/

noncomputable section

namespace Submission.Obl.k4_balanced_native_packet_transport.FullnessMass

open MeasureTheory Set
open Submission.Obl.k4_balanced_native_packet_transport.UWE

/-! ### Plane geometry -/

section Geometry

/-- Coordinates of a `2 × 2` matrix acting on the Euclidean plane. -/
theorem toEuclideanLin_apply_fin2 (M : Matrix (Fin 2) (Fin 2) ℝ)
    (w : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (Matrix.toEuclideanLin M w) i = M i 0 * w 0 + M i 1 * w 1 := by
  fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

theorem norm_sq_fin2 (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

theorem inner_fin2 (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- Parseval's identity for an orthonormal pair of the plane. -/
theorem norm_sq_eq_inner_sq_add {e n : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1)
    (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖z‖ ^ 2 = inner ℝ e z ^ 2 + inner ℝ n z ^ 2 := by
  have he' : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_fin2, he]; norm_num
  have hn' : n 0 ^ 2 + n 1 ^ 2 = 1 := by rw [← norm_sq_fin2, hn]; norm_num
  have hen' : e 0 * n 0 + e 1 * n 1 = 0 := by rw [← inner_fin2]; exact hen
  rw [norm_sq_fin2, inner_fin2, inner_fin2]
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = e 0 * n 1 - e 1 * n 0 := ⟨_, rfl⟩
  have hn0 : n 0 = -e 1 * D := by rw [hD]; linear_combination e 0 * hen' - n 0 * he'
  have hn1 : n 1 = e 0 * D := by rw [hD]; linear_combination e 1 * hen' - n 1 * he'
  have hD2 : D ^ 2 = 1 := by
    rw [hD]
    linear_combination (n 0 ^ 2 + n 1 ^ 2) * he' + hn' - (e 0 * n 0 + e 1 * n 1) * hen'
  rw [hn0, hn1]
  linear_combination (-(z 0 ^ 2 + z 1 ^ 2)) * he' - (-e 1 * z 0 + e 0 * z 1) ^ 2 * hD2

theorem norm_le_abs_inner_add {e n : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1)
    (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖z‖ ≤ |inner ℝ e z| + |inner ℝ n z| := by
  have h := norm_sq_eq_inner_sq_add he hn hen z
  have h1 : ‖z‖ ^ 2 ≤ (|inner ℝ e z| + |inner ℝ n z|) ^ 2 := by
    rw [h]
    nlinarith [abs_nonneg (inner ℝ e z), abs_nonneg (inner ℝ n z), sq_abs (inner ℝ e z),
      sq_abs (inner ℝ n z)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h1

theorem inner_toEuclideanLin (Q : Matrix (Fin 2) (Fin 2) ℝ) (e d : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ e (Matrix.toEuclideanLin Q d) = inner ℝ (Matrix.toEuclideanLin Q.transpose e) d := by
  rw [inner_fin2, inner_fin2, toEuclideanLin_apply_fin2, toEuclideanLin_apply_fin2,
    toEuclideanLin_apply_fin2, toEuclideanLin_apply_fin2]
  simp only [Matrix.transpose_apply]
  ring

theorem toEuclideanLin_mul_inv_apply {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ w) = w := by
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  have h2 := congrArg (fun M => Matrix.toEuclideanLin M w) h1
  simp only [Matrix.toLpLin_mul_same, Matrix.toLpLin_one, LinearMap.comp_apply,
    LinearMap.id_apply] at h2
  exact h2

/-- Trajectories are affine in time with velocity `v l`. -/
theorem y_sub_y (l : Trajectory) (t s : ℝ) : y l s - y l t = (s - t) • v l := by
  ext i
  fin_cases i <;> simp [y, x, v] <;> ring

/-- **Velocity pinning.** If a trajectory stays in the packet ellipse `c + t u + Q(ball κ)`
during a time window of length `q > 0`, and the orthonormal frame `(e, n)` has
`‖Qᵀ e‖ ≤ a`, `‖Qᵀ n‖ ≤ a'`, then its velocity lies within `2 κ (a + a') / q` of `u`. -/
theorem norm_v_sub_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (c u : EuclideanSpace ℝ (Fin 2)) {t₀ q κ a a' : ℝ} (hq : 0 < q) (l : Trajectory)
    (hframe : ∀ t ∈ Set.Icc t₀ (t₀ + q),
      ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ)
    {e n : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (ha : ‖Matrix.toEuclideanLin Q.transpose e‖ ≤ a)
    (ha' : ‖Matrix.toEuclideanLin Q.transpose n‖ ≤ a') :
    ‖v l - u‖ ≤ 2 * κ * (a + a') / q := by
  set w₀ := Matrix.toEuclideanLin Q⁻¹ (y l t₀ - c - t₀ • u) with hw₀
  set w₁ := Matrix.toEuclideanLin Q⁻¹ (y l (t₀ + q) - c - (t₀ + q) • u) with hw₁
  have h₀ : ‖w₀‖ ≤ κ := hframe t₀ ⟨le_rfl, by linarith⟩
  have h₁ : ‖w₁‖ ≤ κ := hframe (t₀ + q) ⟨by linarith, le_rfl⟩
  have hd : ‖w₁ - w₀‖ ≤ 2 * κ := by
    have := norm_sub_le w₁ w₀
    linarith
  have hQd : Matrix.toEuclideanLin Q (w₁ - w₀) = q • (v l - u) := by
    rw [map_sub, hw₀, hw₁, toEuclideanLin_mul_inv_apply hQ, toEuclideanLin_mul_inv_apply hQ]
    have hy := y_sub_y l t₀ (t₀ + q)
    rw [show t₀ + q - t₀ = q by ring] at hy
    rw [smul_sub, ← hy, add_smul]
    abel
  have hnorm : ‖Matrix.toEuclideanLin Q (w₁ - w₀)‖ ≤ (a + a') * (2 * κ) := by
    refine (norm_le_abs_inner_add he hn hen _).trans ?_
    rw [inner_toEuclideanLin, inner_toEuclideanLin]
    have h1 := (abs_real_inner_le_norm (Matrix.toEuclideanLin Q.transpose e) (w₁ - w₀)).trans
      (mul_le_mul ha hd (norm_nonneg _) ((norm_nonneg _).trans ha))
    have h2 := (abs_real_inner_le_norm (Matrix.toEuclideanLin Q.transpose n) (w₁ - w₀)).trans
      (mul_le_mul ha' hd (norm_nonneg _) ((norm_nonneg _).trans ha'))
    linarith
  rw [hQd, norm_smul, Real.norm_of_nonneg hq.le] at hnorm
  rw [le_div_iff₀ hq]
  linarith

/-- The unit normal `n = (-e₁, e₀)` of a unit vector `e` is a unit vector. -/
theorem norm_perp {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) :
    ‖(WithLp.toLp 2 ![-e 1, e 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  have he' : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_fin2, he]; norm_num
  have h : ‖(WithLp.toLp 2 ![-e 1, e 0] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 := by
    rw [norm_sq_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination he'
  have h0 := norm_nonneg (WithLp.toLp 2 ![-e 1, e 0] : EuclideanSpace ℝ (Fin 2))
  nlinarith

/-- The normal `n = (-e₁, e₀)` is orthogonal to `e`. -/
theorem inner_perp (e : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ e (WithLp.toLp 2 ![-e 1, e 0] : EuclideanSpace ℝ (Fin 2)) = 0 := by
  rw [inner_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The rotation-scaling frame `D = [e | g n]` sends the normal `n = (-e₁, e₀)` to `g` times
the second row of `Q'`. -/
theorem norm_frame_transpose_perp {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) {g : ℝ}
    (hg : 0 ≤ g) (Q' : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q').transpose
        (WithLp.toLp 2 ![-e 1, e 0])‖ =
      g * ‖Matrix.toEuclideanLin Q'.transpose (WithLp.toLp 2 ![0, 1])‖ := by
  have he' : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_fin2, he]; norm_num
  have hvec : Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q').transpose
        (WithLp.toLp 2 ![-e 1, e 0]) =
      g • Matrix.toEuclideanLin Q'.transpose (WithLp.toLp 2 ![0, 1]) := by
    ext i
    rw [PiLp.smul_apply, toEuclideanLin_apply_fin2, toEuclideanLin_apply_fin2]
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
    linear_combination (g * Q' 1 i) * he'
  rw [hvec, norm_smul, Real.norm_of_nonneg hg]

/-- The rotation-scaling frame `D = [e | g n]` sends `e` to the first row of `Q'`. -/
theorem norm_frame_transpose_self {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) (g : ℝ)
    (Q' : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q').transpose e‖ =
      ‖Matrix.toEuclideanLin Q'.transpose (WithLp.toLp 2 ![1, 0])‖ := by
  have he' : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_fin2, he]; norm_num
  have hvec : Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q').transpose e =
      Matrix.toEuclideanLin Q'.transpose (WithLp.toLp 2 ![1, 0]) := by
    ext i
    rw [toEuclideanLin_apply_fin2, toEuclideanLin_apply_fin2]
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (Q' 0 i) * he'
  rw [hvec]

/-- The Euclidean operator norm of `Q'ᵀ` is at most the entrywise `ℓ¹` norm of `Q'`. -/
theorem norm_toEuclideanLin_transpose_le (Q' : Matrix (Fin 2) (Fin 2) ℝ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    ‖Matrix.toEuclideanLin Q'.transpose w‖ ≤ (∑ i, ∑ j, |Q' i j|) * ‖w‖ := by
  set z := Matrix.toEuclideanLin Q'.transpose w with hz
  have hz2 : ‖z‖ ≤ |z 0| + |z 1| := by
    have h1 : ‖z‖ ^ 2 ≤ (|z 0| + |z 1|) ^ 2 := by
      rw [norm_sq_fin2]
      nlinarith [abs_nonneg (z 0), abs_nonneg (z 1), sq_abs (z 0), sq_abs (z 1)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hw0 : |w 0| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w 0
  have hw1 : |w 1| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w 1
  have hz0 : |z 0| ≤ |Q' 0 0| * |w 0| + |Q' 1 0| * |w 1| := by
    rw [hz, toEuclideanLin_apply_fin2]
    simp only [Matrix.transpose_apply]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
  have hz1 : |z 1| ≤ |Q' 0 1| * |w 0| + |Q' 1 1| * |w 1| := by
    rw [hz, toEuclideanLin_apply_fin2]
    simp only [Matrix.transpose_apply]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
  simp only [Fin.sum_univ_two]
  have := mul_le_mul_of_nonneg_left hw0 (abs_nonneg (Q' 0 0))
  have := mul_le_mul_of_nonneg_left hw1 (abs_nonneg (Q' 1 0))
  have := mul_le_mul_of_nonneg_left hw0 (abs_nonneg (Q' 0 1))
  have := mul_le_mul_of_nonneg_left hw1 (abs_nonneg (Q' 1 1))
  nlinarith

/-- **Velocity pinning in a rotation-scaling frame.** For `Q = D * Q'` with
`D = !![e 0, -g * e 1; e 1, g * e 0]`, `‖e‖ = 1`, `g ≥ 0`, a trajectory staying in the packet
ellipse during a window of length `q > 0` has velocity within
`2 κ ((1 + g) ∑ |Q' i j|) / q` of `u`. -/
theorem norm_v_sub_le_frame {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) {g : ℝ} (hg : 0 ≤ g)
    {Q' : Matrix (Fin 2) (Fin 2) ℝ} (hQ : (!![e 0, -g * e 1; e 1, g * e 0] * Q').det ≠ 0)
    (c u : EuclideanSpace ℝ (Fin 2)) {t₀ q κ : ℝ} (hq : 0 < q) (l : Trajectory)
    (hframe : ∀ t ∈ Set.Icc t₀ (t₀ + q),
      ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q')⁻¹
        (y l t - c - t • u)‖ ≤ κ) :
    ‖v l - u‖ ≤ 2 * κ * ((1 + g) * ∑ i, ∑ j, |Q' i j|) / q := by
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hframe t₀ ⟨le_rfl, by linarith⟩)
  have h10 : ‖(WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    have h := norm_sq_fin2 (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have h0 := norm_nonneg (WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2))
    nlinarith
  have h01 : ‖(WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    have h := norm_sq_fin2 (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have h0 := norm_nonneg (WithLp.toLp 2 ![(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2))
    nlinarith
  have ha : ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q').transpose e‖ ≤
      ∑ i, ∑ j, |Q' i j| := by
    rw [norm_frame_transpose_self he g Q']
    simpa [h10] using norm_toEuclideanLin_transpose_le Q' (WithLp.toLp 2 ![1, 0])
  have ha' : ‖Matrix.toEuclideanLin (!![e 0, -g * e 1; e 1, g * e 0] * Q').transpose
      (WithLp.toLp 2 ![-e 1, e 0])‖ ≤ g * ∑ i, ∑ j, |Q' i j| := by
    rw [norm_frame_transpose_perp he hg Q']
    have := norm_toEuclideanLin_transpose_le Q' (WithLp.toLp 2 ![0, 1])
    rw [h01, mul_one] at this
    exact mul_le_mul_of_nonneg_left this hg
  have h := norm_v_sub_le hQ c u hq l hframe he (norm_perp he) (inner_perp e) ha ha'
  calc ‖v l - u‖ ≤ 2 * κ * (∑ i, ∑ j, |Q' i j| + g * ∑ i, ∑ j, |Q' i j|) / q := h
    _ = 2 * κ * ((1 + g) * ∑ i, ∑ j, |Q' i j|) / q := by ring

end Geometry

/-! ### Angular bins meeting a velocity ball -/

section Bins

/-- The angular bins of width `δ` meeting the closed ball of radius `ρ` about `w`. -/
def ballBins (δ ρ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun j => Finset.Icc ⌊(w j - ρ) / δ⌋ ⌊(w j + ρ) / δ⌋

theorem bin_mem_ballBins {δ ρ : ℝ} (hδ : 0 < δ) {w z : EuclideanSpace ℝ (Fin 2)}
    (hz : ‖z - w‖ ≤ ρ) : (fun j => ⌊z j / δ⌋) ∈ ballBins δ ρ w := by
  rw [ballBins, Fintype.mem_piFinset]
  intro j
  have hj : |z j - w j| ≤ ρ := by
    have h := PiLp.norm_apply_le (z - w) j
    rw [PiLp.sub_apply, Real.norm_eq_abs] at h
    exact h.trans hz
  obtain ⟨h1, h2⟩ := abs_le.mp hj
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le),
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ.le)⟩

theorem card_Icc_floor_le {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) :
    ((Finset.Icc ⌊a / δ⌋ ⌊b / δ⌋).card : ℝ) ≤ (b - a) / δ + 2 := by
  have hle : ⌊a / δ⌋ ≤ ⌊b / δ⌋ := Int.floor_mono (div_le_div_of_nonneg_right hab hδ.le)
  have hcast : (((Finset.Icc ⌊a / δ⌋ ⌊b / δ⌋).card : ℕ) : ℝ) =
      ((⌊b / δ⌋ + 1 - ⌊a / δ⌋ : ℤ) : ℝ) := by
    rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast]
  push_cast
  have hb : (⌊b / δ⌋ : ℝ) ≤ b / δ := Int.floor_le _
  have ha : a / δ - 1 < (⌊a / δ⌋ : ℝ) := Int.sub_one_lt_floor _
  rw [sub_div]
  linarith

theorem card_ballBins_le {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) (w : EuclideanSpace ℝ (Fin 2)) :
    ((ballBins δ ρ w).card : ℝ) ≤ (2 * ρ / δ + 2) ^ 2 := by
  rw [ballBins, Fintype.card_piFinset, Fin.prod_univ_two, Nat.cast_mul]
  have h (j : Fin 2) : ((Finset.Icc ⌊(w j - ρ) / δ⌋ ⌊(w j + ρ) / δ⌋).card : ℝ) ≤
      2 * ρ / δ + 2 := by
    have := card_Icc_floor_le hδ (show w j - ρ ≤ w j + ρ by linarith)
    rw [show w j + ρ - (w j - ρ) = 2 * ρ by ring] at this
    exact this
  rw [sq]
  exact mul_le_mul (h 0) (h 1) (Nat.cast_nonneg _) (by positivity)

end Bins

/-! ### Clauses of the frozen problem -/

theorem measurable_v : Measurable v := by
  unfold v
  fun_prop

theorem measurable_obs (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  fun_prop

section Valid

variable {p : Problem} {S η : ℝ}

theorem valid_N_pos (hp : p.Valid S η) (k : ℕ) : 0 < p.N k :=
  lt_of_lt_of_le two_pos (hp.1 k)

private theorem valid_L_pos' (hp : p.Valid S η) : 0 < p.L := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  exact hL

private theorem valid_pure_law' (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) {r : ℝ}
    (hr0 : 0 ≤ r) (hrL : r ≤ p.L) :
    Measurable (p.g k γ r) ∧
      (p.incidenceMeasure k γ).map (obs (p.B k γ) (δ (p.N k) r)) =
        (volume.prod Measure.count).withDensity (p.g k γ r) := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  exact hg k γ r hr0 hrL

private theorem valid_angular_law' (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ η * p.L) :
    Measurable (p.G k γ u) ∧
      (p.incidenceMeasure k γ).map
          (fun z : Incidence => (obs (p.B k γ) (δ (p.N k) p.L) z,
            nativeAngularBin (δ (p.N k) u) z)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (p.G k γ u) := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  exact hG k γ u hu huη

/-- Each world's incidence law has total mass at most one. -/
theorem incidenceMeasure_univ_le_one (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) :
    p.incidenceMeasure k γ univ ≤ 1 := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  obtain ⟨M, D, hreg⟩ := hdata
  rcases (hreg k).2.2.2.1 γ with
    ⟨hν, hB, hBu, hBi, hP, hPc, hνfmt, hE, hEI, hEb, hEf, hprior, hfloor⟩
  rw [Problem.incidenceMeasure, Measure.restrict_apply_univ]
  calc ((p.ν k γ).prod volume) (p.E k γ)
      ≤ ((p.ν k γ).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hEI
    _ = 1 := by rw [Measure.prod_prod, measure_univ, Real.volume_Icc]; simp

/-- The prior weights of the worlds are nonnegative and sum to one. -/
theorem valid_weights (hp : p.Valid S η) (k : ℕ) :
    (∀ γ, 0 ≤ p.ω k γ) ∧ ∑ γ, p.ω k γ = 1 := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  obtain ⟨M, D, hreg⟩ := hdata
  exact ⟨(hreg k).2.1, (hreg k).2.2.1⟩

/-- The angular mask and the terminal pure mask are measurable. -/
theorem measurableSet_densityBad (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ η * p.L) (τ : ℝ) :
    MeasurableSet (angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ p.L τ) := by
  have hO := measurable_obs (p.B k γ) (δ (p.N k) p.L)
  have hg := (valid_pure_law' hp k γ (valid_L_pos' hp).le le_rfl).1.comp hO
  have hG := (valid_angular_law' hp k γ hu huη).1.comp
    (hO.prodMk (measurable_nativeAngularBin (δ (p.N k) u)))
  exact (measurableSet_lt measurable_const hG).union
    ((measurableSet_lt hg measurable_const).union (measurableSet_lt measurable_const hg))

end Valid

/-- Off the angular mask and the terminal pure mask, the joint density is at most
`N ^ (-S u + 2 τ)` times the terminal density: the profile offset `f L` cancels. -/
theorem joint_le_of_not_densityBad (p : Problem) (S : ℝ) (k : ℕ) (γ : Fin (p.W k))
    {u τ : ℝ} (hN : 0 < p.N k) {z : Incidence}
    (hz : z ∉ angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ p.L τ) :
    p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) z, nativeAngularBin (δ (p.N k) u) z) ≤
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ)) *
        p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) := by
  have hz' := not_or.mp hz
  have hupper : p.G k γ u
      (obs (p.B k γ) (δ (p.N k) p.L) z, nativeAngularBin (δ (p.N k) u) z) ≤
      ENNReal.ofReal (p.N k ^ (-p.f p.L - S * u + τ)) := le_of_not_gt hz'.1
  have hlower : ENNReal.ofReal (p.N k ^ (-p.f p.L - τ)) ≤
      p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) := le_of_not_gt (not_or.mp hz'.2).1
  have hpow : ENNReal.ofReal (p.N k ^ (-p.f p.L - S * u + τ)) =
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ)) *
        ENNReal.ofReal (p.N k ^ (-p.f p.L - τ)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
    congr 2
    ring
  exact hupper.trans (hpow.trans_le (mul_le_mul' le_rfl hlower))

/-! ### Angular charging of velocity-pinned packets -/

section Charge

variable {p : Problem} {S η : ℝ}

/-- **Angular charging of pinned packets** (one world, any length `L`). Packets `F i` whose
velocities lie in the balls `B(w i, ρ)`, listed above their terminal observations by
measurable lists of size at most `Λ`, carry, off the angular and terminal pure masks, at most
`N ^ (-S u + 2 τ) * Λ * (2 ρ / δ(N, u) + 2) ^ 2` times the total mass of the world. -/
theorem angular_charge_le (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) {u : ℝ} (hu : 0 < u)
    (huη : u ≤ η * p.L) (τ : ℝ) {ι : Type*} [Countable ι] (F : ι → Set Incidence)
    (w : ι → EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ i, ∀ z ∈ F i, ‖v z.1 - w i‖ ≤ ρ) (lst : Observation → Finset ι) {Λ : ℝ}
    (hcard : ∀ o, ((lst o).card : ℝ) ≤ Λ) (hlstm : ∀ i, MeasurableSet {o | i ∈ lst o})
    (hlst : ∀ i, ∀ z ∈ F i, i ∈ lst (obs (p.B k γ) (δ (p.N k) p.L) z)) :
    p.incidenceMeasure k γ
        ((⋃ i, F i) ∩ (angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ p.L τ)ᶜ) ≤
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ) * Λ * (2 * ρ / δ (p.N k) u + 2) ^ 2) *
        p.incidenceMeasure k γ univ := by
  classical
  have hN := valid_N_pos hp k
  have hwd : 0 < δ (p.N k) u := by unfold δ; positivity
  have hO := measurable_obs (p.B k γ) (δ (p.N k) p.L)
  have hA := measurable_nativeAngularBin (δ (p.N k) u)
  obtain ⟨hgm, hpure⟩ := valid_pure_law' hp k γ (valid_L_pos' hp).le le_rfl
  obtain ⟨hGm, hjoint⟩ := valid_angular_law' hp k γ hu huη
  have hBad := measurableSet_densityBad hp k γ hu huη τ
  have hΛ : 0 ≤ Λ := (Nat.cast_nonneg _).trans (hcard (0, 0))
  set Bad := angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ p.L τ with hBad_def
  set X : ℝ := 2 * ρ / δ (p.N k) u + 2 with hX
  -- the permitted angular bins above each terminal observation
  let V : Observation → Finset (Fin 2 → ℤ) := fun o =>
    (lst o).biUnion fun i => ballBins (δ (p.N k) u) ρ (w i)
  have hVm : ∀ b, MeasurableSet {o | b ∈ V o} := by
    intro b
    have heq : {o | b ∈ V o} =
        ⋃ i, ({o | i ∈ lst o} ∩ {_o | b ∈ ballBins (δ (p.N k) u) ρ (w i)}) := by
      ext o
      simp [V, Finset.mem_biUnion]
    rw [heq]
    exact MeasurableSet.iUnion fun i => (hlstm i).inter (MeasurableSet.const _)
  have hVcard : ∀ o, ((V o).card : ENNReal) ≤ ENNReal.ofReal (Λ * X ^ 2) := by
    intro o
    have h1 : ((V o).card : ℝ) ≤
        ∑ i ∈ lst o, ((ballBins (δ (p.N k) u) ρ (w i)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : ∑ i ∈ lst o, ((ballBins (δ (p.N k) u) ρ (w i)).card : ℝ) ≤
        ∑ _i ∈ lst o, X ^ 2 :=
      Finset.sum_le_sum fun i _ => card_ballBins_le hwd hρ (w i)
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : ((V o).card : ℝ) ≤ Λ * X ^ 2 :=
      h1.trans (h2.trans (mul_le_mul_of_nonneg_right (hcard o) (sq_nonneg _)))
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal h3
  -- a measurable enlargement of the packet union
  let F' : ι → Set Incidence := fun i =>
    {z | ‖v z.1 - w i‖ ≤ ρ} ∩ obs (p.B k γ) (δ (p.N k) p.L) ⁻¹' {o | i ∈ lst o}
  have hF' : ∀ i, MeasurableSet (F' i) := fun i =>
    (measurableSet_le ((measurable_v.comp measurable_fst).sub_const (w i)).norm
      measurable_const).inter (hO (hlstm i))
  set Z' := (⋃ i, F' i) ∩ Badᶜ with hZ'_def
  have hZ' : MeasurableSet Z' := (MeasurableSet.iUnion hF').inter hBad.compl
  have hsub : (⋃ i, F i) ∩ Badᶜ ⊆ Z' := by
    rintro z ⟨hz, hzB⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact ⟨mem_iUnion.mpr ⟨i, hw i z hi, hlst i z hi⟩, hzB⟩
  have hgood : ∀ᵐ z ∂(p.incidenceMeasure k γ).restrict Z',
      obs (p.B k γ) (δ (p.N k) p.L) z ∈ (univ : Set Observation) ∧
      nativeAngularBin (δ (p.N k) u) z ∈ V (obs (p.B k γ) (δ (p.N k) p.L) z) ∧
      p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) z, nativeAngularBin (δ (p.N k) u) z) ≤
        ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ)) *
          p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) := by
    filter_upwards [ae_restrict_mem hZ'] with z hz
    obtain ⟨hzF, hzB⟩ := hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzF
    refine ⟨mem_univ _, ?_, joint_le_of_not_densityBad p S k γ hN hzB⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi.2, bin_mem_ballBins hwd hi.1⟩
  have hmain := angular_list_mass_le (p.incidenceMeasure k γ)
    ((p.incidenceMeasure k γ).restrict Z') Measure.restrict_le_self
    (volume.prod Measure.count) _ hO _ hA _ hgm _ hGm hpure hjoint
    (ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ))) (ENNReal.ofReal (Λ * X ^ 2)) univ
    MeasurableSet.univ V hVm hVcard hgood
  rw [Measure.restrict_apply_univ, preimage_univ] at hmain
  calc p.incidenceMeasure k γ ((⋃ i, F i) ∩ Badᶜ)
      ≤ p.incidenceMeasure k γ Z' := measure_mono hsub
    _ ≤ _ := hmain
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), mul_assoc]

/-- **Angular charging of pinned packets** in the normalization `p.L = 1`. -/
theorem angular_charge_le_one (hp : p.Valid S η) (hL : p.L = 1) (k : ℕ) (γ : Fin (p.W k))
    {u : ℝ} (hu : 0 < u) (huη : u ≤ η) (τ : ℝ) {ι : Type*} [Countable ι]
    (F : ι → Set Incidence) (w : ι → EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ i, ∀ z ∈ F i, ‖v z.1 - w i‖ ≤ ρ) (lst : Observation → Finset ι) {Λ : ℝ}
    (hcard : ∀ o, ((lst o).card : ℝ) ≤ Λ) (hlstm : ∀ i, MeasurableSet {o | i ∈ lst o})
    (hlst : ∀ i, ∀ z ∈ F i, i ∈ lst (obs (p.B k γ) (δ (p.N k) 1) z)) :
    p.incidenceMeasure k γ
        ((⋃ i, F i) ∩ (angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ 1 τ)ᶜ) ≤
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ) * Λ * (2 * ρ / δ (p.N k) u + 2) ^ 2) *
        p.incidenceMeasure k γ univ := by
  have h := angular_charge_le hp k γ hu (by rw [hL, mul_one]; exact huη) τ F w hρ hw lst
    hcard hlstm (by rw [hL]; exact hlst)
  rwa [hL] at h

/-- **Weighted angular charging** (any length `L`): the prior-weighted sum over the worlds. -/
theorem weighted_angular_charge_le' (hp : p.Valid S η) (k : ℕ) {u : ℝ} (hu : 0 < u)
    (huη : u ≤ η * p.L) (τ : ℝ) {ι : Type*} [Countable ι]
    (F : Fin (p.W k) → ι → Set Incidence) (w : Fin (p.W k) → ι → EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hw : ∀ γ i, ∀ z ∈ F γ i, ‖v z.1 - w γ i‖ ≤ ρ)
    (lst : Fin (p.W k) → Observation → Finset ι) {Λ : ℝ}
    (hcard : ∀ γ o, ((lst γ o).card : ℝ) ≤ Λ)
    (hlstm : ∀ γ i, MeasurableSet {o | i ∈ lst γ o})
    (hlst : ∀ γ i, ∀ z ∈ F γ i, i ∈ lst γ (obs (p.B k γ) (δ (p.N k) p.L) z)) :
    ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ
        ((⋃ i, F γ i) ∩ (angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ p.L τ)ᶜ) ≤
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ) * Λ * (2 * ρ / δ (p.N k) u + 2) ^ 2) := by
  obtain ⟨hω0, hω1⟩ := valid_weights hp k
  set C := ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ) * Λ * (2 * ρ / δ (p.N k) u + 2) ^ 2)
    with hC
  calc ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ
        ((⋃ i, F γ i) ∩ (angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ p.L τ)ᶜ)
      ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) * C := by
        refine Finset.sum_le_sum fun γ _ => mul_le_mul' le_rfl ?_
        refine (angular_charge_le hp k γ hu huη τ (F γ) (w γ) hρ (hw γ) (lst γ) (hcard γ)
          (hlstm γ) (hlst γ)).trans ?_
        calc C * p.incidenceMeasure k γ univ ≤ C * 1 :=
              mul_le_mul' le_rfl (incidenceMeasure_univ_le_one hp k γ)
          _ = C := mul_one C
    _ = (∑ γ, ENNReal.ofReal (p.ω k γ)) * C := (Finset.sum_mul _ _ _).symm
    _ = C := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => hω0 γ), hω1, ENNReal.ofReal_one,
          one_mul]

/-- **Weighted angular charging** in the normalization `p.L = 1`: for each world `γ`, packets
`F γ i` with velocities in `B(w γ i, ρ)` and terminal lists `lst γ` of size at most `Λ`. -/
theorem weighted_angular_charge_le (hp : p.Valid S η) (hL : p.L = 1) (k : ℕ) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ η) (τ : ℝ) {ι : Type*} [Countable ι]
    (F : Fin (p.W k) → ι → Set Incidence) (w : Fin (p.W k) → ι → EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hw : ∀ γ i, ∀ z ∈ F γ i, ‖v z.1 - w γ i‖ ≤ ρ)
    (lst : Fin (p.W k) → Observation → Finset ι) {Λ : ℝ}
    (hcard : ∀ γ o, ((lst γ o).card : ℝ) ≤ Λ)
    (hlstm : ∀ γ i, MeasurableSet {o | i ∈ lst γ o})
    (hlst : ∀ γ i, ∀ z ∈ F γ i, i ∈ lst γ (obs (p.B k γ) (δ (p.N k) 1) z)) :
    ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ
        ((⋃ i, F γ i) ∩ (angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ 1 τ)ᶜ) ≤
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ) * Λ * (2 * ρ / δ (p.N k) u + 2) ^ 2) := by
  have h := weighted_angular_charge_le' hp k hu (by rw [hL, mul_one]; exact huη) τ F w hρ hw
    lst hcard hlstm (by rw [hL]; exact hlst)
  rwa [hL] at h

/-- The two masks used above are part of every finite density preparation containing `u`. -/
theorem densityBad_subset_preparation (p : Problem) (S : ℝ) (R A : Finset ℝ) (τ : ℝ) (k : ℕ)
    (γ : Fin (p.W k)) {u : ℝ} (huA : u ∈ A) :
    angularDensityBad p S k γ u τ ∪ pureDensityBad p k γ p.L τ ⊆
      densityPreparationBad p S R A τ k γ := by
  rintro z (hz | hz)
  · exact Or.inr (mem_iUnion₂.mpr ⟨u, huA, hz⟩)
  · exact Or.inl (mem_iUnion₂.mpr ⟨p.L, Finset.mem_insert_self _ _, hz⟩)

/-- **Angular charging off a finite density preparation** (one world, any length `L`). -/
theorem prepared_angular_charge_le (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ η * p.L) (τ : ℝ) (R A : Finset ℝ) (huA : u ∈ A) {ι : Type*}
    [Countable ι] (F : ι → Set Incidence) (w : ι → EuclideanSpace ℝ (Fin 2)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hw : ∀ i, ∀ z ∈ F i, ‖v z.1 - w i‖ ≤ ρ) (lst : Observation → Finset ι)
    {Λ : ℝ} (hcard : ∀ o, ((lst o).card : ℝ) ≤ Λ)
    (hlstm : ∀ i, MeasurableSet {o | i ∈ lst o})
    (hlst : ∀ i, ∀ z ∈ F i, i ∈ lst (obs (p.B k γ) (δ (p.N k) p.L) z)) :
    p.incidenceMeasure k γ ((⋃ i, F i) ∩ (densityPreparationBad p S R A τ k γ)ᶜ) ≤
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ) * Λ * (2 * ρ / δ (p.N k) u + 2) ^ 2) *
        p.incidenceMeasure k γ univ :=
  (measure_mono (inter_subset_inter_right _ (compl_subset_compl.mpr
    (densityBad_subset_preparation p S R A τ k γ huA)))).trans
    (angular_charge_le hp k γ hu huη τ F w hρ hw lst hcard hlstm hlst)

/-- **Weighted angular charging off a finite density preparation** (any length `L`). -/
theorem weighted_prepared_angular_charge_le (hp : p.Valid S η) (k : ℕ) {u : ℝ} (hu : 0 < u)
    (huη : u ≤ η * p.L) (τ : ℝ) (R A : Finset ℝ) (huA : u ∈ A) {ι : Type*} [Countable ι]
    (F : Fin (p.W k) → ι → Set Incidence) (w : Fin (p.W k) → ι → EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hw : ∀ γ i, ∀ z ∈ F γ i, ‖v z.1 - w γ i‖ ≤ ρ)
    (lst : Fin (p.W k) → Observation → Finset ι) {Λ : ℝ}
    (hcard : ∀ γ o, ((lst γ o).card : ℝ) ≤ Λ)
    (hlstm : ∀ γ i, MeasurableSet {o | i ∈ lst γ o})
    (hlst : ∀ γ i, ∀ z ∈ F γ i, i ∈ lst γ (obs (p.B k γ) (δ (p.N k) p.L) z)) :
    ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ
        ((⋃ i, F γ i) ∩ (densityPreparationBad p S R A τ k γ)ᶜ) ≤
      ENNReal.ofReal (p.N k ^ (-S * u + 2 * τ) * Λ * (2 * ρ / δ (p.N k) u + 2) ^ 2) := by
  refine le_trans (Finset.sum_le_sum fun γ _ => mul_le_mul' le_rfl (measure_mono
    (inter_subset_inter_right _ (compl_subset_compl.mpr
      (densityBad_subset_preparation p S R A τ k γ huA))))) ?_
  exact weighted_angular_charge_le' hp k hu huη τ F w hρ hw lst hcard hlstm hlst

end Charge

end Submission.Obl.k4_balanced_native_packet_transport.FullnessMass
