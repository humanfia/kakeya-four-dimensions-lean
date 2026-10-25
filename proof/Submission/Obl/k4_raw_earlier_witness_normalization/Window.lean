import Mathlib

/-!
# Window proximity in normalized earlier coordinates

Two incidences of one current chart in one scalar window of size `N ^ (-m)`
carry the same earlier tag. With `n` the unit normal of the current chart and
`eZ = (n 1, -n 0)` its unit tangent, the planar difference `dY` of the two
incidences splits as

    dY - dt u = ⟪eZ, dY⟫ eZ + err n + dt (⟪n, velocity⟫ n - u),

where `|⟪eZ, dY⟫| ≤ N ^ (-m)` (scalar position identity), `|dt| ≤ N ^ (-m)` and
`|err| ≤ 2 thickness` (normal strip). Applying the inverse earlier frame and the
raw frame bounds gives normalized proximity at most
`N ^ (-m) * N ^ (m - s + χ) / 8 + 2 * N ^ (-s + χ) / 8 ≤ N ^ (-s + χ)`.

The coordinate maps are passed as functions together with their defining
equations, so that the lemma applies to the frozen explicit maps as they stand.
-/

namespace Submission.Obl.k4_raw_earlier_witness_normalization

private theorem norm_three_le (a b₀ b₁ : ℝ) :
    ‖(WithLp.toLp 2 ![a, b₀, b₁] : EuclideanSpace ℝ (Fin 3))‖ ≤
      |a| + ‖(WithLp.toLp 2 ![b₀, b₁] : EuclideanSpace ℝ (Fin 2))‖ := by
  have h3 : ‖(WithLp.toLp 2 ![a, b₀, b₁] : EuclideanSpace ℝ (Fin 3))‖ ^ 2 =
      a ^ 2 + (b₀ ^ 2 + b₁ ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_three]
    ring
  have h2 : ‖(WithLp.toLp 2 ![b₀, b₁] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = b₀ ^ 2 + b₁ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have hb := norm_nonneg (WithLp.toLp 2 ![b₀, b₁] : EuclideanSpace ℝ (Fin 2))
  rw [← sq_le_sq₀ (norm_nonneg _) (add_nonneg (abs_nonneg a) hb), h3, add_sq, sq_abs, h2]
  nlinarith [abs_nonneg a]

/-- Decomposition of a planar vector along a unit normal and its tangent. -/
private theorem planar_decomp (n Y : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) :
    Y = (inner ℝ (WithLp.toLp 2 ![n 1, -n 0] : EuclideanSpace ℝ (Fin 2)) Y) •
        (WithLp.toLp 2 ![n 1, -n 0] : EuclideanSpace ℝ (Fin 2)) + (inner ℝ n Y) • n := by
  have hn2 : n 0 ^ 2 + n 1 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq n
    rw [hn, Fin.sum_univ_two] at h
    linarith
  ext i
  fin_cases i
  · simp [PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination (-Y 0) * hn2
  · simp [PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination (-Y 1) * hn2

/-- Normalized window proximity. -/
theorem window_proximity (N m s χ : ℝ) (hN : 0 < N)
    (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (rawPlanar : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2))
    (normalTangent : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hnt : ∀ n : EuclideanSpace ℝ (Fin 2), normalTangent n = WithLp.toLp 2 ![n 1, -n 0])
    (π₀ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3))
    (hπ : ∀ p : EuclideanSpace ℝ (Fin 4), π₀ p = WithLp.toLp 2 ![p 0, p 1, p 2])
    (Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hΦ : ∀ p : EuclideanSpace ℝ (Fin 4), Φ p = WithLp.toLp 2
      ![(p 0 - t₀) / q,
        (Matrix.toEuclideanLin D⁻¹ (rawPlanar p - c - (p 0) • u)) 0,
        (Matrix.toEuclideanLin D⁻¹ (rawPlanar p - c - (p 0) • u)) 1,
        B * p 3])
    (n center velocity : EuclideanSpace ℝ (Fin 2)) (thickness α : ℝ) (hn : ‖n‖ = 1)
    (hframe : |q⁻¹| + ‖Matrix.toEuclideanLin D⁻¹ (normalTangent n)‖ +
        ‖Matrix.toEuclideanLin D⁻¹ ((inner ℝ n velocity) • n - u)‖ ≤ N ^ (m - s + χ) / 8)
    (hthick : thickness * ‖Matrix.toEuclideanLin D⁻¹ n‖ ≤ N ^ (-s + χ) / 8)
    (Z Z' : EuclideanSpace ℝ (Fin 4)) (t t' Y Y' : ℝ)
    (hZ : Z 0 = t) (hZ' : Z' 0 = t')
    (hY : Y = α + inner ℝ (normalTangent n) (rawPlanar Z))
    (hY' : Y' = α + inner ℝ (normalTangent n) (rawPlanar Z'))
    (hS : |inner ℝ n (rawPlanar Z - center - t • velocity)| ≤ thickness)
    (hS' : |inner ℝ n (rawPlanar Z' - center - t' • velocity)| ≤ thickness)
    (ht : |t - t'| ≤ N ^ (-m)) (hYY : |Y - Y'| ≤ N ^ (-m)) :
    ‖π₀ (Φ Z) - π₀ (Φ Z')‖ ≤ N ^ (-s + χ) := by
  set L := Matrix.toEuclideanLin D⁻¹ with hL
  set eZ := normalTangent n with heZ
  set V := (inner ℝ n velocity) • n - u with hV
  set dt := t - t' with hdt
  set dY := rawPlanar Z - rawPlanar Z' with hdY
  set A := inner ℝ eZ dY with hA
  set err := inner ℝ n (dY - dt • velocity) with herr
  -- the normalized difference
  have hdiff : π₀ (Φ Z) - π₀ (Φ Z') =
      WithLp.toLp 2 ![dt / q, (L (dY - dt • u)) 0, (L (dY - dt • u)) 1] := by
    have hlin : L (dY - dt • u) =
        L (rawPlanar Z - c - (Z 0) • u) - L (rawPlanar Z' - c - (Z' 0) • u) := by
      rw [← map_sub, hZ, hZ', hdY, hdt]
      congr 1
      module
    rw [hπ, hπ, hΦ, hΦ, hlin, hZ, hZ']
    ext i
    fin_cases i
    · simp [hdt]
      ring
    · simp
    · simp
  -- the inverse frame applied to the planar difference
  have hsplit : dY - dt • u = A • eZ + err • n + dt • V := by
    have hd := planar_decomp n dY hn
    rw [← hnt n] at hd
    rw [herr, inner_sub_right, inner_smul_right, hV]
    nth_rewrite 1 [hd]
    rw [← heZ, ← hA]
    module
  have hLsplit : ‖L (dY - dt • u)‖ ≤ |A| * ‖L eZ‖ + |err| * ‖L n‖ + |dt| * ‖L V‖ := by
    rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (le_of_eq ?_)) ?_)
    · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    · rw [norm_smul, Real.norm_eq_abs]
  have hnormL : ‖(WithLp.toLp 2 ![(L (dY - dt • u)) 0, (L (dY - dt • u)) 1] :
      EuclideanSpace ℝ (Fin 2))‖ = ‖L (dY - dt • u)‖ := by
    congr 1
    ext i
    fin_cases i <;> simp
  -- scalar bounds
  have hAb : |A| ≤ N ^ (-m) := by
    have : A = Y - Y' := by
      rw [hY, hY', hA, hdY, inner_sub_right]
      ring
    rw [this]
    exact hYY
  have herrb : |err| ≤ 2 * thickness := by
    have : err = inner ℝ n (rawPlanar Z - center - t • velocity) -
        inner ℝ n (rawPlanar Z' - center - t' • velocity) := by
      rw [herr, ← inner_sub_right]
      congr 1
      rw [hdY, hdt]
      module
    rw [this]
    exact (abs_sub _ _).trans (by linarith)
  have hK : 0 < N ^ (-m) := Real.rpow_pos_of_pos hN _
  have hKmul : N ^ (-m) * N ^ (m - s + χ) = N ^ (-s + χ) := by
    rw [← Real.rpow_add hN]
    ring_nf
  have hpos : 0 < N ^ (-s + χ) := Real.rpow_pos_of_pos hN _
  have hdq : |dt / q| = |dt| * |q⁻¹| := by rw [div_eq_mul_inv, abs_mul]
  have hthick' : 0 ≤ thickness := le_trans (abs_nonneg _) hS
  rw [hdiff]
  refine (norm_three_le _ _ _).trans ?_
  rw [hnormL, hdq]
  have h1 : |dt| * |q⁻¹| + (|A| * ‖L eZ‖ + |err| * ‖L n‖ + |dt| * ‖L V‖) ≤
      N ^ (-m) * (|q⁻¹| + ‖L eZ‖ + ‖L V‖) + 2 * (thickness * ‖L n‖) := by
    have e1 : |dt| * |q⁻¹| ≤ N ^ (-m) * |q⁻¹| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    have e2 : |A| * ‖L eZ‖ ≤ N ^ (-m) * ‖L eZ‖ := mul_le_mul_of_nonneg_right hAb (norm_nonneg _)
    have e3 : |err| * ‖L n‖ ≤ 2 * thickness * ‖L n‖ :=
      mul_le_mul_of_nonneg_right herrb (norm_nonneg _)
    have e4 : |dt| * ‖L V‖ ≤ N ^ (-m) * ‖L V‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    nlinarith
  have h2 : N ^ (-m) * (|q⁻¹| + ‖L eZ‖ + ‖L V‖) ≤ N ^ (-s + χ) / 8 := by
    calc N ^ (-m) * (|q⁻¹| + ‖L eZ‖ + ‖L V‖) ≤ N ^ (-m) * (N ^ (m - s + χ) / 8) :=
          mul_le_mul_of_nonneg_left hframe hK.le
      _ = N ^ (-s + χ) / 8 := by rw [← hKmul]; ring
  linarith [add_le_add_left hLsplit (|dt| * |q⁻¹|)]

end Submission.Obl.k4_raw_earlier_witness_normalization
