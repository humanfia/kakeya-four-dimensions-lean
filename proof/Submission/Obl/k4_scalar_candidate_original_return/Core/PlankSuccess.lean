import Submission.Obl.k4_scalar_candidate_original_return.Core.PlankBasic

/-!
# Posterior neighbour lists on one plank, and the representative fit
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid) (π : CmpParams) (k : ℕ) (ℓ : Fin (a.ct k))
  (i : Fin (a.ls k ℓ).n)

/-- Floors at a common positive step of two values closer than the step differ by at most
one. -/
private theorem abs_floor_sub_le_one {A B h : ℝ} (hh : 0 < h) (hAB : |A - B| < h) :
    |⌊A / h⌋ - ⌊B / h⌋| ≤ 1 := by
  have h1 := Int.floor_le (A / h)
  have h2 := Int.lt_floor_add_one (A / h)
  have h3 := Int.floor_le (B / h)
  have h4 := Int.lt_floor_add_one (B / h)
  have hdiv : |A / h - B / h| < 1 := by
    rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh]
    exact hAB
  have hlo := (abs_lt.1 hdiv).1
  have hhi := (abs_lt.1 hdiv).2
  have hup : ((⌊A / h⌋ - ⌊B / h⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
  have hdn : (-2 : ℝ) < ((⌊A / h⌋ - ⌊B / h⌋ : ℤ) : ℝ) := by push_cast; linarith
  have hup' : ⌊A / h⌋ - ⌊B / h⌋ < 2 := by exact_mod_cast hup
  have hdn' : -2 < ⌊A / h⌋ - ⌊B / h⌋ := by exact_mod_cast hdn
  rw [abs_le]
  constructor <;> omega

/-- A base cell of exponent `r` is tiny compared with the plank's time block. -/
private theorem two_pow_mul_cell_le (s : ℝ) (hP : a.PlankHyp π k ℓ i s) :
    (2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r) ≤ 1 / 4 := by
  obtain ⟨hs₀, hc₀, hθ, hθε, hε, hε1⟩ := hP.par_pos
  obtain ⟨hκ0, hκ1⟩ := hP.κ_range
  obtain ⟨-, hshalf⟩ := hP.s_win
  have hN2 : 2 ≤ a.tangent k := hP.N_ge
  have hN : 0 < a.tangent k := lt_of_lt_of_le two_pos hN2
  have hN1 : 1 ≤ a.tangent k := le_trans one_le_two hN2
  have hs_lo : π.σ.s₀ / 2 ≤ s := by
    have := neg_abs_le (s - π.σ.s₀); linarith
  have hs_hi : s ≤ 3 * π.σ.s₀ / 2 := by
    have := le_abs_self (s - π.σ.s₀); linarith
  have hs0 : 0 ≤ s := by linarith
  have hκs : a.κ * s ≤ s := by nlinarith
  have hR : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
  have hkap : kap0 π ≤ π.σ.c₀ / 32000 := by
    unfold kap0
    have : π.θ ≤ 1 / 32 := by linarith
    have := mul_le_mul_of_nonneg_right this hc₀.le
    linarith
  have hexp : kap0 π + a.κ * s + -π.r ≤ -2 := by
    unfold CmpParams.r
    linarith
  calc (2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r)
      ≤ (a.rK k * a.tangent k ^ (a.κ * s)) * a.tangent k ^ (-π.r) :=
        mul_le_mul_of_nonneg_right hP.T_upper (Real.rpow_nonneg hN.le _)
    _ ≤ (a.tangent k ^ (kap0 π) * a.tangent k ^ (a.κ * s)) * a.tangent k ^ (-π.r) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN.le _)
        exact mul_le_mul_of_nonneg_right hP.K_small (Real.rpow_nonneg hN.le _)
    _ = a.tangent k ^ (kap0 π + a.κ * s + -π.r) := by
        rw [Real.rpow_add hN, Real.rpow_add hN]
    _ ≤ a.tangent k ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hexp
    _ ≤ 1 / 4 := by
        rw [Real.rpow_neg hN.le]
        have h2 : a.tangent k ^ (2 : ℝ) = a.tangent k ^ (2 : ℕ) := by
          exact_mod_cast Real.rpow_natCast (a.tangent k) 2
        rw [h2, one_div]
        apply inv_anti₀ (by norm_num)
        nlinarith

include ha

/-- Non-neighbouring jet bins force separated graphs. -/
theorem far_of_not_nbr (m m' : Fin (a.ncand π k ℓ i))
    (h : ¬ Nbr (a.jetBin π k ℓ i m) (a.jetBin π k ℓ i m')) :
    MatchApply.Far (a.Gz π k ℓ i m) (a.Gz π k ℓ i m') (a.jetStep π k) := by
  by_contra hfar
  apply h
  have hN : 0 < a.tangent k := lt_of_lt_of_le two_pos (ha.tangent_input.1 k)
  have hstep : 0 < a.jetStep π k := Real.rpow_pos_of_pos hN _
  intro j
  have hlt : |eval (QuadBounds.sixPts j) (a.Gz π k ℓ i m) -
      eval (QuadBounds.sixPts j) (a.Gz π k ℓ i m')| < a.jetStep π k := by
    by_contra hge
    exact hfar ⟨QuadBounds.sixPts j, QuadBounds.sixPts_mem_disc j, not_lt.mp hge⟩
  exact abs_floor_sub_le_one hstep hlt

/-- A record charged by the covered set has a good cell. -/
theorem goodCell_of_recMass_ne (s : ℝ) (hP : a.PlankHyp π k ℓ i s)
    (m : Fin (a.ncand π k ℓ i)) (O : (Fin 2 → ℤ) × ℤ) (hO : a.recMass π k ℓ i m O ≠ 0) :
    a.cellZ π k ℓ i O.1 ⊆ MatchApply.sq (1 / 4) := by
  obtain ⟨p, hpC, hpO⟩ : (a.cvd π k ℓ i m ∩ a.recordOf π k ⁻¹' {O}).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hO
    unfold recMass
    rw [hne, measure_empty]
  have hpO' : a.recordOf π k p = O := hpO
  have hN2 : 2 ≤ a.tangent k := hP.N_ge
  have hN : 0 < a.tangent k := lt_of_lt_of_le two_pos hN2
  have hw : 0 < a.tangent k ^ (-π.r) := Real.rpow_pos_of_pos hN _
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  have hK1 : 1 ≤ a.rK k := hP.K_ge
  have hK : 0 < a.rK k := lt_of_lt_of_le one_pos hK1
  have hcell := two_pow_mul_cell_le π k ℓ i s hP
  have hy := (hP.fit p.1 (asg_subset_prior ha π k ℓ i m hpC.1) p.2 hpC.2).1
  obtain ⟨hζ0, hζ1⟩ := zeta_mem_of_fit ha k ℓ i p.1 p.2 hpC.2 hy
  intro z hz
  set ζ : Fin 2 → ℝ := fun e => 2 * z e + 1 / 2 with hζdef
  set u := a.psi k ℓ i ζ with hudef
  have hzeta : a.zeta k ℓ i u = ζ := zeta_psi ha k ℓ i ζ
  -- the base point of `z` and the covered point share their base cell
  have hcellEq : ∀ e, ⌊u e / a.tangent k ^ (-π.r)⌋ =
      ⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / a.tangent k ^ (-π.r)⌋ := by
    intro e
    have h1 : ⌊u e / a.tangent k ^ (-π.r)⌋ = O.1 e := hz e
    rw [h1, ← hpO']
    rfl
  have hclose : ∀ e, |u e - (![p.2, y p.1 p.2] : Fin 2 → ℝ) e| < a.tangent k ^ (-π.r) := by
    intro e
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (hcellEq e)
    rw [← sub_div, abs_div, abs_of_pos hw, div_lt_one hw] at h1
    exact h1
  have hc0 : |u 0 - p.2| < a.tangent k ^ (-π.r) := by simpa using hclose 0
  have hc1 : |u 1 - y p.1 p.2| < a.tangent k ^ (-π.r) := by simpa using hclose 1
  -- normalized coordinates
  have hζu0 : ζ 0 = ((2 : ℝ) ^ (a.ls k ℓ).T * (u 0 - a.tStart k ℓ i) + 1) / 3 := by
    rw [← hzeta]; simp [zeta]
  have hζu1 : ζ 1 = ((2 : ℝ) ^ (a.ls k ℓ).T *
      (u 1 - (a.ls k ℓ).u i - u 0 * (a.ls k ℓ).v i) / a.rK k + 2) / 4 := by
    rw [← hzeta]; simp [zeta]
  have hζb0 : a.zeta k ℓ i ![p.2, y p.1 p.2] 0 =
      ((2 : ℝ) ^ (a.ls k ℓ).T * (p.2 - a.tStart k ℓ i) + 1) / 3 := by simp [zeta]
  have hζb1 : a.zeta k ℓ i ![p.2, y p.1 p.2] 1 = ((2 : ℝ) ^ (a.ls k ℓ).T *
      (y p.1 p.2 - (a.ls k ℓ).u i - p.2 * (a.ls k ℓ).v i) / a.rK k + 2) / 4 := by
    simp [zeta]
  -- differences
  have hd0 : |(2 : ℝ) ^ (a.ls k ℓ).T * (u 0 - p.2)| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos hT]
    calc (2 : ℝ) ^ (a.ls k ℓ).T * |u 0 - p.2| ≤
        (2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r) :=
          mul_le_mul_of_nonneg_left hc0.le hT.le
      _ ≤ 1 / 4 := hcell
  have hv : |(a.ls k ℓ).v i| ≤ a.rK k := by
    have := hP.uv_le
    have := abs_nonneg ((a.ls k ℓ).u i)
    linarith
  have hd1 : |(u 1 - y p.1 p.2) - (u 0 - p.2) * (a.ls k ℓ).v i| ≤
      2 * a.rK k * a.tangent k ^ (-π.r) := by
    calc |(u 1 - y p.1 p.2) - (u 0 - p.2) * (a.ls k ℓ).v i|
        ≤ |u 1 - y p.1 p.2| + |(u 0 - p.2) * (a.ls k ℓ).v i| := abs_sub _ _
      _ = |u 1 - y p.1 p.2| + |u 0 - p.2| * |(a.ls k ℓ).v i| := by rw [abs_mul]
      _ ≤ a.tangent k ^ (-π.r) + a.tangent k ^ (-π.r) * a.rK k := by
          apply add_le_add hc1.le
          exact mul_le_mul hc0.le hv (abs_nonneg _) hw.le
      _ ≤ 2 * a.rK k * a.tangent k ^ (-π.r) := by nlinarith
  have hd1' : |(2 : ℝ) ^ (a.ls k ℓ).T *
      ((u 1 - y p.1 p.2) - (u 0 - p.2) * (a.ls k ℓ).v i) / a.rK k| ≤ 1 / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hT, abs_of_pos hK, div_le_iff₀ hK]
    calc (2 : ℝ) ^ (a.ls k ℓ).T * |(u 1 - y p.1 p.2) - (u 0 - p.2) * (a.ls k ℓ).v i|
        ≤ (2 : ℝ) ^ (a.ls k ℓ).T * (2 * a.rK k * a.tangent k ^ (-π.r)) :=
          mul_le_mul_of_nonneg_left hd1 hT.le
      _ = 2 * a.rK k * ((2 : ℝ) ^ (a.ls k ℓ).T * a.tangent k ^ (-π.r)) := by ring
      _ ≤ 2 * a.rK k * (1 / 4) := mul_le_mul_of_nonneg_left hcell (by positivity)
      _ = 1 / 2 * a.rK k := by ring
  have hdiff0 : ζ 0 - a.zeta k ℓ i ![p.2, y p.1 p.2] 0 =
      (2 : ℝ) ^ (a.ls k ℓ).T * (u 0 - p.2) / 3 := by
    rw [hζu0, hζb0]; ring
  have hdiff1 : ζ 1 - a.zeta k ℓ i ![p.2, y p.1 p.2] 1 =
      ((2 : ℝ) ^ (a.ls k ℓ).T * ((u 1 - y p.1 p.2) - (u 0 - p.2) * (a.ls k ℓ).v i) /
        a.rK k) / 4 := by
    rw [hζu1, hζb1]; field_simp; ring
  have hz0 : z 0 = (ζ 0 - 1 / 2) / 2 := by simp [hζdef]
  have hz1 : z 1 = (ζ 1 - 1 / 2) / 2 := by simp [hζdef]
  intro e
  fin_cases e
  · show |z 0| ≤ 1 / 4
    rw [hz0, abs_le]
    have := abs_le.1 hd0
    constructor <;> nlinarith [hζ0.1, hζ0.2]
  · show |z 1| ≤ 1 / 4
    rw [hz1, abs_le]
    have := abs_le.1 hd1'
    constructor <;> nlinarith [hζ1.1, hζ1.2]

/-- The non-neighbour pair mass on records is at most the separated-pair mass. -/
private theorem badPair_le_farMass (s : ℝ) (hP : a.PlankHyp π k ℓ i s) :
    Posterior.badPairMass (a.ρ k ((a.ls k ℓ).world i)) (a.cvd π k ℓ i) (a.recordOf π k)
      (a.jetBin π k ℓ i) Nbr ≤
    MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) := by
  classical
  let g : (Fin 2 → ℤ) × ℤ → ENNReal := fun O => ∑ m, ∑ m',
    if MatchApply.Far (a.Gz π k ℓ i m) (a.Gz π k ℓ i m') (a.jetStep π k) then
      a.recMass π k ℓ i m O * a.recMass π k ℓ i m' O / a.recTotal π k ℓ i O else 0
  have hle : Posterior.badPairMass (a.ρ k ((a.ls k ℓ).world i)) (a.cvd π k ℓ i)
      (a.recordOf π k) (a.jetBin π k ℓ i) Nbr ≤ ∑' O, g O := by
    unfold Posterior.badPairMass
    apply ENNReal.tsum_le_tsum
    intro O
    apply Finset.sum_le_sum
    intro m _
    apply Finset.sum_le_sum
    intro m' _
    split_ifs with hn hf hf
    · exact zero_le
    · exact le_rfl
    · exact le_rfl
    · exact absurd (far_of_not_nbr ha π k ℓ i m m' hn) hf
  have hvan : ∀ q : Fin 2 → ℤ, ¬ (a.cellZ π k ℓ i q ⊆ MatchApply.sq (1 / 4)) →
      ∀ c, g (q, c) = 0 := by
    intro q hq c
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro m' _
    split_ifs
    · have hm0 : a.recMass π k ℓ i m (q, c) = 0 := by
        by_contra hne
        exact hq (goodCell_of_recMass_ne ha π k ℓ i s hP m (q, c) hne)
      rw [hm0, zero_mul, ENNReal.zero_div]
    · rfl
  calc Posterior.badPairMass (a.ρ k ((a.ls k ℓ).world i)) (a.cvd π k ℓ i) (a.recordOf π k)
        (a.jetBin π k ℓ i) Nbr ≤ ∑' O, g O := hle
    _ = ∑' q, ∑' c, g (q, c) := ENNReal.tsum_prod'
    _ = ∑' q : {q : Fin 2 → ℤ | a.cellZ π k ℓ i q ⊆ MatchApply.sq (1 / 4)},
          ∑' c, g (q.1, c) := by
        rw [tsum_subtype_eq_of_support_subset (f := fun q => ∑' c, g (q, c))]
        intro q hq
        by_contra hnot
        apply hq
        exact ENNReal.tsum_eq_zero.mpr (hvan q hnot)
    _ = MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) := rfl

/-- Posterior-maximizing neighbour lists keep the covered mass up to the separated mass. -/
theorem plank_success (s : ℝ) (hP : a.PlankHyp π k ℓ i s) :
    ∃ bstar : (Fin 2 → ℤ) × ℤ → (Fin 6 → ℤ),
      a.ρ k ((a.ls k ℓ).world i) (a.cov π.θ π.σ k ℓ i) ≤
        a.ρ k ((a.ls k ℓ).world i) (⋃ m, a.cvd π k ℓ i m ∩
          a.recordOf π k ⁻¹' {O | Nbr (bstar O) (a.jetBin π k ℓ i m)}) +
        MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) := by
  have := hP.rho_finite
  obtain ⟨bstar, hb⟩ := Posterior.posterior_success (a.ρ k ((a.ls k ℓ).world i))
    (a.cvd π k ℓ i) (cvd_measurable ha π k ℓ i) (cvd_disjoint ha π k ℓ i)
    (a.recordOf π k) (recordOf_fiber_measurable ha π k)
    (a.jetBin π k ℓ i) Nbr
  refine ⟨bstar, ?_⟩
  rw [← iUnion_cvd ha π k ℓ i]
  exact hb.trans (add_le_add le_rfl (badPair_le_farMass ha π k ℓ i s hP))

/-- Lines assigned to a candidate fit every candidate with the same jet bin. -/
theorem rep_fit (s : ℝ) (hP : a.PlankHyp π k ℓ i s) (m m' : Fin (a.ncand π k ℓ i))
    (hbin : a.jetBin π k ℓ i m = a.jetBin π k ℓ i m') :
    ∀ l ∈ a.asg π k ℓ i m, ∀ t ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i),
      |x l t - eval ![t, y l t] (a.cand π k ℓ i m')| ≤
        a.fitTol π.θ π.σ k + 100 * a.jetStep π k * a.tangent k ^ (-π.σ.s₀) := by
  intro l hl t ht
  have hN : 0 < a.tangent k := lt_of_lt_of_le two_pos hP.N_ge
  have hstep : 0 < a.jetStep π k := Real.rpow_pos_of_pos hN _
  set u : Fin 2 → ℝ := ![t, y l t] with hu
  set ζ := a.zeta k ℓ i u with hζ
  set z : Fin 2 → ℝ := fun e => (ζ e - 1 / 2) / 2 with hz
  have hz2 : (fun e => 2 * z e + 1 / 2) = ζ := by
    funext e
    simp only [hz]
    ring
  -- the difference of the two normalized graphs
  set D := a.Gz π k ℓ i m - a.Gz π k ℓ i m' with hD
  have hDdeg : D.totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans
      (max_le (Gz_totalDegree ha π k ℓ i m) (Gz_totalDegree ha π k ℓ i m'))
  have hpts : ∀ j : Fin 6, |eval (QuadBounds.sixPts j) D| ≤ a.jetStep π k := by
    intro j
    have hfl : ⌊eval (QuadBounds.sixPts j) (a.Gz π k ℓ i m) / a.jetStep π k⌋ =
        ⌊eval (QuadBounds.sixPts j) (a.Gz π k ℓ i m') / a.jetStep π k⌋ := congrFun hbin j
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    rw [← sub_div, abs_div, abs_of_pos hstep, div_lt_one hstep] at h1
    rw [hD, map_sub]
    exact h1.le
  -- the base point lies in the square of half-width 1/4
  have hy := (hP.fit l (asg_subset_prior ha π k ℓ i m hl) t ht).1
  obtain ⟨hζ0, hζ1⟩ := zeta_mem_of_fit ha k ℓ i l t ht hy
  have hzsq : ∀ e, |z e| ≤ 1 / 4 := by
    intro e
    fin_cases e
    · show |(ζ 0 - 1 / 2) / 2| ≤ 1 / 4
      rw [abs_le]
      constructor <;> linarith [hζ0.1, hζ0.2]
    · show |(ζ 1 - 1 / 2) / 2| ≤ 1 / 4
      rw [abs_le]
      constructor <;> linarith [hζ1.1, hζ1.2]
  have hDz := QuadBounds.quad_six_points D hDdeg hpts z hzsq
  -- the difference at `z` is the scaled difference of the candidates at `u`
  have hDu : eval z D = a.tangent k ^ π.σ.s₀ *
      (eval u (a.cand π k ℓ i m) - eval u (a.cand π k ℓ i m')) := by
    have hpsi : a.psi k ℓ i ζ = u := psi_zeta ha k ℓ i u
    rw [hD, map_sub, eval_Gz ha, eval_Gz ha, hz2, eval_Gzeta ha, eval_Gzeta ha, hpsi]
    ring
  have hfit := asg_fit ha π k ℓ i m l hl t ht
  have hNs : 0 < a.tangent k ^ π.σ.s₀ := Real.rpow_pos_of_pos hN _
  have hdiff : |eval u (a.cand π k ℓ i m) - eval u (a.cand π k ℓ i m')| ≤
      100 * a.jetStep π k * a.tangent k ^ (-π.σ.s₀) := by
    rw [hDu, abs_mul, abs_of_pos hNs] at hDz
    rw [Real.rpow_neg hN.le, ← div_eq_mul_inv, le_div_iff₀ hNs]
    linarith
  calc |x l t - eval u (a.cand π k ℓ i m')|
      ≤ |x l t - eval u (a.cand π k ℓ i m)| +
          |eval u (a.cand π k ℓ i m) - eval u (a.cand π k ℓ i m')| := abs_sub_le _ _ _
    _ ≤ a.fitTol π.θ π.σ k + 100 * a.jetStep π k * a.tangent k ^ (-π.σ.s₀) :=
        add_le_add hfit hdiff

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
