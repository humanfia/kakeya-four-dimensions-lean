-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGTheorem.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGNumerics

/-!
# Weak global grains from the plane-grains transfer (child 2 of the split of o061)

Sticky Prop. 4.1 up to the final mild rescaling: if there are examples below `σ` and none
above, and the plane-grains transfer holds at `σ`, then there are arbitrarily small extremal
families with weak global grains (a Lipschitz slope `f` with AD twisted slices) and weak local
grains (a Lipschitz plane map with AD local projections).

Parameters, with `e = min ε (1/10)` and `θ = c / (1 + c)`:
* the second transfer with error `ε2 = e c / 100` (input error `η2`);
* the rescaled fibre with error `εF = min (η2/4) (σ/4)`;
* the coarse lower bound at `tF = σ + εF / 4` (error `ηtF`);
* the two-scale decomposition with error `εT = min ηtF (εF/8) (c e / 128)` at `r = τ ^ θ`;
* the first transfer with output error `ε1 = min ηTS εT (εF/8) (η2/8) (c e / 64)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

/-- The plane-grains transfer, in terms of `PGTAt`. -/
def PlaneGrainsTransferAt (σ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ ε : ℝ, 0 < ε → ∃ η d1 : ℝ, 0 < η ∧ 0 < d1 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ (1 / 100 : ℝ) → PGTAt σ c ε η δ

/-- Weak global and local grains (child 2 of the split of o061). -/
theorem gg_theorem {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hbelow : ∀ t, t < σ → Examples t) (habove : ∀ t, σ < t → ¬Examples t)
    (hPGT : PlaneGrainsTransferAt σ) :
    ∀ ε d0 : ℝ, 0 < ε → 0 < d0 → WeakGrainsAt σ ε d0 := by
  intro ε d0 hε hd0
  obtain ⟨c, hc0, hc1, hPf⟩ := hPGT
  -- the exponents
  set e : ℝ := min ε (1 / 10) with he_def
  have he : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have he10 : e ≤ 1 / 10 := min_le_right _ _
  set ε2 : ℝ := e * c / 100 with hε2_def
  have hε2 : 0 < ε2 := by positivity
  obtain ⟨η2, d2, hη2, hd2, hP2⟩ := hPf ε2 hε2
  set εF : ℝ := min (η2 / 4) (σ / 4) with hεF_def
  have hεF : 0 < εF := lt_min (by positivity) (by positivity)
  have hεFη : εF ≤ η2 / 4 := min_le_left _ _
  have hεFσ : εF ≤ σ / 4 := min_le_right _ _
  set tF : ℝ := σ + εF / 4 with htF
  obtain ⟨ηtF, dtF, hηtF, hdtF, hlowF⟩ :=
    (not_examples_iff tF).mp (habove tF (by rw [htF]; linarith))
  set θ : ℝ := c / (1 + c) with hθ_def
  have hθ0 : 0 < θ := by positivity
  have hθ2 : θ ≤ 1 / 2 := by rw [hθ_def, div_le_iff₀ (by positivity)]; linarith
  have hθc : (1 - θ) * c = θ := by rw [hθ_def]; field_simp; ring
  have hθc2 : c / 2 ≤ θ := by rw [hθ_def, le_div_iff₀ (by positivity)]; nlinarith
  set εT : ℝ := min (min ηtF (εF / 8)) (c * e / 128) with hεT_def
  have hεT : 0 < εT := lt_min (lt_min hηtF (by positivity)) (by positivity)
  have hεTη : εT ≤ ηtF := (min_le_left _ _).trans (min_le_left _ _)
  have hεTF : εT ≤ εF / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hεTc : εT ≤ c * e / 128 := min_le_right _ _
  obtain ⟨ηTS, dTS, hηTS, hdTS, hTS⟩ := two_scale_theorem habove εT hεT
  set ε1 : ℝ := min (min ηTS εT) (min (εF / 8) (min (η2 / 8) (c * e / 64))) with hε1_def
  have hε1 : 0 < ε1 := lt_min (lt_min hηTS hεT)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hε1TS : ε1 ≤ ηTS := (min_le_left _ _).trans (min_le_left _ _)
  have hε1T : ε1 ≤ εT := (min_le_left _ _).trans (min_le_right _ _)
  have hε1F : ε1 ≤ εF / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1η : ε1 ≤ η2 / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε1c : ε1 ≤ c * e / 64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨η1, d1, hη1, hd1, hP1⟩ := hPf ε1 hε1
  set τ'max : ℝ := min d2 (1 / 100) with hτ'max
  have hτ'maxpos : 0 < τ'max := lt_min hd2 (by norm_num)
  -- the exponents of the cutoffs are positive
  have hce : 0 < c * e := by positivity
  have p1 : 0 < θ - εT := by nlinarith
  have p2 : 0 < 1 - 2 * θ := by
    rw [hθ_def]
    have : 2 * (c / (1 + c)) < 1 := by rw [← mul_div_assoc, div_lt_one (by positivity)]; linarith
    linarith
  have p3 : 0 < 1 - θ := by linarith
  have p4 : 0 < (1 - θ) * εF - 2 * εT := by nlinarith
  have p5 : 0 < (1 - θ) * εF - θ * (εF / 4) - εT - ε1 := by nlinarith
  have p6 : 0 < θ - εT - ε1 := by nlinarith
  have p7 : 0 < (1 - θ) * (η2 - 2 * εF) - ε1 := by nlinarith
  have p8 : 0 < c * e / 32 - 2 * εT := by linarith
  have p9 : 0 < c * e / 32 - ε2 := by rw [hε2_def]; nlinarith
  have p10 : 0 < c * e / 32 - ε1 := by linarith
  have p11 : 0 < 5 * (c * e / 32) - ε1 := by linarith
  have p12 : 0 < c / 4 := by positivity
  -- the cutoffs on `τ`
  set C4 : ℝ := 1 / (2 * ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈εT⁻¹⌉₊ + 3) *
      (1 + 384 * 2312 * 10 ^ 4 * ((⌈εT⁻¹⌉₊ + 3 : ℕ) : ℝ))) with hC4
  have hC4 : 0 < C4 := by positivity
  obtain ⟨τcut, hτcut, hcut⟩ :=
    cutoff_and (exists_rpow_cutoff p1
      (by positivity : (0 : ℝ) < min (1 / 1000) (min dtF (1 / 100))))
    (cutoff_and (exists_rpow_cutoff p2 (by norm_num : (0 : ℝ) < 25 / 256))
    (cutoff_and (exists_rpow_cutoff p3 (by positivity : (0 : ℝ) < min (1 / 10000000) τ'max))
    (cutoff_and (exists_rpow_cutoff p4 (by positivity : (0 : ℝ) < min (1 / (34 * 10 ^ 7)) C4))
    (cutoff_and (exists_rpow_cutoff p5 (by norm_num : (0 : ℝ) < 1 / 15730))
    (cutoff_and (exists_rpow_cutoff p6 (by norm_num : (0 : ℝ) < 1 / 320))
    (cutoff_and (exists_rpow_cutoff p7 (by norm_num : (0 : ℝ) < 1 / 20873216))
    (cutoff_and (exists_rpow_cutoff p8 (by norm_num : (0 : ℝ) < 1 / 200))
    (cutoff_and (exists_rpow_cutoff p9 (by norm_num : (0 : ℝ) < 1 / 32))
    (cutoff_and (exists_rpow_cutoff p10 (by norm_num : (0 : ℝ) < 1 / 1280))
    (cutoff_and (exists_rpow_cutoff p11 (by norm_num : (0 : ℝ) < 1 / 83200))
    (cutoff_and (exists_rpow_cutoff p12 hd0)
      (exists_rpow_cutoff one_pos (by positivity : (0 : ℝ) < min dTS (1 / 100))))))))))))))
  -- a fine family below `σ`
  have hcε : 0 < c - ε1 := by nlinarith
  set dδ0 : ℝ := τcut ^ (1 / (c - ε1)) with hdδ0_def
  have hdδ0 : 0 < dδ0 := Real.rpow_pos_of_pos hτcut _
  obtain ⟨δ0, hδ0, hδ0d, hδ01, n, x, v, Y, hF0, hS0, hvol0⟩ :=
    hbelow (σ - η1) (by linarith) η1 (min d1 dδ0) hη1 (lt_min hd1 hdδ0)
  -- the first plane-grains transfer
  obtain ⟨τ, hτlo, hτhi, hτ1, n1, x1, v1, Y1, hF1, hS1, hvol1, -, V, hV1, hVv, hVL, hloc⟩ :=
    hP1 δ0 hδ0 (hδ0d.trans (min_le_left _ _)) hδ01 n x v Y hF0 hS0 hvol0
  have hτ : 0 < τ := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ0 c) hτlo
  have hτcut' : τ ≤ τcut := by
    calc τ ≤ δ0 ^ (c - ε1) := hτhi
      _ ≤ dδ0 ^ (c - ε1) := Real.rpow_le_rpow hδ0.le (hδ0d.trans (min_le_right _ _)) hcε.le
      _ = τcut := by
          rw [hdδ0_def, ← Real.rpow_mul hτcut.le, one_div, inv_mul_cancel₀ hcε.ne', Real.rpow_one]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := hcut τ hτ hτcut'
  have hτ1' : τ ≤ 1 := hτ1.trans (by norm_num)
  have hτTS : τ ≤ dTS := by
    have := c13.trans (min_le_left _ _); rwa [Real.rpow_one] at this
  -- the two-scale decomposition at `r = τ ^ θ`
  have hr1 : τ ^ (1 - εT) ≤ τ ^ θ := Real.rpow_le_rpow_of_exponent_ge hτ hτ1' (by nlinarith)
  have hr2 : τ ^ θ ≤ τ ^ εT := Real.rpow_le_rpow_of_exponent_ge hτ hτ1' (by nlinarith)
  obtain ⟨ρc, hrρc, hρcr, hTSat⟩ := hTS τ hτ hτTS hτ1 n1 x1 v1 Y1
    (hF1.mono_error hτ hτ1' hε1TS) (hS1.mono_error hτ hτ1' hε1TS)
    (hvol1.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hτ hτ1' (by linarith)))) (τ ^ θ) hr1 hr2
  have hρchi : ρc ≤ τ ^ (θ - εT) := by
    calc ρc ≤ τ ^ (-εT) * τ ^ θ := hρcr
      _ = τ ^ (θ - εT) := by rw [← Real.rpow_add hτ]; congr 1; ring
  have hρc0 : 0 < ρc := lt_of_lt_of_le (Real.rpow_pos_of_pos hτ θ) hrρc
  -- the coarse lower bound
  have hlow : ∀ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family εT ρc m x' v' Y' → Separated εT ρc m x' v' →
        ENNReal.ofReal (ρc ^ tF) < volume (⋃ q, Y' q) := by
    intro m x' v' Y' hF' hS'
    have hρc1 : ρc ≤ 1 / 100 := hρchi.trans (c1.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hρcd : ρc ≤ dtF := hρchi.trans (c1.trans ((min_le_right _ _).trans (min_le_left _ _)))
    exact hlowF ρc hρc0 hρcd hρc1 m x' v' Y' (hF'.mono_error hρc0 (by linarith) hεTη)
      (hS'.mono_error hρc0 (by linarith) hεTη)
  -- the global grains
  exact gg_from_tau (εF := εF) (εT := εT) (ε1 := ε1) (tF := tF) (τ'max := τ'max) hσ0 hσ1.le
    hε.le (by rw [hε2_def]; nlinarith) hτ hτ1 hε1T hεT hεF hF1 hS1 hvol1 hV1 hVv hVL hloc hTSat
    hlow (fun τ' hτ'0 hτ'm hτ'1 => hP2 τ' hτ'0 (hτ'm.trans (min_le_left _ _)) hτ'1)
    (by linarith)
    (fun ρ0 hρ0lo hρ0hi hτρ0 => ggnum_of hτ hτ1 hσ0.le hσ1.le he heε hc0 hc1.le hθc hθ0 hθ2
      hε2.le (by rw [hε2_def]; nlinarith) hεT hε1.le hεF (by linarith) (by linarith) htF hrρc
      hρchi hρ0lo hρ0hi hτρ0 (c1.trans (min_le_left _ _)) c2 (c3.trans (min_le_left _ _))
      (c3.trans (min_le_right _ _)) (c4.trans (min_le_left _ _)) (c4.trans (min_le_right _ _))
      c5 c6 c7 c8 c9 c10 c11 c12)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
