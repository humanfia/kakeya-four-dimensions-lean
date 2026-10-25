-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.MiddleMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.MiddleAux
import Submission.WZ.Obl.wz_intermediate_twist_normalization.MiddleGlue
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Main

/-!
# The middle offset range from graceful B

`middle_of_GBe : GBe → MiddleRange`.

Parameters, for `ε₀ = min ε 1`, the black box at `ε₀ / 4` with exponent
`η' = min η_B (min (ε₀ / 10) κ)`: `r0 = δ^(η'/4) / 4`, `e = 16 r0²`, `Z = r0 |c| / 1000`,
`ρ = 10 Z |c| δ`, `η = η' / 12`, the threshold `λ = 288 C Kt Z δ² ρ^(-ε₀/4)` with
`Kt = δ^(-η) n / Z²`.

The truncated mass is at least half the mass (`class_mass_le`, at most `15` enlarged classes per
tube), and the truncated energy is at most `λ M' + n 5 δ³ R_far` (`trunc_energy`). Both terms
are at most `δ^(-ε)` times `M'²/2`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN proj CountF slX icX
  nat_succ_le_rpow exists_dyadic)
open WangZahlLot.Obl.wz_compact_offset_normalization (Family Frostman Slope Projection)

/-- `δ ≤ t^(1/s)` gives `δ^s ≤ t`. -/
theorem rpow_le_of_le_rpow_inv {δ s t : ℝ} (hδ : 0 < δ) (hs : 0 < s) (ht : 0 < t)
    (h : δ ≤ t ^ (1 / s)) : δ ^ s ≤ t := by
  calc δ ^ s ≤ (t ^ (1 / s)) ^ s := Real.rpow_le_rpow hδ.le h hs.le
    _ = t := by rw [← Real.rpow_mul ht.le, one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]

theorem rpow_pos_threshold {s t : ℝ} (ht : 0 < t) : 0 < t ^ (1 / s) := Real.rpow_pos_of_pos ht _

/-- The final real inequality. -/
theorem final_real {A m lam F d : ℝ} (hm : 0 < m) (hlam : 0 < lam) (hF : 0 ≤ F)
    (hE : m ^ 2 ≤ A * (lam * m + F)) (h1 : d * lam ≤ m / 2) (h2 : d * F ≤ m ^ 2 / 2) :
    d ≤ A := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < lam * m + F := by positivity
  have : A * (lam * m + F) < d * (lam * m + F) := mul_lt_mul_of_pos_right hlt hpos
  have h3 : d * (lam * m + F) ≤ m ^ 2 := by
    have := mul_le_mul_of_nonneg_right h1 hm.le
    nlinarith
  linarith

/-- The near term of the final estimate. -/
theorem near_arith {δ ε ε0 η a εG C1 Z ρ n m : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC1 : 0 < C1)
    (hZ : 0 < Z) (hρ : 0 < ρ) (hn : 0 ≤ n) (hexp : ε0 / 2 + a + εG + 2 * η ≤ ε)
    (hεG : 0 ≤ εG) (hZa : δ ^ a ≤ 40 * Z) (hρδ : δ ≤ ρ)
    (ht5 : δ ^ (ε0 / 2) ≤ 1 / (46080 * C1)) (hm : δ ^ η * n * δ ^ 2 / 2 ≤ m) :
    δ ^ ε * (288 * C1 * (δ ^ (-η) * n / Z ^ 2) * Z * δ ^ 2 * ρ ^ (-εG)) ≤ m / 2 := by
  have e1 : δ ^ ε * δ ^ (-η) ≤ δ ^ (ε0 / 2) * δ ^ a * δ ^ εG * δ ^ η := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hρε : 0 < ρ ^ εG := Real.rpow_pos_of_pos hρ _
  have e2 : δ ^ εG * ρ ^ (-εG) ≤ 1 := by
    rw [Real.rpow_neg hρ.le, ← div_eq_mul_inv, div_le_one hρε]
    exact Real.rpow_le_rpow hδ.le hρδ hεG
  have e3 : δ ^ a / Z ≤ 40 := by rw [div_le_iff₀ hZ]; linarith
  have e4 : δ ^ (ε0 / 2) * (288 * 40 * C1) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_right ht5 (by positivity : (0 : ℝ) ≤ 288 * 40 * C1)
    calc δ ^ (ε0 / 2) * (288 * 40 * C1) ≤ 1 / (46080 * C1) * (288 * 40 * C1) := this
      _ = 1 / 4 := by field_simp; norm_num
  have hδη : 0 < δ ^ η := Real.rpow_pos_of_pos hδ _
  have hδε2 : 0 ≤ δ ^ (ε0 / 2) := by positivity
  have hP : 0 ≤ n * δ ^ 2 := by positivity
  have hneg : 0 ≤ ρ ^ (-εG) := by positivity
  calc δ ^ ε * (288 * C1 * (δ ^ (-η) * n / Z ^ 2) * Z * δ ^ 2 * ρ ^ (-εG))
      = 288 * C1 * (n * δ ^ 2) * ((δ ^ ε * δ ^ (-η)) * ρ ^ (-εG) / Z) := by
        field_simp
    _ ≤ 288 * C1 * (n * δ ^ 2) *
          ((δ ^ (ε0 / 2) * δ ^ a * δ ^ εG * δ ^ η) * ρ ^ (-εG) / Z) := by
        gcongr
    _ = 288 * C1 * (n * δ ^ 2) * (δ ^ (ε0 / 2) * δ ^ η) *
          ((δ ^ a / Z) * (δ ^ εG * ρ ^ (-εG))) := by
        field_simp
    _ ≤ 288 * C1 * (n * δ ^ 2) * (δ ^ (ε0 / 2) * δ ^ η) * (40 * 1) := by
        gcongr
    _ = (δ ^ (ε0 / 2) * (288 * 40 * C1)) * (δ ^ η * n * δ ^ 2) := by ring
    _ ≤ 1 / 4 * (δ ^ η * n * δ ^ 2) := by gcongr
    _ ≤ m / 2 := by linarith

/-- The far term of the final estimate. -/
theorem far_arith {δ ε ε0 η n m : ℝ} {K : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε0)
    (hε01 : ε0 ≤ 1) (hε0ε : ε0 ≤ ε) (hη : 0 < η) (hηε : 12 * η ≤ ε0) (hn : 0 ≤ n)
    (hK2 : (2 : ℝ) ^ K * δ ≤ 1 / 10) (ht6 : δ ^ (ε0 / 2) ≤ ε0 / 212890)
    (hm : δ ^ η * n * δ ^ 2 / 2 ≤ m) :
    δ ^ ε * (n * (5 * δ ^ 3 * (((K : ℝ) + 1) *
      (36 * δ * (8 * δ ^ (-η) * n) * (27 / 100 + 2 + 4 / 100))))) ≤ m ^ 2 / 2 := by
  set σ := ε0 / 4 with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
  have hδη : 0 < δ ^ η := Real.rpow_pos_of_pos hδ _
  have hKlog : ((K : ℝ) + 1) * δ ^ σ ≤ 8 / ε0 := by
    have h1 := nat_succ_le_rpow hσ0 hσ1 K
    have h2 : ((2 : ℝ) ^ K) ^ σ * δ ^ σ ≤ 1 := by
      rw [← Real.mul_rpow (by positivity) hδ.le]
      exact Real.rpow_le_one (by positivity) (by linarith) hσ0.le
    calc ((K : ℝ) + 1) * δ ^ σ ≤ (2 / σ) * ((2 : ℝ) ^ K) ^ σ * δ ^ σ := by gcongr
      _ = (2 / σ) * (((2 : ℝ) ^ K) ^ σ * δ ^ σ) := by ring
      _ ≤ (2 / σ) * 1 := by gcongr
      _ = 8 / ε0 := by rw [hσ]; field_simp; norm_num
  have e1 : δ ^ ε * δ ^ (-η) ≤ δ ^ σ * δ ^ (ε0 / 2) * (δ ^ η * δ ^ η) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by rw [hσ]; linarith)
  have ht6' : δ ^ (ε0 / 2) * (8 / ε0) ≤ 8 / 212890 := by
    calc δ ^ (ε0 / 2) * (8 / ε0) ≤ ε0 / 212890 * (8 / ε0) :=
          mul_le_mul_of_nonneg_right ht6 (by positivity)
      _ = 8 / 212890 := by field_simp
  have hm2 : (δ ^ η * n * δ ^ 2 / 2) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
  have hQ : 0 ≤ (δ ^ η * δ ^ η) * δ ^ 4 * n ^ 2 := by positivity
  calc δ ^ ε * (n * (5 * δ ^ 3 * (((K : ℝ) + 1) *
        (36 * δ * (8 * δ ^ (-η) * n) * (27 / 100 + 2 + 4 / 100)))))
      = 3326.4 * ((K : ℝ) + 1) * (δ ^ ε * δ ^ (-η)) * δ ^ 4 * n ^ 2 := by ring
    _ ≤ 3326.4 * ((K : ℝ) + 1) * (δ ^ σ * δ ^ (ε0 / 2) * (δ ^ η * δ ^ η)) * δ ^ 4 * n ^ 2 := by
        gcongr
    _ = 3326.4 * (((K : ℝ) + 1) * δ ^ σ) * δ ^ (ε0 / 2) * ((δ ^ η * δ ^ η) * δ ^ 4 * n ^ 2) := by
        ring
    _ ≤ 3326.4 * (8 / ε0) * δ ^ (ε0 / 2) * ((δ ^ η * δ ^ η) * δ ^ 4 * n ^ 2) := by gcongr
    _ = 3326.4 * (δ ^ (ε0 / 2) * (8 / ε0)) * ((δ ^ η * δ ^ η) * δ ^ 4 * n ^ 2) := by ring
    _ ≤ 3326.4 * (8 / 212890) * ((δ ^ η * δ ^ η) * δ ^ 4 * n ^ 2) := by gcongr
    _ ≤ (δ ^ η * n * δ ^ 2 / 2) ^ 2 / 2 := by
        have : (δ ^ η * n * δ ^ 2 / 2) ^ 2 / 2 = 1 / 8 * ((δ ^ η * δ ^ η) * δ ^ 4 * n ^ 2) := by
          ring
        rw [this]
        apply mul_le_mul_of_nonneg_right _ hQ
        norm_num
    _ ≤ m ^ 2 / 2 := by linarith

set_option maxHeartbeats 1000000 in
/-- **The middle range from graceful B.** -/
theorem middle_of_GBe (hGB : GBe) : MiddleRange := by
  intro κ hκ ε hε
  set ε0 := min ε 1 with hε0def
  have hε0 : 0 < ε0 := lt_min hε one_pos
  have hε01 : ε0 ≤ 1 := min_le_right _ _
  have hε0ε : ε0 ≤ ε := min_le_left _ _
  set εG := ε0 / 4 with hεGdef
  have hεG : 0 < εG := by positivity
  obtain ⟨η1, hη1, d1, hd1, C1, hC1, hG1⟩ := hGB.exists_at hεG
  set ηG := min η1 (min (ε0 / 10) κ) with hηGdef
  have hηG : 0 < ηG := lt_min hη1 (lt_min (by positivity) hκ)
  have hηGη1 : ηG ≤ η1 := min_le_left _ _
  have hηGε : ηG ≤ ε0 / 10 := (min_le_right _ _).trans (min_le_left _ _)
  have hηGκ : ηG ≤ κ := (min_le_right _ _).trans (min_le_right _ _)
  have hG := hG1.mono hηG hηGη1
  set dG := min d1 1 with hdGdef
  have hdG : 0 < dG := lt_min hd1 one_pos
  set a := ηG / 4 with hadef
  have ha : 0 < a := by positivity
  set η := ηG / 12 with hηdef
  have hη : 0 < η := by positivity
  -- the thresholds
  set T1 := (1 / 4000 : ℝ) ^ (1 / κ)
  set T2 := (min dG (1 / 2)) ^ (1 / a)
  set T3 := (1 / 4 : ℝ) ^ (1 / (ηG / 12))
  set T4 := (1 / 23280 : ℝ) ^ (1 / (ηG / 4))
  set T5 := (1 / (46080 * C1)) ^ (1 / (ε0 / 2))
  set T6 := (ε0 / 212890) ^ (1 / (ε0 / 2))
  have hT2pos : 0 < min dG (1 / 2) := lt_min hdG (by norm_num)
  refine ⟨η, hη, min (1 / 100) (min T1 (min T2 (min T3 (min T4 (min T5 T6))))), ?_, ?_⟩
  · refine lt_min (by norm_num) (lt_min (rpow_pos_threshold (by norm_num))
      (lt_min (rpow_pos_threshold hT2pos) (lt_min (rpow_pos_threshold (by norm_num))
        (lt_min (rpow_pos_threshold (by norm_num)) (lt_min (rpow_pos_threshold (by positivity))
          (rpow_pos_threshold (by positivity)))))))
  intro δ hδ hδd0 hδ100 n x v Y hfam htrans hF f hf hc100 hδc hκc hcbig
  have hδ1 : δ ≤ 1 := by linarith
  have hδT1 : δ ≤ T1 := hδd0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδT2 : δ ≤ T2 :=
    hδd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδT3 : δ ≤ T3 := hδd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδT4 : δ ≤ T4 := hδd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδT5 : δ ≤ T5 := hδd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))))
  have hδT6 : δ ≤ T6 := hδd0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))))
  have t1 : δ ^ κ ≤ 1 / 4000 := rpow_le_of_le_rpow_inv hδ hκ (by norm_num) hδT1
  have t2 : δ ^ a ≤ min dG (1 / 2) := rpow_le_of_le_rpow_inv hδ ha hT2pos hδT2
  have t3 : δ ^ (ηG / 12) ≤ 1 / 4 := rpow_le_of_le_rpow_inv hδ (by positivity) (by norm_num) hδT3
  have t4 : δ ^ (ηG / 4) ≤ 1 / 23280 :=
    rpow_le_of_le_rpow_inv hδ (by positivity) (by norm_num) hδT4
  have t5 : δ ^ (ε0 / 2) ≤ 1 / (46080 * C1) :=
    rpow_le_of_le_rpow_inv hδ (by positivity) (by positivity) hδT5
  have t6 : δ ^ (ε0 / 2) ≤ ε0 / 212890 :=
    rpow_le_of_le_rpow_inv hδ (by positivity) (by positivity) hδT6
  -- the family
  obtain ⟨hn, hv, hT, hdist, hYm, hYT, hmass⟩ := hfam
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfS : SlopeN f := hf
  have hfc : Continuous f := hfS.continuous
  have hFc : CountF η δ n x v := hF
  set c := f 0 with hcdef
  have hc0 : 0 < |c| := by linarith
  have hcne : c ≠ 0 := abs_pos.mp hc0
  have hc2 : 0 < c ^ 2 := by positivity
  have hc2abs : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  -- the offset range
  have hδc' : δ * c ^ 2 ≤ 1 := hδc.le
  have hcsmall : c ^ 2 * δ ≤ δ ^ (1 / 3 : ℝ) := by
    have h1 : |c| ^ 2 ≤ (δ ^ (-(1 / 3 : ℝ) + ε0 / 4)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg c) hcbig.le 2
    have h2 : (δ ^ (-(1 / 3 : ℝ) + ε0 / 4)) ^ 2 * δ = δ ^ (1 / 3 + ε0 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add_one hδ.ne']
      congr 1; push_cast; ring
    have h3 : δ ^ (1 / 3 + ε0 / 2 : ℝ) ≤ δ ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    rw [hc2abs]
    calc |c| ^ 2 * δ ≤ (δ ^ (-(1 / 3 : ℝ) + ε0 / 4)) ^ 2 * δ := by gcongr
      _ = _ := h2
      _ ≤ _ := h3
  have hcbig2 : δ ^ (-(2 * κ)) ≤ c ^ 2 := by
    have h1 : (δ ^ (-κ)) ^ 2 ≤ |c| ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hδ.le _) hκc.le 2
    rw [hc2abs]
    calc δ ^ (-(2 * κ)) = (δ ^ (-κ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; congr 1; push_cast; ring
      _ ≤ |c| ^ 2 := h1
  -- the parameters
  set r0 := δ ^ a / 4 with hr0def
  have hδa : 0 < δ ^ a := Real.rpow_pos_of_pos hδ _
  have hr0 : 0 < r0 := by positivity
  have hδa1 : δ ^ a ≤ 1 / 2 := t2.trans (min_le_right _ _)
  have hδadG : δ ^ a ≤ dG := t2.trans (min_le_left _ _)
  set Z := r0 * |c| / 1000 with hZdef
  have hZ : 0 < Z := by positivity
  set ρ := 10 * Z * |c| * δ with hρdef
  have hρ0 : 0 < ρ := by positivity
  set e := 16 * r0 ^ 2 with hedef
  have he : e = (δ ^ a) ^ 2 := by rw [hedef, hr0def]; ring
  have he4 : e ≤ 1 / 4 := by
    rw [he]
    calc (δ ^ a) ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hδa.le hδa1 2
      _ = 1 / 4 := by norm_num
  have hρval : ρ = δ ^ a * (c ^ 2 * δ) / 400 := by
    rw [hρdef, hZdef, hr0def, hc2abs]; ring
  have hcδ1 : c ^ 2 * δ ≤ 1 := by linarith
  have hρr : ρ ≤ r0 / 4 := by
    rw [hρval, hr0def]
    have : δ ^ a * (c ^ 2 * δ) ≤ δ ^ a := mul_le_of_le_one_right hδa.le hcδ1
    linarith
  have hZc : 1 ≤ Z * |c| := by
    have hδaκ : δ ^ a * δ ^ (-(2 * κ)) ≥ 4000 := by
      rw [← Real.rpow_add hδ]
      have h1 : δ ^ (a + -(2 * κ)) ≥ δ ^ (-κ) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by rw [hadef]; linarith)
      have h2 : δ ^ (-κ) = (δ ^ κ)⁻¹ := Real.rpow_neg hδ.le κ
      have h3 : (δ ^ κ)⁻¹ ≥ 4000 := by
        have hδκ : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
        rw [ge_iff_le, le_inv_comm₀ (by norm_num) hδκ]
        linarith
      linarith
    have : Z * |c| = δ ^ a * c ^ 2 / 4000 := by rw [hZdef, hr0def, hc2abs]; ring
    rw [this, le_div_iff₀ (by norm_num)]
    calc 1 * 4000 ≤ δ ^ a * δ ^ (-(2 * κ)) := by linarith
      _ ≤ δ ^ a * c ^ 2 := by gcongr
  have hρe : ρ ≤ e / 4 := by
    rw [hρval, he]
    have h1 : δ ^ (1 / 3 : ℝ) ≤ δ ^ a :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by rw [hadef]; linarith)
    have h2 : c ^ 2 * δ ≤ δ ^ a := hcsmall.trans h1
    have h3 : δ ^ a * (c ^ 2 * δ) ≤ δ ^ a * δ ^ a := by gcongr
    have h4 : (δ ^ a) ^ 2 = δ ^ a * δ ^ a := sq _
    have h5 : 0 ≤ δ ^ a * δ ^ a := by positivity
    rw [h4]
    linarith
  have hρdG : ρ ≤ dG := by
    have : ρ ≤ δ ^ a := by
      rw [hρval]
      have := mul_le_of_le_one_right hδa.le hcδ1
      linarith
    exact this.trans hδadG
  have hρle : ρ ≤ δ ^ (1 / 3 : ℝ) := by
    rw [hρval]
    have : δ ^ a * (c ^ 2 * δ) ≤ 1 * δ ^ (1 / 3 : ℝ) :=
      mul_le_mul (by linarith) hcsmall (by positivity) (by norm_num)
    linarith
  have hρ1 : ρ ≤ 1 := hρle.trans (Real.rpow_le_one hδ.le hδ1 (by norm_num))
  have hρηG : ρ ^ ηG ≤ δ ^ (ηG / 3) := by
    calc ρ ^ ηG ≤ (δ ^ (1 / 3 : ℝ)) ^ ηG := Real.rpow_le_rpow hρ0.le hρle hηG.le
      _ = δ ^ (ηG / 3) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
  have hρr0 : ρ ^ ηG ≤ r0 := by
    have h1 : δ ^ (ηG / 3) = δ ^ (ηG / 12) * δ ^ a := by
      rw [← Real.rpow_add hδ]; congr 1; rw [hadef]; ring
    rw [hr0def]
    calc ρ ^ ηG ≤ δ ^ (ηG / 3) := hρηG
      _ = δ ^ (ηG / 12) * δ ^ a := h1
      _ ≤ 1 / 4 * δ ^ a := by gcongr
      _ = δ ^ a / 4 := by ring
  have hρδ : δ ≤ ρ := by
    rw [hρdef]
    have : 10 * Z * |c| * δ = 10 * (Z * |c|) * δ := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hZc hδ.le
    linarith
  -- classes satisfy the hypotheses of the zoom
  have hCG : ∀ k ∈ clIdxSet f x v, ∀ j ∈ clSet c x v k,
      CG c δ Z ρ e r0 (clα c k) (clβ c k) (x j) (v j) := by
    intro k hk j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hα, hβ⟩ := clSet_bounds hc100 hj
    exact {
      hc := hc100, hδ := hδ, hδc := hδc', hv := hv j, hv2 := htrans j, hT := hT j,
      hα := hα, hβ := hβ, hβ3 := abs_clβ_le hc100 (hv i) (htrans i), hZ := hZ, hZc := hZc,
      hZr := le_rfl, hρ := rfl, hr0 := hr0, he16 := le_rfl, he4 := he4, hρe := hρe,
      hρr := hρr }
  -- the threshold
  set Kt := δ ^ (-η) * n / Z ^ 2 with hKtdef
  set lam := 288 * C1 * Kt * Z * δ ^ 2 * ρ ^ (-εG) with hlamdef
  have hlam0 : 0 < lam := by
    have := Real.rpow_pos_of_pos hρ0 (-εG)
    have : 0 < Kt := by rw [hKtdef]; have := Real.rpow_pos_of_pos hδ (-η); positivity
    positivity
  -- the removed mass
  set X := 200 * ρ ^ ηG + 288 * (e + δ) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hclass : ∀ k ∈ clIdxSet f x v,
      clR f lam x v Y k ≤ ENNReal.ofReal ((clSet c x v k).card * (δ ^ 2 * X)) := by
    intro k hk
    have hne : (clSet c x v k).Nonempty := by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
      exact ⟨i, mem_clSet_self c x v i⟩
    exact class_mass_le hG hC1 hYm hYT hFc hfS k hne (hCG k hk) hρdG hρr0 hn
  have hremoved : ∑ k ∈ clIdxSet f x v, clR f lam x v Y k ≤
      ENNReal.ofReal (15 * n * (δ ^ 2 * X)) := by
    calc ∑ k ∈ clIdxSet f x v, clR f lam x v Y k
        ≤ ∑ k ∈ clIdxSet f x v, ENNReal.ofReal ((clSet c x v k).card * (δ ^ 2 * X)) :=
          Finset.sum_le_sum hclass
      _ = ENNReal.ofReal (∑ k ∈ clIdxSet f x v, (clSet c x v k).card * (δ ^ 2 * X)) :=
          (ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity).symm
      _ ≤ ENNReal.ofReal (15 * n * (δ ^ 2 * X)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (sum_card_clSet_le c x v _) (by positivity)
  have hXsmall : 15 * n * (δ ^ 2 * X) ≤ δ ^ η * n * δ ^ 2 / 2 := by
    have h1 : ρ ^ ηG ≤ δ ^ (ηG / 3) := hρηG
    have h2 : e ≤ δ ^ (ηG / 3) := by
      rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by rw [hadef]; push_cast; linarith)
    have h3 : δ ≤ δ ^ (ηG / 3) := by
      calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ (ηG / 3) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have h4 : X ≤ 776 * δ ^ (ηG / 3) := by rw [hXdef]; linarith
    have h5 : δ ^ (ηG / 3) = δ ^ (ηG / 4) * δ ^ η := by
      rw [← Real.rpow_add hδ]; congr 1; rw [hηdef]; ring
    have hδη : 0 < δ ^ η := Real.rpow_pos_of_pos hδ _
    have h6 : 15 * 776 * δ ^ (ηG / 3) ≤ δ ^ η / 2 := by
      rw [h5]
      have := mul_le_mul_of_nonneg_right t4 hδη.le
      linarith
    have hp : 0 ≤ n * δ ^ 2 := by positivity
    calc 15 * n * (δ ^ 2 * X) = 15 * X * (n * δ ^ 2) := by ring
      _ ≤ 15 * (776 * δ ^ (ηG / 3)) * (n * δ ^ 2) := by gcongr
      _ ≤ δ ^ η / 2 * (n * δ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hp; linarith
      _ = δ ^ η * n * δ ^ 2 / 2 := by ring
  -- the truncated mass
  have hM : ENNReal.ofReal (δ ^ η * n * δ ^ 2 / 2) ≤ ∑ i, volume (trY f lam x v Y i) := by
    have h1 := removed_mass hfc hYm lam (x := x) (v := v)
    have h2 : ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤ ∑ i, volume (trY f lam x v Y i) +
        ENNReal.ofReal (δ ^ η * n * δ ^ 2 / 2) :=
      hmass.trans (h1.trans (add_le_add le_rfl (hremoved.trans
        (ENNReal.ofReal_le_ofReal hXsmall))))
    have h3 : ENNReal.ofReal (δ ^ η * n * δ ^ 2) = ENNReal.ofReal (δ ^ η * n * δ ^ 2 / 2) +
        ENNReal.ofReal (δ ^ η * n * δ ^ 2 / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    rw [h3, add_comm (∑ i, volume (trY f lam x v Y i))] at h2
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp h2
  -- the truncated energy
  have hb : 0 < 100 / c ^ 2 := by positivity
  have hc100sq : (100 : ℝ) ≤ c ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hc100.le 2
    rw [hc2abs]; linarith
  obtain ⟨K, hK5, hK10⟩ := exists_dyadic hb (by rw [div_le_one hc2]; exact hc100sq)
  have hE := trunc_energy hδ hv htrans hT hYm hYT hFc hfS hc100 hδc' K hK5 lam
  set Rf := ((K : ℝ) + 1) * (36 * δ * (8 * δ ^ (-η) * n) * (27 / 100 + 2 + 4 / 100)) with hRf
  set F := (n : ℝ) * (5 * δ ^ 3 * Rf) with hFdef
  have hF0 : 0 ≤ F := by positivity
  -- finiteness of the truncated mass
  have hMfin : ∑ i, volume (trY f lam x v Y i) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono (inter_subset_left.trans (hYT i))).trans
        (volume_tube_le hδ (hv i) (htrans i) (hT i)))
  set m := (∑ i, volume (trY f lam x v Y i)).toReal with hmdef
  have hmeq : ∑ i, volume (trY f lam x v Y i) = ENNReal.ofReal m :=
    (ENNReal.ofReal_toReal hMfin).symm
  have hm0 : δ ^ η * n * δ ^ 2 / 2 ≤ m := by
    rw [hmeq] at hM
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hM
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm0
  -- the conclusion
  show ENNReal.ofReal (δ ^ ε) ≤ volume (proj f (⋃ i, Y i))
  by_cases htop : volume (proj f (⋃ i, Y i)) = ⊤
  · rw [htop]; exact le_top
  set A := (volume (proj f (⋃ i, Y i))).toReal with hAdef
  have hAeq : volume (proj f (⋃ i, Y i)) = ENNReal.ofReal A := (ENNReal.ofReal_toReal htop).symm
  rw [hAeq]
  apply ENNReal.ofReal_le_ofReal
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hEr : m ^ 2 ≤ A * (lam * m + F) := by
    rw [hmeq, hAeq, ← ENNReal.ofReal_pow hmpos.le, ← ENNReal.ofReal_mul hlam0.le,
      ← ENNReal.ofReal_add (by positivity) hF0, ← ENNReal.ofReal_mul hA0] at hE
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hE
  apply final_real hmpos hlam0 hF0 hEr
  · have hZlow : δ ^ a ≤ 40 * Z := by
      rw [hZdef, hr0def]
      have h100 : (100 : ℝ) ≤ |c| := hc100.le
      have : δ ^ a / 4 * 100 / 1000 ≤ δ ^ a / 4 * |c| / 1000 := by gcongr
      linarith
    exact near_arith hδ hδ1 hC1 hZ hρ0 hn0.le
      (by rw [hηdef, hadef, hεGdef]; linarith) hεG.le hZlow hρδ t5 hm0
  · have hK2 : (2 : ℝ) ^ K * δ ≤ 1 / 10 := by
      have h1 : 100 * δ ≤ 100 / c ^ 2 := by
        rw [le_div_iff₀ hc2]
        have : 100 * δ * c ^ 2 = 100 * (δ * c ^ 2) := by ring
        linarith
      have h2 : (2 : ℝ) ^ K * (100 * δ) ≤ 10 := by
        calc (2 : ℝ) ^ K * (100 * δ) ≤ 2 ^ K * (100 / c ^ 2) := by gcongr
          _ ≤ 10 := hK10
      linarith
    exact far_arith hδ hδ1 hε0 hε01 hε0ε hη (by rw [hηdef]; linarith) hn0.le hK2 t6 hm0

end WangZahlLot.Obl.wz_intermediate_twist_normalization
