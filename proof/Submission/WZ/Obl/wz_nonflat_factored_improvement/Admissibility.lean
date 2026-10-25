-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Admissibility.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.ScaleAlgebra
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineMap

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

theorem power_density_bound {δ Z ν C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hν : ν ≤ Z / 2) (hc : δ ^ (Z / 2) ≤ C) : δ ^ Z ≤ C * δ ^ ν := by
  calc
    _ ≤ δ ^ (ν + Z / 2) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    _ = δ ^ ν * δ ^ (Z / 2) := Real.rpow_add hδ _ _
    _ ≤ δ ^ ν * C := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hδ.le _)
    _ = _ := mul_comm _ _

theorem coarse_radius_le {b : ℝ} (hb : 0 ≤ b) : coarseRadius b ≤ b := by
  dsimp [coarseRadius, coarseContraction]
  linarith

theorem fine_radius_le {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 < b) : fineRadius δ b ≤ δ / b := by
  have he : fineRadius δ b = (4 * fineContraction) * (δ / b) := by dsimp [fineRadius]; ring
  rw [he]
  exact mul_le_of_le_one_left (div_nonneg hδ hb.le) (by norm_num)

theorem compact_scale_coefficient {δ b ν t : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hscale : δ ^ t ≤ δ / b) :
    256000000 * (δ ^ ν)⁻¹ * (b / δ) ^ 2 ≤ 256000000 * δ ^ (-(ν + 2 * t)) := by
  have hratio : b / δ ≤ δ ^ (-t) := by
    apply (div_le_iff₀ hδ).mpr
    have hh := (le_div_iff₀ hb).mp hscale
    calc
      b = δ ^ (-t) * (δ ^ t * b) := by rw [← mul_assoc, ← Real.rpow_add hδ]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hδ.le _)
  calc
    _ ≤ 256000000 * (δ ^ ν)⁻¹ * (δ ^ (-t)) ^ 2 := by gcongr
    _ = _ := by
      rw [← Real.rpow_neg hδ.le, ← Real.rpow_mul_natCast hδ.le, mul_assoc,
        ← Real.rpow_add hδ]
      congr 2
      norm_num
      ring

set_option maxHeartbeats 400000 in
/-- One choice of all scalar tolerances works for both the two-scale and direct-scale cases. -/
theorem choose_product_parameters {ζ e ηD ηE ηS : ℝ}
    (hζ : 0 < ζ) (he : 0 < e) (hηD : 0 < ηD) (hηE : 0 < ηE) (hηS : 0 < ηS) :
    ∃ β τ t η d : ℝ, ∃ K : ℕ,
      0 < β ∧ β ≤ ζ / 4 ∧ 0 < τ ∧ 0 < t ∧ 0 < η ∧ 0 < d ∧ 0 < K ∧
      ∀ ν δ a b : ℝ, 0 < ν → ν ≤ η → 0 < δ → δ ≤ 1 → δ ≤ d →
      δ ≤ a → a ≤ b → b ≤ δ ^ (ζ / 8) → δ ^ β * b ≤ a →
      2 * ν ≤ ηS ∧ e / 4 + 5 * ν + 2 * β + τ ≤ e ∧
      288 * (δ ^ τ) ^ K * b ^ 2 ≤ δ ^ ν * δ ^ 2 / 2 ∧
      (coarseRadius b) ^ ηD ≤ coarseContraction * δ ^ ν / (4608 * K) ∧
      coarseConvexCoefficient a b (δ ^ (-ν)) ≤ (coarseRadius b) ^ (-ηD) ∧
      coarseSlabCoefficient a b (δ ^ (-ν)) (δ ^ (-2 * ν)) ≤ (coarseRadius b) ^ (-ηD) ∧
      (δ / b ≤ δ ^ t → (fineRadius δ b) ^ ηE ≤ fineContraction * δ ^ ν / (64 * K)) ∧
      (δ ^ t ≤ δ / b → 256000000 * (δ ^ ν)⁻¹ * (b / δ) ^ 2 ≤ δ ^ (-ηS)) := by
  let Z := ζ * ηD / 8
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let τ := e / 16
  let t := ηS / 16
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  let β := min (ζ / 4) (min (e / 16) (Z / 8))
  have hβ : 0 < β := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hβζ : β ≤ ζ / 4 := min_le_left _ _
  have hβe : β ≤ e / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hβZ : β ≤ Z / 8 := (min_le_right _ _).trans (min_le_right _ _)
  let η := min 1 (min (e / 16) (min (Z / 64) (min (t * ηE / 2) (ηS / 16))))
  have hη : 0 < η := lt_min (by norm_num) (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  let K := ⌈4 / τ⌉₊
  have hK : 0 < K := Nat.ceil_pos.mpr (by positivity)
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hKbound : 4 ≤ τ * K := by
    have hh := Nat.le_ceil (4 / τ)
    have hi := (div_le_iff₀ hτ).mp hh
    dsimp [K]
    linarith
  obtain ⟨dC, hdC, HC⟩ := exists_small_rpow (by positivity : 0 < Z / 2)
    (by positivity : 0 < coarseContraction / (4608 * K))
  obtain ⟨dN, hdN, HN⟩ := exists_small_rpow (by positivity : 0 < Z / 2)
    (inv_pos.mpr coarseUniversalConstant_pos)
  obtain ⟨dF, hdF, HF⟩ := exists_small_rpow (by positivity : 0 < t * ηE / 2)
    (by positivity : 0 < fineContraction / (64 * K))
  obtain ⟨dS, hdS, HS⟩ := exists_small_rpow (by positivity : 0 < ηS / 2)
    (by norm_num : 0 < (256000000 : ℝ)⁻¹)
  let d := min (1 / 576) (min dC (min dN (min dF dS)))
  have hd : 0 < d := lt_min (by norm_num) (lt_min hdC (lt_min hdN (lt_min hdF hdS)))
  refine ⟨β, τ, t, η, d, K, hβ, hβζ, hτ, ht, hη, hd, hK, ?_⟩
  intro ν δ a b hν hνη hδ hδ1 hδd hδa hab hbδ hflat
  have hν1 : ν ≤ 1 := hνη.trans (min_le_left _ _)
  have hνe : ν ≤ e / 16 := hνη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνZ : ν ≤ Z / 64 := hνη.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hνF : ν ≤ t * ηE / 2 := hνη.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hνS : ν ≤ ηS / 16 := hνη.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hδsmall : δ ≤ 1 / 576 := hδd.trans (min_le_left _ _)
  have hδC : δ ≤ dC := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδN : δ ≤ dN := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδF : δ ≤ dF := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδS : δ ≤ dS := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hb1 : b ≤ 1 := hbδ.trans (Real.rpow_le_one hδ.le hδ1 (by positivity))
  have hrc : 0 < coarseRadius b := by dsimp [coarseRadius]; positivity
  have hrad : coarseRadius b ≤ δ ^ (ζ / 8) := (coarse_radius_le hb.le).trans hbδ
  have hcpow : (coarseRadius b) ^ ηD ≤ δ ^ Z := by
    have hh := Real.rpow_le_rpow hrc.le hrad hηD.le
    rw [← Real.rpow_mul hδ.le] at hh
    convert hh using 1 <;> dsimp [Z] <;> congr 1 <;> ring
  have hnpow : δ ^ (-Z) ≤ (coarseRadius b) ^ (-ηD) := by
    have hh := Real.rpow_le_rpow_of_nonpos hrc hrad (by linarith : -ηD ≤ 0)
    rw [← Real.rpow_mul hδ.le] at hh
    convert hh using 1 <;> dsimp [Z] <;> congr 1 <;> ring
  have hcount := coarse_coefficients_power_bound hδ hδ1 ha hb hν.le hflat
  have habsorb := absorb_power_constant hδ hδ1 coarseUniversalConstant_pos (HN δ hδ hδN)
    (show 5 * ν + β ≤ Z / 2 by linarith)
  refine ⟨by linarith, ?_, ?_, ?_, hcount.1.trans (habsorb.trans hnpow),
    hcount.2.trans (habsorb.trans hnpow), ?_, ?_⟩
  · dsimp [τ]
    linarith
  · have hrho : (δ ^ τ) ^ K ≤ δ ^ 4 := by
      rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_natCast δ 4]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hKbound
    have hδν : δ ≤ δ ^ ν := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hν1
    calc
      _ ≤ 288 * δ ^ 4 := by
        have hb2 : b ^ 2 ≤ 1 := by nlinarith
        have hh := mul_le_mul hrho hb2 (sq_nonneg b) (by positivity)
        nlinarith only [hh]
      _ = (288 * δ) * (δ * δ ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * (δ * δ ^ 2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hδν (sq_nonneg δ)]
  · have hh := hcpow.trans (power_density_bound hδ hδ1 (by linarith : ν ≤ Z / 2) (HC δ hδ hδC))
    convert hh using 1 <;> ring
  · intro hscale
    have hrpow : (fineRadius δ b) ^ ηE ≤ δ ^ (t * ηE) := by
      have hh := Real.rpow_le_rpow (by dsimp [fineRadius]; positivity : 0 ≤ fineRadius δ b)
        ((fine_radius_le hδ.le hb).trans hscale) hηE.le
      rwa [← Real.rpow_mul hδ.le] at hh
    have hh := hrpow.trans (power_density_bound hδ hδ1 hνF (HF δ hδ hδF))
    convert hh using 1 <;> ring
  · intro hscale
    apply (compact_scale_coefficient hδ hb hscale).trans
    exact absorb_power_constant hδ hδ1 (by norm_num) (HS δ hδ hδS)
      (by dsimp [t]; linarith : ν + 2 * t ≤ ηS / 2)

end WangZahlLot.Obl.wz_nonflat_factored_improvement
