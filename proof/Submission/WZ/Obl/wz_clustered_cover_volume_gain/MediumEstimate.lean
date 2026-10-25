-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.MediumEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainCoverEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodPowers
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.MediumCountPowers
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinementPowers

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory Metric
open scoped ENNReal

set_option maxHeartbeats 3000000

/-- Uniform medium-scale certificate: a sufficiently heavy selection of
coarse boxes either gives a power gain or admits controlled active fibres. -/
theorem medium_estimate {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω) :
    ∀ loss : ℝ, 0 < loss → ∃ Cm H α κ d : ℝ,
      0 < Cm ∧ 0 < H ∧ 0 < α ∧ 0 < κ ∧ 0 < d ∧
      ∀ δ h τ : ℝ, 0 < δ → δ ≤ d → 0 ≤ h → h ≤ H → 0 ≤ τ → τ ≤ H →
      ∀ (n N J : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
        (ρ : ℝ) (y w : Fin N → V) (f : Fin n → Fin N),
      δ ≤ ρ → ρ ≤ 1 → A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      C δ h n x v Y S Z ρ N y w f →
      ∀ Gd : GrainData δ h ρ n N S Z y w f,
      ∀ (U : Finset (Fin N)) (g : Fin N → Fin J) (z₀ : Fin J → V)
        (e₀ : Fin J → V ≃ₗᵢ[ℝ] V) (a₀ b₀ : ℝ),
      ρ ≤ a₀ → a₀ ≤ b₀ →
      (∀ k ∈ U, T ρ (y k) (w k) ⊆ P a₀ b₀ 8 (z₀ (g k)) (e₀ (g k))) →
      O (δ ^ τ) * ∑ i, volume (Y i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), volume (Z i) →
      O (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i) ∨
        ∃ W : Fin n → Set V, MR σ ω δ loss ρ b₀ Cm n N J Y Z W S U f g := by
  intro loss hloss
  let b := min (loss / 100) (1 / 10)
  have hb : 0 < b := lt_min (by positivity) (by norm_num)
  have hbsmall : b ≤ 1 / 10 := min_le_right _ _
  have hbloss : b ≤ loss / 100 := min_le_left _ _
  obtain ⟨Cb, ηb, db, hCb, hηb, hdb, hdb100, Hbody⟩ :=
    grain_cover_density_or_medium hσ hσhalf hω hE b hb
  let en := b * ω / 100
  have hen : 0 < en := by dsimp [en]; positivity
  obtain ⟨κ, ηn, dn, hκ, hηn, hdn, hdn100, Hneigh⟩ := neighborhood_power_gain hσ hσhalf hω hE en hen
  let ν := min (b / 100) (min ηb (min ηn (b * ω / 1000)))
  have hν : 0 < ν := lt_min (by positivity) (lt_min hηb (lt_min hηn (by positivity)))
  have hνb : ν ≤ b / 100 := min_le_left _ _
  have hνηb : ν ≤ ηb := (min_le_right _ _).trans (min_le_left _ _)
  have hνηn : ν ≤ ηn := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνω : ν ≤ b * ω / 1000 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνsmall : ν ≤ 1 / 1000 := by linarith
  obtain ⟨dd, hdd, hdd1, Hdensity⟩ := selected_ball_density_power (show 0 < ν / 100 by positivity)
  obtain ⟨dc, hdc, Hconf⟩ := confinement_density_power_lower hν
  obtain ⟨dp, hdp, Hpower⟩ := uniform_small_power_comparison
    (by norm_num : (0 : ℝ) < 1000000000000000) (show 0 < ν / 2 by positivity)
  let d := min (1 / 20000) (min db (min dn (min dd (min dc dp))))
  refine ⟨mediumConstant Cb σ ω, ν / 100, b * ω / 2, κ, d, mediumConstant_pos hCb,
    by positivity, by positivity, hκ, ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min hdb (lt_min hdn (lt_min hdd (lt_min hdc hdp))))
  intro δ h τ hδ hδd hh hhH hτ hτH n N J x v Y Z S ρ y w f hδρ hρ1 hA hC Gd U g z₀ e₀
    a₀ b₀ hρa₀ ha₀b₀ hcover hkeep
  have hδsmall : δ ≤ 1 / 20000 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδb : δ ≤ db := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδn : δ ≤ dn := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδden : δ ≤ dd := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδconf : δ ≤ dc := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδpow : δ ≤ dp := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hp := Hpower δ hδ hδ1 hδpow
  have hδsq : δ ^ (2 : ℕ) ≤ δ := by nlinarith
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have ha : 0 < Gd.a := hδ.trans_le Gd.short
  have hc : 0 < Gd.c := ha.trans_le (Gd.middle.trans Gd.long)
  have hρc : 0 < ρ * Gd.c := mul_pos hρ hc
  have hρc1 : ρ * Gd.c ≤ 1 := Gd.long.trans Gd.length
  have hθ : 0 < min 1 b₀ := lt_min zero_lt_one (hρ.trans_le (hρa₀.trans ha₀b₀))
  let s := grainAngle δ b ρ Gd.c
  have hs := grainAngle_properties hδ hδ1 hb.le hρc hρc1
  have hconfine := grainAngle_error_bound hδ hδ1 hb.le hρc hρc1 Gd.short
  let Ac := ⌈δ ^ (-b)⌉₊
  have hAc := grain_error_ceiling hδ hδ1 hb.le
  let R := δ ^ (1 - b) / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    have hh := Real.rpow_le_one hδ.le hδ1 (show 0 ≤ 1 - b by linarith)
    dsimp [R]
    linarith
  obtain ⟨lam, X, hXm, hXU, hlamlow, hlam4, hden, hcut⟩ :=
    Hdensity δ hδ hδden h τ R (by linarith) hR hR1 n N x v Y Z S ρ y w f U hA hC hkeep
  have hlam : 0 ≤ lam := (by positivity : 0 ≤ δ ^ (4 : ℕ) / 2).trans hlamlow
  have hcard : (Gd.L : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
    rw [square_rpow hδ]
    exact (Gd.cardinality hδ hδρ hρ1 hA hC).trans (hp 4096 (-(2 * h + 5)) (2 * -100)
      (by norm_num) (by linarith))
  have hDη : 1536 * (δ ^ (2 : ℕ)) ^ ηb ≤ δ ^ ν / 8 := by
    rw [square_rpow hδ]
    have hh := hp 12288 (2 * ηb) ν (by norm_num) (by linarith)
    linarith
  have hda : δ ^ (2 : ℕ) ≤ Gd.a / 20000 := by
    nlinarith only [mul_le_mul_of_nonneg_left hδsmall hδ.le, Gd.short]
  have hw := grain_weight_power_lower hδ ha hρ hθ hs.1 hc hconfine
  have hδratio : δ ≤ ρ / min 1 b₀ := by
    apply (le_div_iff₀ hθ).mpr
    exact (mul_le_mul_of_nonneg_left (min_le_left 1 b₀) hδ.le).trans (by simpa using hδρ)
  have hwlow : δ ^ (2 + b) / 800000000 ≤
      Gd.a * ρ / (800000000 * (min 1 b₀) ^ 2 * s * Gd.c) := by
    calc
      _ = (δ ^ b / 800000000) * δ ^ (2 : ℕ) := by
        rw [Real.rpow_add hδ, Real.rpow_two]
        ring
      _ ≤ (δ ^ b / 800000000) * (ρ / min 1 b₀) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hδratio 2) (by positivity)
      _ ≤ _ := hw
  have hscale : 256 * (δ ^ (2 : ℕ)) ^ 2 ≤
      Gd.a * ρ / (800000000 * (min 1 b₀) ^ 2 * s * Gd.c) := by
    apply le_trans _ hwlow
    have hh := hp (256 * 800000000) 4 (2 + b) (by norm_num) (by linarith only [hbsmall, hνsmall])
    rw [Real.rpow_ofNat] at hh
    nlinarith only [hh]
  have hDcut : δ ^ ν ≤ δ ^ (τ + ν / 100) / 4 * δ ^ h := by
    have hh := hp 4 ν (τ + ν / 100 + h) (by norm_num) (by linarith)
    rw [Real.rpow_add hδ] at hh
    linarith
  have hmassbudget : O (δ ^ loss) ≤ O (δ ^ (τ + ν / 100) / 128) * O (δ ^ h) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ δ ^ (τ + ν / 100) / 128)]
    apply ENNReal.ofReal_le_ofReal
    have hh := hp 128 loss (τ + ν / 100 + h) (by norm_num) (by linarith)
    rw [Real.rpow_add hδ] at hh
    linarith
  have hRs : s = 1 ∨ R ≤ (s / 2) * ρ * Gd.c := by
    by_cases hh : s = 1
    · exact Or.inl hh
    · right
      have he := hs.2.2.2.2 hh
      dsimp [R]
      nlinarith only [he]
  have hAs : s * ρ * Gd.c ≤ (Ac : ℝ) * Gd.a :=
    hconfine.trans (mul_le_mul_of_nonneg_right hAc.2.2 ha.le)
  have hcountbudget := medium_count_power_bound hδ hδ1 hb.le hh hCb hσ hσhalf hω.le hω1
    ha hρ (hρ.trans_le (hρa₀.trans ha₀b₀)) hs.1 hc hAc.2.1 hconfine (by linarith : 18 * b + ν + 2 * h ≤ loss)
  have hraw := Hbody (δ ^ (2 : ℕ)) δ h ρ (by positivity) (hδsq.trans hδb) hδ hρ hρ1
    n N J x v Y Z S y w f hA hC Gd U g z₀ e₀ a₀ b₀ s (δ ^ ν) R lam
    (δ ^ (τ + ν / 100)) loss (mediumConstant Cb σ ω) Ac X hρa₀ ha₀b₀ hs.1 hs.2.1 hAc.1 hcard
    (fun hh => grainAngle_contains_short hρc Gd.middle (by dsimp [R] at hh; linarith)) hAs
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith))
    (Real.rpow_pos_of_pos hδ _) hDη hda hscale hR hRs hlam (Real.rpow_pos_of_pos hδ _)
    hDcut hmassbudget hcountbudget hXm hXU (fun p hp => (hden p hp).2) hcut hcover
  have hlarge : δ ^ (6 * ν) ≤ lam ∨ ∃ W : Fin n → Set V,
      MR σ ω δ loss ρ b₀ (mediumConstant Cb σ ω) n N J Y Z W S U f g := by
    rcases hraw with hthick | htrans | hmedium
    · left
      have hh := hp 92160 (6 * ν) (5 * ν) (by norm_num) (by linarith)
      have hpow : δ ^ (5 * ν) ≤ δ ^ ν := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      linarith only [hh, hpow, hthick, hlam]
    · left
      have hcl := Hconf δ hδ hδ1 hδconf Gd.a ρ Gd.c (δ ^ ν) s Gd.short Gd.middle hρc1 le_rfl hs.2.2.1
      have hh := hp 92160 (6 * ν) (5 * ν) (by norm_num) (by linarith)
      linarith only [hh, hcl, htrans]
    · exact Or.inr hmedium
  rcases hlarge with hlarge | hmedium
  · left
    have hnmax : (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
      rw [square_rpow hδ]
      exact (power_count_bound hδ (admissible_count_eight hδ hA)).trans
        (hp 8 (-(h + 2)) (2 * -100) (by norm_num) (by linarith))
    have hdr : δ ≤ δ ^ (1 - b) / 6 := by
      have hh := hp 6 1 (1 - b) (by norm_num) (by linarith)
      rw [Real.rpow_one] at hh
      linarith
    have hDr : δ ^ (2 : ℕ) ≤ δ ^ (1 - b) / 6 / 8 := by
      have hh := hp 48 2 (1 - b) (by norm_num) (by linarith)
      rw [Real.rpow_two] at hh
      linarith
    have hηq : 128 * (δ ^ (2 : ℕ)) ^ ηn ≤ δ ^ ν := by
      rw [square_rpow hδ]
      exact hp 128 (2 * ηn) ν (by norm_num) (by linarith)
    let W := fun i => Z i ∩ selectedCut U X (f i)
    have hW (i) : MeasurableSet (W i) ∧ W i ⊆ Y i :=
      ⟨(hC.1 i).1.inter (selectedCut_measurable U hXm (f i)), inter_subset_left.trans (hC.1 i).2.1⟩
    have hWmass : O (δ ^ ν * n * δ ^ 2) ≤ ∑ i, volume (W i) := by
      calc
        _ ≤ O (δ ^ (τ + ν / 100 + h) * n * δ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
          exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        _ = O (δ ^ (τ + ν / 100)) * O (δ ^ h * n * δ ^ 2) := by
          rw [Real.rpow_add hδ, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
          congr 1
          ring
        _ ≤ O (δ ^ (τ + ν / 100)) * ∑ i, volume (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
        _ ≤ _ := hcut
    apply Hneigh δ h b ν hδ hδ1 hh hb.le (by linarith) (hδsq.trans hδn) hdr hDr hηq
      (by dsimp [en]; nlinarith only [hνω, hhH, hν]) n x v Y W hnmax hA hW hWmass
    intro i p hpW
    have hpX : p ∈ X := selectedCut_subset U X (f i) hpW.2
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hlarge (by positivity))).trans (hden p hpX).1
  · exact Or.inr hmedium

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
