-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainsAtScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainParams

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

set_option maxHeartbeats 0 in
/-- **Local grains at one scale** (sticky Lemmas 4.9-4.11).  An extremal family with a
`δ^(-η)`-Lipschitz plane map of precision `δ` has an `ε`-extremal refinement whose plane-map
projections of `√ρ`-balls meet every window of length `R ≥ ρ` in at most
`δ^(-ε) (R/ρ)^(1-σ)` intervals of radius `ρ`. -/
theorem grains_at_scale {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hTS : TwoScaleTheoremP σ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) :
    ∃ η d1 : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) → (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) →
        (∀ p ∈ ⋃ i, Y i, ∀ q ∈ ⋃ i, Y i, dist (V p) (V q) ≤ δ ^ (-η) * dist p q) →
        ∀ ρ : ℝ, δ ^ (1 - ε) ≤ ρ → ρ ≤ δ ^ ε →
        ∃ Y' : Fin n → Set Space, (∀ i, Y' i ⊆ Y i) ∧ Family ε δ n x v Y' ∧
          ∀ p ∈ ⋃ i, Y' i, ∀ a R : ℝ, ρ ≤ R →
            ∃ (m : ℕ) (c : Fin m → ℝ),
              ((fun q => inner ℝ (V p) q) '' ((⋃ i, Y' i) ∩ ball p (Real.sqrt ρ))) ∩
                Icc a (a + R) ⊆ ⋃ j, closedBall (c j) ρ ∧
              (m : ℝ) ≤ δ ^ (-ε) * (R / ρ) ^ (1 - σ) := by
  classical
  -- parameters
  set Mτ : ℕ := ⌈16 / ε⌉₊ + 2 with hMτ
  set K : ℕ := Mτ + 2 with hK
  have hMτ2 : 2 ≤ Mτ := by omega
  have hMτR : (2 : ℝ) ≤ Mτ := by exact_mod_cast hMτ2
  have hMτinv : 1 / (Mτ : ℝ) ≤ ε / 16 := by
    have h1 : 16 / ε ≤ (Mτ : ℝ) := by
      have := Nat.le_ceil (16 / ε)
      have h2 : ((⌈16 / ε⌉₊ : ℕ) : ℝ) ≤ Mτ := by exact_mod_cast (show ⌈16 / ε⌉₊ ≤ Mτ by omega)
      linarith
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ hε] at h1
    linarith
  set κ := ε / 8 with hκ
  set εG := σ * ε / 2048 with hεG
  have hεG0 : 0 < εG := by positivity
  obtain ⟨ηG, dG, hηG, hdG, hTSG⟩ := hTS εG hεG0
  set ερ := min (σ * ε / 2048) ηG with hερ
  have hερ0 : 0 < ερ := lt_min (by positivity) hηG
  obtain ⟨ηρ, dρ, hηρ, hdρ, hTSρ⟩ := hTS ερ hερ0
  set εc := min (ε / (64 * Mτ)) ηρ with hεc
  have hεc0 : 0 < εc := lt_min (by positivity) hηρ
  have hεc10 : εc ≤ 1 / 10 := (min_le_left _ _).trans (by
    rw [div_le_iff₀ (by positivity)]; nlinarith)
  obtain ⟨ηc, dc, hηc, hηcεc, hdc, hchain⟩ := cube_bounds_chain hTS K εc hεc0 hεc10
  set η := min ηc (σ * ε / 2048) with hη
  have hη0 : 0 < η := lt_min hηc (by positivity)
  have hηηc : η ≤ ηc := min_le_left _ _
  have hηs : η ≤ σ * ε / 2048 := min_le_right _ _
  have hσε : σ * ε / 2048 ≤ ε / 2048 := by nlinarith
  have hερs : ερ ≤ σ * ε / 2048 := min_le_left _ _
  have hερη : ερ ≤ ηG := min_le_right _ _
  have hεcs : εc ≤ ε / (64 * Mτ) := min_le_left _ _
  have hεcη : εc ≤ ηρ := min_le_right _ _
  have hexp6 : 6 * ερ + εG ≤ ε / 2 := by
    have : σ * ε ≤ ε := by nlinarith
    rw [hεG]; linarith
  have hεGκ : εG ≤ κ := by
    have : σ * ε ≤ ε := by nlinarith
    rw [hεG, hκ]; linarith
  have hκ1 : κ ≤ 1 - εG := by
    have : σ * ε ≤ ε := by nlinarith
    rw [hεG, hκ]; linarith
  have he_early : σ * ε / 16 ≤ σ * (κ - εG) - ερ - 3 * εG := by
    have h1 : σ * εG ≤ εG := by
      have : σ * εG ≤ 1 * εG := mul_le_mul_of_nonneg_right hσ1.le hεG0.le
      linarith
    have h2 : σ * κ = σ * ε / 8 := by rw [hκ]; ring
    have h3 : σ * (κ - εG) = σ * κ - σ * εG := by ring
    rw [h3, h2]
    rw [hεG] at h1 ⊢
    linarith
  have hbudget : 7 * (1 / (2 * (Mτ : ℝ))) + 2 * (ερ + η) +
      (3 * εc + 3 * ερ + (κ + 3 * εG + 3 * ερ)) ≤ ε / 2 := by
    have h1 : εc ≤ ε / 128 := hεcs.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    have h2 : 1 / (2 * (Mτ : ℝ)) ≤ ε / 32 := by
      have : 1 / (2 * (Mτ : ℝ)) = (1 / (Mτ : ℝ)) / 2 := by field_simp
      rw [this]; linarith
    have h3 : σ * ε ≤ ε := by nlinarith
    rw [hκ, hεG]
    linarith only [h1, h2, hερs, hηs, h3, hε]
  have hεc8 : εc ≤ ε / 128 := hεcs.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  -- cutoffs on `δ`
  obtain ⟨c1, hc1, hcut1⟩ := exists_power_cutoff (a := ε / 2) (by positivity)
    (by positivity : (0:ℝ) < min (min dG (1 / 100)) (1 / 32))
  obtain ⟨c2, hc2, hcut2⟩ := exists_power_cutoff (a := ε / 4) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 4096)
  obtain ⟨c3, hc3, hcut3⟩ := exists_power_cutoff (a := ε / (2 * Mτ)) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 3)
  obtain ⟨c4, hc4, hcut4⟩ := exists_power_cutoff (a := σ * ε * ε / 64) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 300000000)
  obtain ⟨Cfin, hCfin⟩ : ∃ C : ℝ, C = 6144 * 54880000 * (32 * 55296 ^ 2 * 3072 * 256 * 4608) :=
    ⟨_, rfl⟩
  have hCfin0 : 0 < Cfin := by rw [hCfin]; norm_num
  obtain ⟨c5, hc5, hcut5⟩ := exists_power_cutoff (a := ε / 2) (by positivity)
    (by positivity : (0:ℝ) < 1 / (Cfin * 158 ^ 2))
  refine ⟨η, min (min (min dc dρ) c5) (min (min c1 c2) (min c3 c4)), hη0,
    hηs.trans (hσε.trans (by linarith)), lt_min (lt_min (lt_min hdc hdρ) hc5)
      (lt_min (lt_min hc1 hc2) (lt_min hc3 hc4)), ?_⟩
  intro δ hδ hδd hδ100 n x v Y V hF hS hvol hVu hVp hVL ρ hρ1 hρ2
  have hδdc : δ ≤ dc := hδd.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδdρ : δ ≤ dρ := hδd.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδc5 : δ ≤ c5 := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδc1 : δ ≤ c1 := hδd.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδc2 : δ ≤ c2 := hδd.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδc3 : δ ≤ c3 := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδc4 : δ ≤ c4 := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hδ1 : δ ≤ 1 := by linarith
  have hq1 := hcut1 δ hδ hδc1
  have hq2 := hcut2 δ hδ hδc2
  have hq3 := hcut3 δ hδ hδc3
  have hq4 := hcut4 δ hδ hδc4
  have hq5 := hcut5 δ hδ hδc5
  have hρ0 : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans_le hρ1
  have hδρ : δ ≤ ρ := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ ≤ ρ := hρ1
  have hρ1' : ρ ≤ 1 := hρ2.trans (Real.rpow_le_one hδ.le hδ1 hε.le)
  -- the grid of window scales
  set t : ℕ → ℝ := fun i => ρ ^ (1 - (i : ℝ) / (2 * Mτ)) with ht
  have htr : ∀ i < K, δ ^ (1 - εc) ≤ t i ∧ t i ≤ δ ^ (2 * εc) := by
    intro i hi
    have hiR : (i : ℝ) ≤ Mτ + 1 := by
      have : i ≤ Mτ + 1 := by omega
      exact_mod_cast this
    have hexp1 : 1 / 4 ≤ 1 - (i : ℝ) / (2 * Mτ) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)] at *
      have : (i : ℝ) / (2 * Mτ) ≤ 3 / 4 := by
        rw [div_le_iff₀ (by positivity)]; linarith only [hiR, hMτR]
      linarith
    have hexp2 : 1 - (i : ℝ) / (2 * Mτ) ≤ 1 := by
      have : 0 ≤ (i : ℝ) / (2 * Mτ) := by positivity
      linarith
    constructor
    · calc δ ^ (1 - εc) ≤ δ ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        _ ≤ ρ := hρ1
        _ = ρ ^ (1 : ℝ) := (Real.rpow_one ρ).symm
        _ ≤ t i := Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1' hexp2
    · calc t i ≤ ρ ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1' hexp1
        _ ≤ (δ ^ ε) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hρ0.le hρ2 (by norm_num)
        _ = δ ^ (ε / 4) := by rw [← Real.rpow_mul hδ.le]; ring_nf
        _ ≤ δ ^ (2 * εc) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  -- cube bounds at the window scales
  obtain ⟨Yc, hYcY, hFc, hcubes⟩ := hchain δ hδ hδdc hδ100 n x v Y
    (hF.mono_error hδ hδ1 hηηc) (hS.mono_error hδ hδ1 hηηc)
    (hvol.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (by linarith)))) t htr
  have hsubc : (⋃ i, Yc i) ⊆ ⋃ i, Y i := iUnion_mono hYcY
  -- the decomposition at scale `ρ`
  have hρr1 : δ ^ (1 - ερ) ≤ ρ :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans hρ1
  have hρr2 : ρ ≤ δ ^ ερ := hρ2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  obtain ⟨ρc, hρc1, hρc2, hTSA⟩ := hTSρ δ hδ hδdρ hδ100 n x v Yc
    (hFc.mono_error hδ hδ1 hεcη) (hS.mono_error hδ hδ1 (hηηc.trans (hηcεc.trans hεcη)))
    ((measure_mono hsubc).trans (hvol.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))))) ρ hρr1 hρr2
  obtain ⟨Y1, k, z, w, Yt, a, s, M, hY1Yc, hY1m, hY1mass, hFamG, hSepG, hvolG, hcontr, hdir,
    hs, hslo, hshi, hYt, hfine, hfib, hcoarse, hclo, hR1, hR2, hP2, θb, hθb, hP3⟩ := hTSA
  have hk : 0 < k := hFamG.1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : 0 < n := hF.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρc0 : 0 < ρc := hρ0.trans_le hρc1
  have hρcsmall : ρc ≤ δ ^ (ε / 2) := by
    calc ρc ≤ δ ^ (-ερ) * ρ := hρc2
      _ ≤ δ ^ (-ερ) * δ ^ ε := mul_le_mul_of_nonneg_left hρ2 (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (ε - ερ) := by rw [← Real.rpow_add hδ]; ring_nf
      _ ≤ δ ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hρcG : ρc ≤ dG := (hρcsmall.trans hq1).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρc100 : ρc ≤ 1 / 100 :=
    (hρcsmall.trans hq1).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρc1' : ρc ≤ 1 := by linarith
  -- the coarse family at the transversality scale
  have hκr1 : ρc ^ (1 - εG) ≤ ρc ^ κ :=
    Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' hκ1
  have hκr2 : ρc ^ κ ≤ ρc ^ εG :=
    Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' hεGκ
  obtain ⟨ρβ, hρβ1, hρβ2, hTSAG⟩ := hTSG ρc hρc0 hρcG hρc100 k z w Yt
    (hFamG.mono_error hρc0 hρc1' hερη) (hSepG.mono_error hρc0 hρc1' hερη)
    (hvolG.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1'
      (by linarith)))) (ρc ^ κ) hκr1 hκr2
  obtain ⟨Z, kβ, zβ, wβ, Ytβ, aβ, sβ, Mβ, hZYt, hZm, hZmass, hFamβ, hSepβ, hvolβ, hcontrβ,
    hdirβ, hsβ, hsβlo, hsβhi, hYtβ, hfineβ, hfibβ, hcoarseβ, hcloβ, hR1β,
    ⟨ρ0G, z0, w0, hρcρ0, hρ0lo, hρ0hi, hw0, hcov0, hsep0⟩, -⟩ := hTSAG
  have hρβ0 : 0 < ρβ := (Real.rpow_pos_of_pos hρc0 _).trans_le hρβ1
  have hρβle : ρβ ≤ ρc ^ (κ - εG) := by
    rw [show κ - εG = -εG + κ by ring, Real.rpow_add hρc0]; exact hρβ2
  have hρβ1' : ρβ ≤ 1 := hρβle.trans (Real.rpow_le_one hρc0.le hρc1' (by
    linarith only [hεGκ]))
  have hρ0G0 : 0 < ρ0G := hρc0.trans_le hρcρ0
  have hρ0G1 : ρ0G ≤ 1 := hρ0hi.trans hρβ1'
  -- the cone bound for the coarse refinement `Z`
  have hw : ∀ j, ‖w j‖ = 1 := hFamG.2.1
  have hZT : ∀ j, Z j ⊆ tube ρc (z j) (w j) := fun j => (hZYt j).trans (hFamG.2.2.2.2.2.1 j)
  set B1 := (ρc / ρβ) ^ (2 - σ - εG) * ((k : ℝ) / (kβ : ℝ)) with hB1def
  have hkβ : 0 < kβ := hFamβ.1
  have hkβR : (0 : ℝ) < kβ := by exact_mod_cast hkβ
  have hB10 : 0 ≤ B1 := by positivity
  have hcone : ∀ (x u : Space), ‖u‖ = 1 → ((Finset.univ.filter fun j =>
      x ∈ Z j ∧ min ‖w j - u‖ ‖w j + u‖ ≤ ρ0G).card : ℝ) ≤ B1 := by
    intro x' u hu
    have h := cone_count_le (δ := ρc) (ρ := ρ0G) (x := z) (v := w) (Y := Z) (z := z0) (w := w0)
      (a := aβ) hρc0 hρcρ0 hw hw0 hZT hcov0 hsep0 hfibβ hB10 x' u hu
    have e : {l | x' ∈ Z l ∧ min ‖w l - u‖ ‖w l + u‖ ≤ ρ0G} =
        ↑(Finset.univ.filter fun j => x' ∈ Z j ∧ min ‖w j - u‖ ‖w j + u‖ ≤ ρ0G) := by
      ext; simp
    rwa [e, Set.ncard_coe_finset] at h
  -- the cone budget
  have hkβlow := counting_constant_ge_one hρβ0 hρβ1' hkβ hFamβ.2.1
    (hSepβ.global_frostman hρβ0 hρβ1' hkβ hFamβ.2.2.1)
  have hB1b : B1 ≤ 56 * (k : ℝ) * ρc ^ (2 - σ - εG) * ρβ ^ σ := by
    have hnk : (k : ℝ) / kβ ≤ 56 * (k : ℝ) * ρβ ^ (-εG) * ρβ ^ 2 := by
      rw [div_le_iff₀ hkβR]
      calc (k : ℝ) = (k : ℝ) * 1 := (mul_one _).symm
        _ ≤ (k : ℝ) * (56 * ρβ ^ (-εG) * (kβ : ℝ) * ρβ ^ 2) :=
            mul_le_mul_of_nonneg_left hkβlow hkR.le
        _ = 56 * (k : ℝ) * ρβ ^ (-εG) * ρβ ^ 2 * (kβ : ℝ) := by ring
    have hpow : (ρc / ρβ) ^ (2 - σ - εG) * (ρβ ^ (-εG) * ρβ ^ 2) =
        ρc ^ (2 - σ - εG) * ρβ ^ σ := by
      rw [Real.div_rpow hρc0.le hρβ0.le, show ρβ ^ 2 = ρβ ^ (2 : ℝ) by norm_cast,
        ← Real.rpow_add hρβ0]
      have : ρβ ^ (-εG + 2) = ρβ ^ (2 - σ - εG) * ρβ ^ σ := by
        rw [← Real.rpow_add hρβ0]; ring_nf
      rw [this]
      field_simp
    calc B1 ≤ (ρc / ρβ) ^ (2 - σ - εG) * (56 * (k : ℝ) * ρβ ^ (-εG) * ρβ ^ 2) :=
          mul_le_mul_of_nonneg_left hnk (Real.rpow_nonneg (div_nonneg hρc0.le hρβ0.le) _)
      _ = 56 * (k : ℝ) * ((ρc / ρβ) ^ (2 - σ - εG) * (ρβ ^ (-εG) * ρβ ^ 2)) := by ring
      _ = 56 * (k : ℝ) * ρc ^ (2 - σ - εG) * ρβ ^ σ := by rw [hpow]; ring
  -- scale facts
  have hsqρ : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ0
  have hsqρ2 : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ0.le
  have hsqδ : Real.sqrt ρ ≤ δ ^ (ε / 2) := by
    rw [show δ ^ (ε / 2) = Real.sqrt (δ ^ ε) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hδ.le]; ring_nf]
    exact Real.sqrt_le_sqrt hρ2
  have hρcsq : ρc ≤ Real.sqrt ρ / 4096 := by
    have h1 : δ ^ (-ερ) * Real.sqrt ρ ≤ 1 / 4096 := by
      calc δ ^ (-ερ) * Real.sqrt ρ ≤ δ ^ (-ερ) * δ ^ (ε / 2) :=
            mul_le_mul_of_nonneg_left hsqδ (Real.rpow_nonneg hδ.le _)
        _ = δ ^ (ε / 2 - ερ) := by rw [← Real.rpow_add hδ]; ring_nf
        _ ≤ δ ^ (ε / 4) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        _ ≤ 1 / 4096 := hq2
    calc ρc ≤ δ ^ (-ερ) * ρ := hρc2
      _ = (δ ^ (-ερ) * Real.sqrt ρ) * Real.sqrt ρ := by rw [mul_assoc, hsqρ2]
      _ ≤ 1 / 4096 * Real.sqrt ρ := mul_le_mul_of_nonneg_right h1 hsqρ.le
      _ = Real.sqrt ρ / 4096 := by ring
  have hsq32 : Real.sqrt ρ ≤ 1 / 32 :=
    hsqδ.trans (hq1.trans (min_le_right _ _))
  have hs0 : 0 < s := hs
  have hsρc : s ≤ ρc := hshi
  -- the block side
  set N : ℕ := ⌊Real.sqrt ρ / s⌋₊ with hN
  have hNlo : Real.sqrt ρ / s - 1 < (N : ℝ) := Nat.sub_one_lt_floor _
  have hNhi : (N : ℝ) ≤ Real.sqrt ρ / s := Nat.floor_le (by positivity)
  have hN1 : 0 < N := by
    have : (1 : ℝ) ≤ Real.sqrt ρ / s := by rw [le_div_iff₀ hs]; linarith
    have : 1 ≤ N := Nat.le_floor (by exact_mod_cast this)
    omega
  set ω := (N : ℝ) * s with hω
  have hωhi : ω ≤ Real.sqrt ρ := by
    rw [hω]; calc (N : ℝ) * s ≤ Real.sqrt ρ / s * s := mul_le_mul_of_nonneg_right hNhi hs.le
      _ = Real.sqrt ρ := by field_simp
  have hωlo : Real.sqrt ρ / 2 ≤ ω := by
    have : Real.sqrt ρ - s < ω := by
      rw [hω]
      have := mul_lt_mul_of_pos_right hNlo hs
      rw [sub_mul, div_mul_cancel₀ _ hs.ne', one_mul] at this
      exact this
    linarith
  have hω0 : 0 < ω := by positivity
  -- parameters of the grain structure
  set L := δ ^ (-η) with hL
  set c := ρc ^ εG / 768 with hc
  set θ := ρc ^ εG * ρc ^ 2 * ω / (55296 * s ^ 3) with hθ
  set μ2 := ρc ^ (2 - σ + ερ) * (k : ℝ) * ρc ^ εG / 3072 with hμ2
  set μmax := ρc ^ (2 - σ - ερ) * (k : ℝ) with hμmax
  set μF := δ ^ (2 - σ + ερ) * (n : ℝ) with hμF
  set D := 32 * ρc / ρ0G with hD
  have hB1c : B1 / c ≤ μ2 / 2 := by
    have hc0 : 0 < c := by positivity
    rw [div_le_iff₀ hc0]
    have he : σ * ε / 16 ≤ σ * (κ - εG) - ερ - 3 * εG := he_early
    have hpow1 : ρc ^ (σ * (κ - εG) - ερ - 3 * εG) ≤ 1 / 300000000 := by
      calc ρc ^ (σ * (κ - εG) - ερ - 3 * εG) ≤ ρc ^ (σ * ε / 16) :=
            Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' he
        _ ≤ (δ ^ (ε / 2)) ^ (σ * ε / 16) := Real.rpow_le_rpow hρc0.le hρcsmall (by positivity)
        _ = δ ^ (σ * ε * ε / 32) := by rw [← Real.rpow_mul hδ.le]; ring_nf
        _ ≤ δ ^ (σ * ε * ε / 64) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
            have : 0 ≤ σ * ε * ε := by positivity
            linarith only [this])
        _ ≤ 1 / 300000000 := hq4
    have hρβσ : ρβ ^ σ ≤ ρc ^ (σ * (κ - εG)) := by
      calc ρβ ^ σ ≤ (ρc ^ (κ - εG)) ^ σ := Real.rpow_le_rpow hρβ0.le hρβle hσ.le
        _ = ρc ^ (σ * (κ - εG)) := by rw [← Real.rpow_mul hρc0.le]; ring_nf
    have hsplit : ρc ^ (2 - σ - εG) * ρc ^ (σ * (κ - εG)) =
        ρc ^ (2 - σ + ερ) * ρc ^ εG * ρc ^ εG * ρc ^ (σ * (κ - εG) - ερ - 3 * εG) := by
      rw [← Real.rpow_add hρc0, ← Real.rpow_add hρc0, ← Real.rpow_add hρc0,
        ← Real.rpow_add hρc0]; ring_nf
    set P := (k : ℝ) * (ρc ^ (2 - σ + ερ) * ρc ^ εG * ρc ^ εG) with hP
    have hP0 : 0 ≤ P := by positivity
    calc B1 ≤ 56 * (k : ℝ) * ρc ^ (2 - σ - εG) * ρβ ^ σ := hB1b
      _ ≤ 56 * (k : ℝ) * ρc ^ (2 - σ - εG) * ρc ^ (σ * (κ - εG)) := by gcongr
      _ = 56 * P * ρc ^ (σ * (κ - εG) - ερ - 3 * εG) := by
          rw [mul_assoc (56 * (k : ℝ)), hsplit, hP]; ring
      _ ≤ 56 * P * (1 / 300000000) := mul_le_mul_of_nonneg_left hpow1 (by positivity)
      _ ≤ μ2 / 2 * c := by
          rw [hμ2, hc]
          have e : ρc ^ (2 - σ + ερ) * (k : ℝ) * ρc ^ εG / 3072 / 2 * (ρc ^ εG / 768) =
              P / 4718592 := by rw [hP]; ring
          rw [e]
          calc 56 * P * (1 / 300000000) = P * (56 / 300000000) := by ring
            _ ≤ P * (1 / 4718592) := mul_le_mul_of_nonneg_left (by norm_num) hP0
            _ = P / 4718592 := by ring
  have hstruct := grain_structure (x := x) (Y := Y) (Y1 := Y1) (V := V) (δ := δ) (L := L)
    (ρc := ρc) (s := s) (θb := θb) (μF := μF) (μmax := μmax) (β := ρ0G) (B1 := B1) (c := c)
    (θ := θ) (μ2 := μ2) (D := D) (N := N) (z := z) (w := w) (M := M) (a := a) (Z := Z)
    hδ.le hF.2.1 hY1m (fun i => (hY1Yc i).trans (hYcY i))
    (fun i p hp => by
      have := hF.2.2.1 i (hF.2.2.2.2.2.1 i hp)
      exact (mem_ball_zero_iff.1 this).le)
    hVu hVp hVL (Real.rpow_nonneg hδ.le _) hw hs hρc0 (by linarith)
    (fun j => by rw [cubeSet, ← hYt j]; exact hFamG.2.2.2.2.2.1 j)
    (fun i => by rw [cubeSet, ← hYt (a i)]; exact hcontr i) hdir hR1 hθb
    (fun j m hm => (hP3 j m hm).1) hfine (by positivity)
    (fun m => card_labels_le hs hYt hcoarse m) (by positivity) hZm
    (fun j => by rw [cubeSet, ← hYt j]; exact hZYt j) hcone (by positivity) (by positivity)
    (by positivity) hB1c hN1 (by linarith) (by linarith) (by positivity)
    (by
      rw [hD, le_div_iff₀ hρ0G0]
      calc 4 * ρc * ρ0G ≤ 4 * ρc * 1 := mul_le_mul_of_nonneg_left hρ0G1 (by positivity)
        _ ≤ 32 * ρc := by linarith only [hρc0])
    (by
      rw [hD]
      have e : 16 * ρc / (32 * ρc / ρ0G) = ρ0G / 2 := by field_simp; ring
      rw [e]; linarith only [hρ0G0])
  obtain ⟨Y'', hY''Y1, hY''m, hmass'', hwin⟩ := hstruct
  have hY''Y : ∀ i, Y'' i ⊆ Y i := fun i => (hY''Y1 i).trans ((hY1Yc i).trans (hYcY i))
  set lam := 1 - 4 * ρc with hlam
  have hlam2 : 1 / 2 ≤ lam := by rw [hlam]; linarith
  -- the expression in the mass bound is at least a quarter of the refined coarse mass
  have hZmass' : ρc ^ εG * (k : ℝ) * ρc ^ 2 ≤ ∑ j, (volume (Z j)).toReal := by
    have hfin : ∀ j, volume (Z j) ≠ ∞ := fun j =>
      ne_top_of_le_ne_top (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne
        (measure_mono ((hZT j).trans (hFamG.2.2.1 j)))
    have h := hZmass
    rw [← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun j _ => hfin j),
      ENNReal.toReal_sum fun j _ => hfin j] at h
    exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun j _ =>
      ENNReal.toReal_nonneg)).1 h
  have hYtc : ∀ j, Yt j = cubeSet s (M j) := fun j => by rw [hYt j]; rfl
  have hMT' : ∀ j, cubeSet s (M j) ⊆ tube ρc (z j) (w j) := fun j => by
    rw [← hYtc j]; exact hFamG.2.2.2.2.2.1 j
  have hsumM := sum_card_cubes_le hs hρc0 hρc1' hw hMT'
  set μlo := ρc ^ (2 - σ + ερ) * (k : ℝ) with hμlo
  have hμlo0 : 0 < μlo := by positivity
  have hunion := card_union_cubes_le hs hρc0 hρc1' hw hMT' hμlo0 (fun q hq => by
    have hq' : q ∈ ⋃ j, Yt j := by
      obtain ⟨j, hj⟩ := mem_iUnion.1 hq; exact mem_iUnion.2 ⟨j, by rw [hYtc j]; exact hj⟩
    have := hclo q hq'
    have e : (fun j => cubeSet s (M j)) = Yt := funext fun j => (hYtc j).symm
    rw [e]; exact this)
  have hexpr : ρc ^ εG * (k : ℝ) * ρc ^ 2 / 4 ≤ (∑ j, (volume (Z j)).toReal) -
      c * (∑ j, ((M j).card : ℝ)) * s ^ 3 -
      2 * θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) * s ^ 3 -
      μ2 * ((Finset.univ.biUnion M).card : ℝ) * s ^ 3 := by
    have e1 : c * (∑ j, ((M j).card : ℝ)) * s ^ 3 ≤ ρc ^ εG * (k : ℝ) * ρc ^ 2 / 2 := by
      calc c * (∑ j, ((M j).card : ℝ)) * s ^ 3 = c * ((∑ j, ((M j).card : ℝ)) * s ^ 3) := by
            ring
        _ ≤ c * ((k : ℝ) * (384 * ρc ^ 2)) :=
            mul_le_mul_of_nonneg_left hsumM (by positivity)
        _ = ρc ^ εG * (k : ℝ) * ρc ^ 2 / 2 := by rw [hc]; ring
    have e2 : 2 * θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) * s ^ 3 = ρc ^ εG * (k : ℝ) * ρc ^ 2 / 8 := by
      rw [hθ, ← hω]
      field_simp
      ring
    have e3 : μ2 * ((Finset.univ.biUnion M).card : ℝ) * s ^ 3 ≤ ρc ^ εG * (k : ℝ) * ρc ^ 2 / 8 := by
      calc μ2 * ((Finset.univ.biUnion M).card : ℝ) * s ^ 3 =
            μ2 * (((Finset.univ.biUnion M).card : ℝ) * s ^ 3) := by ring
        _ ≤ μ2 * (384 * (k : ℝ) * ρc ^ 2 / μlo) :=
            mul_le_mul_of_nonneg_left hunion (by positivity)
        _ = ρc ^ εG * (k : ℝ) * ρc ^ 2 / 8 := by
            rw [hμ2]; field_simp; ring
    linarith
  -- the balanced density
  have hlam0 : 0 < lam := by linarith
  set μhi := δ ^ (2 - σ - ερ) * (n : ℝ) with hμhi
  have hμhi0 : 0 < μhi := by positivity
  have hfineHi : ∀ p, (fineMult Y1 p : ℝ) ≤ μhi := by
    intro p
    have h1 := fineMult_le_of_fibres (lam := lam) hcontr hfib p
    have h2 := hcoarse (lam • p)
    have hB : 0 ≤ (δ / ρc) ^ (2 - σ - ερ) * ((n : ℝ) / (k : ℝ)) := by positivity
    calc (fineMult Y1 p : ℝ) ≤ (fineMult Yt (lam • p) : ℝ) *
          ((δ / ρc) ^ (2 - σ - ερ) * ((n : ℝ) / (k : ℝ))) := h1
      _ ≤ ρc ^ (2 - σ - ερ) * (k : ℝ) * ((δ / ρc) ^ (2 - σ - ερ) * ((n : ℝ) / (k : ℝ))) :=
          mul_le_mul_of_nonneg_right h2 hB
      _ = μhi := by
          rw [hμhi, Real.div_rpow hδ.le hρc0.le]
          field_simp
  have hθbal := balance_density_lower (Y1 := Y1) (M := M) (a := a) (ε := ερ) hs hlam0 hδ hρc0
    hY1m (fun i => by rw [← hYtc (a i)]; exact hcontr i) (fun j m hm => (hP3 j m hm).2)
    (by
      have e : (⋃ j, cubeSet s (M j)) = ⋃ j, Yt j := by simp only [hYtc]
      rw [e]; exact hvolG) hfineHi hμhi0 hY1mass hθb.le
  have hθblow : δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8 ≤ θb := by
    rw [hμhi, fine_density_ratio hδ hnR] at hθbal
    exact theta_from_balance hδ hρc0 hlam2 hθbal
  -- the refined family is `ε`-extremal
  have hmassfinal : δ ^ ε * (n : ℝ) * δ ^ 2 ≤ μF * θb * ((∑ j, (volume (Z j)).toReal) -
      c * (∑ j, ((M j).card : ℝ)) * s ^ 3 -
      2 * θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) * s ^ 3 -
      μ2 * ((Finset.univ.biUnion M).card : ℝ) * s ^ 3) / μmax := by
    have h := grain_mass_arith (σ := σ) (ερ := ερ) (εG := εG) (ε := ε) (ρc := ρc) (θb := θb)
      (n := n) (k := k) hδ hδ1 (hδρ.trans hρc1) hnR hkR hθblow hexpr hερ0.le hεG0.le
      hexp6 (hq1.trans (min_le_right _ _))
    rw [hμF, hμmax]
    convert h using 1
  have hFam'' : Family ε δ n x v Y'' := by
    refine hF.of_subsets_mass hY''Y hY''m ?_
    have hfin : ∀ i, volume (Y'' i) ≠ ∞ := fun i => ne_top_of_le_ne_top
      (hF.shading_finite i) (measure_mono (hY''Y i))
    have h := ENNReal.ofReal_le_ofReal hmassfinal |>.trans hmass''
    rw [shadingMass, ← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ =>
      ENNReal.toReal_nonneg), ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
    refine h.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_toReal (hfin i)).symm
  refine ⟨Y'', hY''Y, hFam'', ?_⟩
  -- the grid ratio
  set g := ρ ^ (-(1 / (2 * (Mτ : ℝ)))) with hg
  have hMτ0 : (0 : ℝ) < Mτ := by linarith only [hMτR]
  have hρ12 : ρ ^ (1 / (2 * (Mτ : ℝ))) ≤ 1 / 3 := by
    calc ρ ^ (1 / (2 * (Mτ : ℝ))) ≤ (δ ^ ε) ^ (1 / (2 * (Mτ : ℝ))) :=
          Real.rpow_le_rpow hρ0.le hρ2 (by positivity)
      _ = δ ^ (ε / (2 * Mτ)) := by rw [← Real.rpow_mul hδ.le]; ring_nf
      _ ≤ 1 / 3 := hq3
  have hgpos : 0 < ρ ^ (1 / (2 * (Mτ : ℝ))) := Real.rpow_pos_of_pos hρ0 _
  have hginv : g = (ρ ^ (1 / (2 * (Mτ : ℝ))))⁻¹ := by rw [hg, Real.rpow_neg hρ0.le]
  have hg3 : 3 ≤ g := by
    rw [hginv, le_inv_comm₀ (by norm_num) hgpos]
    linarith only [hρ12]
  have hg1 : 1 ≤ g := by linarith only [hg3]
  have hgδ : g ≤ δ ^ (-(1 / (2 * (Mτ : ℝ)))) :=
    Real.rpow_le_rpow_of_nonpos hδ hδρ (by
      have : 0 ≤ 1 / (2 * (Mτ : ℝ)) := by positivity
      linarith only [this])
  have hgεc : δ ^ (-εc) ≤ g := by
    have h1 : δ ^ (-εc) ≤ δ ^ (-(ε / (2 * Mτ))) := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      have : εc ≤ ε / (2 * Mτ) := hεcs.trans (by
        apply div_le_div_of_nonneg_left hε.le (by positivity); linarith only [hMτR])
      linarith only [this]
    have h2 : δ ^ (-(ε / (2 * Mτ))) ≤ g := by
      rw [hg]
      have e : δ ^ (-(ε / (2 * Mτ))) = (δ ^ ε) ^ (-(1 / (2 * (Mτ : ℝ)))) := by
        rw [← Real.rpow_mul hδ.le]; ring_nf
      rw [e]
      exact Real.rpow_le_rpow_of_nonpos hρ0 hρ2 (by
        have : 0 ≤ 1 / (2 * (Mτ : ℝ)) := by positivity
        linarith only [this])
    exact h1.trans h2
  have ht_succ : ∀ i : ℕ, t (i + 1) = t i * g := by
    intro i
    simp only [ht, hg]
    rw [← Real.rpow_add hρ0]
    congr 1; push_cast; field_simp; ring
  have ht0 : t 0 = ρ := by simp [ht]
  have ht_mono : ∀ i j : ℕ, i ≤ j → t i ≤ t j := by
    intro i j hij
    apply Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1'
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    have h2 : (i : ℝ) / (2 * Mτ) ≤ j / (2 * Mτ) := div_le_div_of_nonneg_right this (by positivity)
    linarith only [h2]
  have htM : t (Mτ + 1) = Real.sqrt ρ * g := by
    simp only [ht, hg]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hρ0]
    congr 1; push_cast; field_simp; ring
  -- the slab width
  set hw := (2 * ((2 * ω + 2 * ρc) * (ρc / 2 + δ + L * (Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s +
    4 * ρc)) + 2 * ρc) + 2 * s) / lam with hhw
  have hhwb : hw ≤ 78 * δ ^ (-(ερ + η)) * ρ :=
    slab_width_le hδ hδ1 (hδρ.trans hρc1) hρc2 hρcsq hs hsρc hω0.le hωhi
      (by linarith only [hsq32]) hρ0 hL hlam2 hερ0.le hη0.le
  have hhw0 : 0 ≤ hw := by
    rw [hhw]
    apply div_nonneg _ (by linarith only [hlam2])
    have : 0 ≤ L := by rw [hL]; positivity
    positivity
  have hΛ : δ ^ (-(ερ + η)) * Real.sqrt ρ ≤ 1 / 4096 := by
    calc δ ^ (-(ερ + η)) * Real.sqrt ρ ≤ δ ^ (-(ερ + η)) * δ ^ (ε / 2) :=
          mul_le_mul_of_nonneg_left hsqδ (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (ε / 2 - (ερ + η)) := by rw [← Real.rpow_add hδ]; ring_nf
      _ ≤ δ ^ (ε / 4) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
          have h1 : ερ ≤ ε / 2048 := hερs.trans hσε
          have h2 : η ≤ ε / 2048 := hηs.trans hσε
          linarith only [h1, h2, hε])
      _ ≤ 1 / 4096 := hq2
  have h2hw : 2 * hw ≤ Real.sqrt ρ := by
    have h1 : 2 * hw ≤ 156 * (δ ^ (-(ερ + η)) * Real.sqrt ρ) * Real.sqrt ρ := by
      calc 2 * hw ≤ 2 * (78 * δ ^ (-(ερ + η)) * ρ) := by linarith only [hhwb]
        _ = 156 * δ ^ (-(ερ + η)) * ρ := by ring
        _ = 156 * δ ^ (-(ερ + η)) * (Real.sqrt ρ * Real.sqrt ρ) := by rw [hsqρ2]
        _ = 156 * (δ ^ (-(ερ + η)) * Real.sqrt ρ) * Real.sqrt ρ := by ring
    have h2 : 156 * (δ ^ (-(ερ + η)) * Real.sqrt ρ) * Real.sqrt ρ ≤ Real.sqrt ρ := by
      have := mul_le_mul_of_nonneg_right hΛ hsqρ.le
      calc 156 * (δ ^ (-(ερ + η)) * Real.sqrt ρ) * Real.sqrt ρ =
            156 * ((δ ^ (-(ερ + η)) * Real.sqrt ρ) * Real.sqrt ρ) := by ring
        _ ≤ 156 * (1 / 4096 * Real.sqrt ρ) := by linarith only [this]
        _ ≤ Real.sqrt ρ := by linarith only [hsqρ]
    linarith only [h1, h2]
  set H0 := 2 * hw / ρ + 2 with hH0
  have hH01 : 1 ≤ H0 := by
    have : 0 ≤ 2 * hw / ρ := div_nonneg (by linarith only [hhw0]) hρ0.le
    linarith only [this]
  have hH0b : H0 ≤ 158 * δ ^ (-(ερ + η)) := by
    have h1 : 2 * hw / ρ ≤ 156 * δ ^ (-(ερ + η)) := by
      rw [div_le_iff₀ hρ0]; linarith only [hhwb]
    have h2 : 1 ≤ δ ^ (-(ερ + η)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by
      linarith only [hερ0, hη0])
    linarith only [h1, h2]
  have hlam0' : 0 < lam := by linarith only [hlam2]
  -- windows of length at most `2 √ρ`
  have hclaim : ∀ p ∈ ⋃ i, Y'' i, ∀ a R : ℝ, ρ ≤ R → R ≤ 2 * Real.sqrt ρ →
      ∃ (m : ℕ) (c : Fin m → ℝ),
        ((fun q => inner ℝ (V p) q) '' ((⋃ i, Y'' i) ∩ ball p (Real.sqrt ρ))) ∩
          Icc a (a + R) ⊆ ⋃ j, closedBall (c j) ρ ∧
        (m : ℝ) ≤ δ ^ (-ε) * (R / ρ) ^ (1 - σ) := by
    intro p hp a R hR1 hR2
    have hPM : R + 2 * hw ≤ t (Mτ + 1) := by
      rw [htM]
      have : 3 * Real.sqrt ρ ≤ Real.sqrt ρ * g := by nlinarith only [hg3, hsqρ]
      linarith only [hR2, h2hw, this]
    have hex : ∃ i : ℕ, R + 2 * hw ≤ t (i + 1) := ⟨Mτ, hPM⟩
    set i := Nat.find hex with hi
    have hi1 : R + 2 * hw ≤ t (i + 1) := Nat.find_spec hex
    have hiM : i ≤ Mτ := Nat.find_min' hex hPM
    have hti : t i ≤ R + 2 * hw := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, ht0]; linarith only [hR1, hhw0]
      · have h := Nat.find_min hex (show i - 1 < i by omega)
        push Not at h
        rw [Nat.sub_add_cancel hpos] at h
        exact h.le
    obtain ⟨τc, hτc1, hτc2, hcb⟩ := hcubes i (by omega)
    set r := t (i + 1) with hr
    have hrg : r = t i * g := ht_succ i
    have hti0 : 0 < t i := Real.rpow_pos_of_pos hρ0 _
    have hρti : ρ ≤ t i := by rw [← ht0]; exact ht_mono 0 i (Nat.zero_le i)
    have hτc0 : 0 < τc := hti0.trans_le hτc1
    have hτcr : τc ≤ r := by
      rw [hrg]
      calc τc ≤ δ ^ (-εc) * t i := hτc2
        _ ≤ g * t i := mul_le_mul_of_nonneg_right hgεc hti0.le
        _ = t i * g := by ring
    have hr0 : 0 < r := hτc0.trans_le hτcr
    have hδr : δ ≤ r := hδρ.trans (hρti.trans (hτc1.trans hτcr))
    set U := 54880000 * (r / τc) ^ 4 * τc ^ (3 - σ - εc) * δ ^ (σ - 2 * εc) with hU
    have hU0 : 0 ≤ U := by positivity
    have hcubeY1 : ∀ cc, volume ((⋃ i, Y1 i) ∩ closedBall cc r) ≤ ENNReal.ofReal U := by
      intro cc
      refine (measure_mono (inter_subset_inter_left _ (iUnion_mono hY1Yc))).trans ?_
      exact hcb cc r hτcr
    obtain ⟨Nn, cs, hcov, hNn⟩ := hwin p hp a R r U ρ (Real.sqrt ρ) hr0 hU0 hρ0
      (hρ0.le.trans hR1) hsqρ.le hcubeY1
    refine ⟨Nn, cs, hcov, ?_⟩
    have hrM : r ≤ Real.sqrt ρ * g := by rw [← htM]; exact ht_mono (i + 1) (Mτ + 1) (by omega)
    have h2ω : 2 * ω / lam ≤ 4 * ω := by
      rw [div_le_iff₀ hlam0']; nlinarith only [hlam2, hω0]
    have hA8 : Real.sqrt ρ + 2 * ω / lam + r ≤ 8 * g * Real.sqrt ρ := by
      have h1 : Real.sqrt ρ ≤ g * Real.sqrt ρ := le_mul_of_one_le_left hsqρ.le hg1
      linarith only [h2ω, hωhi, hrM, h1, hsqρ]
    have hW3 : R + 2 * hw + 2 * r ≤ 3 * r := by linarith only [hi1]
    have hrτ : r / τc ≤ g := by
      rw [div_le_iff₀ hτc0, hrg]
      exact mul_comm (t i) g ▸ mul_le_mul_of_nonneg_left hτc1 (by linarith only [hg1])
    have hUb : U ≤ 54880000 * g ^ 4 * r ^ (3 - σ - εc) * δ ^ (σ - 2 * εc) := by
      have h1 : (r / τc) ^ 4 ≤ g ^ 4 := pow_le_pow_left₀ (by positivity) hrτ 4
      have h2 : τc ^ (3 - σ - εc) ≤ r ^ (3 - σ - εc) :=
        Real.rpow_le_rpow hτc0.le hτcr (by linarith only [hσ1, hεc8, hε1])
      rw [hU]
      gcongr
    have hρβκ : ρc ^ κ / 16 ≤ ρ0G := by linarith only [hρ0lo, hρβ1]
    have hmf := mf_lower (δ := δ) (ρ := ρ) (ρc := ρc) (σ := σ) (ερ := ερ) (εG := εG) (κ := κ)
      (θb := θb) (ω := ω) (s := s) (k := (k : ℝ)) (ρ0G := ρ0G) hδ hρ0 hρc0 hρc1' hs hkR hωlo
      hρβκ hρ0G1 (by rw [hκ]; positivity) hθblow
    have hrR : r ≤ g * H0 * R := by
      have h1 : R + 2 * hw ≤ H0 * R := by
        have : 2 * hw ≤ 2 * hw / ρ * R := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hρ0]
          exact mul_le_mul_of_nonneg_left hR1 (by linarith only [hhw0])
        rw [hH0]; linarith only [this, hR1, hρ0]
      rw [hrg]
      calc t i * g ≤ (R + 2 * hw) * g := mul_le_mul_of_nonneg_right hti (by linarith only [hg1])
        _ ≤ H0 * R * g := mul_le_mul_of_nonneg_right h1 (by linarith only [hg1])
        _ = g * H0 * R := by ring
    have harith := grain_arith (δ := δ) (ρ := ρ) (ρc := ρc) (r := r) (R := R) (g := g) (H0 := H0)
      (A := Real.sqrt ρ + 2 * ω / lam + r) (W := R + 2 * hw + 2 * r) (U := U)
      (σ := σ) (εc := εc) (e1 := 3 * ερ) (e2 := κ + 3 * εG + 3 * ερ)
      (C2 := 32 * 55296 ^ 2 * 3072 * 256 * 4608)
      hδ hδ1 hδρ hρc1 hρc1' hδr hR1 hg1 hσ hσ1 (by linarith only [hερ0]) (by
        have : 0 < κ := by rw [hκ]; positivity
        linarith only [this, hεG0, hερ0])
      hεc0.le (by linarith only [hεc8, hε1]) (by norm_num) (by positivity) hA8
      (by linarith only [hR1, hρ0, hhw0, hr0]) hW3 hU0 hUb hmf hrR hH01
    have hfin := final_exponent_le (δ := δ) (g := g) (H0 := H0)
      (C := 6144 * 54880000 * (32 * 55296 ^ 2 * 3072 * 256 * 4608))
      (E := 3 * εc + 3 * ερ + (κ + 3 * εG + 3 * ερ)) (a := 1 / (2 * (Mτ : ℝ)))
      (b := ερ + η) (ε := ε) (Rt := (R / ρ) ^ (1 - σ)) hδ hδ1 hg1 hgδ hH01 hH0b hbudget
      (by norm_num) (by
        rw [← hCfin]
        calc Cfin * 158 ^ 2 * δ ^ (ε / 2) ≤ Cfin * 158 ^ 2 * (1 / (Cfin * 158 ^ 2)) :=
              mul_le_mul_of_nonneg_left hq5 (by positivity)
          _ = 1 := by field_simp)
      (Real.rpow_nonneg (div_nonneg (hρ0.le.trans hR1) hρ0.le) _) (by positivity)
      (by linarith only [hερ0, hη0])
    exact hNn.trans (harith.trans hfin)
  -- general windows
  intro p hp a R hR
  by_cases hR2 : R ≤ 2 * Real.sqrt ρ
  · exact hclaim p hp a R hR hR2
  push Not at hR2
  have hpY : p ∈ ⋃ i, Y i := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp; exact mem_iUnion.2 ⟨i, hY''Y i hi⟩
  have hVp1 : ‖V p‖ = 1 := hVu p hpY
  set a' := inner ℝ (V p) p - Real.sqrt ρ with ha'
  have hρR' : ρ ≤ 2 * Real.sqrt ρ := by
    have : ρ ≤ Real.sqrt ρ := by
      calc ρ = Real.sqrt ρ * Real.sqrt ρ := hsqρ2.symm
        _ ≤ Real.sqrt ρ * 1 := mul_le_mul_of_nonneg_left (by linarith only [hsq32]) hsqρ.le
        _ = Real.sqrt ρ := mul_one _
    linarith only [this, hsqρ]
  obtain ⟨m, c, hcov, hm⟩ := hclaim p hp a' (2 * Real.sqrt ρ) hρR' le_rfl
  refine ⟨m, c, ?_, ?_⟩
  · rintro t ⟨⟨q, hq, rfl⟩, -⟩
    apply hcov
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    have hd : |inner ℝ (V p) q - inner ℝ (V p) p| < Real.sqrt ρ := by
      rw [← inner_sub_right]
      calc |inner ℝ (V p) (q - p)| ≤ ‖V p‖ * ‖q - p‖ := abs_real_inner_le_norm _ _
        _ < Real.sqrt ρ := by rw [hVp1, one_mul, ← dist_eq_norm]; exact mem_ball.1 hq.2
    rw [abs_lt] at hd
    simp only [ha', mem_Icc]
    constructor <;> linarith only [hd]
  · refine hm.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hδ.le _))
    exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hR2.le hρ0.le)
      (by linarith only [hσ1])

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
