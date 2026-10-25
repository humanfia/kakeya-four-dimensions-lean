-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.PlaneGrainsTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LocalGrains
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzRefine
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TwoScaleBridge
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSTheorem

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **Weak plane map for a given family** (sticky Lemma 4.3 after regularization): an
`η`-extremal family has an `ε`-extremal refinement with a measurable unit plane map of precision
`δ ^ (σ / 64)`. -/
theorem weak_plane_refine {σ : ℝ} (hσ : 0 < σ) (habove : ∀ t : ℝ, σ < t → ¬ Examples t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η d1 : ℝ, 0 < η ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧ Family ε δ n x v Z ∧
          Separated ε δ n x v ∧ volume (⋃ i, Z i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) ∧
          ∃ P : Space → Space, Measurable P ∧ (∀ p ∈ ⋃ i, Z i, ‖P p‖ = 1) ∧
            ∀ i p, p ∈ Z i → |inner ℝ (v i) (P p)| ≤ δ ^ (σ / 64) := by
  obtain ⟨C, hC, hwp⟩ := weak_plane_map (σ / 8) (by positivity)
  set ε0 := min (ε / 4) (σ / 64) with hε0def
  have hε0 : 0 < ε0 := lt_min (by positivity) (by positivity)
  have hε0ε : ε0 ≤ ε / 4 := min_le_left _ _
  have hε0σ : ε0 ≤ σ / 64 := min_le_right _ _
  obtain ⟨ηr, dr, hηr, hηrε, hdr, href⟩ := uniform_incidence_refinement habove ε0 hε0
  obtain ⟨d1, hd1, hcut1⟩ := exists_power_cutoff (a := σ / 8 - 7 * ε0 / 2)
    (by linarith) (by positivity : (0:ℝ) < 1 / (20 * C))
  obtain ⟨d2, hd2, hcut2⟩ := exists_power_cutoff (a := ε0) hε0 (by norm_num : (0:ℝ) < 1 / 8)
  refine ⟨ηr, min dr (min d1 d2), hηr, lt_min hdr (lt_min hd1 hd2), ?_⟩
  intro δ hδ hδd hδ100 n x v Y hF hS hV
  have hδr : δ ≤ dr := hδd.trans (min_le_left _ _)
  have hδ1' : δ ≤ d1 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ2 : δ ≤ d2 := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨Z0, hZ0Y, hFZ0, hSZ0, -, hVZ0, hup, hlo⟩ := href δ hδ hδr hδ100 n x v Y hF hS hV
  have hn : 0 < n := hFZ0.1
  have hYm : ∀ i, MeasurableSet (Z0 i) := hFZ0.2.2.2.2.1
  have hYT : ∀ i, Z0 i ⊆ tube δ (x i) (v i) := hFZ0.2.2.2.2.2.1
  have hv : ∀ i, ‖v i‖ = 1 := hFZ0.2.1
  have hmass := hFZ0.mass_lower hδ
  obtain ⟨Z, P, hZY, hZm, hZmass, hPm, hPn, hPi⟩ :=
    hwp (δ ^ (σ / 32)) (δ ^ (σ / 64)) δ ((n : ℝ) * δ ^ (2 - σ + ε0)) ((n : ℝ) * δ ^ (2 - σ - ε0))
      (by positivity) (Real.rpow_le_one hδ.le hδ1 (by positivity)) (by positivity) hδ hδ1
      (by positivity) n x v Z0 hv hYm hYT hFZ0.union_subset_ball
      (fun p hp => ⟨(hlo p hp).le, hup p⟩)
      (weak_plane_numeric hε0 hδ hn hC (hcut1 δ hδ hδ1') hmass)
  have hZfam : Family (2 * ε0) δ n x v Z := by
    refine hFZ0.of_subsets_mass hZY hZm ?_
    have h8 : δ ^ (2 * ε0) ≤ δ ^ ε0 / 8 := by
      have := hcut2 δ hδ hδ2
      calc δ ^ (2 * ε0) = δ ^ ε0 * δ ^ ε0 := by rw [← Real.rpow_add hδ]; ring_nf
        _ ≤ δ ^ ε0 * (1 / 8) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = δ ^ ε0 / 8 := by ring
    calc δ ^ (2 * ε0) * (n : ℝ) * δ ^ 2 ≤ δ ^ ε0 / 8 * (n : ℝ) * δ ^ 2 := by gcongr
      _ = (δ ^ ε0 * (n : ℝ) * δ ^ 2) / 8 := by ring
      _ ≤ shadingMass Z0 / 8 := by gcongr
      _ ≤ shadingMass Z := hZmass
  have hZY' : ∀ i, Z i ⊆ Y i := fun i => (hZY i).trans (hZ0Y i)
  refine ⟨Z, hZY', hZfam.mono_error hδ hδ1 (by linarith), hSZ0.mono_error hδ hδ1 (by linarith),
    ?_, P, hPm, hPn, ?_⟩
  · refine (measure_mono (iUnion_mono hZY)).trans (hVZ0.trans ?_)
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  · intro i p hp
    have h := hPi i p hp
    have e : max (δ ^ (σ / 32) / δ ^ (σ / 64)) (δ ^ (σ / 64)) = δ ^ (σ / 64) := by
      have : δ ^ (σ / 32) / δ ^ (σ / 64) = δ ^ (σ / 64) := by
        rw [← Real.rpow_sub hδ]; ring_nf
      rw [this, max_self]
    rwa [e] at h

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- `coarse_plane_mapP` with the coarse union inside the `6 ρc`-neighbourhood of the fine one. -/
theorem coarse_plane_mapP' {σ ε δ ρc : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hn : 0 < n) (hδ : 0 < δ) (hρc : 0 < ρc) (hρc4 : ρc ≤ 1 / 4)
    (hYball : ∀ i, ∀ p ∈ Y i, ‖p‖ ≤ 1)
    (hTS : TwoScaleAtP σ ε δ ρc n x v Y) {V : Space → Space} (hVm : Measurable V)
    (hVu : ∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1)
    (hVp : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ ρc / 2) :
    ∃ (k : ℕ) (z w : Fin k → Space) (Yt Yt'' : Fin k → Set Space) (Vt : Space → Space) (s : ℝ),
      Family ε ρc k z w Yt ∧ Separated ε ρc k z w ∧
      volume (⋃ j, Yt j) ≤ ENNReal.ofReal (ρc ^ (σ - ε)) ∧
      (∀ j, Yt'' j ⊆ Yt j) ∧ (∀ j, MeasurableSet (Yt'' j)) ∧
      (∀ q, δ ^ (2 * ε) * incidence Yt q ≤ incidence Yt'' q) ∧ Measurable Vt ∧
      (∀ q ∈ ⋃ j, Yt'' j, ‖Vt q‖ = 1) ∧
      (∀ j q, q ∈ Yt'' j → |inner ℝ (w j) (Vt q)| ≤ ρc) ∧
      0 < s ∧ ρc / 16 ≤ s ∧ s ≤ ρc ∧ (∀ q q', cubeIndex s q = cubeIndex s q' → Vt q = Vt q') ∧
      (⋃ j, Yt j) ⊆ thickening (6 * ρc) (⋃ i, Y i) := by
  obtain ⟨Y', k, z, w, Yt, a, s, M, hY'Y, hY'm, hY'mass, hFam, hSep, hvol, hcontr, hdir, hs,
    hslo, hshi, hYt, hfine, hfib, hcoarse, -, hR1, -⟩ := hTS
  have hk : 0 < k := hFam.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set A := δ ^ (2 - σ + ε) * (n : ℝ) with hAdef
  set B := (δ / ρc) ^ (2 - σ - ε) * ((n : ℝ) / (k : ℝ)) with hBdef
  set Cc := ρc ^ (2 - σ - ε) * (k : ℝ) with hCdef
  have hB : 0 < B := mul_pos (Real.rpow_pos_of_pos (div_pos hδ hρc) _) (div_pos hnR hkR)
  have hC : 0 < Cc := mul_pos (Real.rpow_pos_of_pos hρc _) hkR
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg hδ.le _) hnR.le
  have hABC : A / (B * Cc) = δ ^ (2 * ε) := by
    have := standard_ratio (σ := σ) (ε := ε) hδ hρc hn hk
    rw [hAdef, hBdef, hCdef]
    convert this using 2
  have hVu' : ∀ p ∈ ⋃ i, Y' i, ‖V p‖ = 1 := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    exact hVu p (mem_iUnion.2 ⟨i, hY'Y i hi⟩)
  obtain ⟨Yt'', Vt, hsub, hmeas, hinc, hVtm, hVtu, hVtp, hcube⟩ :=
    strong_plane_map (v := v) (Y' := Y') (w := w) (Yt := Yt) (a := a) (s := s) (ρc := ρc)
      (lam := 1 - 4 * ρc) (A := A) (B := B) (Cc := Cc) hs hYt hcontr hR1
      (fun i hi => by rw [norm_sub_rev, add_comm]; exact hdir i hi)
      (fun p hp => by rw [incidence_eq_fineMult]; exact hfine p hp)
      hfib (fun q => by rw [incidence_eq_fineMult]; exact hcoarse q)
      V hVm hVu' (fun i p hp => hVp i p (hY'Y i hp)) hA hB hC
  refine ⟨k, z, w, Yt, Yt'', Vt, s, hFam, hSep, hvol, hsub, hmeas, ?_, hVtm, hVtu, hVtp, hs,
    hslo, hshi, hcube, ?_⟩
  · intro q
    rw [← hABC]
    exact hinc q
  · intro q hq
    obtain ⟨j, hj⟩ := mem_iUnion.1 hq
    rw [hYt j] at hj
    obtain ⟨m, hm, hqm⟩ := mem_iUnion₂.1 hj
    obtain ⟨i, -, p, hp, hpm⟩ := hR1 j m hm
    have h1 : dist q ((1 - 4 * ρc) • p) < 2 * s := diam_le_of_mem_gridCube hs hqm hpm
    have h2 : dist ((1 - 4 * ρc) • p) p ≤ 4 * ρc := by
      have e : (1 - 4 * ρc) • p - p = (-(4 * ρc)) • p := by
        rw [sub_smul (1 : ℝ) (4 * ρc) p, one_smul, neg_smul]; abel
      rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
      calc 4 * ρc * ‖p‖ ≤ 4 * ρc * 1 :=
            mul_le_mul_of_nonneg_left (hYball i p (hY'Y i hp)) (by positivity)
        _ = 4 * ρc := mul_one _
    refine mem_thickening_iff.2 ⟨p, mem_iUnion.2 ⟨i, hY'Y i hp⟩, ?_⟩
    calc dist q p ≤ dist q ((1 - 4 * ρc) • p) + dist ((1 - 4 * ρc) • p) p := dist_triangle _ _ _
      _ < 2 * s + 4 * ρc := by linarith
      _ ≤ 6 * ρc := by linarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

set_option maxHeartbeats 2000000 in
/-- **Weak and coarse plane map for a given family** (sticky Lemmas 4.3 and 4.4). -/
theorem cube_plane_refine {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2)
    (habove : ∀ t : ℝ, σ < t → ¬ Examples t) (hTS : TwoScaleTheoremP σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ η d1 : ℝ, 0 < η ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        ∃ ρc : ℝ, δ ^ (σ / 64) ≤ ρc ∧ ρc ≤ δ ^ (σ / 64 - ε) ∧ ρc ≤ 1 / 100 ∧
        ∃ (k : ℕ) (z w : Fin k → Space) (Yt : Fin k → Set Space) (V : Space → Space) (s : ℝ),
          Family ε ρc k z w Yt ∧ Separated ε ρc k z w ∧
          volume (⋃ j, Yt j) ≤ ENNReal.ofReal (ρc ^ (σ - ε)) ∧
          (⋃ j, Yt j) ⊆ thickening (6 * ρc) (⋃ i, Y i) ∧
          Measurable V ∧ (∀ p ∈ ⋃ j, Yt j, ‖V p‖ = 1) ∧
          (∀ j p, p ∈ Yt j → |inner ℝ (w j) (V p)| ≤ ρc) ∧
          0 < s ∧ ρc / 16 ≤ s ∧ s ≤ ρc ∧ (∀ q q', cubeIndex s q = cubeIndex s q' → V q = V q') := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set ε1 := σ * ε' / 1024 with hε1
  have hε10 : 0 < ε1 := by positivity
  have hε1σ : ε1 ≤ σ / 1024 := by rw [hε1]; nlinarith
  have hε1ε : ε1 ≤ ε := by
    have : σ * ε' ≤ 2 * ε' := mul_le_mul_of_nonneg_right hσ2 hε'0.le
    rw [hε1]; linarith
  have hε1pre : ε1 ≤ ε' / 512 := by rw [hε1]; nlinarith
  obtain ⟨η1, d1, hη1, hd1, hTS1⟩ := hTS ε1 hε10
  obtain ⟨ηw, dw, hηw, hdw, hweak⟩ := weak_plane_refine hσ habove η1 hη1
  -- cutoffs on the fine scale
  obtain ⟨c1, hc1, hcut1⟩ := exists_power_cutoff (a := σ * ε' / 512) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨c2, hc2, hcut2⟩ := exists_power_cutoff (a := σ / 128) (by positivity)
    (by norm_num : (0:ℝ) < (1 / 100) / 2)
  obtain ⟨c3, hc3, hcut3⟩ := exists_power_cutoff (a := σ / 128) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨c4, hc4, hcut4⟩ := exists_power_cutoff (a := ε / 2) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 2)
  refine ⟨ηw, min (min (min d1 c1) (min c2 c3)) (min dw c4), hηw,
    lt_min (lt_min (lt_min hd1 hc1) (lt_min hc2 hc3)) (lt_min hdw hc4), ?_⟩
  intro δf hδf hδf0' hδf100 n x v Y hFY hSY hvolY
  have hδf0 : δf ≤ min (min d1 c1) (min c2 c3) := hδf0'.trans (min_le_left _ _)
  have hδfdw : δf ≤ dw := hδf0'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδfc4 : δf ≤ c4 := hδf0'.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Z, hZY, hFam, hSep, hvol, P, hPm, hPu, hPp⟩ :=
    hweak δf hδf hδfdw hδf100 n x v Y hFY hSY hvolY
  have hδfd1 : δf ≤ d1 := hδf0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδfc1 : δf ≤ c1 := hδf0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδfc2 : δf ≤ c2 := hδf0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδfc3 : δf ≤ c3 := hδf0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδf1 : δf ≤ 1 := by linarith
  have hn : 0 < n := hFam.1
  -- the requested coarse scale
  set r := 2 * δf ^ (σ / 64) with hr
  have hq3 : δf ^ (σ / 128) ≤ 1 / 2 := hcut3 δf hδf hδfc3
  have hσ64 : δf ^ (σ / 64) = δf ^ (σ / 128) * δf ^ (σ / 128) := by
    rw [← Real.rpow_add hδf]; ring_nf
  have hr1 : δf ^ (1 - ε1) ≤ r := by
    have : δf ^ (1 - ε1) ≤ δf ^ (σ / 64) :=
      Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by nlinarith)
    have h0 : 0 ≤ δf ^ (σ / 64) := Real.rpow_nonneg hδf.le _
    rw [hr]; linarith
  have hr2 : r ≤ δf ^ ε1 := by
    have h1 : δf ^ (σ / 64) = δf ^ (σ / 64 - ε1) * δf ^ ε1 := by
      rw [← Real.rpow_add hδf]; ring_nf
    have h2 : δf ^ (σ / 64 - ε1) ≤ δf ^ (σ / 128) :=
      Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by linarith)
    have h3 : 0 ≤ δf ^ ε1 := Real.rpow_nonneg hδf.le _
    rw [hr, h1]; nlinarith
  obtain ⟨ρc, hρc1, hρc2, hTSA⟩ := hTS1 δf hδf hδfd1 hδf100 n x v Z hFam hSep hvol r hr1 hr2
  have hr0 : 0 < r := by positivity
  have hρc0 : 0 < ρc := hr0.trans_le hρc1
  have hρcup : ρc ≤ 2 * δf ^ (σ / 128) := by
    calc ρc ≤ δf ^ (-ε1) * r := hρc2
      _ = 2 * δf ^ (σ / 64 - ε1) := by
          rw [hr, show σ / 64 - ε1 = -ε1 + σ / 64 by ring, Real.rpow_add hδf]; ring
      _ ≤ 2 * δf ^ (σ / 128) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by linarith))
            (by norm_num)
  have hq2 : δf ^ (σ / 128) ≤ (1 / 100) / 2 := hcut2 δf hδf hδfc2
  have hρcd : ρc ≤ 1 / 100 := by linarith
  have hρc1' : ρc ≤ 1 := hρcd.trans (by norm_num)
  have hYball : ∀ i, ∀ p ∈ Z i, ‖p‖ ≤ 1 := fun i p hp =>
    (mem_ball_zero_iff.1 (hFam.2.2.1 i (hFam.2.2.2.2.2.1 i hp))).le
  obtain ⟨k, z, w, Yt, Yt'', Vt, s, hFamc, hSepc, hvolc, hsub, hmeas, hinc, hVtm, hVtu, hVtp,
    hs, hslo, hshi, hcube, hnear⟩ := coarse_plane_mapP' hn hδf hρc0 (by linarith) hYball hTSA hPm
      hPu (fun i p hp => (hPp i p hp).trans (by linarith))
  have hρcup' : ρc ≤ δf ^ (σ / 64 - ε) := by
    have hε1' : ε1 ≤ ε / 2 := by
      have : ε1 ≤ ε' / 512 := hε1pre
      linarith only [this, hε'ε, hε]
    have h1 : ρc ≤ 2 * δf ^ (σ / 64 - ε1) := by
      calc ρc ≤ δf ^ (-ε1) * r := hρc2
        _ = 2 * δf ^ (σ / 64 - ε1) := by
            rw [hr, show σ / 64 - ε1 = -ε1 + σ / 64 by ring, Real.rpow_add hδf]; ring
    have h2 : 2 * δf ^ (σ / 64 - ε1) ≤ δf ^ (σ / 64 - ε) := by
      have e : δf ^ (σ / 64 - ε1) = δf ^ (σ / 64 - ε) * δf ^ (ε - ε1) := by
        rw [← Real.rpow_add hδf]; ring_nf
      have h3 : δf ^ (ε - ε1) ≤ 1 / 2 :=
        (Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by linarith)).trans (hcut4 δf hδf hδfc4)
      rw [e]
      have hp : 0 ≤ δf ^ (σ / 64 - ε) := Real.rpow_nonneg hδf.le _
      nlinarith
    exact h1.trans h2
  have hρclow : δf ^ (σ / 64) ≤ ρc := by
    have : δf ^ (σ / 64) ≤ r := by rw [hr]; have := Real.rpow_nonneg hδf.le (σ / 64); linarith
    exact this.trans hρc1
  refine ⟨ρc, hρclow, hρcup', hρcd, k, z, w, Yt'', Vt, s, ?_,
    hSepc.mono_error hρc0 hρc1' (by linarith), ?_, ?_, hVtm, hVtu, hVtp, hs, hslo, hshi,
    hcube⟩
  · -- mass of the refined coarse shadings
    apply hFamc.of_subsets_mass hsub hmeas
    have hfin := hFamc.shading_finite
    have hfin'' : ∀ j, volume (Yt'' j) ≠ ∞ := fun j =>
      ne_top_of_le_ne_top (hfin j) (measure_mono (hsub j))
    have h1 := shadingMass_le_of_incidence hFamc.2.2.2.2.1 hfin hmeas hfin'' hinc
    have h2 := hFamc.mass_lower hρc0
    have hkey : ρc ^ ε ≤ δf ^ (2 * ε1) * ρc ^ ε1 := by
      have e1 : ρc ^ ε = ρc ^ (ε - ε1) * ρc ^ ε1 := by
        rw [← Real.rpow_add hρc0]; ring_nf
      have hε1' : ε1 ≤ ε' / 512 := hε1pre
      have h3 : ρc ^ (ε - ε1) ≤ ρc ^ (ε' / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' (by linarith)
      have h4 : ρc ^ (ε' / 2) ≤ (2 * δf ^ (σ / 128)) ^ (ε' / 2) :=
        Real.rpow_le_rpow hρc0.le hρcup (by positivity)
      have h5 : (2 * δf ^ (σ / 128)) ^ (ε' / 2) = 2 ^ (ε' / 2) * δf ^ (σ * ε' / 256) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδf.le _), ← Real.rpow_mul hδf.le]
        ring_nf
      have h6 : (2 : ℝ) ^ (ε' / 2) ≤ 2 := by
        calc (2 : ℝ) ^ (ε' / 2) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have h7 : δf ^ (σ * ε' / 256) = δf ^ (σ * ε' / 512) * δf ^ (2 * ε1) := by
        rw [← Real.rpow_add hδf, hε1]; ring_nf
      have h8 : δf ^ (σ * ε' / 512) ≤ 1 / 2 := hcut1 δf hδf hδfc1
      have h9 : ρc ^ (ε - ε1) ≤ δf ^ (2 * ε1) := by
        have hp : 0 ≤ δf ^ (2 * ε1) := Real.rpow_nonneg hδf.le _
        calc ρc ^ (ε - ε1) ≤ 2 ^ (ε' / 2) * δf ^ (σ * ε' / 256) := by rw [← h5]; linarith
          _ ≤ 2 * (1 / 2 * δf ^ (2 * ε1)) := by
              rw [h7]; gcongr
          _ = δf ^ (2 * ε1) := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_right h9 (Real.rpow_nonneg hρc0.le _)
    have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    calc ρc ^ ε * (k : ℝ) * ρc ^ 2 ≤ δf ^ (2 * ε1) * ρc ^ ε1 * (k : ℝ) * ρc ^ 2 := by gcongr
      _ = δf ^ (2 * ε1) * (ρc ^ ε1 * (k : ℝ) * ρc ^ 2) := by ring
      _ ≤ δf ^ (2 * ε1) * shadingMass Yt := by
          gcongr
      _ ≤ shadingMass Yt'' := h1
  · exact (measure_mono (iUnion_mono hsub)).trans (hvolc.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' (by linarith))))
  · exact (iUnion_mono hsub).trans (hnear.trans (thickening_subset_of_subset _ (iUnion_mono hZY)))


end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- Plane-grains transfer (the interface of the planned child `wz_extremal_plane_grains_transfer`):
every sufficiently extremal family at `δ` yields an `ε`-extremal family at a coarser scale
`δ' ∈ [δ^c, δ^(c-ε)]` near it, with a unit plane map of precision `δ'` that is `δ'^(-ε)`-Lipschitz
and local grains at every scale. -/
def PlaneGrainsTransfer (σ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ ε : ℝ, 0 < ε → ∃ η d1 : ℝ, 0 < η ∧ 0 < d1 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → Separated η δ n x v →
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
      ∃ δ' : ℝ, δ ^ c ≤ δ' ∧ δ' ≤ δ ^ (c - ε) ∧ δ' ≤ (1 / 100 : ℝ) ∧
        ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
          Family ε δ' m x' v' Y' ∧ Separated ε δ' m x' v' ∧
          volume (⋃ j, Y' j) ≤ ENNReal.ofReal (δ' ^ (σ - ε)) ∧
          (⋃ j, Y' j) ⊆ thickening (10 * δ') (⋃ i, Y i) ∧
          ∃ V : Space → Space, (∀ p, p ∈ (⋃ j, Y' j) → ‖V p‖ = 1) ∧
            (∀ j p, p ∈ Y' j → |inner ℝ (v' j) (V p)| ≤ δ') ∧
            (∀ p q, p ∈ (⋃ j, Y' j) → q ∈ (⋃ j, Y' j) → dist (V p) (V q) ≤ δ' ^ (-ε) * dist p q) ∧
            (∀ ρ : ℝ, δ' ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ j, Y' j) →
              Covering ρ (1 - σ) (δ' ^ (-ε))
                ((fun q : Space => inner ℝ (V p) q) '' ((⋃ j, Y' j) ∩ ball p (Real.sqrt ρ))))

/-- **The plane-grains transfer** (sticky Lemmas 4.3-4.8 and 4.12 for a given family). -/
theorem plane_grains_transfer {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (habove : ∀ t : ℝ, σ < t → ¬ Examples t) : PlaneGrainsTransfer σ := by
  have hTS : TwoScaleTheoremP σ := (two_scale_theorem habove).toP
  have hσ2 : σ ≤ 2 := by linarith
  refine ⟨σ / 64, by positivity, by linarith, ?_⟩
  intro ε hε
  set ε0 := min ε (σ / 256) with hε0
  have hε00 : 0 < ε0 := lt_min hε (by positivity)
  have hε0ε : ε0 ≤ ε := min_le_left _ _
  have hε0σ : ε0 ≤ σ / 256 := min_le_right _ _
  obtain ⟨η5, d5, hη5, hη5ε, hd5, hLG⟩ := local_grains_refine hσ hσ1 hTS hε00
  obtain ⟨η4, d4, hη4, hη4η5, hd4, hLR⟩ := lipschitz_refine hσ hσ2 hTS η5 hη5
  set ε3 := min η4 ε0 with hε3
  have hε30 : 0 < ε3 := lt_min hη4 hε00
  have hε3η4 : ε3 ≤ η4 := min_le_left _ _
  have hε3ε0 : ε3 ≤ ε0 := min_le_right _ _
  obtain ⟨η3, d3, hη3, hd3, hCP⟩ := cube_plane_refine hσ hσ2 habove hTS ε3 hε30
  obtain ⟨c1, hc1, hcut⟩ := exists_power_cutoff (a := σ / 64 - ε3) (by linarith)
    (lt_min hd4 hd5 : (0:ℝ) < min d4 d5)
  refine ⟨η3, min d3 c1, hη3, lt_min hd3 hc1, ?_⟩
  intro δ hδ hδd hδ100 n x v Y hF hS hV
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨ρc, hρc1, hρc2, hρc100, k, z, w, Yt, Vt, s, hFt, hSt, hvolt, hnear, hVtm, hVtu, hVtp,
    hs, hslo, hshi, hcube⟩ := hCP δ hδ (hδd.trans (min_le_left _ _)) hδ100 n x v Y hF hS hV
  have hρc0 : 0 < ρc := (Real.rpow_pos_of_pos hδ _).trans_le hρc1
  have hρc1' : ρc ≤ 1 := by linarith
  have hρcsmall : ρc ≤ min d4 d5 := hρc2.trans (hcut δ hδ (hδd.trans (min_le_right _ _)))
  -- Lipschitz refinement (Lemma 4.7)
  obtain ⟨Y4, hY4, hF4, hLip4⟩ := hLR ρc hρc0 (hρcsmall.trans (min_le_left _ _)) hρc100 k z w Yt
    Vt s (hFt.mono_error hρc0 hρc1' hε3η4) (hSt.mono_error hρc0 hρc1' hε3η4)
    (hvolt.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1'
      (by linarith)))) hVtm hVtu hVtp hs hslo hshi hcube
  have hsub4 : (⋃ j, Y4 j) ⊆ ⋃ j, Yt j := iUnion_mono hY4
  -- local grains (Lemma 4.12)
  obtain ⟨Y5, hY5, hF5, hcov5⟩ := hLG ρc hρc0 (hρcsmall.trans (min_le_right _ _)) hρc100 k z w
    Y4 Vt hF4 (hSt.mono_error hρc0 hρc1' (hε3η4.trans hη4η5))
    ((measure_mono hsub4).trans (hvolt.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' (by linarith)))))
    (fun p hp => hVtu p (hsub4 hp)) (fun j p hp => hVtp j p (hY4 j hp)) hLip4
  have hsub5 : (⋃ j, Y5 j) ⊆ ⋃ j, Y4 j := iUnion_mono hY5
  have hpow : ρc ^ (-ε0) ≤ ρc ^ (-ε) := Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' (by linarith)
  refine ⟨ρc, hρc1, hρc2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)), hρc100,
    k, z, w, Y5, hF5.mono_error hρc0 hρc1' hε0ε,
    hSt.mono_error hρc0 hρc1' (hε3ε0.trans hε0ε), ?_, ?_, Vt, ?_, ?_, ?_, ?_⟩
  · exact (measure_mono (hsub5.trans hsub4)).trans (hvolt.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' (by linarith))))
  · exact (hsub5.trans hsub4).trans (hnear.trans (thickening_mono (by linarith) _))
  · intro p hp; exact hVtu p (hsub4 (hsub5 hp))
  · intro j p hp; exact hVtp j p (hY4 j (hY5 j hp))
  · intro p q hp hq
    refine (hLip4 p (hsub5 hp) q (hsub5 hq)).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    exact Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' (by linarith)
  · intro ρ hρ hρ1 p hp
    exact Covering.mono_constant (hcov5 ρ hρ hρ1 p hp) (hρc0.trans_le hρ) hpow

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
