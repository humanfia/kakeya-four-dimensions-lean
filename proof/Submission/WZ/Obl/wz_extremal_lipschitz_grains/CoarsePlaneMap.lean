-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.CoarsePlaneMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TwoScaleUse
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.StrongPlaneMap

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

theorem incidence_eq_fineMult {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    incidence Y p = (fineMult Y p : ℝ) := by
  rw [incidence_eq_card_through, fineMult_eq_card_through]

/-- **Strong plane map for the coarse family of a two-scale decomposition** (sticky Lemma 4.4).
A fine plane map of precision `ρc / 2` yields refined coarse shadings, still unions of grid
cubes, with a plane map of precision `ρc` constant on the grid cubes, keeping the fraction
`δ^(2ε)` of the coarse incidence at every point. -/
theorem coarse_plane_map {σ ε δ ρc : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hn : 0 < n) (hδ : 0 < δ) (hρc : 0 < ρc)
    (hTS : TwoScaleAt σ ε δ ρc n x v Y) {V : Space → Space} (hVm : Measurable V)
    (hVu : ∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1)
    (hVp : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ ρc / 2) :
    ∃ (k : ℕ) (z w : Fin k → Space) (Yt Yt'' : Fin k → Set Space) (Vt : Space → Space) (s : ℝ),
      Family ε ρc k z w Yt ∧ Separated ε ρc k z w ∧
      volume (⋃ j, Yt j) ≤ ENNReal.ofReal (ρc ^ (σ - ε)) ∧
      (∀ j, Yt'' j ⊆ Yt j) ∧ (∀ j, MeasurableSet (Yt'' j)) ∧
      (∀ q, δ ^ (2 * ε) * incidence Yt q ≤ incidence Yt'' q) ∧ Measurable Vt ∧
      (∀ q ∈ ⋃ j, Yt'' j, ‖Vt q‖ = 1) ∧
      (∀ j q, q ∈ Yt'' j → |inner ℝ (w j) (Vt q)| ≤ ρc) ∧
      0 < s ∧ (∀ q q', cubeIndex s q = cubeIndex s q' → Vt q = Vt q') := by
  obtain ⟨Y', k, z, w, Yt, a, s, M, hY'Y, hY'm, hY'mass, hFam, hSep, hvol, hcontr, hdir, hs, hYt,
    hfine, hfib, hcoarse, -, hR1, -⟩ := hTS
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
    have h1 : (δ / ρc) ^ (2 - σ - ε) * ρc ^ (2 - σ - ε) = δ ^ (2 - σ - ε) := by
      rw [Real.div_rpow hδ.le hρc.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hρc _).ne']
    have h2 : δ ^ (2 - σ + ε) = δ ^ (2 - σ - ε) * δ ^ (2 * ε) := by
      rw [← Real.rpow_add hδ]; ring_nf
    have hd : 0 < δ ^ (2 - σ - ε) := Real.rpow_pos_of_pos hδ _
    have hBC : B * Cc = δ ^ (2 - σ - ε) * (n : ℝ) := by
      rw [hBdef, hCdef]
      calc (δ / ρc) ^ (2 - σ - ε) * ((n : ℝ) / (k : ℝ)) * (ρc ^ (2 - σ - ε) * (k : ℝ))
          = ((δ / ρc) ^ (2 - σ - ε) * ρc ^ (2 - σ - ε)) * ((n : ℝ) / (k : ℝ) * k) := by ring
        _ = _ := by rw [h1, div_mul_cancel₀ _ hkR.ne']
    rw [hBC, hAdef, h2]
    field_simp
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
    hcube⟩
  intro q
  rw [← hABC]
  exact hinc q

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
