-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.RefineBadGaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.RetainedHierarchy

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

theorem refine_bad_gaps {σ ω : ℝ} (hE : Endpoint σ ω) (hOne : OneScale σ ω)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (B n : ℕ) {g g' gap ε D : ℝ} (hg' : 0 < g') (hgg : g' ≤ g)
    (hmesh : (1 - ω / 100) * g < g') (hgap : 0 < gap) (hgap' : gap < ω / 100 * g')
    (hε : 0 < ε) (hD : 0 < D) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ D ∧ d₀ ≤ 1 / 100000 ∧
      ∀ d θ : ℝ, ∀ J : ℕ, 0 < d → d ≤ d₀ → 0 ≤ θ → θ ≤ η →
      ∀ C : HierarchyCertificate d θ g gap J,
      (badGaps d g' J (fun j => (C.tree.layer j).radius)).card ≤ n →
      J + (badGaps d g' J (fun j => (C.tree.layer j).radius)).card ≤ B →
      VolumeBound σ ω κ α d (C.tree.layer J).card C.shading ∨
        RetainedHierarchy d ε g' gap B (C.tree.layer J).card C.shading := by
  induction n generalizing ε D with
  | zero =>
    refine ⟨1, 1, ε, min D (1 / 100000), by norm_num, by norm_num, hε,
      lt_min hD (by norm_num), min_le_left _ _, min_le_right _ _, ?_⟩
    intro d θ J hd hdd hθ hθη C hn hB
    have hd1 : d ≤ 1 := by have hh := hdd.trans (min_le_right _ _); linarith
    have hzero : (badGaps d g' J (fun j => (C.tree.layer j).radius)).card = 0 := by omega
    exact Or.inr (RetainedHierarchy.of_no_bad_gaps C hd hd1 hε.le hθη (by omega) hzero)
  | succ n ih =>
    obtain ⟨αI, κI, ηI, dI, hαI, hκI, hηI, hdI, hdID, hdIsmall, HI⟩ := ih (by linarith : 0 < ε / 2) hD
    let δ : ℝ := min (ε / 4) (min ηI (αI / 8))
    have hδ : 0 < δ := lt_min (by positivity) (lt_min hηI (by positivity))
    have hδε : δ ≤ ε / 4 := min_le_left _ _
    have hδη : δ ≤ ηI := (min_le_right _ _).trans (min_le_left _ _)
    have hδα : δ ≤ αI / 8 := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨αS, κS, ηS, dS, hαS, hκS, hηS, hdS, hdSdI, HS⟩ :=
      uniform_hierarchy_insertion hE hOne hσ hσ1 hω hω1 B hg' hgg hmesh hgap hgap' hδ hdI
    have hκret : 0 < κI * (1 / 56 : ℝ) ^ (1 - σ) := by positivity
    let α := min αS (αI / 2)
    let κ := min κS (κI * (1 / 56 : ℝ) ^ (1 - σ))
    have hκ : 0 < κ := lt_min hκS hκret
    refine ⟨α, κ, min ηS δ, dS, lt_min hαS (by positivity), hκ,
      lt_min hηS hδ, hdS, hdSdI.trans hdID, hdSdI.trans hdIsmall, ?_⟩
    intro d θ J hd hdd hθ hθη C hn hB
    have hd1 : d ≤ 1 := by have hh := hdd.trans (hdSdI.trans hdIsmall); linarith
    have hθηS : θ ≤ ηS := hθη.trans (min_le_left _ _)
    have hθδ : θ ≤ δ := hθη.trans (min_le_right _ _)
    by_cases hzero : (badGaps d g' J (fun j => (C.tree.layer j).radius)).card = 0
    · exact Or.inr (RetainedHierarchy.of_no_bad_gaps C hd hd1 hε.le (by linarith) (by omega) hzero)
    have hnonempty : (badGaps d g' J (fun j => (C.tree.layer j).radius)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨k, hkbad⟩ := hnonempty
    obtain ⟨hk, hbad⟩ := mem_badGaps.mp hkbad
    have hlarge : (C.tree.layer (k + 1)).radius / (C.tree.layer k).radius ≤ d ^ g' :=
      (div_le_iff₀ (C.control.positive k hk.le)).mpr hbad.le
    rcases HS d θ J k hd hdd hθ hθηS (by omega) hk C hlarge with hV | hIns
    · exact Or.inl (hV.mono hd hd1 hκ.le (min_le_left _ _) (min_le_left _ _))
    obtain ⟨r, hr, hlo₁, hlo₂, C₁, hrad, hcard, hunion, hmass⟩ := hIns
    have hradfun : (fun j => (C₁.tree.layer j).radius) =
        insertRadii k r (fun j => (C.tree.layer j).radius) := funext hrad
    have hbad' : (badGaps d g' (J + 1) (fun j => (C₁.tree.layer j).radius)).card + 1 =
        (badGaps d g' J (fun j => (C.tree.layer j).radius)).card := by
      rw [hradfun]
      exact badGaps_insert hk hbad hlo₁ hlo₂
    rcases HI d δ (J + 1) hd (hdd.trans hdSdI) hδ.le hδη C₁ (by omega) (by omega) with hV | hRet
    · left
      have hV' := VolumeBound.of_certificate_refinement C C₁ hd hd1 hκI.le (by linarith : σ ≤ 1) hunion hmass hV
      apply hV'.mono hd hd1 hκ.le (min_le_right _ _)
      have hfac : (θ + δ) * (1 - σ) ≤ θ + δ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (by linarith : 1 - σ ≤ 1)
          (by linarith : 0 ≤ θ + δ)
      have hα : α ≤ αI / 2 := min_le_right _ _
      linarith
    · exact Or.inr (hRet.precompose hd hd1 (by linarith : ε / 2 ≤ ε)
        (by linarith : δ + ε / 2 ≤ ε) hcard hunion hmass)

end WangZahlLot.Obl.wz_multiscale_finite_tower
