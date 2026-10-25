-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyDepth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyRound

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

theorem refine_hierarchy_depth {σ ω : ℝ} (hE : Endpoint σ ω) (hOne : OneScale σ ω)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    {β : ℝ} (hβ : 0 < β) (q : ℕ) {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ D ∧ d₀ ≤ 1 / 100000 ∧
      ∀ d θ : ℝ, 0 < d → d ≤ d₀ → 0 ≤ θ → θ ≤ η →
      ∀ C : HierarchyCertificate d θ (1 + β) (1 / 2) 1,
      VolumeBound σ ω κ α d (C.tree.layer 1).card C.shading ∨
        RetainedHierarchy d ε (depthMesh ω β q) (depthGap ω β q) (2 ^ q)
          (C.tree.layer 1).card C.shading := by
  induction q generalizing ε D with
  | zero =>
    refine ⟨1, 1, ε, min D (1 / 100000), by norm_num, by norm_num, hε,
      lt_min hD (by norm_num), min_le_left _ _, min_le_right _ _, ?_⟩
    intro d θ hd hdd hθ hθη C
    have hd1 : d ≤ 1 := by have hh := hdd.trans (min_le_right _ _); linarith
    right
    simp only [depthMesh, pow_zero, depthGap]
    exact ⟨1, C.mono_error hd hd1 hθη, le_rfl, le_rfl, Subset.rfl,
      mass_retention_self C.shading hd.le hd1 hε.le⟩
  | succ q ih =>
    obtain ⟨αR, κR, ηR, dR, hαR, hκR, hηR, hdR, hdRD, hdRsmall, HR⟩ :=
      refine_hierarchy_round hE hOne hσ hσ1 hω hω1 (2 ^ q)
        (depthMesh_pos hω1 hβ (q + 1)) (depthMesh_succ_le hω.le hω1 q)
        (depthMesh_slack hω hβ q) (depthGap_succ_le ω β q)
        (depthGap_pos hω hω1 hβ (q + 1)) (depthGap_succ_lt hω hω1 hβ q)
        (by linarith : 0 < ε / 2) hD
    let δ : ℝ := min (ε / 4) (min ηR (αR / 8))
    have hδ : 0 < δ := lt_min (by positivity) (lt_min hηR (by positivity))
    have hδε : δ ≤ ε / 4 := min_le_left _ _
    have hδη : δ ≤ ηR := (min_le_right _ _).trans (min_le_left _ _)
    have hδα : δ ≤ αR / 8 := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨αI, κI, ηI, dI, hαI, hκI, hηI, hdI, hdIdR, hdIsmall, HI⟩ := ih hδ hdR
    have hκret : 0 < κR * (1 / 56 : ℝ) ^ (1 - σ) := by positivity
    let α := min αI (αR / 2)
    let κ := min κI (κR * (1 / 56 : ℝ) ^ (1 - σ))
    have hκ : 0 < κ := lt_min hκI hκret
    refine ⟨α, κ, min ηI δ, dI, lt_min hαI (by positivity), hκ,
      lt_min hηI hδ, hdI, hdIdR.trans hdRD, hdIsmall, ?_⟩
    intro d θ hd hdd hθ hθη C
    have hd1 : d ≤ 1 := by have hh := hdd.trans hdIsmall; linarith
    have hθηI : θ ≤ ηI := hθη.trans (min_le_left _ _)
    have hθδ : θ ≤ δ := hθη.trans (min_le_right _ _)
    rcases HI d θ hd hdd hθ hθηI C with hV | hRet
    · exact Or.inl (hV.mono hd hd1 hκ.le (min_le_left _ _) (min_le_left _ _))
    obtain ⟨J, C₁, hJ, hcard, hunion, hmass⟩ := hRet
    rcases HR d δ J hd (hdd.trans hdIdR) hδ.le hδη hJ C₁ with hV | hRet
    · left
      have hV' := VolumeBound.of_certificate_refinement C C₁ hd hd1 hκR.le
        (by linarith : σ ≤ 1) hunion hmass hV
      apply hV'.mono hd hd1 hκ.le (min_le_right _ _)
      have hfac : (θ + δ) * (1 - σ) ≤ θ + δ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (by linarith : 1 - σ ≤ 1)
          (by linarith : 0 ≤ θ + δ)
      have hα : α ≤ αR / 2 := min_le_right _ _
      linarith
    · right
      have hh := hRet.precompose hd hd1 (by linarith : ε / 2 ≤ ε)
        (by linarith : δ + ε / 2 ≤ ε) hcard hunion hmass
      simpa only [pow_succ, Nat.mul_comm] using hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
