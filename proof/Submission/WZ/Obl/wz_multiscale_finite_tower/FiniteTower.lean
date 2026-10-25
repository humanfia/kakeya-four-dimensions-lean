-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.FiniteTower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyDepth
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyBase
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedFinal
import Submission.WZ.Obl.wz_multiscale_finite_tower.Iteration

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

lemma Admissible.aligned_retained_cardinality {d η θ ζ M L K' L' h : ℝ} {u : Space}
    {n m : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    {x' v' : Fin m → Space} {Z : Fin m → Set Space}
    (hA : Admissible d η M L n x v Y)
    (F : AlignedFamily d (d ^ θ) K' L' u h m x' v' Z)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hret : ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    (1 / 56 : ℝ) * d ^ (η + ζ) * n ≤ m := by
  have hh := ((mul_le_mul' le_rfl hA.2.2.2.1).trans hret).trans (F.mass_upper hd.le hd1)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le ζ)] at hh
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 56 * (m : ℝ) * d ^ 2)).mp hh
  have he : d ^ ζ * (d ^ η * n * d ^ 2) = (d ^ (η + ζ) * n) * d ^ 2 := by
    rw [Real.rpow_add hd]
    ring
  rw [he] at hr
  have hc := (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp hr
  linarith

/-- The buffered hierarchy induction gives the required finite local tower. -/
theorem finite_tower_all_depths {σ ω : ℝ} (hE : Endpoint σ ω) (hOne : OneScale σ ω)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (q : ℕ) : DepthProperty σ ω q := by
  intro ε D hε hD
  apply hE.attach_cutoff hσ1 hD
  let β : ℝ := (1 - ω / 100) ^ q / 2
  have hb : 0 < 1 - ω / 100 := by linarith
  have hβ : 0 < β := by dsimp [β]; positivity
  have hmesh : depthMesh ω β q ≤ 2 * (1 - ω / 100) ^ q := by
    dsimp [depthMesh, β]
    have hp := pow_pos hb q
    linarith
  obtain ⟨dF, hdF, _, HF⟩ := exists_scale_cutoff (1 / 10000000000000) (ε / 4) 1
    (by norm_num) (by positivity) (by norm_num)
  obtain ⟨αH, κH, ηH, dH, hαH, hκH, hηH, hdH, hdHdF, _, HH⟩ :=
    refine_hierarchy_depth hE hOne hσ hσ1 hω hω1 hβ q (by linarith : 0 < ε / 4) hdF
  let δ : ℝ := min ηH (min (ε / 8) (αH / 8))
  have hδ : 0 < δ := lt_min hηH (lt_min (by positivity) (by positivity))
  have hδη : δ ≤ ηH := min_le_left _ _
  have hδε : δ ≤ ε / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδα : δ ≤ αH / 8 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ηA, dA, hηA, hdA, hdAdH, hdAsmall, HA⟩ := prepare_aligned_family hδ hdH
  let η : ℝ := min ηA δ
  have hη : 0 < η := lt_min hηA hδ
  have hηδ : η ≤ δ := min_le_right _ _
  have hκ : 0 < κH * (1 / 56 : ℝ) ^ (1 - σ) := by positivity
  refine ⟨αH / 2, by positivity, κH * (1 / 56 : ℝ) ^ (1 - σ), hκ,
    η, hη, dA, hdA, ?_⟩
  intro d hd hd100 hdd n x v Y hA
  have hdsmall : d ≤ 1 / 100000 := hdd.trans hdAsmall
  have hd1 : d < 1 := by linarith
  obtain ⟨m, X, V, Z, u, h, F, _, hZY, hmass⟩ :=
    HA d hd hdd n x v Y (hA.mono_error hd hd1.le (min_le_left _ _))
  let C : HierarchyCertificate d δ (1 + β) (1 / 2) 1 :=
    initialHierarchy hd (by linarith) hd1 hδ.le (by linarith) (by norm_num) F
  rcases HH d δ hd (hdd.trans hdAdH) hδ.le hδη C with hV | hRet
  · left
    have hcard := hA.aligned_retained_cardinality F hd hd1.le hmass
    have hV' := VolumeBound.of_refinement hd (by norm_num : (0 : ℝ) < 1 / 56)
      hκH.le hA.1 (by linarith : σ ≤ 1) hcard hZY hV
    apply hV'.mono hd hd1.le hκ.le le_rfl
    have hfac : (η + δ) * (1 - σ) ≤ η + δ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (by linarith : 1 - σ ≤ 1)
        (by linarith : 0 ≤ η + δ)
    linarith
  · right
    obtain ⟨J, Cfin, hJ, _, hsub, hret⟩ := hRet
    have hsmall : 10000000000000 * d ^ (ε / 2 - ε / 4) ≤ 1 := by
      have hh := HF d hd (hdd.trans (hdAdH.trans hdHdF))
      rw [show ε / 2 - ε / 4 = ε / 4 by ring]
      linarith
    have HT := Cfin.control.tower.mono hd hd1.le le_rfl hmesh hJ
    have Hret := retained_tower_of_aligned_family hd hdsmall
      (by linarith : ε / 4 ≤ ε / 2) hsmall Cfin.family HT
    have Hret' := Hret.precompose hd hd1.le (by positivity : 0 ≤ ε / 4) hsub hret
    have Hret'' := Hret'.precompose hd hd1.le hδ.le hZY hmass
    exact Hret''.mono hd hd1.le (by linarith) le_rfl le_rfl

end WangZahlLot.Obl.wz_multiscale_finite_tower
