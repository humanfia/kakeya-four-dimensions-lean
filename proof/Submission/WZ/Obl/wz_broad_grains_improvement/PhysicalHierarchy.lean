-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.PhysicalHierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedPhysicalAlternative
import Submission.WZ.Obl.wz_multiscale_finite_tower.FiniteTower

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_multiscale_finite_tower
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (coverScale contraction)

set_option maxHeartbeats 1600000

/- The following generalizes the implication chain in the accepted o034 files
UniformInsertion, RefineBadGaps, HierarchyRound, HierarchyDepth and FiniteTower.
Only a uniform physical-step hypothesis is needed, instead of the stronger
all-family exact-unit OneScale hypothesis. The accepted geometric insertion,
certificate, mass and counting lemmas are imported and used directly. -/

theorem uniform_hierarchy_insertion_of_physical {σ ω : ℝ} (hE : Endpoint σ ω) (hStep : PhysicalStep σ ω)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (B : ℕ) {g g' gap ε D : ℝ} (hg' : 0 < g') (hgg : g' ≤ g)
    (hmesh : (1 - ω / 100) * g < g') (hgap : 0 < gap) (hgap' : gap < ω / 100 * g')
    (hε : 0 < ε) (hD : 0 < D) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ D ∧
      ∀ d θ : ℝ, ∀ J k : ℕ, 0 < d → d ≤ d₀ → 0 ≤ θ → θ ≤ η → J ≤ B → k < J →
      ∀ C : HierarchyCertificate d θ g gap J,
      (C.tree.layer (k + 1)).radius / (C.tree.layer k).radius ≤ d ^ g' →
      VolumeBound σ ω κ α d (C.tree.layer J).card C.shading ∨
      ∃ r : ℝ, 0 < r ∧ d ^ g' * (C.tree.layer k).radius ≤ r ∧
        d ^ g' * r ≤ (C.tree.layer (k + 1)).radius ∧
      ∃ C' : HierarchyCertificate d ε g gap (J + 1),
        (∀ j, (C'.tree.layer j).radius =
          if j ≤ k then (C.tree.layer j).radius else if j = k + 1 then r else (C.tree.layer (j - 1)).radius) ∧
        (C'.tree.layer (J + 1)).card ≤ (C.tree.layer J).card ∧
        (⋃ i, C'.shading i) ⊆ (⋃ i, C.shading i) ∧
        ENNReal.ofReal (d ^ ε) * (∑ i, volume (C.shading i)) ≤ ∑ i, volume (C'.shading i) := by
  let ζ : ℝ := ε / 200
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  obtain ⟨αP, κP, ηP, cP, hαP, hκP, hηP, hηP1, hcP, hcP1, HP⟩ :=
    hStep ζ g' hζ hg'
  let loss : ℝ := g' * αP / (100 * ((B : ℝ) + 1))
  have hloss : 0 < loss := by dsimp [loss]; positivity
  obtain ⟨aE, ηE, dE, haE, hηE, hηE1, hdE, hdED, HE⟩ :=
    hE.all_physical_scales hσ hσ1 hω.le hloss hD
  let χ : ℝ := min ζ (min ηP (min ηE (min 1 loss)))
  have hχ : 0 < χ := lt_min hζ (lt_min hηP (lt_min hηE (lt_min zero_lt_one hloss)))
  have hχζ : χ ≤ ζ := min_le_left _ _
  have hχηP : χ ≤ ηP := (min_le_right _ _).trans (min_le_left _ _)
  have hχηE : χ ≤ ηE := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hχ1 : χ ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hχloss : χ ≤ loss := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcover : 1 ≤ coverScale := by norm_num [coverScale, contraction]
  obtain ⟨q, hq, dB, hdB, hdBdE, HB⟩ := exists_insertion_budget B hζ hcover hmesh hgap' hdE
  obtain ⟨dP, hdP, hdPdB, hcutP⟩ := exists_scale_cutoff cP g' dB hcP hg' hdB
  obtain ⟨dG, hdG, hdGdP, hcutG⟩ := exists_scale_cutoff (1 / 64) gap dP (by norm_num) hgap hdP
  obtain ⟨ηA, d₀, hηA, hd₀, hd₀dG, hd₀small, HA⟩ := prepare_hierarchy_analysis B hχ hdG
  let c : ℝ := min 1 (min aE κP)
  have hc : 0 < c := lt_min zero_lt_one (lt_min haE hκP)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hca : c ≤ aE := (min_le_right _ _).trans (min_le_left _ _)
  have hck : c ≤ κP := (min_le_right _ _).trans (min_le_right _ _)
  have hκ : 0 < (c / 256) ^ B / 56 := by positivity
  have hgainbudget : 2 * χ + (B : ℝ) * (χ / 8 + 2 * χ + loss) ≤ g' * αP / 2 := by
    have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have hχB := mul_le_mul_of_nonneg_left hχloss hb
    have he : 100 * ((B : ℝ) + 1) * loss = g' * αP := by
      dsimp [loss]
      field_simp
    nlinarith only [hχB, hχloss, hloss, hχ, hb, he]
  refine ⟨g' * αP / 2, (c / 256) ^ B / 56, min ηA (χ / 2), d₀,
    by positivity, hκ, lt_min hηA (by positivity), hd₀,
    hd₀dG.trans (hdGdP.trans (hdPdB.trans (hdBdE.trans hdED))), ?_⟩
  intro d θ J k hd hdd hθ hθη hJB hk C hlarge
  have hd1 : d < 1 := by have hh := hdd.trans hd₀small; linarith
  have hddG : d ≤ dG := hdd.trans hd₀dG
  have hddP : d ≤ dP := hddG.trans hdGdP
  have hddB : d ≤ dB := hddP.trans hdPdB
  have hddE : d ≤ dE := hddB.trans hdBdE
  have hθA : θ ≤ ηA := hθη.trans (min_le_left _ _)
  have hθχ : θ ≤ χ / 2 := hθη.trans (min_le_right _ _)
  obtain ⟨C₁, hrad₁, hcard₁, hunion₁, hmass₁, ⟨A⟩⟩ :=
    HA d θ g gap J hd hdd hθA hJB (hcutG d hd hddG) C
  have hlarge₁ : (C₁.tree.layer (k + 1)).radius / (C₁.tree.layer k).radius ≤ d ^ g' := by
    simpa only [hrad₁] using hlarge
  have budget := HB d hd hddB
  have hn := budget.card hd hχ1 C₁
  have hnret : (1 / 56 : ℝ) * d ^ χ * (C.tree.layer J).card ≤ (C₁.tree.layer J).card := by
    have hh := C.family.retained_cardinality C₁.family hd hd1.le hmass₁
    apply le_trans _ hh
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by linarith : θ + χ / 4 ≤ χ)) (by norm_num))
      (Nat.cast_nonneg _)
  rcases A.cover_alternative C₁.control HP hd hd1 hζ hχηP hk hlarge₁ (hcutP d hd hddP)
    hq hn budget.balance with hV | ⟨Dcover⟩
  · left
    have hbase (j) (hj : j < J) : FibreVolumeBound A σ ω j (c * d ^ loss) :=
      FibreVolumeBound.mono C₁.control hj (mul_le_mul_of_nonneg_right hca (Real.rpow_nonneg hd.le _))
        (A.endpoint_fibre C₁.control hd hd1.le hddE hχηE HE hj)
    have hcmul : c * d ^ loss ≤ κP := by
      calc
        _ ≤ c * 1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one hd.le hd1.le hloss.le) hc.le
        _ ≤ κP := by simpa only [mul_one] using hck
    have hV' := FibreVolumeBound.mono C₁.control hk
      (mul_le_mul_of_nonneg_right hcmul (Real.rpow_nonneg
        (div_pos (C₁.control.positive (k + 1) (by omega)) (C₁.control.positive k hk.le)).le _)) hV
    have hh := A.gain_volume_bound C₁.control hd hd1.le hχ.le (by positivity : 0 ≤ χ / 8) hloss.le
      hc hc1 hαP.le hσ (by linarith : σ ≤ 1) (C.tree.layer J).card_pos hnret hJB hk hlarge₁ hbase hV'
    exact hh.mono hd hd1.le hκ.le le_rfl (by linarith)
  · right
    obtain ⟨r, hr, hlo₁, hlo₂, C₂, hrad₂, hcard₂, hunion₂, hmass₂⟩ :=
      insert_indexed_covers C₁ hk (Classical.choice Dcover) hd hd1 hχ.le hχζ hζ
        (by dsimp [ζ]; linarith : 100 * ζ ≤ ε / 2) hgg le_rfl hgap.le
        (by linarith : 0 ≤ ω / 100) (by linarith : ω / 100 ≤ 1) hcover hlarge₁ hq hn
        (budget.span hd) (budget.length hd.le hq hJB) budget.coefficient budget.span_constant budget.mesh budget.upper
    let C' := C₂.mono_error hd hd1.le (show ε / 2 ≤ ε by linarith)
    refine ⟨r, hr, by simpa only [hrad₁] using hlo₁, by simpa only [hrad₁] using hlo₂,
      C', ?_, hcard₂.trans hcard₁, hunion₂.trans hunion₁, ?_⟩
    · intro j
      change (C₂.tree.layer j).radius = _
      simpa only [hrad₁] using hrad₂ j
    · exact mass_retention_comp hd hd1.le (by dsimp [ζ] at hχζ; linarith : χ / 4 + ε / 2 ≤ ε) hmass₁ hmass₂

theorem refine_bad_gaps_of_physical {σ ω : ℝ} (hE : Endpoint σ ω) (hStep : PhysicalStep σ ω)
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
      uniform_hierarchy_insertion_of_physical hE hStep hσ hσ1 hω hω1 B hg' hgg hmesh hgap hgap' hδ hdI
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

theorem refine_hierarchy_round_of_physical {σ ω : ℝ} (hE : Endpoint σ ω) (hStep : PhysicalStep σ ω)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (B : ℕ) {g g' gap gap' ε D : ℝ} (hg' : 0 < g') (hgg : g' ≤ g)
    (hmesh : (1 - ω / 100) * g < g') (hgap : gap' ≤ gap)
    (hgap' : 0 < gap') (hgap'' : gap' < ω / 100 * g') (hε : 0 < ε) (hD : 0 < D) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ D ∧ d₀ ≤ 1 / 100000 ∧
      ∀ d θ : ℝ, ∀ J : ℕ, 0 < d → d ≤ d₀ → 0 ≤ θ → θ ≤ η → J ≤ B →
      ∀ C : HierarchyCertificate d θ g gap J,
      VolumeBound σ ω κ α d (C.tree.layer J).card C.shading ∨
        RetainedHierarchy d ε g' gap' (2 * B) (C.tree.layer J).card C.shading := by
  obtain ⟨α, κ, η, d₀, hα, hκ, hη, hd₀, hd₀D, hd₀small, HI⟩ :=
    refine_bad_gaps_of_physical hE hStep hσ hσ1 hω hω1 (2 * B) B hg' hgg hmesh hgap' hgap'' hε hD
  refine ⟨α, κ, η, d₀, hα, hκ, hη, hd₀, hd₀D, hd₀small, ?_⟩
  intro d θ J hd hdd hθ hθη hJB C
  have hd1 : d ≤ 1 := by have hh := hdd.trans hd₀small; linarith
  let C' := C.weaken_gap hd hd1 hgap
  have hbad := badGaps_card_le d g' J (fun j => (C'.tree.layer j).radius)
  exact HI d θ J hd hdd hθ hθη C' (hbad.trans hJB) (by omega)

theorem refine_hierarchy_depth_of_physical {σ ω : ℝ} (hE : Endpoint σ ω) (hStep : PhysicalStep σ ω)
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
      refine_hierarchy_round_of_physical hE hStep hσ hσ1 hω hω1 (2 ^ q)
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

theorem finite_tower_all_depths_of_physical {σ ω : ℝ} (hE : Endpoint σ ω) (hStep : PhysicalStep σ ω)
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
    refine_hierarchy_depth_of_physical hE hStep hσ hσ1 hω hω1 hβ q (by linarith : 0 < ε / 4) hdF
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

end WangZahlLot.Obl.wz_broad_grains_improvement
