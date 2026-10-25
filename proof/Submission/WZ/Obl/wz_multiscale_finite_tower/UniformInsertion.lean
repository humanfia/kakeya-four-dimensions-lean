-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.UniformInsertion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyAlternative
import Submission.WZ.Obl.wz_multiscale_finite_tower.CertificateMonotonicity

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (coverScale contraction)

theorem uniform_hierarchy_insertion {σ ω : ℝ} (hE : Endpoint σ ω) (hOne : OneScale σ ω)
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
    hOne.physical_on_large_gap hσ hω hω1 hζ hg'
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

end WangZahlLot.Obl.wz_multiscale_finite_tower
