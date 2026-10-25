import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualPrune
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualMenus

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

private theorem block_zt_mem {α : Type} [MeasurableSpace α] (cfg : Data α) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) {t : ℝ}
    (ht : t ∈ Data.I (cfg.T k s) (cfg.j k s i)) :
    (blockFrame cfg k s i L).zt t ∈ Icc (0 : ℝ) 1 := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ cfg.T k s := by positivity
  have hq : 0 < ((2 : ℝ) ^ cfg.T k s)⁻¹ := by positivity
  have hend : (((cfg.j k s i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ cfg.T k s =
      ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s + ((2 : ℝ) ^ cfg.T k s)⁻¹ := by
    field_simp
  change (t - ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s) /
    ((2 : ℝ) ^ cfg.T k s)⁻¹ ∈ Icc (0 : ℝ) 1
  change _ ≤ t ∧ t ≤ _ at ht
  rw [hend] at ht
  exact ⟨div_nonneg (by linarith [ht.1]) hq.le, (div_le_one hq).mpr (by linarith [ht.2])⟩

/-- The final residual support count, in original units and against the unchanged
original velocity palette. The ambient hypotheses are precisely those used by deep pruning. -/
theorem residual_support_at {α : Type} [MeasurableSpace α] {cfg : Data α}
    {k : ℕ} {s se R v' : ℝ}
    (hN : 0 < cfg.N k) (hK1 : 1 ≤ cfg.K k)
    (hν : IsProbabilityMeasure (cfg.ν k)) (hπ : IsProbabilityMeasure (cfg.π k))
    (hb : Measurable (cfg.b k))
    (hμ : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k se R)
    (hv'1 : R⁻¹ ≤ v') (hv'2 : v' ≤ R)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (θ : Measure (α × ℝ)) (C : Fin 4 → ℝ)
    (Γ Λ : Type) [Fintype Γ] [Fintype Λ] (lab : α → Λ) (crs : Λ → Γ)
    (chartOf : Γ → ℤ × ℤ) (pc : Γ → Fin 6 → ℝ) (D2 : Λ → ℝ)
    (χ H m v Kz M₀ : ℝ) (δp : ℝ≥0∞) (hH : 1 ≤ H) (hKz : 0 ≤ Kz) :
    ResidualSupportAt cfg k s se R v' i L θ C Γ Λ lab crs chartOf pc D2 χ H m v Kz M₀ δp := by
  classical
  letI : IsProbabilityMeasure (cfg.ν k) := hν
  letI : IsProbabilityMeasure (cfg.π k) := hπ
  dsimp only [ResidualSupportAt]
  intro hlab hθ hθsupp hZ hpc hchart hfit hcoarse hoffset hnest hvar hchartList hsmall hδ0 hδtop
  let F := blockFrame cfg k s i L
  let σ := cfg.N k ^ (-m)
  let τv := cfg.N k ^ (-v)
  have hσ : 0 < σ := Real.rpow_pos_of_pos hN _
  have hτv : 0 < τv := Real.rpow_pos_of_pos hN _
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  let state := fun p : α × ℝ => outBins F C σ τv (cfg.b k p.1) p.2
  let control := fun p : α × ℝ => vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3)
  have hfinite : θ univ < ⊤ := by
    let E := cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)
    have heq : θ univ = θ E := measure_congr (by
      filter_upwards [hθsupp] with p hp
      simp only [mem_univ, E, mem_prod, hp.1, hp.2, and_self])
    rw [heq]
    apply ((hθ _).trans (hμ _)).trans_lt
    rw [Measure.smul_apply, Measure.prod_prod, volume_I]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)
  letI : IsFiniteMeasure θ := ⟨hfinite⟩
  choose G hGcard hGmem using hcoarse
  choose Fo hFocard hFomem using hoffset
  choose Ch hChcard hChmem using hchartList
  have hM₀ : 0 ≤ M₀ := (Nat.cast_nonneg (Ch 0 0).card).trans (hChcard 0 0)
  have hbase : ∀ᵐ p ∂θ, F.zt p.2 ∈ Icc (0 : ℝ) 1 ∧ |F.zZ (cfg.b k p.1) p.2| ≤ Kz := by
    filter_upwards [hθsupp, hZ] with p hp hz
    exact ⟨block_zt_mem cfg k s i L hp.2, hz⟩
  have hoptions : ∀ᵐ p ∂θ, (state p).2 ∈
      residualBinOptions τv H
        (residualBaseValue (pc (crs (lab p.1))) σ Kz (state p).1) ⌊D2 (lab p.1) / τv⌋ := by
    filter_upwards [hbase, hfit] with p hp hf
    apply mem_residualBinOptions hτv hf
    · exact (residualBaseValue_close hσ hKz hH₀ (hpc (crs (lab p.1))) hp.1 hp.2 rfl).trans hsmall
    · rfl
  let candidates := residualCandidateUniverse crs pc D2 σ Kz τv H
  have hcandidates : ∀ᵐ p ∂θ, state p ∈ candidates := by
    filter_upwards [hbase, hoptions] with p hp ho
    exact mem_residualCandidateUniverse crs pc D2 σ Kz τv H (lab p.1)
      (mem_residualBaseCells hσ hp.1 hp.2) ho
  let menus := residualOutputMenu pc σ Kz τv H Ch G Fo
  let compat := fun o : (Fin 2 → ℤ) × ℤ => {w : ℤ | o ∈ menus w}
  have hcompat : ∀ᵐ p ∂θ, control p ∈ compat (state p) := by
    have hChall := ae_all_iff.mpr fun z => ae_all_iff.mpr fun w => hChmem z w
    have hGall := ae_all_iff.mpr hGmem
    have hFoall := ae_all_iff.mpr fun ch => ae_all_iff.mpr fun γ => hFomem ch γ
    filter_upwards [hbase, hoptions, hChall, hGall, hFoall] with p hp ho hch hg hfo
    let ch : ℤ × ℤ := (⌊cfg.b k p.1 3 / χ⌋, ⌊cfg.b k p.1 0 / χ⌋)
    have hc : ch ∈ Ch (state p).1 (control p) := hch _ _ rfl rfl
    have hγ : crs (lab p.1) ∈ G ch := hg ch rfl
    have hd : ⌊D2 (lab p.1) / τv⌋ ∈ Fo ch (crs (lab p.1)) := hfo ch _ rfl rfl
    change state p ∈ menus (control p)
    apply Finset.mem_biUnion.mpr
    refine ⟨(state p).1, mem_residualBaseCells hσ hp.1 hp.2, Finset.mem_image.mpr ⟨(state p).2, ?_, rfl⟩⟩
    exact mem_residualVelocityMenu pc σ Kz τv H Ch G Fo _ _ hc hγ hd ho
  obtain ⟨θ', hθ'le, hmass, hdom⟩ := residual_output_prune hν hK1 hb hμ hB hBe hv'1 hv'2
    i L θ C hθ hθsupp hnest hσ hτv hvar δp hδ0 hδtop
  letI : IsFiniteMeasure θ' := isFiniteMeasure_of_le θ hθ'le
  let πV := paletteBins (cfg.π k) (cfg.N k ^ (-v'))
  letI : IsProbabilityMeasure πV := by
    unfold πV paletteBins
    exact (Measure.isProbabilityMeasure_map_iff (measurable_vbin _).aemeasurable).mpr hπ
  let Fs := candidates.filter (fun o => θ' {p | state p = o} ≠ 0)
  have hFs : ∀ᵐ p ∂θ', state p ∈ Fs := by
    have havoid : ∀ᵐ p ∂θ', ∀ o : (Fin 2 → ℤ) × ℤ,
        θ' {q | state q = o} = 0 → state p ≠ o := by
      apply ae_all_iff.mpr
      intro o
      by_cases ho : θ' {q | state q = o} = 0
      · have hh : ∀ᵐ p ∂θ', state p ≠ o := ae_iff.mpr (by simpa only [not_not] using ho)
        exact hh.mono fun p hp _ => hp
      · exact Eventually.of_forall fun p hp => (ho hp).elim
    filter_upwards [ae_mono hθ'le hcandidates, havoid] with p hp hn
    exact Finset.mem_filter.mpr ⟨hp, fun hz => hn (state p) hz rfl⟩
  let Bcount := ((1 / σ + 2) * (2 * Kz / σ + 2)) * (M₀ * H ^ 3 * cfg.N k ^ (cfg.d * v) * 7)
  have hBcount : 0 ≤ Bcount := by dsimp [Bcount]; positivity
  have hlist : ∀ w, ((Submission.Lib.K4OutputReferenceMenus.paletteStates Fs compat w).card : ℝ≥0∞) ≤
      ENNReal.ofReal Bcount := by
    intro w
    have hsub : Submission.Lib.K4OutputReferenceMenus.paletteStates Fs compat w ⊆ menus w := by
      intro o ho
      have hh : o ∈ Fs ∧ w ∈ compat o := by
        simpa only [Submission.Lib.K4OutputReferenceMenus.paletteStates, Finset.mem_filter] using ho
      exact hh.2
    have hsubcount : ((Submission.Lib.K4OutputReferenceMenus.paletteStates Fs compat w).card : ℝ) ≤
        ((menus w).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have hcount : ((Submission.Lib.K4OutputReferenceMenus.paletteStates Fs compat w).card : ℝ) ≤ Bcount :=
      hsubcount.trans
        (residualOutputMenu_card pc hσ hKz hτv hH hM₀ (Real.rpow_nonneg hN.le _)
          Ch G Fo hChcard hGcard hFocard w)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcount
  have hcount : (Fs.card : ℝ≥0∞) ≤ (ENNReal.ofReal (cfg.K k) / δp) * ENNReal.ofReal Bcount := by
    apply Submission.Lib.K4OutputReferenceMenus.palette_support_count_of_caps θ' πV state control
      Fs compat (fun _ _ => (Set.to_countable _).measurableSet) _ _
    · intro o ho
      exact hdom o (compat o)
    · exact ae_mono hθ'le hcompat
    · intro o ho
      exact (Finset.mem_filter.mp ho).2
    · exact hlist
  have hcountR : (Fs.card : ℝ) ≤ (ENNReal.ofReal (cfg.K k) / δp).toReal * Bcount := by
    have hfin : (ENNReal.ofReal (cfg.K k) / δp) * ENNReal.ofReal Bcount ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hδ0) ENNReal.ofReal_ne_top
    have hh := ENNReal.toReal_mono hfin hcount
    simpa only [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofReal hBcount] using hh
  refine ⟨θ', hθ'le, hmass, Fs, ?_, hFs⟩
  have hinv : 1 / σ = cfg.N k ^ m := by
    dsimp [σ]
    rw [one_div, ← Real.rpow_neg hN.le, neg_neg]
  dsimp only [Bcount] at hcountR
  have hspace : 2 * Kz / σ = 2 * Kz * cfg.N k ^ m := by
    rw [div_eq_mul_inv, ← one_div σ, hinv]
  rw [hinv, hspace] at hcountR
  convert hcountR using 1 <;> ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
