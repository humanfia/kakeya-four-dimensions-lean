import Mathlib
-- Adapted from: here:o078 (session x0262, branch x0262 of o078).

/-!
# Slicing a two-colour pair law

A finite family of measures `ρ ι` on the plane (indexed by pairs `ι = (i, j)` of colour
indices), whose colour marginals have densities bounded by `C π₁ i` and `C π₂ j`, has a
slice `{ζ} × ℝ` carrying at least a quarter of the mass (when the mass sits over
`ζ ∈ [-1, 1]`), whose one-dimensional slice measures satisfy the same marginal density bounds
and inherit every almost-sure property. This is the Fubini step of the paper's local graph
matching (Corollary 3.4), done with Radon--Nikodym densities.
-/

namespace Submission.Lib.K4QuadSheetMatching

open MeasureTheory Set
open scoped ENNReal

theorem exists_good_slice {n₁ n₂ : ℕ} (ρ : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ))
    [hfin : ∀ ι, IsFiniteMeasure (ρ ι)] {C : ℝ} (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
    (h1 : ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ j, ρ (i, j) B ≤ ENNReal.ofReal (C * π₁ i) * volume B)
    (h2 : ∀ j (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ i, ρ (i, j) B ≤ ENNReal.ofReal (C * π₂ j) * volume B)
    (Good : Fin n₁ × Fin n₂ → Set (ℝ × ℝ)) (hGoodm : ∀ ι, MeasurableSet (Good ι))
    (hG : ∀ ι, ρ ι (Good ι)ᶜ = 0)
    (hsupp : ∀ ι, ρ ι {z | z.1 ∉ Icc (-1 : ℝ) 1} = 0)
    {m : ℝ} (hm : 0 < m) (hmass : ENNReal.ofReal m ≤ ∑ ι, ρ ι univ) :
    ∃ ζ ∈ Icc (-1 : ℝ) 1, ∃ σ : Fin n₁ × Fin n₂ → Measure ℝ,
      (∀ ι, IsFiniteMeasure (σ ι)) ∧
      ENNReal.ofReal (m / 4) ≤ ∑ ι, σ ι univ ∧
      (∀ i (E : Set ℝ), MeasurableSet E →
        ∑ j, σ (i, j) E ≤ ENNReal.ofReal (C * π₁ i) * volume E) ∧
      (∀ j (E : Set ℝ), MeasurableSet E →
        ∑ i, σ (i, j) E ≤ ENNReal.ofReal (C * π₂ j) * volume E) ∧
      (∀ ι, σ ι {s | (ζ, s) ∉ Good ι} = 0) := by
  classical
  -- densities
  have hle : ∀ ι : Fin n₁ × Fin n₂, ρ ι ≤ ENNReal.ofReal (C * π₁ ι.1) • volume := by
    intro ι
    refine Measure.le_iff.mpr (fun B hB => ?_)
    calc ρ ι B ≤ ∑ j, ρ (ι.1, j) B :=
          Finset.single_le_sum (f := fun j => ρ (ι.1, j) B) (fun _ _ => zero_le')
            (Finset.mem_univ ι.2)
      _ ≤ ENNReal.ofReal (C * π₁ ι.1) * volume B := h1 ι.1 B hB
      _ = (ENNReal.ofReal (C * π₁ ι.1) • volume) B := by rw [Measure.smul_apply, smul_eq_mul]
  have hac : ∀ ι, ρ ι ≪ volume := fun ι => Measure.absolutelyContinuous_of_le_smul (hle ι)
  set h : Fin n₁ × Fin n₂ → ℝ × ℝ → ℝ≥0∞ := fun ι => (ρ ι).rnDeriv volume with hh
  have hhm : ∀ ι, Measurable (h ι) := fun ι => Measure.measurable_rnDeriv _ _
  have hint : ∀ ι (B : Set (ℝ × ℝ)), ∫⁻ z in B, h ι z = ρ ι B := fun ι B =>
    Measure.setLIntegral_rnDeriv (hac ι) B
  -- almost-everywhere bounds in the plane
  have ae1 : ∀ i, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), ∑ j, h (i, j) z ≤ ENNReal.ofReal (C * π₁ i) := by
    intro i
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (Finset.measurable_sum _ (fun j _ => hhm (i, j))) (fun B hB _ => ?_)
    rw [lintegral_finset_sum _ (fun j _ => hhm (i, j)), setLIntegral_const]
    simp_rw [hint]
    exact h1 i B hB
  have ae2 : ∀ j, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), ∑ i, h (i, j) z ≤ ENNReal.ofReal (C * π₂ j) := by
    intro j
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (Finset.measurable_sum _ (fun i _ => hhm (i, j))) (fun B hB _ => ?_)
    rw [lintegral_finset_sum _ (fun i _ => hhm (i, j)), setLIntegral_const]
    simp_rw [hint]
    exact h2 j B hB
  have aeG : ∀ ι, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), z ∉ Good ι → h ι z = 0 := by
    intro ι
    have h0 : ∫⁻ z in (Good ι)ᶜ, h ι z = 0 := by rw [hint, hG]
    rw [setLIntegral_eq_zero_iff (hGoodm ι).compl (hhm ι)] at h0
    exact h0
  have hSm : MeasurableSet {z : ℝ × ℝ | z.1 ∉ Icc (-1 : ℝ) 1} :=
    (measurableSet_Icc.preimage measurable_fst).compl
  have aeS : ∀ ι, ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), z.1 ∉ Icc (-1 : ℝ) 1 → h ι z = 0 := by
    intro ι
    have h0 : ∫⁻ z in {z : ℝ × ℝ | z.1 ∉ Icc (-1 : ℝ) 1}, h ι z = 0 := by rw [hint, hsupp]
    rw [setLIntegral_eq_zero_iff hSm (hhm ι)] at h0
    exact h0
  -- Fubini: the same properties on almost every slice
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume :=
    Measure.volume_eq_prod ℝ ℝ
  have slice1 : ∀ᵐ ζ ∂(volume : Measure ℝ), ∀ i, ∀ᵐ s ∂(volume : Measure ℝ),
      ∑ j, h (i, j) (ζ, s) ≤ ENNReal.ofReal (C * π₁ i) := by
    rw [ae_all_iff]; intro i
    have := ae1 i; rw [hvol] at this
    exact Measure.ae_ae_of_ae_prod this
  have slice2 : ∀ᵐ ζ ∂(volume : Measure ℝ), ∀ j, ∀ᵐ s ∂(volume : Measure ℝ),
      ∑ i, h (i, j) (ζ, s) ≤ ENNReal.ofReal (C * π₂ j) := by
    rw [ae_all_iff]; intro j
    have := ae2 j; rw [hvol] at this
    exact Measure.ae_ae_of_ae_prod this
  have sliceG : ∀ᵐ ζ ∂(volume : Measure ℝ), ∀ ι, ∀ᵐ s ∂(volume : Measure ℝ),
      (ζ, s) ∉ Good ι → h ι (ζ, s) = 0 := by
    rw [ae_all_iff]; intro ι
    have := aeG ι; rw [hvol] at this
    exact Measure.ae_ae_of_ae_prod this
  have sliceS : ∀ᵐ ζ ∂(volume : Measure ℝ), ∀ ι, ∀ᵐ s ∂(volume : Measure ℝ),
      ζ ∉ Icc (-1 : ℝ) 1 → h ι (ζ, s) = 0 := by
    rw [ae_all_iff]; intro ι
    have := aeS ι; rw [hvol] at this
    exact Measure.ae_ae_of_ae_prod this
  -- the slice masses
  set Mι : Fin n₁ × Fin n₂ → ℝ → ℝ≥0∞ := fun ι ζ => ∫⁻ s, h ι (ζ, s) with hMι
  have hMιm : ∀ ι, Measurable (Mι ι) := fun ι => (hhm ι).lintegral_prod_right'
  have hMιint : ∀ ι, ∫⁻ ζ, Mι ι ζ = ρ ι univ := by
    intro ι
    rw [hMι]
    simp only
    rw [← lintegral_prod _ (hhm ι).aemeasurable, ← hvol, ← setLIntegral_univ, hint]
  have sliceFin : ∀ᵐ ζ ∂(volume : Measure ℝ), ∀ ι, Mι ι ζ < ⊤ := by
    rw [ae_all_iff]; intro ι
    refine ae_lt_top (hMιm ι) ?_
    rw [hMιint]; exact measure_ne_top _ _
  set M : ℝ → ℝ≥0∞ := fun ζ => ∑ ι, Mι ι ζ with hM
  have hMm : Measurable M := Finset.measurable_sum _ (fun ι _ => hMιm ι)
  have hMint : ∫⁻ ζ, M ζ = ∑ ι, ρ ι univ := by
    rw [hM]; simp only
    rw [lintegral_finset_sum _ (fun ι _ => hMιm ι)]
    exact Finset.sum_congr rfl (fun ι _ => hMιint ι)
  have hMout : ∀ᵐ ζ ∂(volume : Measure ℝ), ζ ∉ Icc (-1 : ℝ) 1 → M ζ = 0 := by
    filter_upwards [sliceS] with ζ hζ hout
    rw [hM]; simp only
    refine Finset.sum_eq_zero (fun ι _ => ?_)
    rw [hMι]; simp only
    exact lintegral_eq_zero_iff' (by fun_prop) |>.mpr ((hζ ι).mono (fun s hs => hs hout))
  -- a heavy good slice
  have hexists : ∃ ζ ∈ Icc (-1 : ℝ) 1, ENNReal.ofReal (m / 4) ≤ M ζ ∧
      (∀ i, ∀ᵐ s ∂(volume : Measure ℝ), ∑ j, h (i, j) (ζ, s) ≤ ENNReal.ofReal (C * π₁ i)) ∧
      (∀ j, ∀ᵐ s ∂(volume : Measure ℝ), ∑ i, h (i, j) (ζ, s) ≤ ENNReal.ofReal (C * π₂ j)) ∧
      (∀ ι, ∀ᵐ s ∂(volume : Measure ℝ), (ζ, s) ∉ Good ι → h ι (ζ, s) = 0) ∧
      (∀ ι, Mι ι ζ < ⊤) := by
    by_contra hcon
    push Not at hcon
    have hae : ∀ᵐ ζ ∂(volume : Measure ℝ), M ζ ≤ (Icc (-1 : ℝ) 1).indicator
        (fun _ => ENNReal.ofReal (m / 4)) ζ := by
      filter_upwards [slice1, slice2, sliceG, sliceFin, hMout] with ζ e1 e2 eG eF eO
      by_cases hζ : ζ ∈ Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hζ]
        by_contra hlt
        push Not at hlt
        obtain ⟨ι, hι⟩ := hcon ζ hζ hlt.le e1 e2 eG
        exact absurd (eF ι) (not_lt.mpr hι)
      · rw [eO hζ]; exact zero_le'
    have hbound : ∫⁻ ζ, M ζ ≤ ENNReal.ofReal (m / 4) * ENNReal.ofReal 2 := by
      calc ∫⁻ ζ, M ζ ≤ ∫⁻ ζ, (Icc (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (m / 4)) ζ :=
            lintegral_mono_ae hae
        _ = ENNReal.ofReal (m / 4) * ENNReal.ofReal 2 := by
            rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]; norm_num
    rw [hMint] at hbound
    have := hmass.trans hbound
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    linarith
  obtain ⟨ζ, hζ, hMζ, e1, e2, eG, eF⟩ := hexists
  have hhs : ∀ ι, Measurable (fun s : ℝ => h ι (ζ, s)) := fun ι =>
    (hhm ι).comp measurable_prodMk_left
  refine ⟨ζ, hζ, fun ι => (volume : Measure ℝ).withDensity (fun s => h ι (ζ, s)), ?_, ?_, ?_, ?_, ?_⟩
  · intro ι
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact eF ι
  · calc ENNReal.ofReal (m / 4) ≤ M ζ := hMζ
      _ = ∑ ι, (volume : Measure ℝ).withDensity (fun s => h ι (ζ, s)) univ := by
          rw [hM]; simp only
          refine Finset.sum_congr rfl (fun ι _ => ?_)
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  · intro i E hE
    simp_rw [withDensity_apply _ hE]
    rw [← lintegral_finset_sum _ (fun j _ => hhs (i, j))]
    calc ∫⁻ s in E, ∑ j, h (i, j) (ζ, s) ≤ ∫⁻ _ in E, ENNReal.ofReal (C * π₁ i) :=
          lintegral_mono_ae ((ae_restrict_iff' hE).mpr ((e1 i).mono (fun s hs _ => hs)))
      _ = ENNReal.ofReal (C * π₁ i) * volume E := setLIntegral_const _ _
  · intro j E hE
    simp_rw [withDensity_apply _ hE]
    rw [← lintegral_finset_sum _ (fun i _ => hhs (i, j))]
    calc ∫⁻ s in E, ∑ i, h (i, j) (ζ, s) ≤ ∫⁻ _ in E, ENNReal.ofReal (C * π₂ j) :=
          lintegral_mono_ae ((ae_restrict_iff' hE).mpr ((e2 j).mono (fun s hs _ => hs)))
      _ = ENNReal.ofReal (C * π₂ j) * volume E := setLIntegral_const _ _
  · intro ι
    have hBm : MeasurableSet {s : ℝ | (ζ, s) ∉ Good ι} :=
      ((hGoodm ι).preimage measurable_prodMk_left).compl
    rw [withDensity_apply _ hBm, setLIntegral_eq_zero_iff hBm (hhs ι)]
    exact (eG ι).mono (fun s hs hb => hs hb)

end Submission.Lib.K4QuadSheetMatching
