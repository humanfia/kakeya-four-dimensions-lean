/-
Adapted from: here:o168 (session x0569, branch x0569-o196port at c22aeb8a,
Submission/Obl/k4_scalar_guarded_entropic_path/NodalMask.lean, AngularMask.lean and
PaletteFrostman.lean; there adapted from x0569's files of the same names in
Submission/Obl/k4_scalar_guarded_tangent_preparation/). Own code of this tree. The masks of
the source are replaced here by exceptional sets that the reference law does not charge
(the form in which `PathGeometry.PreparedViews` provides them), and the palette is
`Info.velocityPalette`.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.ProfileZero
import Submission.Obl.k4_scalar_guarded_entropic_path.RawStage
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.FiniteCode

/-!
# Pure ceilings and palette bins from null exceptional sets

A law `σ ≤ μ_g` that does not charge the two-sided pure exception at depth `r` has pure
observations at depth `r` with law at most `N^{-f(r)+τ}` times the reference measure. If it
does not charge the terminal pure exception nor the angular exception at velocity resolution
`u`, every velocity bin of width `N^{-u}` carries `σ`-mass at most `N^{-S u + 2τ}`, and the
normalized velocity palette of `σ` gives every finer bin mass at most `2 N^{-S u + 2τ} / θ`
when `σ` has mass at least `θ`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Reference

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem measurable_obsMap (N r : ℝ) : Measurable (obsMap N r) := by
  have hy : Measurable (fun z : Incidence => Split.y z.1 z.2) := by
    unfold Split.y; fun_prop
  have hx : Measurable (fun z : Incidence => Split.x z.1 z.2) := by
    unfold Split.x; fun_prop
  have hv : Measurable (fun z : Incidence => (![z.2, Split.y z.1 z.2] : Fin 2 → ℝ)) := by
    rw [measurable_pi_iff]
    intro i
    fin_cases i
    · exact measurable_snd
    · exact hy
  exact hv.prodMk (Int.measurable_floor.comp (hx.div_const _))

/-- The terminal observation together with the velocity bin at resolution `u`. -/
abbrev angObs (N L u : ℝ) (z : Incidence) : ((Fin 2 → ℝ) × ℤ) × ℤ :=
  (obsMap N L z, (⌊z.1.2 1 / (N ^ (-u))⌋ : ℤ))

theorem measurable_angObs (N L u : ℝ) : Measurable (angObs N L u) := by
  refine (measurable_obsMap N L).prodMk ?_
  exact Int.measurable_floor.comp ((by fun_prop : Measurable
    (fun z : Incidence => z.1.2 1)).div_const _)

/-- The two-sided pure exception of world `g` at depth `r` with tolerance `τ`. -/
def pureExc (p : Code) (k : ℕ) (g : Fin (p.1 k)) (r τ : ℝ) : Set Incidence :=
  {z | p.density k g r (obsMap (p.N k) r z) < ENNReal.ofReal (p.N k ^ (-p.profile r - τ)) ∨
    ENNReal.ofReal (p.N k ^ (-p.profile r + τ)) < p.density k g r (obsMap (p.N k) r z)}

/-- The terminal angular exception of world `g` at velocity resolution `u` with
tolerance `τ`. -/
def angExc (p : Code) (k : ℕ) (g : Fin (p.1 k)) (u τ : ℝ) : Set Incidence :=
  {z | ENNReal.ofReal (p.N k ^ (-p.profile p.L - p.S * u + τ)) <
    p.angularDensity k g u (angObs (p.N k) p.L u z)}

/-- A law under `μ` that does not charge the complement of `A` lies under `μ` restricted
to `A`. -/
theorem le_restrict_of_null {μ σ : Measure Incidence} (hσ : σ ≤ μ) {A : Set Incidence}
    (hA : σ Aᶜ = 0) : σ ≤ μ.restrict A := by
  have hae : ∀ᵐ z ∂σ, z ∈ A := by
    rw [ae_iff]
    exact hA
  calc σ = σ.restrict A := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ ≤ μ.restrict A := Measure.restrict_mono subset_rfl hσ

/-- A law under an incidence law of an exact problem is finite. -/
theorem isFiniteMeasure_of_le_mu {p : Code} (hp : Split.Exact p) {k : ℕ} {g : Fin (p.1 k)}
    {σ : Measure Incidence} (hσ : σ ≤ Split.mu p k g) : IsFiniteMeasure σ :=
  ⟨lt_of_le_of_lt ((hσ Set.univ).trans (mu_univ_le_one' hp k g)) ENNReal.one_lt_top⟩

/-- **Pure ceiling.** A law under `μ_g` not charging the pure exception at `r ∈ [0, L]` has
pure observations at `r` with law at most `N^{-f(r)+τ}` times the reference measure. -/
theorem map_obsMap_le {p : Code} (hp : Split.Exact p) {k : ℕ} {g : Fin (p.1 k)}
    {r τ : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L) {σ : Measure Incidence}
    (hσ : σ ≤ Split.mu p k g) (hnull : σ (pureExc p k g r τ) = 0) :
    σ.map (obsMap (p.N k) r) ≤ ENNReal.ofReal (p.N k ^ (-p.profile r + τ)) •
      ((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure ℤ)) := by
  obtain ⟨hgm, hmap0⟩ := hp.2.2.1 k g r hr hrL
  have hmap : (Split.mu p k g).map (obsMap (p.N k) r) =
      ((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure ℤ)).withDensity
        (p.density k g r) := hmap0
  set M := ENNReal.ofReal (p.N k ^ (-p.profile r + τ)) with hM
  have hΦ := measurable_obsMap (p.N k) r
  have hset : MeasurableSet {v : (Fin 2 → ℝ) × ℤ | p.density k g r v ≤ M} :=
    measurableSet_le hgm measurable_const
  have hle : σ ≤ (Split.mu p k g).restrict
      (obsMap (p.N k) r ⁻¹' {v | p.density k g r v ≤ M}) := by
    apply le_restrict_of_null hσ
    apply measure_mono_null _ hnull
    intro z hz
    simp only [mem_compl_iff, mem_preimage, mem_ofPred_eq, not_le] at hz
    exact Or.inr hz
  refine Measure.le_iff.mpr fun A hA => ?_
  calc σ.map (obsMap (p.N k) r) A
      ≤ ((Split.mu p k g).restrict (obsMap (p.N k) r ⁻¹' {v | p.density k g r v ≤ M})).map
          (obsMap (p.N k) r) A := (Measure.map_mono hle hΦ) A
    _ = (((Split.mu p k g).map (obsMap (p.N k) r)).restrict {v | p.density k g r v ≤ M}) A := by
        rw [Measure.restrict_map hΦ hset]
    _ = (((volume.prod Measure.count).withDensity (p.density k g r)).restrict
          {v | p.density k g r v ≤ M}) A := by
        rw [hmap]
    _ = ((volume.prod Measure.count).withDensity (p.density k g r))
          (A ∩ {v | p.density k g r v ≤ M}) := Measure.restrict_apply hA
    _ = ∫⁻ v in A ∩ {v | p.density k g r v ≤ M}, p.density k g r v
          ∂(volume.prod Measure.count) := withDensity_apply _ (hA.inter hset)
    _ ≤ ∫⁻ _ in A ∩ {v | p.density k g r v ≤ M}, M ∂(volume.prod Measure.count) :=
        setLIntegral_mono measurable_const (fun v hv => hv.2)
    _ = M * (volume.prod Measure.count) (A ∩ {v | p.density k g r v ≤ M}) :=
        setLIntegral_const _ _
    _ ≤ M * (volume.prod Measure.count) A := by
        gcongr; exact inter_subset_left
    _ = (M • (volume.prod Measure.count)) A := rfl

/-- Markov: the reference volume where a density is at least `m` is at most its total
mass over `m`. -/
theorem ref_density_ge_le {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (g : Y → ℝ≥0∞)
    (hg : Measurable g) (m : ℝ≥0∞) :
    m * ν {y | m ≤ g y} ≤ (ν.withDensity g) Set.univ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact mul_meas_ge_le_lintegral hg m

/-- **Velocity bins.** A law under `μ_g` not charging the terminal pure exception nor the
angular exception at resolution `u` gives every velocity bin of width `N^{-u}` mass at most
`N^{-S u + 2τ}`. -/
theorem velocity_bin_mass_le {p : Code} (hp : Split.Exact p) {k : ℕ} {g : Fin (p.1 k)}
    {u τ : ℝ} (hu : 0 < u) (huU : u ≤ p.U) {σ : Measure Incidence}
    (hσ : σ ≤ Split.mu p k g) (hL : σ (pureExc p k g p.L τ) = 0)
    (hA : σ (angExc p k g u τ) = 0) (e : ℤ) :
    σ {z | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) = e} ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) := by
  have hL0 : 0 < p.L := exact_length_pos hp
  have hN1 : 1 ≤ p.N k := exact_N_ge_one hp k
  have hNpos : 0 < p.N k := by linarith
  obtain ⟨hGm, hGmap0⟩ := hp.2.2.2.1 k g u hu huU
  obtain ⟨hgm, hgmap0⟩ := hp.2.2.1 k g p.L hL0.le le_rfl
  have hGmap : (Split.mu p k g).map (angObs (p.N k) p.L u) =
      (((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure ℤ)).prod
        (Measure.count : Measure ℤ)).withDensity (p.angularDensity k g u) := hGmap0
  have hgmap : (Split.mu p k g).map (obsMap (p.N k) p.L) =
      ((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure ℤ)).withDensity
        (p.density k g p.L) := hgmap0
  set M := ENNReal.ofReal (p.N k ^ (-p.profile p.L - p.S * u + τ)) with hM
  set m := ENNReal.ofReal (p.N k ^ (-p.profile p.L - τ)) with hm
  have hm0 : m ≠ 0 := by
    rw [hm, ENNReal.ofReal_ne_zero_iff]; exact Real.rpow_pos_of_pos hNpos _
  have hmtop : m ≠ ⊤ := ENNReal.ofReal_ne_top
  set ref := ((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure ℤ)) with href
  set good : Set Incidence := {z | p.angularDensity k g u (angObs (p.N k) p.L u z) ≤ M} ∩
      {z | m ≤ p.density k g p.L (obsMap (p.N k) p.L z)} with hgood
  have hgoodm : MeasurableSet good :=
    (measurableSet_le (hGm.comp (measurable_angObs _ _ _)) measurable_const).inter
      (measurableSet_le measurable_const (hgm.comp (measurable_obsMap _ _)))
  have hσ' : σ ≤ (Split.mu p k g).restrict good := by
    apply le_restrict_of_null hσ
    apply measure_mono_null _ (measure_union_null hA hL)
    intro z hz
    simp only [hgood, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, not_and_or, not_le] at hz
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  set Se : Set (((Fin 2 → ℝ) × ℤ) × ℤ) :=
    {w | w.2 = e ∧ p.angularDensity k g u w ≤ M ∧ m ≤ p.density k g p.L w.1} with hSe
  have hSem : MeasurableSet Se := by
    refine (measurableSet_eq_fun measurable_snd measurable_const).inter
      ((measurableSet_le hGm measurable_const).inter
        (measurableSet_le measurable_const (hgm.comp measurable_fst)))
  have hsub : {z : Incidence | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) = e} ∩ good ⊆
      angObs (p.N k) p.L u ⁻¹' Se := by
    rintro z ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  have hvol : m * ref {o | m ≤ p.density k g p.L o} ≤ 1 := by
    calc m * ref {o | m ≤ p.density k g p.L o} ≤ (ref.withDensity (p.density k g p.L)) univ :=
          ref_density_ge_le ref _ hgm m
      _ = (Split.mu p k g).map (obsMap (p.N k) p.L) univ := by rw [hgmap]
      _ = Split.mu p k g univ := by
          rw [Measure.map_apply (measurable_obsMap _ _) MeasurableSet.univ, preimage_univ]
      _ ≤ 1 := mu_univ_le_one' hp k g
  have hMm : M / m = ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) := by
    rw [hM, hm, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hNpos _),
      ← Real.rpow_sub hNpos]
    congr 2; ring
  rw [← hMm]
  calc σ {z | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) = e}
      ≤ ((Split.mu p k g).restrict good) {z | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) = e} := hσ' _
    _ = Split.mu p k g ({z : Incidence | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) = e} ∩ good) :=
        Measure.restrict_apply' hgoodm
    _ ≤ Split.mu p k g (angObs (p.N k) p.L u ⁻¹' Se) := measure_mono hsub
    _ = ((Split.mu p k g).map (angObs (p.N k) p.L u)) Se :=
        (Measure.map_apply (measurable_angObs _ _ _) hSem).symm
    _ = ∫⁻ w in Se, p.angularDensity k g u w ∂(ref.prod Measure.count) := by
        rw [hGmap, withDensity_apply _ hSem]
    _ ≤ ∫⁻ _ in Se, M ∂(ref.prod Measure.count) :=
        setLIntegral_mono measurable_const (fun w hw => hw.2.1)
    _ = M * (ref.prod Measure.count) Se := setLIntegral_const _ _
    _ ≤ M * (ref.prod Measure.count) ({o | m ≤ p.density k g p.L o} ×ˢ {e}) := by
        gcongr
        rintro w ⟨h1, _, h3⟩
        exact ⟨h3, h1⟩
    _ = M * ref {o | m ≤ p.density k g p.L o} := by
        rw [Measure.prod_prod, Measure.count_singleton, mul_one]
    _ ≤ M / m := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)]
        calc M * ref {o | m ≤ p.density k g p.L o} * m
            = M * (m * ref {o | m ≤ p.density k g p.L o}) := by ring
          _ ≤ M * 1 := by gcongr
          _ = M := mul_one M

/-- A fine floor bin lies in two coarse floor bins. -/
theorem fine_bin_subset {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w) (e : ℤ) :
    {v : ℝ | (⌊v / w'⌋ : ℤ) = e} ⊆
      {v | (⌊v / w⌋ : ℤ) = ⌊(e : ℝ) * w' / w⌋} ∪
        {v | (⌊v / w⌋ : ℤ) = ⌊(e : ℝ) * w' / w⌋ + 1} := by
  intro v hv
  have hw : 0 < w := lt_of_lt_of_le hw' hww'
  simp only [mem_ofPred_eq] at hv
  have h1 := Int.floor_le (v / w')
  have h2 := Int.lt_floor_add_one (v / w')
  rw [hv] at h1 h2
  have hv1 : (e : ℝ) * w' ≤ v := by rwa [le_div_iff₀ hw'] at h1
  have hv2 : v < (e : ℝ) * w' + w' := by
    have := (div_lt_iff₀ hw').mp h2; linarith
  set a := (e : ℝ) * w' / w with ha
  have hva1 : a ≤ v / w := by rw [ha]; exact div_le_div_of_nonneg_right hv1 hw.le
  have hva2 : v / w < a + 1 := by
    rw [ha, div_add_one hw.ne', div_lt_div_iff_of_pos_right hw]; linarith
  have hf1 : ⌊a⌋ ≤ ⌊v / w⌋ := Int.floor_mono hva1
  have hf2 : ⌊v / w⌋ ≤ ⌊a⌋ + 1 := by
    have : ⌊v / w⌋ ≤ ⌊a + 1⌋ := Int.floor_mono hva2.le
    rwa [Int.floor_add_one] at this
  rcases eq_or_lt_of_le hf1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm hf2 (by omega))

/-- **Palette bins.** If `σ ≤ μ_g` does not charge the terminal pure exception nor the
angular exception at resolution `u` and has mass at least `θ`, its normalized velocity
palette gives every velocity bin of width `w' ≤ N^{-u}` mass at most
`2 N^{-S u + 2τ} / θ`. -/
theorem palette_bin_le {p : Code} (hp : Split.Exact p) {k : ℕ} {g : Fin (p.1 k)}
    {u τ θ : ℝ} (hu0 : 0 < u) (huU : u ≤ p.U) {σ : Measure Incidence}
    (hσ : σ ≤ Split.mu p k g) (hL : σ (pureExc p k g p.L τ) = 0)
    (hA : σ (angExc p k g u τ) = 0)
    (hθ : 0 < θ) (hmass : ENNReal.ofReal θ ≤ σ Set.univ)
    {w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ p.N k ^ (-u)) (e : ℤ) :
    Info.velocityPalette σ {v | (⌊v / w'⌋ : ℤ) = e} ≤
      ENNReal.ofReal (2 * p.N k ^ (-p.S * u + 2 * τ) / θ) := by
  have hfin : IsFiniteMeasure σ := isFiniteMeasure_of_le_mu hp hσ
  have hNpos : 0 < p.N k := by linarith [exact_N_ge_one hp k]
  have hσ0 : σ Set.univ ≠ 0 := by
    intro h; rw [h] at hmass
    exact absurd hmass (not_le.mpr (ENNReal.ofReal_pos.mpr hθ))
  have hmeasv : Measurable (fun z : Incidence => z.1.2 1) := by fun_prop
  have hbin : ∀ e' : ℤ, σ {z | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) = e'} ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) :=
    fun e' => velocity_bin_mass_le hp hu0 huU hσ hL hA e'
  have hsub := fine_bin_subset hw' hww' e
  have hpal : Info.velocityPalette σ {v | (⌊v / w'⌋ : ℤ) = e} =
      (σ Set.univ)⁻¹ * σ ((fun z : Incidence => z.1.2 1) ⁻¹' {v | (⌊v / w'⌋ : ℤ) = e}) := by
    have hms : MeasurableSet {v : ℝ | (⌊v / w'⌋ : ℤ) = e} := by
      have h : Measurable (fun v : ℝ => (⌊v / w'⌋ : ℤ)) :=
        Int.measurable_floor.comp (measurable_id.div_const w')
      exact h (measurableSet_singleton e)
    rw [Info.velocityPalette, if_neg hσ0, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hmeasv hms]
  rw [hpal]
  calc (σ Set.univ)⁻¹ * σ ((fun z : Incidence => z.1.2 1) ⁻¹' {v | (⌊v / w'⌋ : ℤ) = e})
      ≤ (ENNReal.ofReal θ)⁻¹ * (σ {z | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) =
            ⌊(e : ℝ) * w' / p.N k ^ (-u)⌋} +
          σ {z | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) = ⌊(e : ℝ) * w' / p.N k ^ (-u)⌋ + 1}) := by
        have hsub' : (fun z : Incidence => z.1.2 1) ⁻¹' {v | (⌊v / w'⌋ : ℤ) = e} ⊆
            {z : Incidence | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) =
              ⌊(e : ℝ) * w' / p.N k ^ (-u)⌋} ∪
            {z : Incidence | (⌊z.1.2 1 / (p.N k ^ (-u))⌋ : ℤ) =
              ⌊(e : ℝ) * w' / p.N k ^ (-u)⌋ + 1} := fun z hz => hsub hz
        exact mul_le_mul' (ENNReal.inv_le_inv.mpr hmass)
          ((measure_mono hsub').trans (measure_union_le _ _))
    _ ≤ (ENNReal.ofReal θ)⁻¹ * (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) +
          ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ))) := by
        gcongr <;> exact hbin _
    _ = ENNReal.ofReal (2 * p.N k ^ (-p.S * u + 2 * τ) / θ) := by
        have hpow : 0 ≤ p.N k ^ (-p.S * u + 2 * τ) := Real.rpow_nonneg hNpos.le _
        rw [← ENNReal.ofReal_add hpow hpow,
          ← ENNReal.ofReal_inv_of_pos hθ, ← ENNReal.ofReal_mul (inv_nonneg.mpr hθ.le)]
        congr 1; ring

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Reference
