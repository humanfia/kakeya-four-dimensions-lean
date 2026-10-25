import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.CellCurl
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.BlockKernel
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.FourStep
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.PathCover
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Continuity

/-!
# The curl of the field on one block

All the data of one packet block of the Cartesian field certificate: the
incidence measure `μ ≤ H ν⊗dt` on the block, its base-cell ceiling, the fine
state palette domination, the angular cap, the polynomial field `𝒯` and its
relation to `X'`, and the joint support count at width `w₁`. The genuine
four-switch path law of `μ` gives every coefficient of the curl of the
rescaled field a bound in terms of these data.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial ProbabilityTheory
open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching
open Submission.Lib.K4ScalarActualSwitching

/-- The joint support of the incidence measure at base mesh `ξ` and hidden width `w₁`. -/
def jointSupport (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ) (h ξ w₁ : ℝ) :
    Set ((Fin 2 → ℤ) × ℤ) :=
  {q | μ {p | (fun i => ⌊ubase z₀ h p.1 p.2 i / ξ⌋) = q.1 ∧ ⌊xL p.1 p.2 / w₁⌋ = q.2} ≠ 0}

set_option maxHeartbeats 1600000 in
theorem exists_block_curl_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (νg : Measure (ℕ × (Fin 5 → ℝ))) [IsProbabilityMeasure νg]
      (πg : Measure ℝ) [IsProbabilityMeasure πg]
      (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (A : Set (ℕ × (Fin 5 → ℝ))) (t₀ h : ℝ)
      (z₀ : Fin 2 → ℝ) (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ)
      (H K₁ lam δs δv δb r pang εT ξ w₁ Jb K : ℝ),
      MeasurableSet A →
      (∀ᵐ l ∂νg, ∀ i, |l.2 i| ≤ H) →
      0 < h → (∀ t ∈ Icc t₀ (t₀ + h), |t| ≤ 1) →
      μ ≤ ENNReal.ofReal H • (νg.prod volume) →
      μ {p | p.1 ∈ A ∧ p.2 ∈ Icc t₀ (t₀ + h)}ᶜ = 0 →
      ENNReal.ofReal (h / H) * νg A ≤ μ univ → μ univ ≠ 0 →
      (∀ᵐ p ∂μ, ∀ t ∈ Icc t₀ (t₀ + h), ∀ i, |ubase z₀ h p.1 t i| ≤ H) →
      (∀ q : Fin 2 → ℤ, μ {p | (fun i => ⌊ubase z₀ h p.1 p.2 i / ξ⌋) = q} ≤
        ENNReal.ofReal (H * h * ξ ^ 2) * νg A) →
      (∀ (q : Fin 3 → ℤ) (c : ℤ), μ {p | physState δs p = q ∧ p.1.2 1 ∈ {v : ℝ | ⌊v / δv⌋ = c}} ≤
        ENNReal.ofReal H * μ {p | physState δs p = q} * πg {v : ℝ | ⌊v / δv⌋ = c}) →
      (∀ c : ℤ, πg {v : ℝ | ⌊v / δb⌋ = c} ≤ ENNReal.ofReal pang) →
      (∀ i, (𝒯 i).totalDegree ≤ D) → (∀ i b, |(𝒯 i).coeff b| ≤ H) →
      (∀ᵐ p ∂μ, ∀ t ∈ Icc t₀ (t₀ + h), |p.1.2 3 + 2 * t * p.1.2 4 -
        ∑ i : Fin 2, eval (ubase z₀ h p.1 t) (𝒯 i) * (![1, p.1.2 1] : Fin 2 → ℝ) i| ≤ εT) →
      (jointSupport μ z₀ h ξ w₁).Finite → ((jointSupport μ z₀ h ξ w₁).ncard : ℝ) ≤ Jb →
      1 ≤ H → 1 ≤ K₁ → 2 * H ≤ lam → 1 ≤ lam → 0 < δs → δs ≤ 1 → 0 < δv → 0 < δb → 0 < r →
      r + δv / 2 ≤ δb → 0 ≤ pang → 0 ≤ εT → 0 < ξ → ξ / lam ≤ 1 / 2 → 0 < w₁ →
      lam ^ (D + 1) * (((D + 1) ^ 2 : ℕ) * H) ≤ K → H + δv ≤ K → 1 / r ≤ K → 1 ≤ K →
      4 * max ((H + 1) * δs / (h * lam)) ((4 * H + 1) * δs / h) + 4 * (δv / 2) ≤ 1 / 2 →
      4 * (H / K₁) + 4 * (H * (3 * pang)) ≤ 1 / 2 →
      ∀ e : Fin 2 →₀ ℕ,
        |(pderiv 0 (scaleField lam (𝒯 1)) - pderiv 1 (scaleField lam (𝒯 0))).coeff e| ≤
          C * K ^ 4 * ((H * (H * K₁)) ^ 4 * lam ^ 4) ^ (6 * D + 1) * (H ^ 2 * lam ^ 2) ^ (2 * D) *
            (Jb * (2 * (ξ / (2 * lam) + (4 * max ((H + 1) * δs / (h * lam)) ((4 * H + 1) * δs / h) +
              4 * (δv / 2)))) ^ 2) *
            (w₁ / (2 * h) + (4 * (lam * εT + (1 + K) * (2 * C * K) *
              (4 * max ((H + 1) * δs / (h * lam)) ((4 * H + 1) * δs / h) + 4 * (δv / 2)) +
                K * (δv / 2)) + 3 * max ((H + 1) * δs / (h * lam)) ((4 * H + 1) * δs / h)) +
              max ((H + 1) * δs / (h * lam)) ((4 * H + 1) * δs / h)) / (1 / 2) ^ (6 * D + 1) +
          C * (lam ^ (D + 2) * (((D + 1) ^ 2 : ℕ) * (2 * (((D : ℝ) + 1) * H)))) * (ξ / lam) *
            ((H * (H * K₁)) ^ 4 * lam ^ 4) ^ (2 * D) * (H ^ 2 * lam ^ 2) ^ (2 * D) /
              (1 / 2) ^ (2 * D) := by
  obtain ⟨Ccov, hCcov, hcover⟩ := exists_path_cover_constant D
  obtain ⟨Ccurl, hCcurl, hcurl⟩ := exists_cell_curl_constant.{0, 0} D
  refine ⟨max Ccov Ccurl, lt_max_of_lt_left hCcov, ?_⟩
  intro νg _ πg _ μ A t₀ h z₀ 𝒯 H K₁ lam δs δv δb r pang εT ξ w₁ Jb K hA hbdd hh hblock
    hμdom hμsupp hμmass hμpos hu hcellcap hpal hang h𝒯deg h𝒯coeff hfield hJfin hJcard
    hH1 hK₁ hlamH hlam1 hδs hδs1 hδv hδb hr hrδ hpang hεT hξ hξlam hw₁ hKfield hKv hKr hK1
    hsmall hloss e
  set C := max Ccov Ccurl with hCdef
  set b := max ((H + 1) * δs / (h * lam)) ((4 * H + 1) * δs / h) with hbdef
  set ρE := ξ / (2 * lam) + (4 * b + 4 * (δv / 2)) with hρEdef
  set ε := w₁ / (2 * h) + (4 * (lam * εT + (1 + K) * (2 * C * K) * (4 * b + 4 * (δv / 2)) +
    K * (δv / 2)) + 3 * b) + b with hεdef
  set L := (H * (H * K₁)) ^ 4 * lam ^ 4 with hLdef
  set M := H ^ 2 * lam ^ 2 with hMdef
  set KP := lam ^ (D + 2) * (((D + 1) ^ 2 : ℕ) * (2 * (((D : ℝ) + 1) * H))) with hKPdef
  have hH0 : 0 ≤ H := by linarith
  have hK₁0 : 0 < K₁ := by linarith
  have hlam : 0 < lam := by linarith
  have hb : 0 ≤ b := le_max_of_le_right (by positivity)
  set I := Icc t₀ (t₀ + h) with hIdef
  -- the incidence measure is dominated by the restricted prior
  have hμdom₁ : μ ≤ ENNReal.ofReal H • ((νg.restrict A).prod volume) := by
    have hsuppA : μ (A ×ˢ univ)ᶜ = 0 := by
      apply measure_mono_null _ hμsupp
      intro p hp
      simp only [mem_compl_iff, mem_prod, mem_univ, and_true] at hp
      simp only [mem_compl_iff, mem_setOf_eq, not_and]
      exact fun h' => absurd h' hp
    have hrestrict : μ = μ.restrict (A ×ˢ univ) :=
      (Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hsuppA)).symm
    rw [hrestrict]
    calc
      μ.restrict (A ×ˢ univ) ≤ (ENNReal.ofReal H • (νg.prod volume)).restrict (A ×ˢ univ) :=
        Measure.restrict_mono le_rfl hμdom
      _ = ENNReal.ofReal H • ((νg.restrict A).prod volume) := by
        rw [Measure.restrict_smul, ← Measure.prod_restrict, Measure.restrict_univ]
  have hsuppI : μ (univ ×ˢ I)ᶜ = 0 := by
    apply measure_mono_null _ hμsupp
    intro p hp
    simp only [mem_compl_iff, mem_prod, mem_univ, true_and] at hp
    simp only [mem_compl_iff, mem_setOf_eq, not_and]
    exact fun _ h' => absurd h' hp
  -- disintegration over lines
  obtain ⟨hμfin, κ, hκ, hjoint, Llong, hLlong, hlong, hshort⟩ :=
    block_disintegration μ (νg.restrict A) (t₀ := t₀) (Hd := H) (q := h / K₁) hh
      (div_pos hh hK₁0) hμdom₁ hsuppI
  haveI := hμfin
  haveI := hκ
  set ν := μ.fst with hνdef
  have hjoint' : ν ⊗ₘ κ = μ := hjoint
  -- the rounded palette
  set control : (ℕ × (Fin 5 → ℝ)) → ℝ := fun l => vround δv (l.2 1) with hcontroldef
  have hcontrol : Measurable control := (measurable_vround δv).comp (measurable_pi_apply 1 |>.comp measurable_snd)
  set π' := πg.map (vround δv) with hπ'def
  have hπ'prob : IsProbabilityMeasure π' := inferInstance
  have hrect := rounded_palette_rect μ (physState δs) (measurable_physState δs)
    (fun p => p.1.2 1) (by fun_prop) πg (ENNReal.ofReal H) δv hpal
  have hrect' : ∀ q (S : Set ℝ), MeasurableSet S →
      (ν ⊗ₘ κ) {ω | physState δs ω = q ∧ control ω.1 ∈ S} ≤
        ENNReal.ofReal H * (ν ⊗ₘ κ) (physState δs ⁻¹' {q}) * π' S := by
    rw [hjoint']
    exact hrect
  have hthin := rounded_palette_thin πg hδv hδb hrδ (ENNReal.ofReal pang) hang
  -- the four-switch law
  obtain ⟨θ, hθfin, hθmass, hθdom, hθstates, hθrels, hθsep⟩ :=
    four_step_package ν κ (physState δs) (measurable_physState δs) control hcontrol π' Llong hLlong
      (ENNReal.ofReal H) (ENNReal.ofReal (H * h / (h / K₁))) (3 * ENNReal.ofReal pang) r h hh
      hrect' hthin hlong
  rw [hjoint'] at hθmass hθdom hθstates
  -- path coordinates, normalized and rescaled increments
  set obs : History (ℕ × (Fin 5 → ℝ)) → (((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) :=
    normalizeIncrements lam ∘ normalizeIncrements h ∘ actualPathCoordinates control with hobsdef
  have hobs : Measurable obs := (measurable_normalizeIncrements lam).comp
    ((measurable_normalizeIncrements h).comp (measurable_actualPathCoordinates control hcontrol))
  set νΘ : Measure (((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ)) :=
    μ.prod (Measure.pi fun _ : Fin 4 => π') with hνΘdef
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin 4 => π') := inferInstance
  have hνΘuniv : νΘ univ = μ univ := by
    rw [hνΘdef, ← univ_prod_univ, Measure.prod_prod,
      measure_univ (μ := Measure.pi fun _ : Fin 4 => π'), mul_one]
  haveI : IsFiniteMeasure νΘ := inferInstance
  haveI : NeZero νΘ := ⟨fun h0 => hμpos (by rw [← hνΘuniv, h0, Measure.coe_zero, Pi.zero_apply])⟩
  set ρ := θ.map obs with hρdef
  have hρeq : ρ = ((θ.map (actualPathCoordinates control)).map (normalizeIncrements h)).map
      (normalizeIncrements lam) := by
    rw [hρdef, Measure.map_map (measurable_normalizeIncrements lam)
        (measurable_normalizeIncrements h),
      Measure.map_map ((measurable_normalizeIncrements lam).comp (measurable_normalizeIncrements h))
        (measurable_actualPathCoordinates control hcontrol)]
    rfl
  have hρdom : ρ ≤ ENNReal.ofReal L • (νΘ.prod volume) := by
    have h1 := (map_normalizeIncrements_le νΘ _ _ lam hlam hθdom).1
    rw [← hρeq] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    have hHK : H * h / (h / K₁) = H * K₁ := by field_simp
    rw [hHK, ← ENNReal.ofReal_mul hH0, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  have hρuniv : ρ univ = θ univ := by
    rw [hρdef, Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
  -- the retained path mass is at least half the incidence mass
  have hμfinite : μ univ ≠ ⊤ := measure_ne_top _ _
  set m := (μ univ).toReal with hmdef
  have hm : 0 < m := ENNReal.toReal_pos hμpos hμfinite
  have hνA : νg A ≤ ENNReal.ofReal (H / h) * μ univ := by
    have h1 : ENNReal.ofReal (H / h) * (ENNReal.ofReal (h / H) * νg A) ≤
        ENNReal.ofReal (H / h) * μ univ := mul_le_mul_right hμmass _
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      show H / h * (h / H) = 1 by field_simp, ENNReal.ofReal_one, one_mul] at h1
    exact h1
  have hshort' : μ (Prod.fst ⁻¹' Llongᶜ) ≤ ENNReal.ofReal (H / K₁) * μ univ := by
    refine hshort.trans ?_
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    calc
      ENNReal.ofReal (h / K₁) * νg A ≤ ENNReal.ofReal (h / K₁) * (ENNReal.ofReal (H / h) * μ univ) :=
        mul_le_mul_right hνA _
      _ = ENNReal.ofReal (H / K₁) * μ univ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
  have hθhalf : ENNReal.ofReal (1 / 2 * m) ≤ θ univ := by
    have hθfinite : θ univ ≠ ⊤ := measure_ne_top _ _
    have hreal : m ≤ (θ univ).toReal + 4 * ((H / K₁) * m) + 4 * (H * (3 * pang)) * m := by
      have h1 := hθmass.trans (add_le_add (add_le_add le_rfl (mul_le_mul_right hshort' 4)) le_rfl)
      have hrhs : θ univ + 4 * (ENNReal.ofReal (H / K₁) * μ univ) +
          4 * (ENNReal.ofReal H * (3 * ENNReal.ofReal pang)) * μ univ =
          ENNReal.ofReal ((θ univ).toReal + 4 * ((H / K₁) * m) + 4 * (H * (3 * pang)) * m) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_toReal hθfinite,
          hmdef, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hμfinite, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hH0, ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hμfinite]
      rw [hrhs] at h1
      have h2 : ENNReal.ofReal m ≤ ENNReal.ofReal ((θ univ).toReal + 4 * ((H / K₁) * m) +
          4 * (H * (3 * pang)) * m) := by
        rw [hmdef, ENNReal.ofReal_toReal hμfinite]; exact h1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    have hθreal : 1 / 2 * m ≤ (θ univ).toReal := by
      have h3 : 4 * ((H / K₁) * m) + 4 * (H * (3 * pang)) * m ≤ 1 / 2 * m := by
        have := mul_le_mul_of_nonneg_right hloss hm.le
        linarith
      linarith
    calc
      ENNReal.ofReal (1 / 2 * m) ≤ ENNReal.ofReal (θ univ).toReal := ENNReal.ofReal_le_ofReal hθreal
      _ = θ univ := ENNReal.ofReal_toReal hθfinite
  -- the simulated start, controls and starting height
  set xs : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ) → Fin 2 → ℝ :=
    fun θ' d => ubase z₀ h θ'.1.1 θ'.1.2 d / lam with hxsdef
  have hxscont : Continuous xs := by
    apply continuous_pi
    intro d
    exact ((continuous_apply d).comp ((continuous_ubase z₀ h).comp continuous_fst)).div_const lam
  have hxs : Measurable xs := hxscont.measurable
  set vs : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ) → Fin 4 → ℝ := fun θ' => θ'.2 with hvsdef
  set X₀s : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ) → ℝ :=
    fun θ' => xL θ'.1.1 θ'.1.2 / h with hX₀sdef
  have hX₀cont : Continuous X₀s := (continuous_xL.comp continuous_fst).div_const h
  -- the joint cells
  set J := jointSupport μ z₀ h ξ w₁ with hJdef
  set F : Finset ((Fin 2 → ℤ) × ℤ) := hJfin.toFinset with hFdef
  set center : (Fin 2 → ℤ) → Fin 2 → ℝ := fun q d => ((q d : ℝ) + 1 / 2) * (ξ / lam)
    with hcenterdef
  set E : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ) → (Fin 2 → ℤ) × ℤ → Set (Fin 2 → ℝ) :=
    fun _ i => Icc (fun d => center i.1 d - ρE) (fun d => center i.1 d + ρE) with hEdef
  set cs : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ) → (Fin 2 → ℤ) × ℤ → ℝ :=
    fun _ i => ((i.2 : ℝ) + 1 / 2) * w₁ / h with hcsdef
  set At := scaleField lam (𝒯 0) with hAtdef
  set Bt := scaleField lam (𝒯 1) with hBtdef
  set S : Set ((((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ)) :=
    {z | z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1 ∧ xs z.1 ∈ halfBox ∧ (∀ i, |vs z.1 i| ≤ K) ∧
      1 / K ≤ |vs z.1 1 - vs z.1 0| ∧ 1 / K ≤ |vs z.1 3 - vs z.1 2| ∧
      ∃ i ∈ F, switchedBaseEndpoint (xs z.1) (vs z.1) z.2 ∈ E z.1 i ∧
        |X₀s z.1 + eval z.2 (brokenHeight At Bt (xs z.1) (vs z.1)) - cs z.1 i| ≤ ε} with hSdef
  have hSmeas : MeasurableSet S := by
    have hmap : Continuous fun z : (((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
        ((xs z.1, z.1.2, z.2) : (Fin 2 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
      (hxscont.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk
        continuous_snd)
    have hend : Continuous fun z : (((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
        switchedBaseEndpoint (xs z.1) (vs z.1) z.2 :=
      continuous_switchedBaseEndpoint.comp hmap
    have hbh := (continuous_brokenHeight_eval At Bt).comp hmap
    have hheight : Continuous fun z : (((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
        X₀s z.1 + eval z.2 (brokenHeight At Bt (xs z.1) (vs z.1)) :=
      (hX₀cont.comp continuous_fst).add hbh
    have hv (i : Fin 4) : Measurable fun z : (((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ)) ×
        (Fin 4 → ℝ) => vs z.1 i := by fun_prop
    have hset : S = {z | z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1} ∩ ({z | xs z.1 ∈ halfBox} ∩
        ((⋂ i, {z | |vs z.1 i| ≤ K}) ∩ ({z | 1 / K ≤ |vs z.1 1 - vs z.1 0|} ∩
          ({z | 1 / K ≤ |vs z.1 3 - vs z.1 2|} ∩
            ⋃ i ∈ F, ({z | switchedBaseEndpoint (xs z.1) (vs z.1) z.2 ∈ E z.1 i} ∩
              {z | |X₀s z.1 + eval z.2 (brokenHeight At Bt (xs z.1) (vs z.1)) - cs z.1 i| ≤ ε}))))) := by
      ext z
      simp only [hSdef, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop]
    rw [hset]
    refine (measurableSet_Icc.preimage measurable_snd).inter
      ((measurableSet_halfBox.preimage (hxs.comp measurable_fst)).inter
        ((MeasurableSet.iInter fun i => measurableSet_le (hv i).abs measurable_const).inter
          ((measurableSet_le measurable_const ((hv 1).sub (hv 0)).abs).inter
            ((measurableSet_le measurable_const ((hv 3).sub (hv 2)).abs).inter ?_))))
    refine Finset.measurableSet_biUnion F fun i _ => ?_
    exact (measurableSet_Icc.preimage hend.measurable).inter
      (measurableSet_le ((hheight.sub continuous_const).abs.measurable) measurable_const)
  -- good incidences
  set cellOf : (ℕ × (Fin 5 → ℝ)) × ℝ → (Fin 2 → ℤ) × ℤ :=
    fun p => ((fun i => ⌊ubase z₀ h p.1 p.2 i / ξ⌋), ⌊xL p.1 p.2 / w₁⌋) with hcellOfdef
  have hocc : ∀ᵐ p ∂μ, cellOf p ∈ J := by
    have hsub : {p | ¬ cellOf p ∈ J} ⊆ ⋃ q ∈ Jᶜ, cellOf ⁻¹' {q} := by
      intro p hp
      exact mem_biUnion (x := cellOf p) hp rfl
    apply ae_iff.mpr
    refine measure_mono_null hsub ((measure_biUnion_null_iff (Set.to_countable _)).mpr ?_)
    intro q hq
    have hq' : μ {p | (fun i => ⌊ubase z₀ h p.1 p.2 i / ξ⌋) = q.1 ∧ ⌊xL p.1 p.2 / w₁⌋ = q.2} = 0 := by
      simpa [hJdef, jointSupport] using hq
    have hpre : cellOf ⁻¹' {q} =
        {p | (fun i => ⌊ubase z₀ h p.1 p.2 i / ξ⌋) = q.1 ∧ ⌊xL p.1 p.2 / w₁⌋ = q.2} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, hcellOfdef, Prod.ext_iff]
    rw [hpre]
    exact hq'
  have hline : ∀ᵐ p ∂μ, ∀ i, |p.1.2 i| ≤ H := by
    have hbad : νg {l | ¬ ∀ i, |l.2 i| ≤ H} = 0 := ae_iff.mp hbdd
    apply ae_iff.mpr
    have hsub : {p : (ℕ × (Fin 5 → ℝ)) × ℝ | ¬ ∀ i, |p.1.2 i| ≤ H} ⊆
        {l | ¬ ∀ i, |l.2 i| ≤ H} ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp, mem_univ _⟩
    refine measure_mono_null hsub ?_
    have h1 := Measure.le_iff'.mp hμdom ({l | ¬ ∀ i, |l.2 i| ≤ H} ×ˢ (univ : Set ℝ))
    rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, hbad, zero_mul, mul_zero] at h1
    exact le_antisymm h1 bot_le
  have htimeI : ∀ᵐ p ∂μ, p.2 ∈ I := by
    filter_upwards [mem_ae_iff.mpr hsuppI] with p hp
    exact hp.2
  set Pgood : (ℕ × (Fin 5 → ℝ)) × ℝ → Prop := fun p => p.2 ∈ I ∧ (∀ i, |p.1.2 i| ≤ H) ∧
    (∀ t ∈ I, ∀ i, |ubase z₀ h p.1 t i| ≤ H) ∧
    (∀ t ∈ I, |p.1.2 3 + 2 * t * p.1.2 4 -
      ∑ i : Fin 2, eval (ubase z₀ h p.1 t) (𝒯 i) * (![1, p.1.2 1] : Fin 2 → ℝ) i| ≤ εT) ∧
    cellOf p ∈ J with hPgooddef
  have hgood : ∀ᵐ p ∂μ, Pgood p := by
    filter_upwards [htimeI, hline, hu, hfield, hocc] with p h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hpaths := hθstates Pgood hgood
  have hrels := hθrels (switchRel H δs) (measurableSet_switchRel H δs)
    (fun ω z hst => switchRel_of_state hH0 hδs hδs1 ω z hst)
  -- every retained path is successful
  have hKr' : 1 / K ≤ r := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < K)]
    rw [div_le_iff₀ hr] at hKr
    linarith
  have hCcovC : Ccov ≤ C := le_max_left _ _
  have hsucc : ∀ᵐ z ∂θ, obs z ∈ S := by
    filter_upwards [hpaths, hrels, hθsep] with z hz hrel hsep
    set ee : Fin 5 → (ℕ × (Fin 5 → ℝ)) × ℝ := ![z.1.1.1.1, z.1.1.1.2, z.1.1.2, z.1.2, z.2]
      with heedef
    have hee (k : Fin 5) : Pgood (ee k) := by
      fin_cases k
      · exact hz.1
      · exact hz.2.1
      · exact hz.2.2.1
      · exact hz.2.2.2.1
      · exact hz.2.2.2.2
    have heerel (j : Fin 4) : switchRel H δs (ee j.castSucc) (ee j.succ).1 := by
      fin_cases j
      · exact hrel.1
      · exact hrel.2.1
      · exact hrel.2.2.1
      · exact hrel.2.2.2
    have hres := hcover 𝒯 z₀ t₀ h lam H δs δv εT ξ w₁ K ee (cellOf (ee 4)).1 (cellOf (ee 4)).2
      h𝒯deg h𝒯coeff hh hlam1 hH0 hδs hδv hεT hξ hw₁ hlamH hKfield (by linarith) hsmall
      (fun k => (hee k).1) hblock (fun k => (hee k).2.1) (fun k => (hee k).2.2.1)
      (fun k => (hee k).2.2.2.1) heerel rfl rfl
    obtain ⟨hδbox, hxhalf, hvbd, hendp, hht⟩ := hres
    -- identify the observed coordinates
    have hobsz : obs z = ((z.1.1.1.1, fun j : Fin 4 => vround δv ((ee j.succ).1.2 1)),
        fun j : Fin 4 => ((ee j.succ).2 - (ee j.castSucc).2) / (h * lam)) := by
      simp only [hobsdef, Function.comp_apply, actualPathCoordinates_apply, normalizeIncrements]
      refine Prod.ext (Prod.ext rfl ?_) ?_
      · funext j
        fin_cases j <;> rfl
      · funext j
        fin_cases j <;> simp [heedef] <;> field_simp
    rw [hobsz]
    refine ⟨hδbox, hxhalf, fun j => (hvbd j).trans hKv, ?_, ?_, cellOf (ee 4), ?_, hendp, ?_⟩
    · exact hKr'.trans hsep.1
    · exact hKr'.trans hsep.2
    · exact (Set.Finite.mem_toFinset hJfin).mpr (hee 4).2.2.2.2
    · refine hht.trans ?_
      simp only [hεdef]
      gcongr
  -- the successful paths carry all the retained mass
  have hρS : ENNReal.ofReal (1 / 2 * (νΘ univ).toReal) ≤ ρ S := by
    rw [hνΘuniv, hρdef, Measure.map_apply hobs hSmeas]
    have hfull : θ (obs ⁻¹' S) = θ univ := by
      apply le_antisymm (measure_mono (subset_univ _))
      have hnull : θ (obs ⁻¹' S)ᶜ = 0 := by
        exact ae_iff.mp hsucc
      calc
        θ univ ≤ θ (obs ⁻¹' S) + θ (obs ⁻¹' S)ᶜ := measure_univ_le_add_compl _
        _ = θ (obs ⁻¹' S) := by rw [hnull, add_zero]
    rw [hfull]
    exact hθhalf
  -- floor-cell ceilings of the start law
  have hcellΘ : ∀ q : Fin 2 → ℤ, νΘ {θ' | (fun d => ⌊xs θ' d / (ξ / lam)⌋) = q} ≤
      ENNReal.ofReal (M * (ξ / lam) ^ 2 * (νΘ univ).toReal) := by
    intro q
    have hset : {θ' : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ) |
        (fun d => ⌊xs θ' d / (ξ / lam)⌋) = q} =
        {p : (ℕ × (Fin 5 → ℝ)) × ℝ | (fun i => ⌊ubase z₀ h p.1 p.2 i / ξ⌋) = q} ×ˢ univ := by
      ext θ'
      simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true, hxsdef]
      have hdiv (d : Fin 2) : ubase z₀ h θ'.1.1 θ'.1.2 d / lam / (ξ / lam) =
          ubase z₀ h θ'.1.1 θ'.1.2 d / ξ := by field_simp
      simp only [hdiv]
    rw [hset, hνΘdef, Measure.prod_prod, measure_univ (μ := Measure.pi fun _ : Fin 4 => π'),
      mul_one, ← hνΘdef, hνΘuniv]
    calc
      μ {p | (fun i => ⌊ubase z₀ h p.1 p.2 i / ξ⌋) = q} ≤ ENNReal.ofReal (H * h * ξ ^ 2) * νg A :=
        hcellcap q
      _ ≤ ENNReal.ofReal (H * h * ξ ^ 2) * (ENNReal.ofReal (H / h) * μ univ) :=
        mul_le_mul_right hνA _
      _ = ENNReal.ofReal (M * (ξ / lam) ^ 2 * m) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hmdef,
          ← ENNReal.ofReal_toReal hμfinite, ← ENNReal.ofReal_mul (by positivity),
          ENNReal.toReal_ofReal (ENNReal.toReal_nonneg)]
        congr 1
        simp only [hMdef]
        field_simp
  -- the endpoint cells
  have hEmeas : ∀ θ' (i : (Fin 2 → ℤ) × ℤ), i ∈ F → MeasurableSet (E θ' i) :=
    fun _ _ _ => measurableSet_Icc
  have hρE : 0 ≤ ρE := by positivity
  have hareaSum : ∀ θ', (∑ i ∈ F, volume (E θ' i)) ≤ ENNReal.ofReal (Jb * (2 * ρE) ^ 2) := by
    intro θ'
    have hvol : ∀ i ∈ F, volume (E θ' i) = ENNReal.ofReal (2 * ρE) ^ 2 :=
      fun i _ => volume_scalar_base_cell (center i.1) ρE
    rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hcard : (F.card : ℝ) = (J.ncard : ℝ) := by
      rw [hFdef, Set.ncard_eq_toFinset_card J hJfin]
    rw [hcard]
    exact hJcard
  -- data of the successful paths
  have hbox : ∀ z ∈ S, z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1 := fun z hz => hz.1
  have hdata : ∀ z ∈ S, xs z.1 ∈ halfBox ∧ (∀ i, |vs z.1 i| ≤ K) ∧
      1 / K ≤ |vs z.1 1 - vs z.1 0| ∧ 1 / K ≤ |vs z.1 3 - vs z.1 2| :=
    fun z hz => ⟨hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1⟩
  have hcov' : ∀ z ∈ S, ∃ i ∈ F, switchedBaseEndpoint (xs z.1) (vs z.1) z.2 ∈ E z.1 i ∧
      |X₀s z.1 + eval z.2 (brokenHeight At Bt (xs z.1) (vs z.1)) - cs z.1 i| ≤ ε :=
    fun z hz => hz.2.2.2.2.2
  -- the curl sup bound
  have hKP : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z (pderiv 0 Bt - pderiv 1 At)| ≤ KP :=
    fun z hz => scaleField_curl_eval_le hlam1 (𝒯 0) (𝒯 1) (h𝒯deg 0) (h𝒯deg 1) hH0
      (h𝒯coeff 0) (h𝒯coeff 1) z hz
  have hL1 : 1 ≤ L := by
    simp only [hLdef]
    have h1 : 1 ≤ H * (H * K₁) := one_le_mul_of_one_le_of_one_le hH1
      (one_le_mul_of_one_le_of_one_le hH1 hK₁)
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ hlam1)
  have hM1 : 1 ≤ M := by
    simp only [hMdef]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH1) (one_le_pow₀ hlam1)
  have hε0 : 0 ≤ ε := by positivity
  have hJb : 0 ≤ Jb := le_trans (Nat.cast_nonneg _) hJcard
  have hfinal := hcurl At Bt (scaleField_degree lam _ (h𝒯deg 0)) (scaleField_degree lam _ (h𝒯deg 1))
    K L M (1 / 2) (Jb * (2 * ρE) ^ 2) ε (ξ / lam) KP hK1 (by linarith) hM1 (by norm_num)
    (by linarith) (mul_nonneg hJb (by positivity)) hε0 (div_pos hξ hlam) hξlam (by positivity) hKP
    (((ℕ × (Fin 5 → ℝ)) × ℝ) × (Fin 4 → ℝ)) νΘ ρ S xs vs X₀s ((Fin 2 → ℤ) × ℤ) F E cs
    hxs hSmeas hcellΘ hρdom hρS hbox hdata hEmeas hareaSum hcov' e
  have hCcurlC : Ccurl ≤ C := le_max_right _ _
  refine hfinal.trans ?_
  gcongr

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
