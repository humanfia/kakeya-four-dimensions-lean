import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpTransport
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpCover
set_option autoImplicit false

/-! Pulled-back transported laws, dyadic thickness arithmetic, and the per-chart
intermediate upper comparison: the new pure density at depth `s` is controlled by the old
pure density at depth `r + s`, up to the exact factor `|det Q| / ν(A)`. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion (x y v δ obs)

/-- The chart normalization on observations with an arbitrary discrete label. -/
noncomputable def labelChartEquiv (I' : Type*) [MeasurableSpace I'] (D t₀ : ℝ)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) (hD : 0 < D)
    (hQ : Q.det ≠ 0) : (EuclideanSpace ℝ (Fin 3) × I') ≃ᵐ (EuclideanSpace ℝ (Fin 3) × I') :=
  (chartAffEquiv D t₀ c u Q hD hQ).prodCongr (MeasurableEquiv.refl I')

theorem coe_labelChartEquiv (I' : Type*) [MeasurableSpace I'] {D t₀ : ℝ}
    (c u : EuclideanSpace ℝ (Fin 2)) {Q : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < D)
    (hQ : Q.det ≠ 0) :
    (labelChartEquiv I' D t₀ c u Q hD hQ : EuclideanSpace ℝ (Fin 3) × I' → _) =
      Prod.map (chartAff D t₀ c u Q) id := by
  funext o
  show (chartAffEquiv D t₀ c u Q hD hQ o.1, o.2) = (chartAff D t₀ c u Q o.1, o.2)
  rw [chartAffEquiv_apply]

theorem map_labelChartEquiv (I' : Type*) [MeasurableSpace I'] [MeasurableSingletonClass I']
    [Countable I'] {D t₀ : ℝ} (c u : EuclideanSpace ℝ (Fin 2))
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < D) (hQ : Q.det ≠ 0) :
    Measure.map (labelChartEquiv I' D t₀ c u Q hD hQ)
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure I')) =
      ENNReal.ofReal (|Q.det| / D) •
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure I') := by
  have h := Measure.map_prod_map (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (Measure.count : Measure I') (chartAffEquiv D t₀ c u Q hD hQ).measurable measurable_id
  rw [Measure.map_id, coe_chartAffEquiv, map_chartAff_volume hD c u hQ,
    Measure.prod_smul_left] at h
  rw [coe_labelChartEquiv, ← h]

/-- **Pulled-back transported law.** If the new observation of a transported incidence is
the chart image of an old observation `Jn`, then `|det Q| / ν(A)` times the law of `Jn`
under the old restricted selection has density `G ∘ chart`, where `G` is any density of
the new observation law. -/
theorem pullback_law {I' : Type*} [MeasurableSpace I'] [MeasurableSingletonClass I']
    [Countable I'] (ν : Measure Line) [IsFiniteMeasure ν] (A : Set Line)
    (θ : Line ≃ᵐ Line) {D t₀ : ℝ} (hD : 0 < D) {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (hνA : ν A ≠ 0)
    {E : Set Point} (hE : MeasurableSet E)
    (Onew : Point → EuclideanSpace ℝ (Fin 3) × I') (hOnew : Measurable Onew)
    (Jn : Point → EuclideanSpace ℝ (Fin 3) × I') (hJn : Measurable Jn)
    (hcomm : ∀ z, Onew (incEquiv θ D t₀ hD z) = (chartAff D t₀ c u Q (Jn z).1, (Jn z).2))
    {G : EuclideanSpace ℝ (Fin 3) × I' → ℝ≥0∞} (hG : Measurable G)
    (hlaw : Measure.map Onew ((((ν A)⁻¹ • Measure.map θ (ν.restrict A)).prod volume).restrict E)
      = ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity G) :
    (ENNReal.ofReal |Q.det| / ν A) •
        Measure.map Jn (((ν.restrict A).prod volume).restrict (incEquiv θ D t₀ hD ⁻¹' E)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity
        (fun p => G (chartAff D t₀ c u Q p.1, p.2)) := by
  set e := labelChartEquiv I' D t₀ c u Q hD hQ
  set ref := (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure I')
  set m := Measure.map Jn (((ν.restrict A).prod volume).restrict (incEquiv θ D t₀ hD ⁻¹' E))
  have hνA' : ν A ≠ ⊤ := measure_ne_top ν A
  -- the new law is `D / ν(A)` times the chart image of `m`
  have h1 : Measure.map e m = (ν A / ENNReal.ofReal D) • ref.withDensity G := by
    rw [← hlaw, selected_law_transport ν A θ hD hE, Measure.map_smul _ hOnew.aemeasurable,
      Measure.map_map hOnew (incEquiv θ D t₀ hD).measurable, smul_smul]
    have hfun : Onew ∘ (incEquiv θ D t₀ hD) = e ∘ Jn := by
      funext z
      simp only [Function.comp_apply, hcomm, e, coe_labelChartEquiv, Prod.map]
      rfl
    rw [hfun, ← Measure.map_map e.measurable hJn]
    have hc : ν A / ENNReal.ofReal D * (ENNReal.ofReal D / ν A) = 1 := by
      have hD0 : ENNReal.ofReal D ≠ 0 := by simpa using hD
      calc ν A / ENNReal.ofReal D * (ENNReal.ofReal D / ν A)
          = (ν A * (ν A)⁻¹) * (ENNReal.ofReal D * (ENNReal.ofReal D)⁻¹) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]; ring
        _ = 1 := by
            rw [ENNReal.mul_inv_cancel hνA hνA', ENNReal.mul_inv_cancel hD0 ENNReal.ofReal_ne_top,
              one_mul]
    rw [hc, one_smul]
  -- pull back along the chart equivalence
  set cP := ENNReal.ofReal (|Q.det| / D) with hcP
  have hcP0 : cP ≠ 0 := by
    rw [hcP, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos (abs_pos.mpr hQ) hD
  have hcPtop : cP ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsym : Measure.map e.symm ref = cP⁻¹ • ref := by
    have h2 : Measure.map e.symm (Measure.map e ref) = ref := e.map_symm_map
    have h3 : Measure.map e ref = cP • ref := map_labelChartEquiv I' c u hD hQ
    rw [h3, Measure.map_smul _ e.symm.measurable.aemeasurable] at h2
    calc Measure.map e.symm ref = cP⁻¹ • (cP • Measure.map e.symm ref) := by
          rw [smul_smul, ENNReal.inv_mul_cancel hcP0 hcPtop, one_smul]
      _ = cP⁻¹ • ref := by rw [h2]
  have hm : m = (ν A / ENNReal.ofReal D) •
      ref.withDensity (fun o => cP⁻¹ * G (e o)) := by
    have h3 : m = Measure.map e.symm (Measure.map e m) := e.map_symm_map.symm
    rw [h3, h1, Measure.map_smul _ e.symm.measurable.aemeasurable,
      map_equiv_withDensity ref e.symm _ hsym hG]
    rfl
  rw [hm, smul_smul, smul_withDensity_eq _ _ (f := fun o => cP⁻¹ * G (e o))
    ((hG.comp e.measurable).const_mul _)]
  congr 1
  funext o
  rw [← mul_assoc]
  have hconst : ENNReal.ofReal |Q.det| / ν A * (ν A / ENNReal.ofReal D) * cP⁻¹ = 1 := by
    have hcP' : cP = ENNReal.ofReal |Q.det| * (ENNReal.ofReal D)⁻¹ := by
      rw [hcP, ENNReal.ofReal_div_of_pos hD, div_eq_mul_inv]
    calc ENNReal.ofReal |Q.det| / ν A * (ν A / ENNReal.ofReal D) * cP⁻¹
        = (ν A * (ν A)⁻¹) * (ENNReal.ofReal |Q.det| * (ENNReal.ofReal D)⁻¹) * cP⁻¹ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ = 1 := by
          rw [ENNReal.mul_inv_cancel hνA hνA', one_mul, ← hcP',
            ENNReal.mul_inv_cancel hcP0 hcPtop]
  rw [hconst, one_mul, coe_labelChartEquiv]
  rfl


theorem delta_pos (N r : ℝ) : 0 < δ N r := by
  unfold δ; positivity

/-- The product of two dyadic thicknesses is the thickness of the sum, or twice it. -/
theorem delta_mul_delta (N r s : ℝ) :
    δ N r * δ N s = δ N (r + s) ∨ δ N r * δ N s = 2 * δ N (r + s) := by
  unfold δ
  set a := r * Real.log N / Real.log 2
  set b := s * Real.log N / Real.log 2
  have hab : (r + s) * Real.log N / Real.log 2 = a + b := by
    simp only [a, b]; ring
  rw [hab, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have h1 : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := Int.le_floor_add a b
  have h2 : ⌊a + b⌋ ≤ ⌊a⌋ + ⌊b⌋ + 1 := by
    have := Int.le_floor_add_floor a b
    omega
  rcases (show ⌊a + b⌋ = ⌊a⌋ + ⌊b⌋ ∨ ⌊a + b⌋ = ⌊a⌋ + ⌊b⌋ + 1 by omega) with h | h
  · left; rw [h]; congr 1; ring
  · right
    rw [h, show -(⌊a⌋ : ℤ) + -⌊b⌋ = -(⌊a⌋ + ⌊b⌋ + 1) + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm]

/-- The hidden label at a thickness `a ∈ {f, 2f}` determines the label at `f` up to `±1`. -/
theorem hidden_label_offset {a f : ℝ} (hf : 0 < f) (ha : a = f ∨ a = 2 * f) (B w w' : ℝ)
    (h : ⌊B * w / a⌋ = ⌊B * w' / a⌋) :
    ⌊B * w' / f⌋ - ⌊B * w / f⌋ ∈ ({-1, 0, 1} : Finset ℤ) := by
  rcases ha with rfl | rfl
  · rw [h, sub_self]; simp
  · set y := B * w / f
    set y' := B * w' / f
    have hy : B * w / (2 * f) = y / 2 := by simp only [y]; field_simp
    have hy' : B * w' / (2 * f) = y' / 2 := by simp only [y']; field_simp
    rw [hy, hy'] at h
    set m := ⌊y / 2⌋
    have h1 := Int.floor_le (y / 2)
    have h2 := Int.lt_floor_add_one (y / 2)
    have h3 := Int.floor_le (y' / 2)
    have h4 := Int.lt_floor_add_one (y' / 2)
    rw [← h] at h3 h4
    have k1 : 2 * m ≤ ⌊y⌋ := Int.le_floor.mpr (by push_cast; linarith)
    have k2 : ⌊y⌋ < 2 * m + 2 := Int.floor_lt.mpr (by push_cast; linarith)
    have k3 : 2 * m ≤ ⌊y'⌋ := Int.le_floor.mpr (by push_cast; linarith)
    have k4 : ⌊y'⌋ < 2 * m + 2 := Int.floor_lt.mpr (by push_cast; linarith)
    have : ⌊y'⌋ - ⌊y⌋ = -1 ∨ ⌊y'⌋ - ⌊y⌋ = 0 ∨ ⌊y'⌋ - ⌊y⌋ = 1 := by omega
    rcases this with h5 | h5 | h5 <;> rw [h5] <;> simp


theorem measurable_chartAff (D t₀ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Measurable (chartAff D t₀ c u Q) := by
  have h : chartAff D t₀ c u Q =
      fun w => Matrix.toEuclideanLin (chartMatrix D u Q) w + chartShift D t₀ c Q :=
    funext (chartAff_eq D t₀ c u Q)
  rw [h]
  exact ((LinearMap.continuous_of_finiteDimensional _).measurable).add_const _

/-- A restricted law below a full law has an a.e. smaller density. -/
theorem density_le_of_law_le {α : Type*} [MeasurableSpace α] (ref : Measure α) [SigmaFinite ref]
    {f g : α → ℝ≥0∞} (hf : Measurable f) {m m' : Measure α} (hmm : m ≤ m')
    (hm : m = ref.withDensity f) (hm' : m' = ref.withDensity g) : f ≤ᵐ[ref] g := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf
  intro Y hY _
  rw [← withDensity_apply _ hY, ← withDensity_apply _ hY, ← hm, ← hm']
  exact hmm Y

theorem prod_restrict_le (ν : Measure Line) [IsFiniteMeasure ν] (A : Set Line) (S : Set Point) :
    ((ν.restrict A).prod volume).restrict S ≤ (ν.prod volume).restrict S := by
  have h : (ν.restrict A).prod (volume : Measure ℝ) = (ν.prod volume).restrict (A ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [h]
  exact Measure.restrict_mono subset_rfl Measure.restrict_le_self


/-- **Intermediate upper comparison for one chart.** At new depth `s`, the new pure density
exceeds `3 |det Q| / ν(A)` times `X₀` only on a set whose new mass is at most
`6 D / ν(A)` times the old prior mass, on the pulled-back selection, of the event that the
old pure density at depth `r + s` exceeds `X₀`. -/
theorem chart_pure_upper (ν : Measure Line) [IsFiniteMeasure ν] (A : Set Line)
    (θ : Line ≃ᵐ Line) {D t₀ : ℝ} (hD : 0 < D) {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (hνA : ν A ≠ 0)
    (hy : ∀ l t, y (θ l) t =
      Matrix.toEuclideanLin Q⁻¹ (y l (t₀ + t / D) - c - (t₀ + t / D) • u))
    (hx : ∀ l t, x (θ l) t 3 = x l (t₀ + t / D) 3)
    {E : Set Point} (hE : MeasurableSet E) {Eold : Set Point}
    (hsub : incEquiv θ D t₀ hD ⁻¹' E ⊆ Eold) (B N r s : ℝ)
    {g : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞}
    (hglaw : Measure.map (obs B (δ N (r + s))) ((ν.prod volume).restrict Eold) =
      obsRef.withDensity g)
    {G : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞} (hG : Measurable G)
    (hGlaw : Measure.map (obs (B / δ N r) (δ N s))
      ((((ν A)⁻¹ • Measure.map θ (ν.restrict A)).prod volume).restrict E) =
        obsRef.withDensity G)
    (X₀ : ℝ≥0∞) :
    ((((ν A)⁻¹ • Measure.map θ (ν.restrict A)).prod volume).restrict E)
        {z | ENNReal.ofReal |Q.det| / ν A * (3 * X₀) < G (obs (B / δ N r) (δ N s) z)} ≤
      ENNReal.ofReal D / ν A * (6 * ((ν.prod volume).restrict (incEquiv θ D t₀ hD ⁻¹' E))
        {z | X₀ < g (obs B (δ N (r + s)) z)}) := by
  classical
  set e := incEquiv θ D t₀ hD
  set S := e ⁻¹' E with hS
  have hSm : MeasurableSet S := e.measurable hE
  set μS := ((ν.restrict A).prod volume).restrict S with hμS
  set Jf := obs B (δ N (r + s))
  set Jn := obs B (δ N r * δ N s)
  set cc := ENNReal.ofReal |Q.det| / ν A
  have hJf : Measurable Jf := measurable_obs _ _
  have hJn : Measurable Jn := measurable_obs _ _
  -- the old fine density of the pulled-back selection
  have hμS_le : μS ≤ (ν.prod volume).restrict Eold :=
    (prod_restrict_le ν A S).trans (Measure.restrict_mono hsub le_rfl)
  have habs : Measure.map Jf μS ≪ obsRef := by
    refine Measure.AbsolutelyContinuous.mk fun Y hY hY0 => ?_
    have h1 : Measure.map Jf ((ν.prod volume).restrict Eold) Y = 0 := by
      rw [hglaw]; exact withDensity_absolutelyContinuous _ _ hY0
    exact le_antisymm ((Measure.map_mono hμS_le hJf Y).trans h1.le) zero_le
  set H := (Measure.map Jf μS).rnDeriv obsRef
  have hH : Measurable H := Measure.measurable_rnDeriv _ _
  have hlawH : Measure.map Jf μS = obsRef.withDensity H :=
    (Measure.withDensity_rnDeriv_eq _ _ habs).symm
  -- the new density in old continuous coordinates
  have hcomm : ∀ z, obs (B / δ N r) (δ N s) (e z) =
      (chartAff D t₀ c u Q (Jn z).1, (Jn z).2) := fun z =>
    obs_incEquiv hD hy hx (delta_pos N r).ne' (delta_pos N s).ne' z
  have hlawG := pullback_law ν A θ hD hQ hνA hE (obs (B / δ N r) (δ N s))
    (measurable_obs _ _) Jn hJn hcomm hG hGlaw
  -- labels
  have hOff : ∀ z z', (Jn z).2 = (Jn z').2 → (Jf z').2 - (Jf z).2 ∈ ({-1, 0, 1} : Finset ℤ) := by
    intro z z' h
    exact hidden_label_offset (delta_pos N (r + s)) (delta_mul_delta N r s) B _ _ h
  have hcover := cover_bad_mass μS (volume : Measure (EuclideanSpace ℝ (Fin 3))) Jf hJf Jn hJn
    (fun z => rfl) hH hlawH (hG.comp ((measurable_chartAff D t₀ c u Q).prodMap measurable_id))
    cc hlawG
    ({-1, 0, 1} : Finset ℤ) hOff X₀
  have hcard : ((({-1, 0, 1} : Finset ℤ).card : ℕ) : ℝ≥0∞) = 3 := by
    rw [show ({-1, 0, 1} : Finset ℤ).card = 3 by rfl]; norm_num
  rw [hcard] at hcover
  -- the old fine density is below the full old density
  have hHg : H ≤ᵐ[obsRef] g := density_le_of_law_le obsRef hH
    (Measure.map_mono hμS_le hJf) hlawH hglaw
  have hHg' : ∀ᵐ z ∂μS, H (Jf z) ≤ g (Jf z) :=
    ae_of_ae_map hJf.aemeasurable (habs.ae_le hHg)
  have hold : μS {z | X₀ < H (Jf z)} ≤ (ν.prod volume).restrict S {z | X₀ < g (Jf z)} := by
    calc μS {z | X₀ < H (Jf z)} ≤ μS {z | X₀ < g (Jf z)} := by
          apply measure_mono_ae
          filter_upwards [hHg'] with z hz hlt
          exact lt_of_lt_of_le hlt hz
      _ ≤ _ := prod_restrict_le ν A S _
  -- back to the new incidences
  have hbad : MeasurableSet {z : Point | cc * (3 * X₀) < G (obs (B / δ N r) (δ N s) z)} :=
    measurableSet_lt measurable_const (hG.comp (measurable_obs _ _))
  rw [selected_law_transport ν A θ hD hE, Measure.smul_apply,
    Measure.map_apply e.measurable hbad, smul_eq_mul]
  have hpre : e ⁻¹' {z : Point | cc * (3 * X₀) < G (obs (B / δ N r) (δ N s) z)} =
      {z | cc * (3 * X₀) < (fun p => G (chartAff D t₀ c u Q p.1, p.2)) (Jn z)} := by
    ext z
    simp only [mem_preimage, mem_ofPred_eq]
    rw [hcomm z]
  rw [hpre]
  gcongr
  calc μS {z | cc * (3 * X₀) < (fun p => G (chartAff D t₀ c u Q p.1, p.2)) (Jn z)}
      ≤ 2 * 3 * μS {z | X₀ < H (Jf z)} := hcover
    _ ≤ 2 * 3 * (ν.prod volume).restrict S {z | X₀ < g (Jf z)} := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp
