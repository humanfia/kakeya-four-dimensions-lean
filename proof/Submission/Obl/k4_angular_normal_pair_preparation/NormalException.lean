-- Adapted from this LOT tree, o104, session x0472, commit 48795996,
-- Submission/Obl/k4_terminal_time_extension/NormalException.lean (the capped exceptional mass of
-- one source chart) and Saturation.lean (`measurable_obs`); and from o206, sessions x0709/x0753,
-- commit f0f3bdbb, Submission/Obl/k4_coarse_pair_frame_preparation/ObservationSection.lean
-- (observation-space measurability of old lists).
import Submission.Obl.k4_angular_normal_pair_preparation.NormalMeasure
import Submission.Obl.k4_angular_normal_pair_preparation.ObservationSection

/-!
# The angular normal-exception bound for one source chart (paper Lemma 3.5)

Fix a world and a source chart `b` of the old terminal system, on an old block of
length `2^-T₀` inside a new block `Icc a (a + ℓ)`.  For witness charts `b'`
whose velocity ellipse meets that of `b` only inside a closed ball of radius `ρ`
("exceptional" pairs: far normals), consider the incidences `p = (l, t)` of the
new block with

* `l` assigned to `b`, the extrapolated source test `R` small (`|R| ≤ ε`) with
  derivative floor `β` at `p`,
* `b'` in the terminal-observation list of `p`,
* the velocity of `l` in both velocity ellipses.

Under the joint terminal/angular density cap `G ≤ cap` (at velocity depth `δu`),
their total mass, summed over all exceptional witnesses, is at most

  `cap * ℓ π κ'² |det Q| * 16 (1 + B ε / (β δL)) * H * (4 ρ / δu + 2)²`,

with `κ' = κ + 2 κ 2^T₀ ℓ` and `H` the list size: the four factors are spatial
area, hidden bins, list multiplicity and velocity bins of the paper's estimate.
`source_exceptional_pairs` converts this into a bound for the two-time pair law.
-/

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Set MvPolynomial
open scoped ENNReal

theorem measurable_obs (B δ : ℝ) :
    Measurable (obs B δ : (ℕ × (Fin 6 → ℝ)) × ℝ → EuclideanSpace ℝ (Fin 3) × ℤ) := by
  have h1 : Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
      (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2] : EuclideanSpace ℝ (Fin 3))) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [x_def] <;> fun_prop
  have h2 : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => B * (x p.1 p.2) 3 / δ) := by
    have : Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => B * (x p.1 p.2) 3 / δ) := by
      simp only [x_def]
      fun_prop
    exact this.measurable
  exact h1.measurable.prodMk h2.floor

/-- The joint terminal/angular observation of the frozen angular cap. -/
noncomputable def angObs (B δL δu : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) :=
  (obs B δL p, fun i : Fin 2 => ⌊(v p.1) i / δu⌋)

theorem measurable_angObs (B δL δu : ℝ) :
    Measurable (angObs B δL δu : (ℕ × (Fin 6 → ℝ)) × ℝ → _) := by
  refine (measurable_obs B δL).prodMk ?_
  rw [measurable_pi_iff]
  intro i
  have hc : Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (v p.1) i / δu) := by
    fin_cases i <;> simp [v_def] <;> fun_prop
  exact hc.measurable.floor

/-- The exceptional incidences of source `b` with witness `b'`. -/
def excIncidences {ι : Type*} (A : Set (ℕ × (Fin 6 → ℝ))) (a ℓ : ℝ) (R : MvPolynomial (Fin 4) ℝ)
    (ε β B δL : ℝ) (lst : EuclideanSpace ℝ (Fin 3) × ℤ → Finset ι) (b' : ι)
    (V : Set (EuclideanSpace ℝ (Fin 2))) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {p | p.1 ∈ A ∧ p.2 ∈ Icc a (a + ℓ) ∧ |eval (x p.1 p.2) R| ≤ ε ∧
    β ≤ |eval (x p.1 p.2) (pderiv 3 R)| ∧ b' ∈ lst (obs B δL p) ∧ v p.1 ∈ V}

/-- **Capped exceptional mass of one source.** -/
theorem source_exceptional_capped {ι : Type*} [Fintype ι]
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (G : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ℝ≥0∞)
    {B δL δu : ℝ} (hB : 0 < B) (hδL : 0 < δL) (hδu : 0 < δu) (hG : Measurable G)
    (hmap : Measure.map (angObs B δL δu) μ =
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).prod
        Measure.count).withDensity G)
    {κ j₀ a ℓ ε β ρ H cap : ℝ} {T₀ : ℕ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hρ : 0 ≤ ρ) (hH : 0 ≤ H) (hcap : 0 ≤ cap)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) (A : Set (ℕ × (Fin 6 → ℝ)))
    (hbox : ∀ l ∈ A, ∀ t ∈ Icc (j₀ / (2 : ℝ) ^ T₀) ((j₀ + 1) / (2 : ℝ) ^ T₀),
      ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ)
    (ha : a ≤ j₀ / (2 : ℝ) ^ T₀) (hb : (j₀ + 1) / (2 : ℝ) ^ T₀ ≤ a + ℓ)
    (lst : EuclideanSpace ℝ (Fin 3) × ℤ → Finset ι)
    (hlst : ∀ o, ((lst o).card : ℝ) ≤ H)
    (hlstm : ∀ b', MeasurableSet {o | b' ∈ lst o})
    (Exc : ι → Prop) [DecidablePred Exc] (V : ι → Set (EuclideanSpace ℝ (Fin 2))) (w₀ : ι → EuclideanSpace ℝ (Fin 2))
    (hV : ∀ b', Exc b' → V b' ⊆ Metric.closedBall (w₀ b') ρ) :
    ∑ b' : {b' : ι // Exc b'}, μ (excIncidences A a ℓ R ε β B δL lst b' (V b') ∩
        {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap}) ≤
      ENNReal.ofReal (cap * ((ℓ * (Real.pi * (κ + 2 * κ * (2 : ℝ) ^ T₀ * ℓ) ^ 2 * |Q.det|)) *
        (16 * (1 + ε / (β * (δL / B))))) * H * (4 * ρ / δu + 2) ^ 2) := by
  classical
  set κ' : ℝ := κ + 2 * κ * (2 : ℝ) ^ T₀ * ℓ with hκ'
  have hκ'0 : 0 ≤ κ' := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
    by_cases hℓ : 0 ≤ ℓ
    · positivity
    · -- an empty new block: the old block cannot fit
      exfalso
      push Not at hℓ
      have hlt : j₀ / (2 : ℝ) ^ T₀ < (j₀ + 1) / (2 : ℝ) ^ T₀ :=
        div_lt_div_of_pos_right (by linarith) h2
      linarith
  have hh : 0 < δL / B := div_pos hδL hB
  set Y : Set (EuclideanSpace ℝ (Fin 3) × ℤ) :=
    (Prod.fst ⁻¹' boxCylinder a (a + ℓ) κ' c u Q) ∩ hidClosed R ε β (δL / B) with hY
  have hYm : MeasurableSet Y :=
    (measurable_fst (isClosed_boxCylinder _ _ _ c u Q).measurableSet).inter
      (measurableSet_hidClosed R ε β _)
  -- velocity bins of each exceptional witness
  set VB : ι → Set (Fin 2 → ℤ) := fun b' =>
    (fun w : EuclideanSpace ℝ (Fin 2) => fun i : Fin 2 => ⌊w i / δu⌋) '' V b' with hVB
  have hVBcard : ∀ b', Exc b' → (VB b').Finite ∧
      (((VB b').ncard : ℕ) : ℝ) ≤ (4 * ρ / δu + 2) ^ 2 :=
    fun b' hb' => velocity_bins_card_le hρ hδu (hV b' hb')
  -- each exceptional incidence observes into the product region
  have hsub : ∀ b' : {b' : ι // Exc b'},
      excIncidences A a ℓ R ε β B δL lst b' (V b') ∩
        {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap} ⊆
      angObs B δL δu ⁻¹' (((Y ∩ {o | (b' : ι) ∈ lst o}) ×ˢ VB b') ∩
        {q | G q ≤ ENNReal.ofReal cap}) := by
    rintro b' p ⟨⟨hpA, hpt, hval, hder, hlist, hvel⟩, hcapp⟩
    refine ⟨⟨⟨⟨?_, ?_⟩, hlist⟩, ?_⟩, hcapp⟩
    · -- spatial cylinder
      refine ⟨by simpa [angObs, obs_def] using hpt, ?_⟩
      have h := box_extrapolate (hbox p.1 hpA) ha hb hpt
      simpa [angObs, chartBox, Submission.Obl.k4_terminal_label_saturation.chartBox, obs_def, y_def, x_def] using h
    · -- closed hidden bin
      refine ⟨(x p.1 p.2) 3, ?_, ?_, ?_⟩
      · simp only [angObs, obs_def]
        set z := B * (x p.1 p.2) 3 / δL with hz
        have hfl1 := Int.floor_le z
        have hfl2 := Int.lt_floor_add_one z
        have hx3 : (x p.1 p.2) 3 = z * (δL / B) := by
          rw [hz]; field_simp
        rw [hx3]
        constructor
        · exact mul_le_mul_of_nonneg_right hfl1 hh.le
        · exact mul_le_mul_of_nonneg_right hfl2.le hh.le
      · have hxe : ![(angObs B δL δu p).1.1 0, (angObs B δL δu p).1.1 1,
            (angObs B δL δu p).1.1 2, (x p.1 p.2) 3] = x p.1 p.2 := by
          funext i
          fin_cases i <;> simp [angObs, obs_def, x_def]
        rw [hxe]; exact hval
      · have hxe : ![(angObs B δL δu p).1.1 0, (angObs B δL δu p).1.1 1,
            (angObs B δL δu p).1.1 2, (x p.1 p.2) 3] = x p.1 p.2 := by
          funext i
          fin_cases i <;> simp [angObs, obs_def, x_def]
        rw [hxe]; exact hder
    · exact ⟨v p.1, hvel, rfl⟩
  -- the capped density bound for one witness
  have hone : ∀ b' : {b' : ι // Exc b'},
      μ (excIncidences A a ℓ R ε β B δL lst b' (V b') ∩
        {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap}) ≤
      ENNReal.ofReal cap * (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        Measure.count) (Y ∩ {o | (b' : ι) ∈ lst o}) * ENNReal.ofReal ((4 * ρ / δu + 2) ^ 2)) := by
    intro b'
    obtain ⟨hfin, hcard⟩ := hVBcard b' b'.2
    have hZm : MeasurableSet (((Y ∩ {o | (b' : ι) ∈ lst o}) ×ˢ VB b') ∩
        {q | G q ≤ ENNReal.ofReal cap}) :=
      ((hYm.inter (hlstm b')).prod hfin.measurableSet).inter
        (measurableSet_le hG measurable_const)
    calc μ (excIncidences A a ℓ R ε β B δL lst b' (V b') ∩
          {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap})
        ≤ μ (angObs B δL δu ⁻¹' (((Y ∩ {o | (b' : ι) ∈ lst o}) ×ˢ VB b') ∩
            {q | G q ≤ ENNReal.ofReal cap})) := measure_mono (hsub b')
      _ = (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).prod
            Measure.count).withDensity G (((Y ∩ {o | (b' : ι) ∈ lst o}) ×ˢ VB b') ∩
              {q | G q ≤ ENNReal.ofReal cap}) := by
          rw [← hmap, Measure.map_apply (measurable_angObs B δL δu) hZm]
      _ = ∫⁻ q in ((Y ∩ {o | (b' : ι) ∈ lst o}) ×ˢ VB b') ∩ {q | G q ≤ ENNReal.ofReal cap},
            G q ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).prod
              Measure.count) := withDensity_apply _ hZm
      _ ≤ ∫⁻ _ in ((Y ∩ {o | (b' : ι) ∈ lst o}) ×ˢ VB b') ∩ {q | G q ≤ ENNReal.ofReal cap},
            ENNReal.ofReal cap ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
              Measure.count).prod Measure.count) :=
          setLIntegral_mono' hZm (fun q hq => hq.2)
      _ = ENNReal.ofReal cap * (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            Measure.count).prod Measure.count) (((Y ∩ {o | (b' : ι) ∈ lst o}) ×ˢ VB b') ∩
              {q | G q ≤ ENNReal.ofReal cap}) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal cap * (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            Measure.count).prod Measure.count) ((Y ∩ {o | (b' : ι) ∈ lst o}) ×ˢ VB b') :=
          mul_le_mul' le_rfl (measure_mono inter_subset_left)
      _ = ENNReal.ofReal cap * (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            Measure.count) (Y ∩ {o | (b' : ι) ∈ lst o}) * Measure.count (VB b')) := by
          rw [Measure.prod_prod]
      _ ≤ _ := by
          apply mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
          rw [Measure.count_apply_finite _ hfin, ← ENNReal.ofReal_natCast]
          apply ENNReal.ofReal_le_ofReal
          rw [← Set.ncard_eq_toFinset_card _ hfin]
          exact hcard
  -- list multiplicity
  have hlists : ∑ b' : {b' : ι // Exc b'},
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count)
        (Y ∩ {o | (b' : ι) ∈ lst o}) ≤
      ENNReal.ofReal H * ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count) Y := by
    set lam2 := (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure ℤ)
    have hm : ∀ b' : {b' : ι // Exc b'}, MeasurableSet (Y ∩ {o | (b' : ι) ∈ lst o}) :=
      fun b' => hYm.inter (hlstm b')
    calc ∑ b' : {b' : ι // Exc b'}, lam2 (Y ∩ {o | (b' : ι) ∈ lst o})
        = ∑ b' : {b' : ι // Exc b'}, ∫⁻ o, (Y ∩ {o | (b' : ι) ∈ lst o}).indicator 1 o ∂lam2 := by
          apply Finset.sum_congr rfl
          intro b' _
          exact (lintegral_indicator_one (hm b')).symm
      _ = ∫⁻ o, ∑ b' : {b' : ι // Exc b'}, (Y ∩ {o | (b' : ι) ∈ lst o}).indicator 1 o ∂lam2 :=
          (lintegral_finsetSum _ (fun b' _ => measurable_one.indicator (hm b'))).symm
      _ ≤ ∫⁻ o, Y.indicator (fun _ => ENNReal.ofReal H) o ∂lam2 := by
          apply lintegral_mono
          intro o
          by_cases hoY : o ∈ Y
          · rw [indicator_of_mem hoY]
            calc ∑ b' : {b' : ι // Exc b'}, (Y ∩ {o | (b' : ι) ∈ lst o}).indicator
                  (1 : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) o
                ≤ ∑ b' : {b' : ι // Exc b'}, ({o | (b' : ι) ∈ lst o}).indicator
                  (1 : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) o := by
                  apply Finset.sum_le_sum
                  intro b' _
                  exact indicator_le_indicator_of_subset inter_subset_right (fun _ => by simp) o
              _ = (((Finset.univ.filter (fun b' : {b' : ι // Exc b'} =>
                    (b' : ι) ∈ lst o)).card : ℕ) : ℝ≥0∞) := by
                  simp only [indicator_apply, mem_ofPred_eq, Pi.one_apply]
                  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
                    nsmul_eq_mul, mul_one]
              _ ≤ (((lst o).card : ℕ) : ℝ≥0∞) := by
                  have : (Finset.univ.filter (fun b' : {b' : ι // Exc b'} =>
                      (b' : ι) ∈ lst o)).card ≤ (lst o).card := by
                    refine Finset.card_le_card_of_injOn (fun b' => (b' : ι)) ?_ ?_
                    · intro b' hb'
                      simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hb'
                      exact hb'
                    · intro b₁ _ b₂ _ h12
                      exact Subtype.ext h12
                  exact_mod_cast this
              _ ≤ ENNReal.ofReal H := by
                  rw [← ENNReal.ofReal_natCast]
                  exact ENNReal.ofReal_le_ofReal (hlst o)
          · rw [indicator_of_notMem hoY]
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro b' _
            exact indicator_of_notMem (fun h => hoY h.1) _
      _ = ENNReal.ofReal H * lam2 Y := lintegral_indicator_const hYm _
  -- assemble
  have hY := volume_cylinder_hidClosed_le a (a + ℓ) κ' hκ'0 c u Q hQ R hR hε hβ hh
  calc ∑ b' : {b' : ι // Exc b'}, μ (excIncidences A a ℓ R ε β B δL lst b' (V b') ∩
          {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap})
      ≤ ∑ b' : {b' : ι // Exc b'}, ENNReal.ofReal cap *
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count)
            (Y ∩ {o | (b' : ι) ∈ lst o}) * ENNReal.ofReal ((4 * ρ / δu + 2) ^ 2)) :=
        Finset.sum_le_sum (fun b' _ => hone b')
    _ = ENNReal.ofReal cap * ENNReal.ofReal ((4 * ρ / δu + 2) ^ 2) *
          ∑ b' : {b' : ι // Exc b'}, ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            Measure.count) (Y ∩ {o | (b' : ι) ∈ lst o}) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b' _
        ring
    _ ≤ ENNReal.ofReal cap * ENNReal.ofReal ((4 * ρ / δu + 2) ^ 2) *
          (ENNReal.ofReal H * ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            Measure.count) Y) := mul_le_mul' le_rfl hlists
    _ ≤ ENNReal.ofReal cap * ENNReal.ofReal ((4 * ρ / δu + 2) ^ 2) *
          (ENNReal.ofReal H * ENNReal.ofReal ((a + ℓ - a) * (Real.pi * κ' ^ 2 * |Q.det|) *
            (16 * (1 + ε / (β * (δL / B)))))) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hY)
    _ = _ := by
        rw [← ENNReal.ofReal_mul hcap, ← ENNReal.ofReal_mul hH, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- The two-time pair law of a source restricted to a time set `J` at the source
time: its mass is `|J|` times the one-time mass at the witness time. -/
theorem pair_measure_eq {ν : Measure (ℕ × (Fin 6 → ℝ))} [SFinite ν] (J : Set ℝ)
    (hJ : MeasurableSet J) (Ω : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hΩ : MeasurableSet Ω) :
    (ν.prod ((volume : Measure ℝ).prod volume)) {p | p.2.1 ∈ J ∧ (p.1, p.2.2) ∈ Ω} =
      volume J * (ν.prod volume) Ω := by
  have hm : MeasurableSet {p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) | p.2.1 ∈ J ∧ (p.1, p.2.2) ∈ Ω} :=
    (measurable_fst.comp measurable_snd hJ).inter
      ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)) hΩ)
  rw [Measure.prod_apply hm, Measure.prod_apply hΩ,
    ← lintegral_const_mul _ (measurable_measure_prodMk_left hΩ)]
  apply lintegral_congr
  intro l
  have hs : Prod.mk l ⁻¹' {p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) | p.2.1 ∈ J ∧ (p.1, p.2.2) ∈ Ω} =
      J ×ˢ (Prod.mk l ⁻¹' Ω) := by
    ext q
    simp
  rw [hs, Measure.prod_prod]

/-- **Exceptional pairs of one source.**  The pairs whose source incidence lies in
`F` (inside the old block) and whose witness incidence is exceptional, in `E`
and below the angular density cap, have pair mass at most `2^-T₀` times the
bound of `source_exceptional_capped`. -/
theorem source_exceptional_pairs {ι : Type*} [Fintype ι]
    (ν : Measure (ℕ × (Fin 6 → ℝ))) [SFinite ν] (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hE : MeasurableSet E)
    (G : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ) → ℝ≥0∞)
    {B δL δu : ℝ} (hB : 0 < B) (hδL : 0 < δL) (hδu : 0 < δu) (hG : Measurable G)
    (hmap : Measure.map (angObs B δL δu) ((ν.prod volume).restrict E) =
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).prod
        Measure.count).withDensity G)
    {κ j₀ a ℓ ε β ρ H cap : ℝ} {T₀ : ℕ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hρ : 0 ≤ ρ) (hH : 0 ≤ H) (hcap : 0 ≤ cap)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) (A : Set (ℕ × (Fin 6 → ℝ)))
    (hAm : MeasurableSet A)
    (hbox : ∀ l ∈ A, ∀ t ∈ Icc (j₀ / (2 : ℝ) ^ T₀) ((j₀ + 1) / (2 : ℝ) ^ T₀),
      ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ)
    (ha : a ≤ j₀ / (2 : ℝ) ^ T₀) (hb : (j₀ + 1) / (2 : ℝ) ^ T₀ ≤ a + ℓ)
    (F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hF : ∀ p ∈ F, p.2 ∈ Icc (j₀ / (2 : ℝ) ^ T₀) ((j₀ + 1) / (2 : ℝ) ^ T₀))
    (lst : EuclideanSpace ℝ (Fin 3) × ℤ → Finset ι)
    (hlst : ∀ o, ((lst o).card : ℝ) ≤ H)
    (hlstm : ∀ b', MeasurableSet {o | b' ∈ lst o})
    (Exc : ι → Prop) [DecidablePred Exc] (V : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hVm : ∀ b', MeasurableSet (V b')) (w₀ : ι → EuclideanSpace ℝ (Fin 2))
    (hV : ∀ b', Exc b' → V b' ⊆ Metric.closedBall (w₀ b') ρ) :
    ∑ b' : {b' : ι // Exc b'}, (ν.prod ((volume : Measure ℝ).prod volume))
        {p | (p.1, p.2.1) ∈ F ∧ (p.1, p.2.2) ∈ excIncidences A a ℓ R ε β B δL lst b' (V b') ∧
          (p.1, p.2.2) ∈ E ∧ G (angObs B δL δu (p.1, p.2.2)) ≤ ENNReal.ofReal cap} ≤
      ENNReal.ofReal ((2 : ℝ) ^ T₀)⁻¹ *
      ENNReal.ofReal (cap * ((ℓ * (Real.pi * (κ + 2 * κ * (2 : ℝ) ^ T₀ * ℓ) ^ 2 * |Q.det|)) *
        (16 * (1 + ε / (β * (δL / B))))) * H * (4 * ρ / δu + 2) ^ 2) := by
  classical
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  set J := Icc (j₀ / (2 : ℝ) ^ T₀) ((j₀ + 1) / (2 : ℝ) ^ T₀) with hJdef
  have hJvol : volume J ≤ ENNReal.ofReal ((2 : ℝ) ^ T₀)⁻¹ := by
    rw [hJdef, Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    field_simp
    ring_nf
    rfl
  have hexcm : ∀ b', MeasurableSet (excIncidences A a ℓ R ε β B δL lst b' (V b')) := by
    intro b'
    have hcx (S : MvPolynomial (Fin 4) ℝ) :
        Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => eval (x p.1 p.2) S) := by
      have : Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => eval (x p.1 p.2) S) := by
        apply S.continuous_eval.comp
        apply continuous_pi
        intro i
        fin_cases i <;> simp [x_def] <;> fun_prop
      exact this.measurable
    have hvm : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => v p.1) := by
      have : Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => v p.1) := by
        apply (PiLp.continuous_toLp 2 _).comp
        apply continuous_pi
        intro i
        fin_cases i <;> simp <;> fun_prop
      exact this.measurable
    exact (measurable_fst hAm).inter ((measurable_snd measurableSet_Icc).inter
      ((measurableSet_le (hcx R).abs measurable_const).inter
        ((measurableSet_le measurable_const (hcx _).abs).inter
          (((measurable_obs B δL) (hlstm b')).inter (hvm (hVm b'))))))
  have hcapm : MeasurableSet {p : (ℕ × (Fin 6 → ℝ)) × ℝ | G (angObs B δL δu p) ≤ ENNReal.ofReal cap} :=
    measurableSet_le (hG.comp (measurable_angObs B δL δu)) measurable_const
  have hcapped := source_exceptional_capped ((ν.prod volume).restrict E) G hB hδL hδu hG hmap
    hκ hε hβ hρ hH hcap c u Q hQ R hR A hbox ha hb lst hlst hlstm Exc V w₀ hV
  calc ∑ b' : {b' : ι // Exc b'}, (ν.prod ((volume : Measure ℝ).prod volume))
        {p | (p.1, p.2.1) ∈ F ∧ (p.1, p.2.2) ∈ excIncidences A a ℓ R ε β B δL lst b' (V b') ∧
          (p.1, p.2.2) ∈ E ∧ G (angObs B δL δu (p.1, p.2.2)) ≤ ENNReal.ofReal cap}
      ≤ ∑ b' : {b' : ι // Exc b'}, volume J * ((ν.prod volume).restrict E)
          (excIncidences A a ℓ R ε β B δL lst b' (V b') ∩
            {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap}) := by
        apply Finset.sum_le_sum
        intro b' _
        have hΩm := ((hexcm b').inter hE).inter hcapm
        calc (ν.prod ((volume : Measure ℝ).prod volume))
              {p | (p.1, p.2.1) ∈ F ∧ (p.1, p.2.2) ∈ excIncidences A a ℓ R ε β B δL lst b' (V b') ∧
                (p.1, p.2.2) ∈ E ∧ G (angObs B δL δu (p.1, p.2.2)) ≤ ENNReal.ofReal cap}
            ≤ (ν.prod ((volume : Measure ℝ).prod volume))
              {p | p.2.1 ∈ J ∧ (p.1, p.2.2) ∈ (excIncidences A a ℓ R ε β B δL lst b' (V b') ∩ E) ∩
                {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap}} := by
              apply measure_mono
              rintro p ⟨hpF, hpX, hpE, hpG⟩
              exact ⟨hF _ hpF, ⟨hpX, hpE⟩, hpG⟩
          _ = volume J * (ν.prod volume) ((excIncidences A a ℓ R ε β B δL lst b' (V b') ∩ E) ∩
                {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap}) := pair_measure_eq J
                measurableSet_Icc _ hΩm
          _ = volume J * ((ν.prod volume).restrict E)
                (excIncidences A a ℓ R ε β B δL lst b' (V b') ∩
                  {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap}) := by
              rw [Measure.restrict_apply ((hexcm b').inter hcapm)]
              congr 2
              ext p
              simp only [mem_inter_iff, mem_ofPred_eq]
              tauto
    _ = volume J * ∑ b' : {b' : ι // Exc b'}, ((ν.prod volume).restrict E)
          (excIncidences A a ℓ R ε β B δL lst b' (V b') ∩
            {p | G (angObs B δL δu p) ≤ ENNReal.ofReal cap}) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul' hJvol hcapped

end Submission.Obl.k4_angular_normal_pair_preparation
