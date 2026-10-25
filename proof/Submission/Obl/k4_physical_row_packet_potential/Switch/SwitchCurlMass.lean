-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/SwitchCurlMass.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The genuine six-switch experiment bounds the original mass of
large-curl starting incidences.

If the starts where the field `T` has curl above `θ` carried more than the
stated budget, `Submission.Lib.K4PolynomialNorming.actual_substantial_six_basis_switch_family`
would produce one actual start/control row and a set of signed durations of
volume above `Vbound`, all with certified direction bases and polynomial
endpoints in the enlarged original support. The six-leg volume bound
`six_switch_volume_of_large_skew` caps that volume by `Vbound`.
The support enlargement follows `exists_rectangular_target_enlargement_of_coordinate_error`
(`Submission.Lib.K4PolynomialNorming`, session x0001), with the target kept explicit.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.SixSwitchVolume
import Submission.Lib.K4PolynomialNorming.ActualSixSwitchSource
import Submission.Lib.K4PolynomialNorming.FieldCurlStart

set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory ProbabilityTheory MvPolynomial Matrix
open scoped ProbabilityTheory ENNReal
open Submission.Lib.K4PolynomialNorming Submission.Lib.K4CubicTests
open Submission.Lib.K4ScalarActualSwitching Submission.Lib.K4ScalarSwitching

theorem two_prod_bound {a b c e U : ℝ} (ha : |a| ≤ U) (hb : |b| ≤ U) (hc : |c| ≤ U)
    (he : |e| ≤ U) : |a * b - c * e| ≤ 2 * U ^ 2 := by
  have hU : 0 ≤ U := (abs_nonneg a).trans ha
  have h1 : |a * b| ≤ U * U := by rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hU
  have h2 : |c * e| ≤ U * U := by rw [abs_mul]; exact mul_le_mul hc he (abs_nonneg _) hU
  calc |a * b - c * e| ≤ |a * b| + |c * e| := abs_sub _ _
    _ ≤ U * U + U * U := add_le_add h1 h2
    _ = 2 * U ^ 2 := by ring

theorem two_prod_bound' {a b c e U : ℝ} (ha : |a| ≤ U) (hb : |b| ≤ U) (hc : |c| ≤ U)
    (he : |e| ≤ U) : |-(a * b) + c * e| ≤ 2 * U ^ 2 := by
  rw [show -(a * b) + c * e = c * e - a * b by ring]
  exact two_prod_bound hc he ha hb

/-- A `3 × 3` matrix with bounded entries and determinant floor has an inverse
with explicitly bounded entries. -/
theorem inv_fin_three_bound (M : Matrix (Fin 3) (Fin 3) ℝ) (U d : ℝ) (hd : 0 < d)
    (hM : ∀ i j, |M i j| ≤ U) (hdet : d ≤ |M.det|) :
    M * M⁻¹ = 1 ∧ ∀ i j, |M⁻¹ i j| ≤ 2 * U ^ 2 / d := by
  have hdet0 : M.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdet; linarith
  refine ⟨Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet0), ?_⟩
  have hadj : ∀ i j, |adjugate M i j| ≤ 2 * U ^ 2 := by
    intro i j
    rw [adjugate_fin_three]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, of_apply, cons_val',
        cons_val_zero, cons_val_one, cons_val_two, empty_val', cons_val_fin_one] <;>
      first
      | exact two_prod_bound (hM _ _) (hM _ _) (hM _ _) (hM _ _)
      | exact two_prod_bound' (hM _ _) (hM _ _) (hM _ _) (hM _ _)
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', abs_mul, abs_inv,
    inv_mul_eq_div]
  have hpos : 0 < |M.det| := lt_of_lt_of_le hd hdet
  calc |adjugate M i j| / |M.det| ≤ 2 * U ^ 2 / |M.det| :=
        div_le_div_of_nonneg_right (hadj i j) hpos.le
    _ ≤ 2 * U ^ 2 / d := div_le_div_of_nonneg_left (by positivity) hd hdet

/-- The doubled-width rectangular target, kept explicit. -/
def explicitTarget {ι : Type*} (I : Finset ι) (centers : ι → Fin 4 → ℝ) (widths : Fin 4 → ℝ) :
    Set ((Fin 3 → ℝ) × ℝ) :=
  {y | ∃ i ∈ I, ∀ j, |(splitHeadCoordinates 3).symm y j - centers i j| ≤ 2 * widths j}

theorem explicitTarget_measurable {ι : Type*} (I : Finset ι) (centers : ι → Fin 4 → ℝ)
    (widths : Fin 4 → ℝ) : MeasurableSet (explicitTarget I centers widths) := by
  classical
  have he : explicitTarget I centers widths =
      ⋃ i ∈ I, ⋂ j, {y | |(splitHeadCoordinates 3).symm y j - centers i j| ≤ 2 * widths j} := by
    ext y
    simp [explicitTarget]
  rw [he]
  refine Finset.measurableSet_biUnion _ (fun i _ => MeasurableSet.iInter (fun j => ?_))
  exact measurableSet_le (continuous_abs.measurable.comp
    (((measurable_pi_apply j).comp (splitHeadCoordinates 3).symm.measurable).sub_const _))
    measurable_const

theorem mem_explicitTarget_of_near {ι : Type*} (I : Finset ι) (centers : ι → Fin 4 → ℝ)
    (widths η : Fin 4 → ℝ) (hηr : ∀ j, η j ≤ widths j) (T : Set ((Fin 3 → ℝ) × ℝ))
    (hcover : ∀ y ∈ T, ∃ i ∈ I, ∀ j,
      |(splitHeadCoordinates 3).symm y j - centers i j| ≤ widths j)
    (x y : (Fin 3 → ℝ) × ℝ) (hy : y ∈ T)
    (hxy : ∀ j, |(splitHeadCoordinates 3).symm x j - (splitHeadCoordinates 3).symm y j| ≤ η j) :
    x ∈ explicitTarget I centers widths := by
  obtain ⟨i, hi, hiy⟩ := hcover y hy
  refine ⟨i, hi, fun j => ?_⟩
  calc |(splitHeadCoordinates 3).symm x j - centers i j|
      = |((splitHeadCoordinates 3).symm x j - (splitHeadCoordinates 3).symm y j) +
          ((splitHeadCoordinates 3).symm y j - centers i j)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ η j + widths j := add_le_add (hxy j) (hiy j)
    _ ≤ 2 * widths j := by linarith [hηr j]

theorem splitHead_symm_zero (y : (Fin 3 → ℝ) × ℝ) :
    (splitHeadCoordinates 3).symm y 0 = y.2 := by
  rw [show y = (y.1, y.2) from rfl, splitHeadCoordinates_symm_apply]
  rfl

theorem splitHead_symm_succ (y : (Fin 3 → ℝ) × ℝ) (a : Fin 3) :
    (splitHeadCoordinates 3).symm y a.succ = y.1 a := by
  rw [show y = (y.1, y.2) from rfl, splitHeadCoordinates_symm_apply]
  simp

end Submission.Obl.k4_physical_row_packet_potential.Switch

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory ProbabilityTheory MvPolynomial Matrix
open scoped ProbabilityTheory ENNReal
open Submission.Lib.K4PolynomialNorming Submission.Lib.K4CubicTests
open Submission.Lib.K4ScalarActualSwitching Submission.Lib.K4ScalarSwitching

/-- The retained-path weight of the six-switch experiment started on `w₀`. -/
noncomputable def sixSwitchWeight {L C : Type*} (w₀ : L × ℝ → ENNReal) (control : L → C)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set L) : (ℕ → L × ℝ) → ENNReal :=
  fun x => causalRetentionWeights w₀
    (basisPencilRetention (fun z => control z.1) v r (Prod.fst ⁻¹' Long)) 6
      (Preorder.frestrictLe 6 x)

/-- The normalized skew threshold of the six-switch contradiction. -/
noncomputable def switchSkewScale (r U θ : ℝ) : ℝ :=
  θ / (2 * ((3 : ℕ) : ℝ) ^ 2 * (2 * U ^ 2 / r ^ 3) * (2 * U ^ 2 / r ^ 3))

/-- Volume budget of the six-switch contradiction. -/
noncomputable def switchVolumeBound (D cNorm : ℕ) {ι : Type*} (I : Finset ι)
    (widths : Fin 4 → ℝ) (r U θ Λ : ℝ) : ENNReal :=
  ENNReal.ofReal Λ⁻¹ +
    (((I.card : ENNReal) * ∏ a : Fin 3, ENNReal.ofReal (4 * widths a.succ)) * 4) *
      ENNReal.ofReal (4 * (((D + 1 : ℕ) : ℝ) + 1) * (2 * widths 0) /
        (r ^ 3 * switchSkewScale r U θ / Λ ^ cNorm))

/-- The original mass of starts with curl above `θ` is at most the six-switch
budget. The inputs are those of `actual_six_switch_polynomial_source`, with
the large-curl indicator as starting weight. -/
theorem six_switch_large_curl_mass_le (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {L Q C ι : Type*} [MeasurableSpace L] [MeasurableSpace Q] [MeasurableSpace C]
      [MeasurableSingletonClass Q] [Countable Q]
      [MeasurableSingletonClass C] [Countable C] [StandardBorelSpace C] [Nonempty C]
      [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
      (ν : Measure L) [IsFiniteMeasure ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
      [IsProbabilityMeasure (ν ⊗ₘ κ)]
      (state : L × ℝ → Q) (hstate : Measurable state)
      (control : L → C) (hcontrol : Measurable control)
      (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r)
      (Long : Set L) (hLong : MeasurableSet Long)
      (μ : Measure (L × ℝ)) [SFinite μ] (π : Measure C) [SigmaFinite π]
      (K Dt p : ENNReal) (a h U : ℝ) (hh : 0 < h) (hU : 0 < U)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (T i).totalDegree ≤ D)
      (point : L × ℝ → (Fin 3 → ℝ) × ℝ) (hpoint : Measurable point)
      (θ : ℝ) (hθ : 0 < θ)
      (hzero : (ν ⊗ₘ κ).withDensity
        ((largeFieldCurlStart T (fun z => (point z).1) θ).indicator 1) ≤ μ)
      (hrect : ∀ q (A : Set C), MeasurableSet A →
        (ν ⊗ₘ κ) {z | state z = q ∧ control z.1 ∈ A} ≤
          K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
      (htime : ∀ l ∈ Long, κ l ≤ ((ENNReal.ofReal h)⁻¹ * Dt) • (volume : Measure ℝ))
      (hbroad : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
        Module.finrank ℝ W < 3 →
          (conditionalResampling (ν ⊗ₘ κ) state hstate z).map (fun y => control y.1)
            {c | Metric.infDist (v c) (W : Set _) < r} ≤ p)
      (ht : ∀ᵐ z ∂ν ⊗ₘ κ, z.2 ∈ Icc a (a + h))
      (hv : ∀ᵐ z ∂ν ⊗ₘ κ, ∀ j, |v (control z.1) j| ≤ U)
      (Target : Set ((Fin 3 → ℝ) × ℝ)) (hsupport : ∀ᵐ z ∂ν ⊗ₘ κ, point z ∈ Target)
      (I : Finset ι) (centers : ι → Fin 4 → ℝ) (widths : Fin 4 → ℝ)
      (η : Fin 4 → ℝ) (hηwidth : ∀ j, η j ≤ widths j)
      (hcover : ∀ y ∈ Target, ∃ i ∈ I, ∀ j,
        |(splitHeadCoordinates 3).symm y j - centers i j| ≤ widths j)
      (herror : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity
          (sixSwitchWeight ((largeFieldCurlStart T (fun z => (point z).1) θ).indicator 1)
            control v r Long),
        ∀ j, |(splitHeadCoordinates 3).symm
          (codedSixSwitchEndpoint T (fun z => (point z).1) v
            (sixSwitchCoordinates control a h x) + point (x 0)) j -
              (splitHeadCoordinates 3).symm (point (x 6)) j| ≤ η j)
      (Λ : ℝ) (hΛ : 2 ≤ Λ) (hwidth0 : 0 ≤ widths 0),
      (ν ⊗ₘ κ) (largeFieldCurlStart T (fun z => (point z).1) θ) ≤
        (K * Dt) ^ 6 * (μ.prod (Measure.pi (fun _ : Fin 6 => π))) univ *
            switchVolumeBound D cNorm I widths r U θ Λ +
          6 * ((ν ⊗ₘ κ) (Prod.fst ⁻¹' Long)ᶜ + p) := by
  obtain ⟨cNorm, hvol⟩ := six_switch_volume_of_large_skew D
  refine ⟨cNorm, ?_⟩
  intro L Q C ι _ _ _ _ _ _ _ _ _ _ _ ν _ κ _ _ state hstate control hcontrol v r hr Long hLong
    μ _ π _ K Dt p a h U hh hU T hT point hpoint θ hθ hzero hrect htime hbroad ht hv
    Target hsupport I centers widths η hηwidth hcover herror Λ hΛ hwidth0
  set Large := largeFieldCurlStart T (fun z => (point z).1) θ with hLargeDef
  have hLargem : MeasurableSet Large :=
    largeFieldCurlStart_measurable T _ (measurable_fst.comp hpoint) θ
  set w₀ : L × ℝ → ENNReal := Large.indicator 1 with hw₀Def
  have hw₀ : Measurable w₀ := measurable_one.indicator hLargem
  have hw₀1 : ∀ z, w₀ z ≤ 1 := by
    intro z
    by_cases hz : z ∈ Large
    · simp [w₀, hz]
    · simp [w₀, hz]
  have hwGood : ∀ z, w₀ z ≠ 0 → z ∈ Large := by
    intro z hz
    by_contra hn
    exact hz (by simp [w₀, hn])
  have hmass : ((ν ⊗ₘ κ).withDensity w₀) univ = (ν ⊗ₘ κ) Large := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_indicator hLargem]
    simp
  by_contra hlt
  have hlt' := lt_of_not_ge hlt
  let tgt := explicitTarget I centers widths
  let Fset : Set (((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ)) :=
    {z | codedSixSwitchEndpoint T (fun z => (point z).1) v z + point z.1.1 ∈ tgt}
  have hF : MeasurableSet Fset :=
    codedSixSwitchEndpoint_target_measurable T (fun z => (point z).1)
      (measurable_fst.comp hpoint) v (fun row => point row.1) (hpoint.comp measurable_fst)
      tgt (explicitTarget_measurable I centers widths)
  haveI := stateTimeSwitch_markov ν κ state hstate
  have hstates := kernelPathMeasure_weighted_ae_states (ν ⊗ₘ κ)
    (fun _ => stateTimeSwitch ν κ state hstate)
    (fun _ => stateTimeSwitch_invariant ν κ state hstate)
    (sixSwitchWeight w₀ control v r Long) (fun _ z => point z ∈ Target) (fun _ => hsupport)
  have htarget : ∀ᵐ x ∂(actualSwitchedPathMeasure ν κ state hstate).withDensity
      (sixSwitchWeight w₀ control v r Long), sixSwitchCoordinates control a h x ∈ Fset := by
    filter_upwards [hstates, herror] with x hx he
    exact mem_explicitTarget_of_near I centers widths η hηwidth Target hcover _ _ (hx 6) he
  obtain ⟨row, A, hAm, hvolA, hcert⟩ := actual_substantial_six_basis_switch_family
    ν κ state hstate control hcontrol v r hr Long hLong Large hLargem w₀ hw₀ hw₀1 hwGood
    μ π K Dt p (switchVolumeBound D cNorm I widths r U θ Λ) a h U hh hzero hrect htime
    hbroad ht hv Fset hF htarget (by rw [hmass]; exact hlt')
  -- A is nonempty, which fixes the row certificates
  have hAne : A.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, measure_empty] at hvolA
    exact (not_lt_of_ge bot_le) hvolA
  obtain ⟨δ0, hδ0⟩ := hAne
  obtain ⟨⟨hstart, hdets, hentries, _⟩, _⟩ := hcert δ0 hδ0
  set Am := directionBlockMatrix v row.2 0
  set Bm := directionBlockMatrix v row.2 1
  have hr3 : 0 < r ^ 3 := pow_pos hr 3
  obtain ⟨hAinv, hAibound⟩ := inv_fin_three_bound Am U (r ^ 3) hr3
    (fun i j => hentries 0 i j) (hdets 0)
  obtain ⟨hBinv, hBibound⟩ := inv_fin_three_bound Bm U (r ^ 3) hr3
    (fun i j => hentries 1 i j) (hdets 1)
  set Ua : ℝ := 2 * U ^ 2 / r ^ 3
  have hUa : 0 < Ua := by positivity
  have hscale : 2 * ((3 : ℕ) : ℝ) ^ 2 * Ua * Ua * switchSkewScale r U θ = θ := by
    simp only [switchSkewScale, Ua]
    field_simp
  have hskew : ∃ i j, 2 * ((3 : ℕ) : ℝ) ^ 2 * Ua * Ua * switchSkewScale r U θ <
      |eval (point row.1).1 (pderiv j (T i)) - eval (point row.1).1 (pderiv i (T j))| := by
    obtain ⟨i, j, hij⟩ := hstart
    exact ⟨i, j, by rw [hscale]; exact hij⟩
  have hsc : 0 < switchSkewScale r U θ := by
    simp only [switchSkewScale]
    positivity
  have hbound := hvol T hT (point row.1).1 Am Bm Am⁻¹ Bm⁻¹ hAinv hBinv Ua Ua (r ^ 3)
    (switchSkewScale r U θ) hUa.le hUa.le hr3 hsc hAibound hBibound (hdets 0) hskew Λ
    (2 * widths 0) hΛ (by linarith) A I
    (fun i a => centers i a.succ - 2 * widths a.succ - (point row.1).1 a)
    (fun i a => centers i a.succ + 2 * widths a.succ - (point row.1).1 a)
    (fun i => centers i 0 - (point row.1).2) hAm
    (by
      intro δ hδ k
      have hbox := (hcert δ hδ).1.2.2.2 k
      simpa only [MeasurableEquiv.symm_apply_apply] using hbox)
    (by
      intro δ hδ
      obtain ⟨i, hi, hij⟩ := (hcert δ hδ).2
      refine ⟨i, hi, ?_, ?_⟩
      · intro b
        have hb := hij b.succ
        rw [splitHead_symm_succ] at hb
        have hdisp := directionBlockMatrix_displacement v row.2
          ((splitHeadCoordinates 5).symm (splitHeadCoordinates 5 δ))
        rw [MeasurableEquiv.symm_apply_apply] at hdisp
        have hfst : (codedSixSwitchEndpoint T (fun z => (point z).1) v
            (row, splitHeadCoordinates 5 δ)).1 = fun b => ∑ i : Fin 6, δ i * v (row.2 i) b := by
          simp only [codedSixSwitchEndpoint, MeasurableEquiv.symm_apply_apply]
        have hval : (codedSixSwitchEndpoint T (fun z => (point z).1) v
            (row, splitHeadCoordinates 5 δ)).1 b =
            (Am *ᵥ (fun k => δ (selI k)) + Bm *ᵥ (fun k => δ (selJ k))) b := by
          rw [hfst, ← hdisp]
          rfl
        simp only [Prod.fst_add, Pi.add_apply] at hb
        rw [hval] at hb
        constructor <;> [linarith [(abs_le.mp hb).1]; linarith [(abs_le.mp hb).2]]
      · have hb := hij 0
        rw [splitHead_symm_zero] at hb
        have hsnd := codedSixSwitchEndpoint_height T (fun z => (point z).1) v
          (row, splitHeadCoordinates 5 δ)
        simp only [MeasurableEquiv.symm_apply_apply] at hsnd
        simp only [Prod.snd_add] at hb
        rw [hsnd] at hb
        have he : eval δ (twoBasisEndpointHeight T (point row.1).1 Am Bm) -
            (centers i 0 - (point row.1).2) =
            eval δ (twoBasisEndpointHeight T (point row.1).1 Am Bm) + (point row.1).2 -
              centers i 0 := by ring
        rw [he]
        exact hb)
  have hcalc : (∑ i ∈ I, ∏ b : Fin 3, ENNReal.ofReal
      ((centers i b.succ + 2 * widths b.succ - (point row.1).1 b) -
        (centers i b.succ - 2 * widths b.succ - (point row.1).1 b))) =
      (I.card : ENNReal) * ∏ b : Fin 3, ENNReal.ofReal (4 * widths b.succ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.cast_one, one_mul]
    apply Finset.prod_congr rfl
    intro b _
    congr 1
    ring
  rw [hcalc] at hbound
  exact (not_le_of_gt hvolA) hbound

end Submission.Obl.k4_physical_row_packet_potential.Switch
