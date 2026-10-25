import Submission.Obl.k4_fixed_budget_quadratic_recovery.PosteriorInterface
import Submission.Obl.k4_fixed_budget_quadratic_recovery.NormalCover
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GroupAtlas
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ObservedCandidates
import Submission.Obl.k4_fixed_budget_quadratic_recovery.RecoveryNumerics
import Submission.Obl.k4_fixed_budget_quadratic_recovery.SourceComponents

set_option maxHeartbeats 800000

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set Filter

/-- Scalar mesh projection and finite posterior recovery give the complete
fixed-budget geometric atlas at the supplied original observation. -/
theorem fixed_budget_recovery_of_posterior
    (hmesh : ScalarMeshProjection) (hpost : PosteriorBinRecovery) :
    FixedBudgetQuadraticRecovery := by
  classical
  intro d s m S U hd hd1 hs hs1 hsm hS hU hUm
  obtain ⟨e, he, R₀, hR₀, hposterior⟩ := hpost d hd hd1
  let θ := min e (1 / 8)
  have hθ : 0 < θ := lt_min he (by norm_num)
  have hθe : θ ≤ e := min_le_left _ _
  have hθ8 : θ ≤ 1 / 8 := min_le_right _ _
  let c := s * θ / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hcs : c < s := by
    have hmul := mul_le_mul_of_nonneg_left hθ8 hs.le
    dsimp [c]
    nlinarith only [hmul, hs]
  refine ⟨c, hc, lt_min hcs (hcs.trans hs1), 3 ^ 6, 4, by norm_num, ?_⟩
  intro ε hε hε1
  let a := min (ε / 20) (s * θ / 100)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haκ : a ≤ s * θ / 100 := min_le_right _ _
  have haε : a < ε := by have := min_le_left (ε / 20) (s * θ / 100); dsimp [a]; linarith
  have ha1 : a ≤ 1 := haε.le.trans hε1
  obtain ⟨δ, hδ, hδκ, hδa, η₀, hη₀, hη₀δ, N₁, hN₁, hcover⟩ :=
    finite_scalar_fit_cover_normalized hmesh hd hd1 hs hs1 hsm hS hU hUm hcs
      (κ := s * θ / 100) (by positivity) ha ha1
  let η := min (η₀ / 10) (s * θ / 100)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηκ : η ≤ s * θ / 100 := min_le_right _ _
  have hηη₀ : η < η₀ := by have := min_le_left (η₀ / 10) (s * θ / 100); dsimp [η]; linarith
  have hηδ : η ≤ δ := hηη₀.le.trans hη₀δ
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    ((eventually_recovery_bounds hs hθ hθe ha.le haκ haε hδκ hηκ hηη₀).and
      ((tendsto_rpow_atTop hs).eventually_ge_atTop R₀))
  refine ⟨η, hη, max N₁ N₂, hN₁.trans (le_max_left _ _), ?_⟩
  intro N hN ν μ b O base signal hlaw hmass hO hbase hsignal hobs
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hNN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  have hNtwo : 2 ≤ N := hN₁.trans hNN₁
  have hNone : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have := hlaw.1.isFiniteMeasure
  obtain ⟨⟨hRange, hAgreement, hSeparation, hBad, hResidual, hCoefficient, hRounding⟩, hScale⟩ := hN₂ N hNN₂
  obtain ⟨n, P, A, hn, hP, hdisj, hres, hfitbudget⟩ :=
    hcover N hNN₁ η hηη₀.le (ℕ × (Fin 6 → ℝ)) ν μ b hlaw.1
  choose F hF hFc using fun i => exists_quadratic_coefficients (hP i).1 (hP i).2.1
  let R := N ^ s
  let Y := 2 * N ^ η
  let H := N ^ a
  let τ := 2 * (N ^ δ * N ^ (-s))
  let K := 7 * N ^ (η + δ - d * s)
  let ρ := N ^ (-(s * θ / 2))
  let base' : (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ × ℝ :=
    fun o => ((base o) 0, (base o) 1)
  have hbase' : Measurable base' := by fun_prop
  have hY : 1 ≤ Y := by
    have := Real.one_le_rpow hNone hη.le
    dsimp [Y]
    linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 0 ≤ H := Real.rpow_nonneg hNpos.le a
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hNpos _
  have hpow (z : ℝ) : R ^ z = N ^ (s * z) := by
    dsimp [R]
    rw [← Real.rpow_mul hNpos.le]
  have hsθ : 0 < s * θ := mul_pos hs hθ
  have hse : s * θ ≤ s * e := mul_le_mul_of_nonneg_left hθe hs.le
  have hnR : (n : ℝ) ≤ R ^ (d + e) := by
    rw [hpow]
    apply hn.trans (Real.rpow_le_rpow_of_exponent_le hNone ?_)
    nlinarith only [haκ, hse, hsθ]
  have hYeq : 6 * H * Y ^ 2 = 24 * N ^ (a + 2 * η) := by
    have hp : (N ^ η) ^ (2 : ℕ) = N ^ (2 * η) := by
      rw [← Real.rpow_mul_natCast hNpos.le]
      congr 1
      ring
    dsimp [H, Y]
    rw [mul_pow, hp, Real.rpow_add hNpos]
    ring
  have hFY : 6 * H * Y ^ 2 ≤ R ^ e := by rw [hYeq, hpow]; exact hRange
  have hτ : 2 * τ ≤ R ^ (-1 + e) := by
    rw [hpow]
    have hp : N ^ δ * N ^ (-s) = N ^ (δ - s) := by
      rw [← Real.rpow_add hNpos]
      congr 1
    dsimp [τ]
    rw [hp]
    linarith only [hAgreement]
  have hsep : 864 * R ^ (-e) ≤ ρ := by
    rw [hpow]
    simpa only [mul_neg] using hSeparation
  let C : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun i => {p | b p.1 ∈ A i}
  have hCm : ∀ i, MeasurableSet (C i) := fun i =>
    (hlaw.1.1.comp measurable_fst) (hP i).2.2.1
  have hCd : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p hp hq => Set.disjoint_left.mp (hdisj hij) hp hq)
  let comp := observedComponents μ C O
  have hcomp (i : Fin n) : IsFiniteMeasure (comp i) := observedComponents_isFinite μ C O i
  letI : ∀ i, IsFiniteMeasure (comp i) := hcomp
  let Good : Fin n → (EuclideanSpace ℝ (Fin 3) × ℤ) → Prop := fun i o =>
    (base' o).1 ∈ Icc (0 : ℝ) 1 ∧ |(base' o).2| ≤ Y ∧
      |signal o - quadraticValue (F i) (base' o).1 (base' o).2| ≤ τ
  have hGood : ∀ i, MeasurableSet {o | Good i o} := by
    intro i
    have hq : Measurable (fun o => quadraticValue (F i) (base' o).1 (base' o).2) := by
      unfold quadraticValue
      fun_prop
    exact (measurableSet_Icc.preimage hbase'.fst).inter
      ((measurableSet_le hbase'.snd.abs measurable_const).inter
        (measurableSet_le ((hsignal.sub hq).abs) measurable_const))
  have hsamples : ∀ᵐ p ∂μ, ∀ i, p ∈ C i → Good i (O p) := by
    have hraw := scalarFit_observed_samples hlaw O base signal hobs P F hF A
      (fun i => (hP i).2.2.2.2)
    have herr := observation_error_le_scalar_fit hNone hηδ hs1.le
    filter_upwards [hraw] with p hp
    intro i hi
    obtain ⟨ht, hy, hv⟩ := hp i hi
    refine ⟨ht, hy, hv.trans ?_⟩
    dsimp [τ]
    linarith only [herr]
  have hagree : ∀ i, ∀ᵐ o ∂comp i, Good i o :=
    observedComponents_ae μ C hCm O hO Good hGood (fun i => hsamples.mono (fun p hp => hp i))
  have hmarg : ∀ i E, MeasurableSet E →
      comp i (base' ⁻¹' E) ≤ ENNReal.ofReal K * volume E := by
    intro i E hE
    have hh := scalarFit_observed_marginal_cap_power hNone hs.le hδ.le hlaw O base
      (hobs.mono (fun p hp => hp.1)) (P i) (A i) (hP i).2.2.2.2 E hE
    change (μ.restrict (C i)).map O (base' ⁻¹' E) ≤ _
    rw [Measure.map_apply hO (hbase' hE), Measure.restrict_apply (hO (hbase' hE))]
    have hset : O ⁻¹' (base' ⁻¹' E) ∩ C i =
        {p | b p.1 ∈ A i ∧ base' (O p) ∈ E} := by ext p; simp [C, and_comm]
    rw [hset]
    exact hh
  obtain ⟨L, hLm, hLcard, hLmass⟩ :=
    hposterior R hScale n comp hcomp base' signal F Y H τ K ρ hbase' hsignal
      hY hK hH hρ hnR hFc hFY hτ hsep hagree hmarg
  have hloss : (n : ℝ) * K * (2 * Y) * R ^ (-2 * e) ≤ N ^ (-η) / 4 := by
    calc
      _ ≤ N ^ (d * s + a) * K * (2 * Y) * R ^ (-2 * e) := by gcongr
      _ = 28 * N ^ (a + δ + 2 * η - 2 * s * e) := by
        dsimp [K, Y]
        rw [hpow]
        calc
          _ = 28 * (N ^ (d * s + a) * N ^ (η + δ - d * s) * N ^ η * N ^ (s * (-2 * e))) := by ring
          _ = 28 * N ^ ((d * s + a) + (η + δ - d * s) + η + s * (-2 * e)) := by
            rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          _ = _ := by congr 2; ring
      _ ≤ _ := by linarith only [hBad]
  let U₀ : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := ⋃ i, C i
  have hU₀m : MeasurableSet U₀ := MeasurableSet.iUnion hCm
  have hres' : μ.real U₀ᶜ < N ^ (-η₀) := by
    convert hres using 2
    ext p
    simp [U₀, C]
  have hcovered : μ.real U₀ = μ.real univ - μ.real U₀ᶜ := by
    have hh := measureReal_compl hU₀m (μ := μ)
    linarith
  have htotal := observedComponents_total_real μ C hCm hCd O hO
  change (∑ i, comp i).real univ = μ.real U₀ at htotal
  rw [htotal, hcovered] at hLmass
  have hmassreal : N ^ (-η) ≤ μ.real univ := by
    have hh := ENNReal.toReal_mono (measure_ne_top μ univ) hmass
    simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg hNpos.le _), measureReal_def] using hh
  have hsuccess : μ.real univ / 2 ≤ ∑ i, (comp i).real {o | coefficientBin ρ (F i) ∈ L o} := by
    linarith only [hLmass, hres'.le, hResidual, hloss, hmassreal]
  have hcenter : ∀ i j, |binCoefficients ρ (coefficientBin ρ (F i)) j| ≤ H + ρ := by
    intro i j
    have h₁ := hFc i j
    have h₂ := coefficientBin_error hρ (F i) j
    rw [abs_le] at h₁ h₂ ⊢
    constructor <;> linarith only [h₁, h₂]
  obtain ⟨k, Q, B, lst, hkn, hQ, hBd, hlst, hlstm, hEq⟩ :=
    grouped_scalar_atlas (Real.one_le_rpow hNone hη.le) hρ.le (by positivity : 0 ≤ H + ρ)
      (pow_nonneg hNpos.le 7) b hlaw.1.2.2.2.2.1 O P F hF A
      (fun i => (hP i).2.2.2.1) (fun i => (hP i).2.2.2.2) hdisj
      (fun i => coefficientBin ρ (F i)) (binCoefficients ρ) hcenter
      (fun i => coefficientBin_error hρ (F i)) L hLcard hLm
  have hn2 : (n : ℝ) ≤ N ^ (2 : ℕ) := by
    have hds : d * s ≤ 1 := by nlinarith only [hd, hd1, hs, hs1]
    convert hn.trans (Real.rpow_le_rpow_of_exponent_le hNone (show d * s + a ≤ 2 by linarith only [hds, ha1])) using 1 <;> norm_num
  have hformat : 10 + (n : ℝ) * N ^ (7 : ℕ) ≤ N ^ (3 ^ 6 : ℕ) :=
    (grouped_format_count hNtwo hn2).trans (pow_le_pow_right₀ hNone (by norm_num : 13 ≤ (3 ^ 6 : ℕ)))
  have hfinalfit : N ^ δ * N ^ (-s) + 24 * ρ * (N ^ η) ^ 2 ≤ N ^ (-c) := by
    dsimp [ρ, c]
    linarith only [hfitbudget, hRounding]
  have hsource := observedComponents_success_real μ C hCm hCd O hO
    (fun i => coefficientBin ρ (F i)) L hLm
  change (∑ i, (comp i).real {o | coefficientBin ρ (F i) ∈ L o}) =
    μ.real {p | ∃ i, b p.1 ∈ A i ∧ coefficientBin ρ (F i) ∈ L (O p)} at hsource
  have hsuccess' : μ.real univ / 2 ≤ μ.real {p | ∃ j, b p.1 ∈ B j ∧ j ∈ lst (O p)} := by
    rw [← hEq, ← hsource]
    exact hsuccess
  refine ⟨k, Q, B, lst, ?_, ?_, hBd, hlst, hlstm, ?_⟩
  · exact (show (k : ℝ) ≤ n by exact_mod_cast hkn).trans
      (hn.trans (Real.rpow_le_rpow_of_exponent_le hNone (by linarith)))
  · intro j
    obtain ⟨hdeg, hcoeff, hmeas, hfmt, hfit⟩ := hQ j
    refine ⟨hdeg, fun f => (hcoeff f).trans hCoefficient, hmeas, ?_, ?_⟩
    · exact Submission.Obl.k4_finite_width_output_exclusion.fmt_mono hformat hfmt
    · intro z hz t ht
      exact (hfit hz t ht).trans hfinalfit
  · apply (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top μ _)).mp
    have hh : (1 / 2 : ℝ) * μ.real univ ≤
        μ.real {p | ∃ j, b p.1 ∈ B j ∧ j ∈ lst (O p)} := by linarith only [hsuccess']
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      measureReal_def] using hh

end Submission.Obl.k4_fixed_budget_quadratic_recovery
