import Mathlib
import ChallengeDeps
import Submission.Obl.k4_original_prior_line_extraction.LineJets
import Submission.Obl.k4_original_prior_line_extraction.WindowLaw
import Submission.Obl.k4_original_prior_line_extraction.JetEvents
import Submission.Obl.k4_original_prior_line_extraction.JetSelection
import Submission.Obl.k4_original_prior_line_extraction.Parameters

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_original_prior_line_extraction
set_option linter.unusedVariables false

/-!
# `Submission.k4_original_prior_line_extraction`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_original_prior_line_extraction`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_original_prior_line_extraction/`
belong to this obligation.
-/

theorem Submission.k4_original_prior_line_extraction : ∀ (V : Finset (EuclideanSpace ℝ (Fin 3))) (K J : ℕ), (∀ v ∈ V, ‖v‖ = 1) → 1 ≤ K → K < J → ∀ (B : ℕ → ℝ) (c η : ℝ), (∀ m : ℕ, m ≤ J + 1 → 0 < B m) → 0 < c → 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ → ∀ (n₁ n₂ : ℕ) (F₁ : Fin n₁ → EuclideanSpace ℝ (Fin 3) → ℝ) (F₂ : Fin n₂ → EuclideanSpace ℝ (Fin 3) → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))), (∀ (i : Fin n₁) (v : EuclideanSpace ℝ (Fin 3)), v ∈ V → ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (3 : ℝ) / 4 → ContDiffOn ℝ (J + 1) (fun t : ℝ => F₁ i (x + t • v)) (Set.Ioo (-1 : ℝ) 1)) → (∀ (i : Fin n₂) (v : EuclideanSpace ℝ (Fin 3)), v ∈ V → ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (3 : ℝ) / 4 → ContDiffOn ℝ (J + 1) (fun t : ℝ => F₂ i (x + t • v)) (Set.Ioo (-1 : ℝ) 1)) → (∀ (i : Fin n₁) (v : EuclideanSpace ℝ (Fin 3)), v ∈ V → ∀ m : ℕ, m ≤ J + 1 → ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => iteratedDeriv m (fun t : ℝ => F₁ i (x + t • v)) 0) (Metric.ball 0 1)) → (∀ (i : Fin n₂) (v : EuclideanSpace ℝ (Fin 3)), v ∈ V → ∀ m : ℕ, m ≤ J + 1 → ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => iteratedDeriv m (fun t : ℝ => F₂ i (x + t • v)) 0) (Metric.ball 0 1)) → (∀ (i : Fin n₁) (v : EuclideanSpace ℝ (Fin 3)), v ∈ V → ∀ m : ℕ, m ≤ J + 1 → ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (3 : ℝ) / 4 → |iteratedDeriv m (fun t : ℝ => F₁ i (x + t • v)) 0| ≤ B m * (M * R ^ ε)) → (∀ (i : Fin n₂) (v : EuclideanSpace ℝ (Fin 3)), v ∈ V → ∀ m : ℕ, m ≤ J + 1 → ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (3 : ℝ) / 4 → |iteratedDeriv m (fun t : ℝ => F₂ i (x + t • v)) 0| ≤ B m * (M * R ^ ε)) → (∀ i, 0 ≤ π₁ i) → (∀ i, 0 ≤ π₂ i) → (∑ i, π₁ i) = 1 → (∑ i, π₂ i) = 1 → ENNReal.ofReal (R ^ (-ε)) ≤ μ Set.univ → μ Set.univ ≤ 1 → (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₁ i) * MeasureTheory.volume U) → (∀ (i : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₂ i) * MeasureTheory.volume U) → μ {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧ |F₁ p.1.1 p.2 - F₂ p.1.2 p.2| ≤ M * R ^ (-1 + ε) ∧ c * (M * R ^ (-ε)) ≤ ∑ v ∈ V, ∑ j ∈ Finset.range (K + 1), |iteratedDeriv j (fun t : ℝ => F₁ p.1.1 (p.2 + t • v) - F₂ p.1.2 (p.2 + t • v)) 0|}ᶜ = 0 → ∃ (g₁ : Fin n₁ → ℝ → ℝ) (g₂ : Fin n₂ → ℝ → ℝ) (ν : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (∀ i, ContDiffOn ℝ (J + 1) (g₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ i, ContDiffOn ℝ (J + 1) (g₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ (i : Fin n₁) (m : ℕ), m ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m (g₁ i) t| ≤ R ^ η) ∧ (∀ (i : Fin n₂) (m : ℕ), m ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m (g₂ i) t| ≤ R ^ η) ∧ MeasureTheory.IsProbabilityMeasure ν ∧ (∀ (i : Fin n₁) (U : Set ℝ), MeasurableSet U → ν {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ η * π₁ i) * MeasureTheory.volume U) ∧ (∀ (i : Fin n₂) (U : Set ℝ), MeasurableSet U → ν {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ η * π₂ i) * MeasureTheory.volume U) ∧ ν {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |g₁ p.1.1 p.2 - g₂ p.1.2 p.2| ≤ R ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ R ^ (-η) ≤ |iteratedDeriv j (g₁ p.1.1) p.2 - iteratedDeriv j (g₂ p.1.2) p.2|}ᶜ = 0 := by
  classical
  intro V K J hV hK hKJ B c η hB hc hη
  let D : ℝ := (V.card : ℝ) + 1
  let A : ℝ := ∑ m ∈ Finset.range (J + 2), B m
  let b : ℝ := c / (4 * D * (K + 1))
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro m hm
    exact (hB m (by have := Finset.mem_range.mp hm; omega)).le
  have hBA (m : ℕ) (hm : m ≤ J + 1) : B m ≤ A := by
    apply Finset.single_le_sum
    · intro j hj
      exact (hB j (by have := Finset.mem_range.mp hj; omega)).le
    · exact Finset.mem_range.mpr (by omega)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbr : 0 < windowStep ^ K * b := mul_pos (pow_pos windowStep_pos K) hb
  obtain ⟨ε₀, hε₀, R₀, hR₀, hnum⟩ := extraction_parameters
    D A (D * windowVolume) (windowStep ^ K * b) c η hD.le hA
      (mul_nonneg hD.le windowVolume_pos.le) hbr hc hη
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M ε hR hM hε hεsmall n₁ n₂ F₁ F₂ π₁ π₂ μ
    hF₁ hF₂ hcont₁ hcont₂ hder₁ hder₂ hπ₁ hπ₂ hsum₁ hsum₂
    hmass hmassOne hcap₁ hcap₂ hsupp
  letI : IsFiniteMeasure μ := ⟨lt_of_le_of_lt hmassOne (by simp)⟩
  have hRtwo : 2 ≤ R := hR₀.trans hR
  have hRone : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hpow : 0 < R ^ ε := Real.rpow_pos_of_pos hRpos _
  have hpowneg : 0 < R ^ (-ε) := Real.rpow_pos_of_pos hRpos _
  obtain ⟨hzero, hupper, hmarg, hlower, hεη⟩ := hnum R ε hR hε hεsmall
  let E : Base → Set ((Fin n₁ × Fin n₂) × Base) :=
    fun v => jetEvent F₁ F₂ v K (M * R ^ (-1 + ε)) (b * (M * R ^ (-ε)))
  have hcover : ∀ᵐ p ∂μ, p ∈ ⋃ v ∈ V, E v := by
    filter_upwards [hsupp] with p hp
    have hx : ‖p.2‖ ≤ (3 : ℝ) / 4 := hp.1.trans (by norm_num)
    have hsmall : D * (M * R ^ (-1 + ε)) ≤ c * (M * R ^ (-ε)) / 2 := by
      calc
        D * (M * R ^ (-1 + ε)) = M * (D * R ^ (-1 + ε)) := by ring
        _ ≤ M * ((c / 2) * R ^ (-ε)) := mul_le_mul_of_nonneg_left hzero hM.le
        _ = c * (M * R ^ (-ε)) / 2 := by ring
    obtain ⟨v, hv, j, hj₁, hjK, hgap⟩ := finite_jet_witness V K
      (fun v j => iteratedDeriv j
        (fun t : ℝ => F₁ p.1.1 (p.2 + t • v) - F₂ p.1.2 (p.2 + t • v)) 0)
      hc (mul_pos hM hpowneg) (by positivity)
      (fun v hv => by simpa using hp.2.1) hsmall hp.2.2
    have hjJ : j ≤ J + 1 := by omega
    have hdiff := Submission.Obl.k4_matching_switching_target_certificate.iteratedDeriv_sub_of_isOpen
      (n := j) isOpen_Ioo
      ((hF₁ p.1.1 v hv p.2 hx).of_le (by exact_mod_cast hjJ))
      ((hF₂ p.1.2 v hv p.2 hx).of_le (by exact_mod_cast hjJ))
      (x := (0 : ℝ)) (by norm_num)
    have hdiff' : iteratedDeriv j
        (fun t : ℝ => F₁ p.1.1 (p.2 + t • v) - F₂ p.1.2 (p.2 + t • v)) 0 =
        iteratedDeriv j (fun t : ℝ => F₁ p.1.1 (p.2 + t • v)) 0 -
          iteratedDeriv j (fun t : ℝ => F₂ p.1.2 (p.2 + t • v)) 0 := hdiff
    rw [hdiff'] at hgap
    have hgap' : b * (M * R ^ (-ε)) ≤
        |iteratedDeriv j (fun t : ℝ => F₁ p.1.1 (p.2 + t • v)) 0 -
          iteratedDeriv j (fun t : ℝ => F₂ p.1.2 (p.2 + t • v)) 0| := by
      simpa only [b, D] using hgap
    refine mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, ?_⟩⟩
    exact (jetEvent_iff F₁ F₂ v K _ _ p).mpr ⟨hp.1, hp.2.1, j, hj₁, hjK, hgap'⟩
  obtain ⟨v, hv, hEmass⟩ := select_mass_event μ V E hcover hpowneg hmass
  have hvunit : ‖v‖ = 1 := hV v hv
  have hE : MeasurableSet (E v) := measurableSet_jetEvent F₁ F₂ v K _ _
    (fun i m hm => hcont₁ i v hv m (by omega))
    (fun i m hm => hcont₂ i v hv m (by omega))
  have hEball (p : (Fin n₁ × Fin n₂) × Base) (hp : p ∈ E v) :
      ‖p.2‖ ≤ (1 : ℝ) / 2 := ((jetEvent_iff F₁ F₂ v K _ _ p).mp hp).1
  obtain ⟨y, hy, ν, hνprob, hν₁, hν₂, hνsupp⟩ := extract_window_law
    μ π₁ π₂ hπ₁ hπ₂ hsum₁ hpow (div_pos hpowneg hD)
      hcap₁ hcap₂ hE hEball hEmass v hvunit
  let g₁ : Fin n₁ → ℝ → ℝ := fun i => lineFunction (F₁ i) v y M
  let g₂ : Fin n₂ → ℝ → ℝ := fun i => lineFunction (F₂ i) v y M
  have hy' : ‖y‖ ≤ (3 : ℝ) / 4 := hy.trans (by norm_num)
  have hcoeff : windowVolume * R ^ ε / (R ^ (-ε) / D) =
      (D * windowVolume) * R ^ (2 * ε) := by
    rw [Real.rpow_neg hRpos.le]
    have hpne : R ^ ε ≠ 0 := hpow.ne'
    have hppow : R ^ (2 * ε) = R ^ ε * R ^ ε := by
      rw [← Real.rpow_add hRpos]
      congr 1
      ring
    rw [hppow]
    field_simp
    <;> ring
  refine ⟨g₁, g₂, ν, ?_, ?_, ?_, ?_, hνprob, ?_, ?_, ?_⟩
  · intro i
    exact lineFunction_contDiffOn v y M (J + 1) (hF₁ i v hv y hy')
  · intro i
    exact lineFunction_contDiffOn v y M (J + 1) (hF₂ i v hv y hy')
  · intro i m hm t ht
    have hbound : |iteratedDeriv m (g₁ i) t| ≤ B m * R ^ ε := by
      apply lineFunction_bound hvunit hy hM (mul_nonneg (hB m hm).le hpow.le) m
        (fun x hx => ?_) ht
      convert hder₁ i v hv m hm x hx using 1 <;> ring
    exact hbound.trans ((mul_le_mul_of_nonneg_right (hBA m hm) hpow.le).trans hupper)
  · intro i m hm t ht
    have hbound : |iteratedDeriv m (g₂ i) t| ≤ B m * R ^ ε := by
      apply lineFunction_bound hvunit hy hM (mul_nonneg (hB m hm).le hpow.le) m
        (fun x hx => ?_) ht
      convert hder₂ i v hv m hm x hx using 1 <;> ring
    exact hbound.trans ((mul_le_mul_of_nonneg_right (hBA m hm) hpow.le).trans hupper)
  · intro i U hU
    have h := hν₁ i U hU
    rw [hcoeff] at h
    apply h.trans
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hmarg (hπ₁ i))) le_rfl
  · intro i U hU
    have h := hν₂ i U hU
    rw [hcoeff] at h
    apply h.trans
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hmarg (hπ₂ i))) le_rfl
  · change ∀ᵐ p ∂ν, p.2 ∈ Icc (0 : ℝ) 1 ∧
      |g₁ p.1.1 p.2 - g₂ p.1.2 p.2| ≤ R ^ (-1 + η) ∧
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ K ∧ R ^ (-η) ≤
        |iteratedDeriv j (g₁ p.1.1) p.2 - iteratedDeriv j (g₂ p.1.2) p.2|
    filter_upwards [hνsupp] with p hp
    have hEv := (jetEvent_iff F₁ F₂ v K _ _
      (p.1, y + (windowStep * p.2) • v)).mp hp.2
    refine ⟨hp.1, ?_, ?_⟩
    · calc
        |g₁ p.1.1 p.2 - g₂ p.1.2 p.2| =
            M⁻¹ * |F₁ p.1.1 (y + (windowStep * p.2) • v) -
              F₂ p.1.2 (y + (windowStep * p.2) • v)| := by
          dsimp [g₁, g₂, lineFunction]
          rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hM)]
        _ ≤ M⁻¹ * (M * R ^ (-1 + ε)) :=
          mul_le_mul_of_nonneg_left hEv.2.1 (inv_nonneg.mpr hM.le)
        _ = R ^ (-1 + ε) := by field_simp
        _ ≤ R ^ (-1 + η) := Real.rpow_le_rpow_of_exponent_le hRone (by linarith)
    · obtain ⟨j, hj₁, hjK, hgap⟩ := hEv.2.2
      refine ⟨j, hj₁, hjK, hlower.trans ?_⟩
      have hjetgap := lineFunction_gap (F := F₁ p.1.1) (G := F₂ p.1.2) v y hM
        (mul_nonneg hb.le hpowneg.le) hjK (t := p.2) (by
          convert hgap using 1 <;> ring)
      convert hjetgap using 1 <;> ring
