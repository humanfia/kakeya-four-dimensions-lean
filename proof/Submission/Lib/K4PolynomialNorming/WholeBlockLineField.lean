/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.PolynomialLineField
import Submission.Lib.K4PolynomialRemez

open Set MeasureTheory MvPolynomial ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- A field fit on any positive-duration retained time set extends over
the whole block, with no interval component or good time selected. -/
theorem quadratic_line_field_fit_on_whole_block {σ : Type*} [Fintype σ]
    (T : σ → MvPolynomial σ ℝ) (D : ℕ) (hD : ∀ j, (T j).totalDegree ≤ D)
    (c u : σ → ℝ) (b d : ℝ) (S : Set ℝ)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 ≤ ε)
    (hS : S ⊆ Icc (0:ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hfit : ∀ t ∈ S, |b+2*t*d-∑ j, u j*MvPolynomial.eval (c+t • u) (T j)| ≤ ε) :
    ∀ t ∈ Icc (0:ℝ) 1,
      |b+2*t*d-∑ j, u j*MvPolynomial.eval (c+t • u) (T j)| ≤
        (8*((D:ℝ)+2)/η)^(D+1)*ε := by
  have hsmall : ∀ t ∈ S, |(quadraticLineFieldResidual T c u b d).eval t| ≤ ε := by
    simpa only [quadraticLineFieldResidual_eval] using hfit
  have h := Submission.Lib.K4PolynomialRemez.polynomial_remez_unit
    (quadraticLineFieldResidual T c u b d) (D+1)
      (quadraticLineFieldResidual_natDegree_le T c u b d D hD) S hη hη1 hε hS hmass hsmall
  have hconstant : ((D+1:ℕ):ℝ)+1 = (D:ℝ)+2 := by push_cast; ring
  simpa only [quadraticLineFieldResidual_eval,hconstant] using h

/-- The ORIGINAL normalized time probability supplies the long-row
Remez duration through its density ceiling. A fit is needed only almost
everywhere for that original row law. -/
theorem quadratic_line_field_fit_of_original_time_cap {σ : Type*} [Fintype σ]
    (T : σ → MvPolynomial σ ℝ) (D : ℕ) (hD : ∀ j, (T j).totalDegree ≤ D)
    (c u : σ → ℝ) (b d : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (K ε : ℝ) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hcap : μ ≤ ENNReal.ofReal K • volume)
    (hbox : ∀ᵐ t ∂μ, t ∈ Icc (0:ℝ) 1)
    (hfit : ∀ᵐ t ∂μ, |b+2*t*d-∑ j, u j*MvPolynomial.eval (c+t • u) (T j)| ≤ ε) :
    ∀ t ∈ Icc (0:ℝ) 1,
      |b+2*t*d-∑ j, u j*MvPolynomial.eval (c+t • u) (T j)| ≤
        (8*((D:ℝ)+2)*K)^(D+1)*ε := by
  let S := {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧
    |b+2*t*d-∑ j, u j*MvPolynomial.eval (c+t • u) (T j)| ≤ ε}
  have hS : MeasurableSet S := by
    have hc : Continuous (fun t : ℝ => |(quadraticLineFieldResidual T c u b d).eval t|) :=
      (Polynomial.continuous (quadraticLineFieldResidual T c u b d)).abs
    have hset : S = Icc (0:ℝ) 1 ∩
        {t : ℝ | |(quadraticLineFieldResidual T c u b d).eval t| ≤ ε} := by
      ext t
      simp only [S,Set.mem_inter_iff,Set.mem_ofPred_eq,quadraticLineFieldResidual_eval]
    rw [hset]
    exact (measurableSet_Icc : MeasurableSet (Icc (0:ℝ) 1)).inter
      (measurableSet_le hc.measurable (measurable_const (a := ε)))
  have hμS : μ S = 1 := by
    calc
      _ = μ univ := by
        apply measure_congr
        filter_upwards [hbox,hfit] with t ht hf
        simp only [S,Set.mem_ofPred_eq,ht,hf,and_self,Set.mem_univ]
      _ = _ := measure_univ
  have hKpos : 0 < K := by linarith
  have hmass : ENNReal.ofReal (1/K) ≤ volume S := by
    rw [ENNReal.ofReal_div_of_pos hKpos,ENNReal.ofReal_one]
    apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hKpos).ne' ENNReal.ofReal_ne_top).mpr
    have h := hcap S
    rw [hμS] at h
    simpa only [Measure.smul_apply,smul_eq_mul,mul_comm] using h
  have h := quadratic_line_field_fit_on_whole_block T D hD c u b d S (1/K) ε
    (by positivity) ((div_le_one hKpos).mpr hK) hε (fun _ hx => hx.1) hmass
    (fun _ hx => hx.2)
  have hfactor : 8*((D:ℝ)+2)/(1/K) = 8*((D:ℝ)+2)*K := by
    simp only [div_eq_mul_inv,one_mul,inv_inv]
  simpa only [hfactor] using h

/-- An ORIGINAL incidence-a.e. field fit becomes a whole-block fit on
long lines using only their original normalized time ceilings. Neither
the starting law nor a successful-path posterior is substituted. -/
theorem original_incidence_quadratic_field_fit_on_whole_block_ae {L σ : Type*}
    [MeasurableSpace L] [Fintype σ]
    (ν : Measure L) [SFinite ν] (κ : Kernel L ℝ) [IsMarkovKernel κ]
    (time : ℝ → ℝ) (htime : Measurable time)
    (T : σ → MvPolynomial σ ℝ) (D : ℕ) (hD : ∀ j, (T j).totalDegree ≤ D)
    (c u : L → σ → ℝ) (b d : L → ℝ)
    (Long : Set L) (K ε : ℝ) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hcap : ∀ l ∈ Long, (κ l).map time ≤ ENNReal.ofReal K • volume)
    (hbox : ∀ᵐ z ∂ν ⊗ₘ κ, time z.2 ∈ Icc (0:ℝ) 1)
    (hfit : ∀ᵐ z ∂ν ⊗ₘ κ,
      |b z.1+2*(time z.2)*d z.1-∑ j,
        u z.1 j*MvPolynomial.eval (c z.1+(time z.2) • u z.1) (T j)| ≤ ε) :
    ∀ᵐ z ∂ν ⊗ₘ κ, z.1 ∈ Long → ∀ t ∈ Icc (0:ℝ) 1,
      |b z.1+2*t*d z.1-∑ j, u z.1 j*MvPolynomial.eval (c z.1+t • u z.1) (T j)| ≤
        (8*((D:ℝ)+2)*K)^(D+1)*ε := by
  have hboxes := Measure.ae_ae_of_ae_compProd hbox
  have hfits := Measure.ae_ae_of_ae_compProd hfit
  have hrows : ∀ᵐ l ∂ν, l ∈ Long → ∀ t ∈ Icc (0:ℝ) 1,
      |b l+2*t*d l-∑ j, u l j*MvPolynomial.eval (c l+t • u l) (T j)| ≤
        (8*((D:ℝ)+2)*K)^(D+1)*ε := by
    filter_upwards [hboxes,hfits] with l hb hf
    intro hl
    let μ := (κ l).map time
    letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    have hb' : ∀ᵐ t ∂μ, t ∈ Icc (0:ℝ) 1 :=
      (ae_map_iff htime.aemeasurable measurableSet_Icc).mpr hb
    have hsmall : ∀ᵐ t ∂κ l,
        |(quadraticLineFieldResidual T (c l) (u l) (b l) (d l)).eval (time t)| ≤ ε := by
      simpa only [quadraticLineFieldResidual_eval] using hf
    have hsmall' : ∀ᵐ t ∂μ,
        |(quadraticLineFieldResidual T (c l) (u l) (b l) (d l)).eval t| ≤ ε :=
      (ae_map_iff htime.aemeasurable (measurableSet_le
        (Polynomial.continuous (quadraticLineFieldResidual T (c l) (u l) (b l) (d l))).abs.measurable
        (measurable_const (a := ε)))).mpr hsmall
    apply quadratic_line_field_fit_of_original_time_cap T D hD (c l) (u l) (b l) (d l)
      μ K ε hK hε (hcap l hl) hb'
    simpa only [quadraticLineFieldResidual_eval] using hsmall'
  have hfst : ∀ᵐ l ∂(ν ⊗ₘ κ).fst, l ∈ Long → ∀ t ∈ Icc (0:ℝ) 1,
      |b l+2*t*d l-∑ j, u l j*MvPolynomial.eval (c l+t • u l) (T j)| ≤
        (8*((D:ℝ)+2)*K)^(D+1)*ε := by
    simpa only [Measure.fst_compProd] using hrows
  exact ae_of_ae_map measurable_fst.aemeasurable hfst

end Submission.Lib.K4PolynomialNorming
