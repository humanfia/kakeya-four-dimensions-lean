/- Adapted from this LOT tree, obligation o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
   Submission/Lib/K4ChartLifting/NormalizeProblem.lean. Original provenance is retained below. -/
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.NormPriorForm

/-!
# Normalization through an atlas preserves the per-sample problem conditions

`SampleProblem.normalize` (paper Lemma 2.13, first part, at one sample, without the
density hypotheses): if a sample satisfies the per-sample conditions of the frozen problem
predicate and `s` is an atlas at thickness `δ` (geometry, chart tests, selected
incidences with the lower derivative bound, formats, positive assigned prior masses,
total selected mass `≥ 1/κ₀`), then the normalized problem -- worlds the charts of `s`,
priors `normPrior`, events `normEventOf`, native tests `P_c / δ`, scales `B / δ`, weights
`∝ ω q ν(A_c)` -- satisfies the per-sample conditions with slack `3κ₀`, format exponent
`M + 7 M₀ + M₁ + Mδ + 20` and degree bound `max (max D D₀) 1`.
-/
namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MeasureTheory MvPolynomial

namespace ChartSystem
variable {W T₀ : ℕ} (s : ChartSystem W T₀)

theorem unsubstBound_le (c : Fin s.count) {N : ℝ} {M₀ : ℕ} (hN : 1 ≤ N)
    (hcu : ‖s.center c‖ + ‖s.speed c‖ ≤ N ^ M₀)
    (hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) ≤ N ^ M₀) :
    (s.frameOf c).unsubstBound ≤ 12 * N ^ (2 * M₀) := by
  have h1 : 1 ≤ N ^ M₀ := one_le_pow₀ hN
  have ht := s.frameOf_t₀_le_one c
  have hq := s.frameOf_q_le_one c
  have h2M : N ^ (2 * M₀) = N ^ M₀ * N ^ M₀ := by rw [two_mul, pow_add]
  unfold Frame.unsubstBound
  have a : 1 + |(s.frameOf c).t₀| + |(s.frameOf c).q| ≤ 3 := by linarith
  have b : 1 + ‖(s.frameOf c).c‖ + ‖(s.frameOf c).u‖ ≤ 2 * N ^ M₀ := by
    show 1 + ‖s.center c‖ + ‖s.speed c‖ ≤ 2 * N ^ M₀
    linarith
  have d : 1 + ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frameOf c).D e e'| ≤ 2 * N ^ M₀ := by
    show 1 + ∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'| ≤ 2 * N ^ M₀
    linarith
  calc (1 + |(s.frameOf c).t₀| + |(s.frameOf c).q|) * (1 + ‖(s.frameOf c).c‖ + ‖(s.frameOf c).u‖) *
        (1 + ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frameOf c).D e e'|)
      ≤ 3 * (2 * N ^ M₀) * (2 * N ^ M₀) := by
        gcongr
    _ = 12 * N ^ (2 * M₀) := by rw [h2M]; ring

/-- Coefficients of the normalized native test. -/
theorem abs_coeff_normNative_le (c : Fin s.count) {N δ : ℝ} {M₀ Mδ : ℕ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδi : δ⁻¹ ≤ N ^ Mδ)
    (hcu : ‖s.center c‖ + ‖s.speed c‖ ≤ N ^ M₀)
    (hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) ≤ N ^ M₀)
    (hdeg : (s.test c).totalDegree ≤ 2) (hcoef : ∀ e, |(s.test c).coeff e| ≤ N ^ M₀)
    (e : Fin 4 →₀ ℕ) :
    |(s.normNative δ c).coeff e| ≤ N ^ (Mδ + 5 * M₀ + 15) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hU := s.unsubstBound_le c hN1 hcu hDs
  have hU1 := (s.frameOf c).one_le_unsubstBound
  have hL1 : coeffL1 (s.test c) ≤ 81 * N ^ M₀ := by
    have := coeffL1_le_of_coeff_le (s.test c) hdeg (N ^ M₀) hcoef
    norm_num at this; exact this
  have hpow : (s.frameOf c).unsubstBound ^ (s.test c).totalDegree ≤
      (s.frameOf c).unsubstBound ^ 2 := pow_le_pow_right₀ hU1 hdeg
  have hU2 : (s.frameOf c).unsubstBound ^ 2 ≤ 144 * N ^ (4 * M₀) := by
    have : N ^ (4 * M₀) = N ^ (2 * M₀) * N ^ (2 * M₀) := by rw [← pow_add]; ring_nf
    rw [this]; nlinarith
  refine ((s.frameOf c).abs_coeff_normTest_le δ (s.test c) e).trans ?_
  rw [abs_of_pos (inv_pos.mpr hδ)]
  have h15 : (81 * 144 : ℝ) ≤ N ^ 15 := by
    calc (81 * 144 : ℝ) ≤ 2 ^ 15 := by norm_num
      _ ≤ N ^ 15 := pow_le_pow_left₀ (by norm_num) hN 15
  have hfin : N ^ (Mδ + 5 * M₀ + 15) = N ^ Mδ * (N ^ M₀ * N ^ (4 * M₀)) * N ^ 15 := by
    rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
  rw [hfin]
  have hL0 := coeffL1_nonneg (s.test c)
  calc δ⁻¹ * (coeffL1 (s.test c) * (s.frameOf c).unsubstBound ^ (s.test c).totalDegree)
      ≤ N ^ Mδ * ((81 * N ^ M₀) * (144 * N ^ (4 * M₀))) := by
        apply mul_le_mul hδi _ (by positivity) (by positivity)
        exact mul_le_mul hL1 (hpow.trans hU2) (by positivity) (by positivity)
    _ = (81 * 144) * (N ^ Mδ * (N ^ M₀ * N ^ (4 * M₀))) := by ring
    _ ≤ N ^ 15 * (N ^ Mδ * (N ^ M₀ * N ^ (4 * M₀))) :=
        mul_le_mul_of_nonneg_right h15 (by positivity)
    _ = _ := by ring

/-- Sizes of normalized incidences. -/
theorem normEvent_bdd (c : Fin s.count) (hD : IsUnit (s.frame c).det) {N : ℝ} {M₀ : ℕ}
    (hN : 2 ≤ N) (hcu : ‖s.center c‖ + ‖s.speed c‖ ≤ N ^ M₀)
    (hDi : (∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'|) ≤ N ^ M₀)
    (hAb : ∀ l ∈ s.assignment c, (l.1 : ℝ) ≤ N ^ M₀ ∧ ∀ e, |l.2 e| ≤ N ^ M₀) :
    ∀ p ∈ s.normEventOf c, (p.1.1 : ℝ) ≤ N ^ (3 * M₀ + 4) ∧ ∀ e, |p.1.2 e| ≤ N ^ (3 * M₀ + 4) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  intro p hp
  have hA : (p.1.1, (s.frameOf c).denormCoeff p.1.2) ∈ s.assignment c := hp.1
  obtain ⟨h1, h2⟩ := hAb _ hA
  have hP4 : (16 : ℝ) ≤ N ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ N ^ 4 := pow_le_pow_left₀ (by norm_num) hN 4
  have hfin : N ^ (3 * M₀ + 4) = N ^ (2 * M₀) * N ^ M₀ * N ^ 4 := by
    rw [← pow_add, ← pow_add]; ring_nf
  refine ⟨h1.trans (pow_le_pow_right₀ hN1 (by omega)), fun e => ?_⟩
  have hR : 1 ≤ N ^ M₀ := one_le_pow₀ hN1
  have key := (s.frameOf c).abs_normCoeff_le ((s.frameOf c).denormCoeff p.1.2) (N ^ M₀) hR h2 e
  rw [(s.frameOf c).normCoeff_denormCoeff (s.frameOf_q_pos c).ne' hD] at key
  have hb := s.normBound_le c hN1 hcu hDi
  rw [hfin]
  calc |p.1.2 e| ≤ (s.frameOf c).normBound * N ^ M₀ := key
    _ ≤ (16 * N ^ (2 * M₀)) * N ^ M₀ := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = 16 * (N ^ (2 * M₀) * N ^ M₀) := by ring
    _ ≤ N ^ 4 * (N ^ (2 * M₀) * N ^ M₀) := mul_le_mul_of_nonneg_right hP4 (by positivity)
    _ = N ^ (2 * M₀) * N ^ M₀ * N ^ 4 := by ring

theorem normZ_pos (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ)
    (hpos : ∀ c, 0 < (ν (s.world c) (s.assignment c)).toReal) {κ : ℝ} (hκ : 0 < κ)
    (htotal : ENNReal.ofReal κ⁻¹ ≤
      ∑ c, ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c)) :
    0 < s.normZ ω ν := by
  by_contra h
  push Not at h
  have hT : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  have hterm : ∀ c, 0 ≤ ω (s.world c) * ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀) :=
    fun c => mul_nonneg (hω _) (div_nonneg (hpos c).le hT.le)
  have hzero : ∀ c, ω (s.world c) = 0 := by
    intro c
    have hsum0 : s.normZ ω ν = 0 := le_antisymm h (Finset.sum_nonneg fun c _ => hterm c)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hterm c)).mp hsum0 c (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 (div_pos (hpos c) hT).ne'
  have : ∑ c, ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c) = 0 := by
    simp [hzero]
  rw [this] at htotal
  have : (0 : ENNReal) < ENNReal.ofReal κ⁻¹ := ENNReal.ofReal_pos.mpr (inv_pos.mpr hκ)
  exact absurd htotal (not_le.mpr this)

end ChartSystem

open ChartSystem in
/-- **Normalization through an atlas** (paper Lemma 2.13, first part, at one sample): the
normalized problem of an atlas satisfies all the per-sample problem conditions, with slack
`3κ₀`, thickness-scaled native tests and derivative scales, and explicit format bounds. -/
theorem SampleProblem.normalize {N K : ℝ} {M D W T₀ M₀ D₀ M₁ Mδ : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Trajectory} {E : Fin W → Set Incidence}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hP : SampleProblem N K M D W ω ν E P B) (s : ChartSystem W T₀) {κ₀ δ : ℝ}
    (hgeo : s.Geometry N κ₀ M₀ D₀)
    (hchart : ∀ c, ∀ l ∈ s.assignment c, ∀ t ∈ timeBlock T₀ (s.block c),
      ‖Matrix.toEuclideanLin ((s.frame c)⁻¹) (planarPoint l t - s.center c - t • s.speed c)‖ ≤ κ₀ ∧
      |MvPolynomial.eval (graphPoint l t) (s.test c)| ≤ κ₀ * δ ∧
      |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) (s.test c))| ≤
        κ₀ * B (s.world c) ∧
      |MvPolynomial.eval (graphPoint l t)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (s.test c)))| ≤
        κ₀ * B (s.world c) ^ 2 / δ)
    (hev : ∀ c, ∀ p ∈ s.event c, p ∈ E (s.world c) ∧ p.1 ∈ s.assignment c ∧
      p.2 ∈ timeBlock T₀ (s.block c) ∧ B (s.world c) / κ₀ ≤
        |MvPolynomial.eval (graphPoint p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (s.test c))|)
    (hFm : ∀ c, MeasurableSet (s.event c))
    (hFf : ∀ c i, PolynomialFormat N M₀ D₀
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ s.event c})
    (hdeg : ∀ c, (s.test c).totalDegree ≤ 2) (hcoef : ∀ c e, |(s.test c).coeff e| ≤ N ^ M₀)
    (hmassc : ∀ c, 1 ≤ N ^ M₁ * (ν (s.world c) (s.assignment c)).toReal)
    (htotal : ENNReal.ofReal κ₀⁻¹ ≤
      ∑ c, ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c))
    (hN : 2 ≤ N) (hT₀ : (2 : ℝ) ^ T₀ ≤ N ^ M₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδi : δ⁻¹ ≤ N ^ Mδ) (hκ₀ : 1 ≤ κ₀) :
    SampleProblem N (3 * κ₀) (M + 7 * M₀ + M₁ + Mδ + 20) (max (max D D₀) 1) s.count
      (s.normWeight ω ν) (s.normPrior ν) s.normEventOf (s.normNative δ) (s.normScale B δ) := by
  classical
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hle : ∀ a, a ≤ M + 7 * M₀ + M₁ + Mδ + 20 → N ^ a ≤ N ^ (M + 7 * M₀ + M₁ + Mδ + 20) :=
    fun a ha => pow_le_pow_right₀ hN1 ha
  have hprob : ∀ γ, IsProbabilityMeasure (ν γ) := hP.prob
  obtain ⟨hcount, hdisj, hgeoc⟩ := hgeo
  have hD : ∀ c, IsUnit (s.frame c).det := fun c => isUnit_iff_ne_zero.mpr (hgeoc c).1
  have hνpos : ∀ c, 0 < (ν (s.world c) (s.assignment c)).toReal := by
    intro c
    have h := hmassc c
    by_contra hc
    push Not at hc
    have : N ^ M₁ * (ν (s.world c) (s.assignment c)).toReal ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have hνne : ∀ c, ν (s.world c) (s.assignment c) ≠ 0 := fun c h0 => by
    have := hνpos c; rw [h0, ENNReal.toReal_zero] at this; exact lt_irrefl _ this
  have hZ : 0 < s.normZ ω ν := s.normZ_pos ω ν hP.weight_nonneg hνpos (by linarith) htotal
  have hA : ∀ c, MeasurableSet (s.assignment c) := fun c => (hgeoc c).2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcount.trans (hle _ (by omega))
  · exact s.normWeight_nonneg ω ν hP.weight_nonneg
  · exact s.normWeight_sum ω ν hZ
  · exact fun c => s.normPrior_isProbability ν c (hνne c)
  · exact fun c => div_pos (hP.scale_pos _) hδ
  · intro c
    show B (s.world c) / δ ≤ _
    rw [div_eq_mul_inv]
    calc B (s.world c) * δ⁻¹ ≤ N ^ M * N ^ Mδ :=
          mul_le_mul (hP.scale_le _) hδi (inv_nonneg.mpr hδ.le) (by positivity)
      _ = N ^ (M + Mδ) := (pow_add _ _ _).symm
      _ ≤ _ := hle _ (by omega)
  · intro c
    show (B (s.world c) / δ)⁻¹ ≤ _
    rw [inv_div]
    have hB := hP.scale_pos (s.world c)
    calc δ / B (s.world c) ≤ 1 / B (s.world c) := div_le_div_of_nonneg_right hδ1 hB.le
      _ = (B (s.world c))⁻¹ := one_div _
      _ ≤ N ^ M := hP.scale_inv_le _
      _ ≤ _ := hle _ (by omega)
  · exact fun c => ((s.frameOf c).totalDegree_normTest_le δ _).trans (hdeg c)
  · intro c e
    obtain ⟨_, hcu, hfr, _, _, _, _⟩ := hgeoc c
    have hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) ≤ N ^ M₀ := by
      have : ∑ e : Fin 2, ∑ e' : Fin 2, (|s.frame c e e'| + |(s.frame c)⁻¹ e e'|) =
          (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) +
            ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'| := by
        simp only [Finset.sum_add_distrib]
      have h0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'| :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    exact (s.abs_coeff_normNative_le c hN hδ hδi hcu hDs (hdeg c) (hcoef c) e).trans
      (hle _ (by omega))
  · intro c
    obtain ⟨m, hm, cc, i, A, hj, hν⟩ := hP.prior (s.world c)
    obtain ⟨_, hcu, hfr, _, _, hAf, _⟩ := hgeoc c
    have hDs : (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) ≤ N ^ M₀ ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'|) ≤ N ^ M₀ := by
      have : ∑ e : Fin 2, ∑ e' : Fin 2, (|s.frame c e e'| + |(s.frame c)⁻¹ e e'|) =
          (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) +
            ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'| := by
        simp only [Finset.sum_add_distrib]
      have h0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'| :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      have h1 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'| :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      constructor <;> linarith
    have hdet := s.abs_det_normMatrix_inv_le c (hD c) hN1 hT₀ hDs.1
    have hνinv : ((ν (s.world c) (s.assignment c)).toReal)⁻¹ ≤ N ^ M₁ := by
      rw [inv_le_iff_one_le_mul₀ (hνpos c)]
      linarith [hmassc c, mul_comm (N ^ M₁) (ν (s.world c) (s.assignment c)).toReal]
    have hcc : ∀ j, 0 ≤ cc j := fun j => (hj j).1
    refine ⟨m, hm.trans (hle _ (by omega)),
      fun j => cc j * |(s.frameOf c).normMatrix.det|⁻¹ / (ν (s.world c) (s.assignment c)).toReal,
      i, fun j => (s.frameOf c).denormCoeff ⁻¹' (A j ∩ {x | (i j, x) ∈ s.assignment c}),
      fun j => ⟨?_, ?_, ?_, ?_, ?_⟩,
      s.normPrior_form ν c (hD c) (hA c) cc hcc i A hν (hνne c)⟩
    · exact div_nonneg (mul_nonneg (hcc j) (inv_nonneg.mpr (abs_nonneg _))) (hνpos c).le
    · dsimp only
      rw [div_eq_mul_inv]
      calc cc j * |(s.frameOf c).normMatrix.det|⁻¹ * ((ν (s.world c) (s.assignment c)).toReal)⁻¹
          ≤ N ^ M * N ^ (7 * M₀) * N ^ M₁ := by
            apply mul_le_mul (mul_le_mul (hj j).2.1 hdet (inv_nonneg.mpr (abs_nonneg _))
              (by positivity)) hνinv (inv_nonneg.mpr (hνpos c).le) (by positivity)
        _ = N ^ (M + 7 * M₀ + M₁) := by rw [← pow_add, ← pow_add]
        _ ≤ _ := hle _ (by omega)
    · exact (hj j).2.2.1.trans (hle _ (by omega))
    · dsimp only
      have h := Fmt.inter (hj j).2.2.2.1 (hAf (i j))
      have h' := (s.frameOf c).fmt_denorm_piece h
      refine h'.mono ?_ (by omega)
      calc N ^ M + N ^ M₀ ≤ N ^ (M + M₀) + N ^ (M + M₀) :=
            add_le_add (pow_le_pow_right₀ hN1 (by omega)) (pow_le_pow_right₀ hN1 (by omega))
        _ ≤ N ^ (M + M₀) * N := by nlinarith [pow_pos hNpos (M + M₀)]
        _ = N ^ (M + M₀ + 1) := (pow_succ _ _).symm
        _ ≤ _ := hle _ (by omega)
    · dsimp only
      intro x hx b
      have hx' : (s.frameOf c).denormCoeff x ∈ A j := hx.1
      have hb := (hj j).2.2.2.2 _ hx'
      have hR : 1 ≤ N ^ M := one_le_pow₀ hN1
      have key := (s.frameOf c).abs_normCoeff_le ((s.frameOf c).denormCoeff x) (N ^ M) hR hb b
      rw [(s.frameOf c).normCoeff_denormCoeff (s.frameOf_q_pos c).ne' (hD c)] at key
      have hbd := s.normBound_le c hN1 hcu hDs.2
      have hP4 : (16 : ℝ) ≤ N ^ 4 := by
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ ≤ N ^ 4 := pow_le_pow_left₀ (by norm_num) hN 4
      calc |x b| ≤ (s.frameOf c).normBound * N ^ M := key
        _ ≤ (16 * N ^ (2 * M₀)) * N ^ M := mul_le_mul_of_nonneg_right hbd (by positivity)
        _ ≤ (N ^ 4 * N ^ (2 * M₀)) * N ^ M := by gcongr
        _ = N ^ (4 + 2 * M₀ + M) := by rw [← pow_add, ← pow_add]
        _ ≤ _ := hle _ (by omega)
  · exact fun c => (s.frameOf c).measurableSet_normEvent (hA c) (hFm c)
  · intro c p hp
    exact ⟨Set.mem_univ _, hp.2.1⟩
  · intro c p hp
    obtain ⟨_, hcu, hfr, _, _, _, hAb⟩ := hgeoc c
    have hDi : (∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'|) ≤ N ^ M₀ := by
      have : ∑ e : Fin 2, ∑ e' : Fin 2, (|s.frame c e e'| + |(s.frame c)⁻¹ e e'|) =
          (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'|) +
            ∑ e : Fin 2, ∑ e' : Fin 2, |(s.frame c)⁻¹ e e'| := by
        simp only [Finset.sum_add_distrib]
      have h0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |s.frame c e e'| :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    obtain ⟨b1, b2⟩ := s.normEvent_bdd c (hD c) hN hcu hDi hAb p hp
    exact ⟨b1.trans (hle _ (by omega)), fun e => (b2 e).trans (hle _ (by omega))⟩
  · intro c i
    obtain ⟨_, _, _, _, _, hAf, _⟩ := hgeoc c
    have h := (s.frameOf c).fmt_normEvent_slice i (hAf i) (hFf c i)
    refine h.mono ?_ (by omega)
    have h2 : (2 : ℝ) ≤ N ^ M₀ * 2 := by
      have := one_le_pow₀ (n := M₀) hN1; linarith
    calc N ^ M₀ + 2 + N ^ M₀ ≤ N ^ M₀ * 4 := by
          have := one_le_pow₀ (n := M₀) hN1; linarith
      _ ≤ N ^ M₀ * N ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
      _ = N ^ (M₀ + 2) := (pow_add _ _ _).symm
      _ ≤ _ := hle _ (by omega)
  · intro c
    have h := s.normPrior_native ν c (hD c) (hA c) (by linarith) hδ (hP.scale_pos _).le
      (hchart c)
    refine h.mono fun l hl τ hτ => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hl τ hτ
    exact ⟨h1, h2, h3, h4⟩
  · intro c
    exact s.normEvent_lower ν c (hA c) (hFm c) (by linarith) hδ (hP.scale_pos _).le
      (fun p hp => (hev c p hp).2.2.2)
  · have hm := s.normMass ω ν hP.weight_nonneg hP.weight_sum hZ hD hA hFm hdisj
      (fun c p hp => ⟨(hev c p hp).2.1, (hev c p hp).2.2.1⟩) htotal
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hm
    exact inv_anti₀ (by linarith) (by linarith)

end Submission.Obl.k4_raw_native_atlas_normalization.Kernel
