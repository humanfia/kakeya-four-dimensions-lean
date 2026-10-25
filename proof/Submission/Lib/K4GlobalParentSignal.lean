/-
# Global physical parent signals and original-time coefficient tables

Adapted from: here:o265
Original proofs by session x1030, commits eb51e610, df7a007b,
381c4e41 and e3ae05f8. This general part has no frozen-problem or
unproved-obligation dependency.
-/
import Mathlib
import ChallengeDeps
import Submission.Lib.K4ProjectedGroups.LineSignal
import Submission.Lib.K4CubicTests.PolynomialTaylor
import Submission.Lib.K4QuadraticSheets.QuadTest

set_option autoImplicit false

namespace Submission.Lib.K4GlobalParentSignal

open Set MeasureTheory
open scoped ENNReal

noncomputable section

abbrev Ln := ℕ × (Fin 6 → ℝ)
abbrev Ev := Ln × ℝ
abbrev Po := MvPolynomial (Fin 4) ℝ
abbrev P2 := EuclideanSpace ℝ (Fin 2)

def xp (l : Ln) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0+t*l.2 3, l.2 1+t*l.2 4, l.2 2+t*l.2 5]

def y (l : Ln) (t : ℝ) : P2 := WithLp.toLp 2 ![(xp l t) 1, (xp l t) 2]

def v (l : Ln) : P2 := WithLp.toLp 2 ![l.2 3, l.2 4]

/-- The derivative along the actual original trajectory. -/
def rate (P : Po) (l : Ln) (t : ℝ) : ℝ :=
  ∑ i : Fin 4, MvPolynomial.eval (xp l t) (MvPolynomial.pderiv i P) *
    (![1, l.2 3, l.2 4, l.2 5] i)

theorem hasDerivAt_signal (P : Po) (l : Ln) (t : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval (xp l s) P) (rate P l t) t := by
  apply Submission.Lib.K4CubicTests.hasDerivAt_eval_finite_polynomial_curve
    P (xp l) ![1, l.2 3, l.2 4, l.2 5] t
  intro i
  fin_cases i
  · simpa [xp] using (hasDerivAt_id t).mul_const (1 : ℝ)
  · simpa [xp] using ((hasDerivAt_id t).mul_const (l.2 3)).const_add (l.2 0)
  · simpa [xp] using ((hasDerivAt_id t).mul_const (l.2 4)).const_add (l.2 1)
  · simpa [xp] using ((hasDerivAt_id t).mul_const (l.2 5)).const_add (l.2 2)

theorem rate_eq_coefficients {P : Po} (hP : P.totalDegree ≤ 2) (l : Ln) (t : ℝ) :
    rate P l t = Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
      2 * t * Submission.Lib.K4ProjectedGroups.sc2 P l.2 := by
  have hsignal (s : ℝ) : MvPolynomial.eval (xp l s) P =
      Submission.Lib.K4ProjectedGroups.sc0 P l.2 +
        s * Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
        s ^ 2 * Submission.Lib.K4ProjectedGroups.sc2 P l.2 :=
    Submission.Lib.K4ProjectedGroups.sig_eq hP l.2 s
  have hpoly : HasDerivAt (fun s => MvPolynomial.eval (xp l s) P)
      (Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
        2 * t * Submission.Lib.K4ProjectedGroups.sc2 P l.2) t := by
    convert
      (((hasDerivAt_id t).mul_const (Submission.Lib.K4ProjectedGroups.sc1 P l.2)).const_add
        (Submission.Lib.K4ProjectedGroups.sc0 P l.2)).add
        (((hasDerivAt_id t).pow 2).mul_const (Submission.Lib.K4ProjectedGroups.sc2 P l.2))
      using 1
    · funext s
      exact hsignal s
    · simp
  exact (hasDerivAt_signal P l t).unique hpoly

/-- A whole-unit-time bound gives a trajectory derivative bound, with no
physical coefficient or hidden-velocity loss. -/
theorem abs_rate_le {P : Po} (hP : P.totalDegree ≤ 2) {l : Ln} {K : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp l t) P| ≤ K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |rate P l t| ≤ 24 * K := by
  have h1 := Submission.Lib.K4ProjectedGroups.abs_sc1_le hbound
  have h2 := Submission.Lib.K4ProjectedGroups.abs_sc2_le hbound
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  rw [rate_eq_coefficients hP]
  calc
    _ ≤ |Submission.Lib.K4ProjectedGroups.sc1 P l.2| +
        2 * |t| * |Submission.Lib.K4ProjectedGroups.sc2 P l.2| := by
      simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
        abs_add_le (Submission.Lib.K4ProjectedGroups.sc1 P l.2)
          (2 * t * Submission.Lib.K4ProjectedGroups.sc2 P l.2)
    _ ≤ 8 * K + 2 * 1 * (8 * K) := by gcongr
    _ = _ := by ring

/-- The same bound controls differences between any two original times. -/
theorem signal_variation {P : Po} (hP : P.totalDegree ≤ 2) {l : Ln} {K : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp l t) P| ≤ K)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |MvPolynomial.eval (xp l t) P - MvPolynomial.eval (xp l s) P| ≤
      24 * K * |t - s| := by
  have h1 := Submission.Lib.K4ProjectedGroups.abs_sc1_le hbound
  have h2 := Submission.Lib.K4ProjectedGroups.abs_sc2_le hbound
  have hts : |t + s| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg ht.1 hs.1)]
    linarith [ht.2, hs.2]
  have heq : MvPolynomial.eval (xp l t) P - MvPolynomial.eval (xp l s) P =
      (t-s) * (Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
        (t+s) * Submission.Lib.K4ProjectedGroups.sc2 P l.2) := by
    rw [show MvPolynomial.eval (xp l t) P =
      Submission.Lib.K4ProjectedGroups.sig P l.2 t from rfl,
      show MvPolynomial.eval (xp l s) P =
      Submission.Lib.K4ProjectedGroups.sig P l.2 s from rfl,
      Submission.Lib.K4ProjectedGroups.sig_eq hP,
      Submission.Lib.K4ProjectedGroups.sig_eq hP]
    ring
  rw [heq, abs_mul, mul_comm (|t-s|)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    _ ≤ |Submission.Lib.K4ProjectedGroups.sc1 P l.2| +
        |t+s| * |Submission.Lib.K4ProjectedGroups.sc2 P l.2| := by
      simpa only [abs_mul] using abs_add_le
        (Submission.Lib.K4ProjectedGroups.sc1 P l.2)
        ((t+s) * Submission.Lib.K4ProjectedGroups.sc2 P l.2)
    _ ≤ 8*K + 2*(8*K) := by gcongr
    _ = _ := by ring

/-- The original global parent bounds, without a normalization by a packet's
thickness. This is a measurable condition on whole original lines. -/
def goodLines (P : Po) (K B : ℝ) : Set Ln :=
  {l | ∀ t ∈ Icc (0 : ℝ) 1,
    |MvPolynomial.eval (xp l t) P| ≤ K ∧
    |MvPolynomial.eval (xp l t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧
    |MvPolynomial.eval (xp l t)
      (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K * B ^ 2}

theorem isClosed_goodLines (P : Po) (K B : ℝ) : IsClosed (goodLines P K B) := by
  have hcont (F : Po) (t : ℝ) :
      Continuous (fun l : Ln => |MvPolynomial.eval (xp l t) F|) :=
    ((Submission.Lib.K4ProjectedGroups.continuous_sig F t).comp continuous_snd).abs
  simp only [goodLines, ofPred_forall]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    (isClosed_le (hcont P t) continuous_const).inter
      ((isClosed_le (hcont (MvPolynomial.pderiv 3 P) t) continuous_const).inter
        (isClosed_le (hcont (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P)) t)
          continuous_const))

theorem measurableSet_goodLines (P : Po) (K B : ℝ) : MeasurableSet (goodLines P K B) :=
  (isClosed_goodLines P K B).measurableSet

/-- Regularity is imposed only at counted events. -/
def regularEvents (P : Po) (K B : ℝ) : Set Ev :=
  {p | B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)|}

theorem measurableSet_regularEvents (P : Po) (K B : ℝ) :
    MeasurableSet (regularEvents P K B) := by
  have hcont : Continuous (fun p : Ev =>
      |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)|) :=
    ((Submission.Lib.K4ProjectedGroups.continuous_sig_uncurry (MvPolynomial.pderiv 3 P)).comp
      (continuous_fst.snd.prodMk continuous_snd)).abs
  exact (isClosed_le continuous_const hcont).measurableSet

/-- Removing the exceptional original lines preserves every original event law
exactly, including an event selected after the parent bounds are obtained. -/
theorem restrict_goodLines (ν : Measure Ln) {P : Po} {K B : ℝ}
    (hgood : ∀ᵐ l ∂ν, l ∈ goodLines P K B) (E : Set Ev) :
    (ν.prod volume).restrict (E ∩ Prod.fst ⁻¹' goodLines P K B) =
      (ν.prod volume).restrict E := by
  have hprod : ∀ᵐ p ∂ν.prod (volume : Measure ℝ), p.1 ∈ goodLines P K B :=
    (Measure.ae_prod_iff_ae_ae
      ((measurableSet_goodLines P K B).preimage measurable_fst)).mpr
        (hgood.mono fun _ h => Filter.Eventually.of_forall fun _ => h)
  apply Measure.restrict_congr_set
  filter_upwards [hprod] with p hp
  simp only [mem_inter_iff, mem_preimage, hp, and_true]

/-- The global parent's hidden curvature bound is global in physical space:
its second hidden partial is constant. -/
theorem hidden_curvature_global (ν : Measure Ln) [IsProbabilityMeasure ν]
    {P : Po} (hP : P.totalDegree ≤ 2) {K B : ℝ}
    (hgood : ∀ᵐ l ∂ν, l ∈ goodLines P K B) (z : Fin 4 → ℝ) :
    |MvPolynomial.eval z (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K * B ^ 2 := by
  obtain ⟨l, hl⟩ := hgood.exists
  have hb := (hl 0 (by norm_num)).2.2
  have hconst (w : Fin 4 → ℝ) :=
    Submission.Lib.K4QuadraticSheets.eval_pderiv2_eq_qc P hP w
  change |MvPolynomial.eval z
    (MvPolynomial.pderiv (Fin.last 3) (MvPolynomial.pderiv (Fin.last 3) P))| ≤ _
  rw [hconst]
  simpa only [show (3 : Fin 4) = Fin.last 3 from rfl, hconst] using hb

/-- In units `X=P/a` and `W=B*w/a`, the hidden curvature of the
global parent gains a factor `a`. -/
theorem normalized_hidden_curvature (ν : Measure Ln) [IsProbabilityMeasure ν]
    {P : Po} (hP : P.totalDegree ≤ 2) {K B a : ℝ} (hB : 0 < B) (ha : 0 ≤ a)
    (hgood : ∀ᵐ l ∂ν, l ∈ goodLines P K B) (z : Fin 4 → ℝ) :
    |a / B ^ 2 *
      MvPolynomial.eval z (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K * a := by
  rw [abs_mul, abs_of_nonneg (div_nonneg ha (sq_nonneg B))]
  calc
    _ ≤ a / B ^ 2 * (K * B ^ 2) := mul_le_mul_of_nonneg_left
      (hidden_curvature_global ν hP hgood z) (div_nonneg ha (sq_nonneg B))
    _ = _ := by field_simp

/-- The parent signal in ORIGINAL time, followed by the two unchanged
physical base lines. There is no old thickness or clock in this table. -/
def globalCoefficients (P : Po) (l : Ln) : Fin 7 → ℝ :=
  ![Submission.Lib.K4ProjectedGroups.sc0 P l.2,
    Submission.Lib.K4ProjectedGroups.sc1 P l.2,
    Submission.Lib.K4ProjectedGroups.sc2 P l.2,
    l.2 0, l.2 3, l.2 1, l.2 4]

theorem continuous_globalCoefficients (P : Po) : Continuous (globalCoefficients P) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact (Submission.Lib.K4ProjectedGroups.continuous_sc0 P).comp continuous_snd
  · exact (Submission.Lib.K4ProjectedGroups.continuous_sc1 P).comp continuous_snd
  · exact (Submission.Lib.K4ProjectedGroups.continuous_sc2 P).comp continuous_snd
  · change Continuous (fun l : Ln => l.2 0)
    exact (continuous_apply 0).comp continuous_snd
  · change Continuous (fun l : Ln => l.2 3)
    exact (continuous_apply 3).comp continuous_snd
  · change Continuous (fun l : Ln => l.2 1)
    exact (continuous_apply 1).comp continuous_snd
  · change Continuous (fun l : Ln => l.2 4)
    exact (continuous_apply 4).comp continuous_snd

theorem measurable_globalCoefficients (P : Po) : Measurable (globalCoefficients P) :=
  (continuous_globalCoefficients P).measurable

theorem measurableSet_bounded_globalCoefficients (P : Po) (K : ℝ) :
    MeasurableSet {l | ∀ i, |globalCoefficients P l i| ≤ 8 * K} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    (isClosed_le (((continuous_apply i).comp (continuous_globalCoefficients P)).abs)
      continuous_const).measurableSet

/-- The table represents the exact physical parent in original time. -/
theorem global_signal {P : Po} (hP : P.totalDegree ≤ 2) (l : Ln) (t : ℝ) :
    globalCoefficients P l 0 + globalCoefficients P l 1 * t +
      globalCoefficients P l 2 * t ^ 2 = MvPolynomial.eval (xp l t) P := by
  change Submission.Lib.K4ProjectedGroups.sc0 P l.2 +
    Submission.Lib.K4ProjectedGroups.sc1 P l.2 * t +
    Submission.Lib.K4ProjectedGroups.sc2 P l.2 * t ^ 2 =
      Submission.Lib.K4ProjectedGroups.sig P l.2 t
  rw [Submission.Lib.K4ProjectedGroups.sig_eq hP]
  ring

theorem global_rate {P : Po} (hP : P.totalDegree ≤ 2) (l : Ln) (t : ℝ) :
    globalCoefficients P l 1 + 2 * globalCoefficients P l 2 * t = rate P l t := by
  rw [rate_eq_coefficients hP]
  change Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
    2 * Submission.Lib.K4ProjectedGroups.sc2 P l.2 * t = _
  ring

theorem globalCoefficients_bound {P : Po} {K B : ℝ} {l : Ln}
    (hl : l ∈ goodLines P K B) (hplanar : ‖y l 0‖ + ‖v l‖ ≤ K) (i : Fin 7) :
    |globalCoefficients P l i| ≤ 8 * K := by
  have hK : 0 ≤ K := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hplanar
  have hsignal := fun t ht => (hl t ht).1
  have hy : ‖y l 0‖ ≤ K := by linarith [norm_nonneg (v l)]
  have hv : ‖v l‖ ≤ K := by linarith [norm_nonneg (y l 0)]
  have hy0 : |l.2 0| ≤ K := by
    simpa [y, xp] using (PiLp.norm_apply_le (y l 0) (0 : Fin 2)).trans hy
  have hy1 : |l.2 1| ≤ K := by
    simpa [y, xp] using (PiLp.norm_apply_le (y l 0) (1 : Fin 2)).trans hy
  have hv0 : |l.2 3| ≤ K := by
    simpa [v] using (PiLp.norm_apply_le (v l) (0 : Fin 2)).trans hv
  have hv1 : |l.2 4| ≤ K := by
    simpa [v] using (PiLp.norm_apply_le (v l) (1 : Fin 2)).trans hv
  have hK8 : K ≤ 8 * K := by linarith
  fin_cases i
  · exact (Submission.Lib.K4ProjectedGroups.abs_sc0_le hsignal).trans hK8
  · exact Submission.Lib.K4ProjectedGroups.abs_sc1_le hsignal
  · exact Submission.Lib.K4ProjectedGroups.abs_sc2_le hsignal
  · exact hy0.trans hK8
  · exact hv0.trans hK8
  · exact hy1.trans hK8
  · exact hv1.trans hK8

end

end Submission.Lib.K4GlobalParentSignal
