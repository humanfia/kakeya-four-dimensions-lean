-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceQGroups
import Submission.Obl.k4_finite_affine_parent_sources.SourceRawCeilings
import Submission.Obl.k4_finite_affine_parent_sources.SourceCoordinates
import Submission.Obl.k4_finite_affine_parent_sources.MajorFrame
import Submission.Obl.k4_finite_affine_parent_sources.PathMass

/-!
# Native-signal groups of an actual path label

`labelFrame p Q Bw δp` normalises an actual path label `Q` by its own chart (time block, centre,
velocity, major-axis frame) but keeps the hidden scale `Bw / δp` of a fixed parent. At every
counted incidence of a descendant `Q` of the parent `b₀`, the native point in this frame satisfies
the hypotheses of the accepted oscillation partition with constant `7 κ`, the test of `Q` at
thickness `δ(r_Q) / δp` and the parent's test as signal (`label_framePoint_good`). The label's
full prior obeys the saturation floor `ν(A_Q) ≥ N^(-f r_Q) |det Q| / κ` (`label_prior_floor`).

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

/-- The frame of an actual path label with a fixed hidden scale. -/
def labelFrame {W : ℕ} (p : PathData W) (Q : Fin p.C) (Bw δp : ℝ) : PFrame :=
  affineSourceFrame ((p.bin Q : ℝ) / (2 : ℝ) ^ p.T (p.lev Q)) (((2 : ℝ) ^ p.T (p.lev Q))⁻¹)
    (Bw / δp) (p.center Q) (p.velocity Q) (MajorFrame.frame (p.frame Q))

theorem labelFrame_F {W : ℕ} (p : PathData W) (Q : Fin p.C) (Bw δp : ℝ) :
    (labelFrame p Q Bw δp).F = ⟨(p.bin Q : ℝ) / (2 : ℝ) ^ p.T (p.lev Q),
      ((2 : ℝ) ^ p.T (p.lev Q))⁻¹, p.center Q, p.velocity Q, MajorFrame.frame (p.frame Q)⟩ := rfl

theorem labelFrame_sc {W : ℕ} (p : PathData W) (Q : Fin p.C) (Bw δp : ℝ) :
    (labelFrame p Q Bw δp).sc = Bw / δp := rfl

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

theorem labelFrame_q_pos (Q : Fin p.C) (Bw δp : ℝ) : 0 < (labelFrame p Q Bw δp).F.q := by
  rw [labelFrame_F]; positivity

theorem labelFrame_det (Q : Fin p.C) (Bw δp : ℝ) :
    IsUnit (labelFrame p Q Bw δp).F.D.det := by
  rw [labelFrame_F]
  exact isUnit_iff_ne_zero.mpr (MajorFrame.det_ne_zero (hp.chart Q).1)

/-- **The saturation floor of a label's full prior.** -/
theorem label_prior_floor [∀ w, SigmaFinite (ν w)] (hNk : 0 < Nk) (Q : Fin p.C) :
    ENNReal.ofReal (Nk ^ (-f (p.r (p.lev Q))) * |(p.frame Q).det| / p.κ) ≤
      ν (p.world Q) (p.assigned Q) := by
  have hsat := (hp.saturation Q).1
  have hsub : p.counted Q ⊆ p.packet Q := fun z hz =>
    ⟨(hp.counted_support Q z hz).2.1, (hp.counted_support Q z hz).2.2.1⟩
  have hpk : ((ν (p.world Q)).prod volume) (p.packet Q) =
      ν (p.world Q) (p.assigned Q) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev Q))⁻¹) := by
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc]
    congr 2
    rw [← sub_div]
    ring
  have h := hsat.trans ((measure_mono hsub).trans_eq hpk)
  have hq : (0 : ℝ) < ((2 : ℝ) ^ p.T (p.lev Q))⁻¹ := by positivity
  have hκ : 0 < p.κ := lt_of_lt_of_le one_pos hp.one_le_slack
  have heq : ENNReal.ofReal (Nk ^ (-f (p.r (p.lev Q))) * |(p.frame Q).det| /
      ((2 : ℝ) ^ p.T (p.lev Q) * p.κ)) =
      ENNReal.ofReal (Nk ^ (-f (p.r (p.lev Q))) * |(p.frame Q).det| / p.κ) *
        ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev Q))⁻¹) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [heq] at h
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top).mp h

theorem block_unit (Q : Fin p.C) {t : ℝ}
    (ht : t ∈ Icc ((p.bin Q : ℝ) / (2 : ℝ) ^ p.T (p.lev Q))
      (((p.bin Q : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev Q))) :
    (t - (p.bin Q : ℝ) / (2 : ℝ) ^ p.T (p.lev Q)) / ((2 : ℝ) ^ p.T (p.lev Q))⁻¹ ∈
      Icc (0 : ℝ) 1 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ p.T (p.lev Q) := by positivity
  have heq : (t - (p.bin Q : ℝ) / (2 : ℝ) ^ p.T (p.lev Q)) / ((2 : ℝ) ^ p.T (p.lev Q))⁻¹ =
      t * (2 : ℝ) ^ p.T (p.lev Q) - p.bin Q := by
    field_simp
  rw [heq]
  obtain ⟨h1, h3⟩ := ht
  rw [div_le_iff₀ h2] at h1
  rw [le_div_iff₀ h2] at h3
  constructor <;> linarith

/-- **Native hypotheses at a counted incidence of a descendant label.** -/
theorem label_framePoint_good (Q b₀ : Fin p.C)
    (hdesc : forestAncestor p.lev p.par Q (p.lev b₀) = b₀) (hlev : p.lev b₀ ≤ p.lev Q)
    (hB : 0 < B (p.world Q)) {x : Incidence} (hx : x ∈ p.counted Q) :
    framePoint (labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))) x ∈
      goodSet (7 * p.κ) (δ Nk (p.r (p.lev Q)) / δ Nk (p.r (p.lev b₀)))
        ((labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).normTest
          (δ Nk (p.r (p.lev b₀))) (p.test Q))
        ((labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).normTest
          (δ Nk (p.r (p.lev b₀))) (p.test b₀)) := by
  have hδ (r : ℝ) : 0 < δ Nk r := by
    show 0 < (2 : ℝ) ^ (-(⌊r * Real.log Nk / Real.log 2⌋ : ℤ))
    positivity
  have hsupQ := hp.counted_support Q x hx
  obtain ⟨-, -, htubeQ⟩ := (hp.chart Q).2.2.2.2.2.2.2.2.2.1 x.1 hsupQ.2.1
  obtain ⟨hposQ, hQ1, hQ2', hQ3⟩ := htubeQ x.2 hsupQ.2.2.1
  obtain ⟨-, hw, hsub⟩ := hp.ancestor Q (p.lev b₀) hlev
  rw [hdesc] at hw hsub
  have hx0 := hsub hx
  have hsup0 := hp.counted_support b₀ x hx0
  obtain ⟨-, -, htube0⟩ := (hp.chart b₀).2.2.2.2.2.2.2.2.2.1 x.1 hsup0.2.1
  obtain ⟨-, h01, h02, h03⟩ := htube0 x.2 hsup0.2.2.1
  rw [hw] at h02 h03
  have hdetQ := (hp.chart Q).1
  refine framePoint_good _ (labelFrame_q_pos hp Q _ _) (labelFrame_det hp Q _ _) hB
    (hδ _) (hδ _) rfl hp.one_le_slack (p.test Q) (p.test b₀) (hp.chart Q).2.2.2.2.1
    (hp.chart b₀).2.2.2.2.1 x (block_unit hp Q hsupQ.2.2.1) ?_ hQ1 hsupQ.2.2.2 hQ2' hQ3
    h01 h02 h03
  rw [labelFrame_F]
  exact MajorFrame.fit hdetQ _ p.κ hposQ

/-- **Native-signal groups of a descendant label**, in its own frame with the parent's hidden
scale, from a density mask at one grid depth and a floor of the prepared incidences. -/
theorem path_label_groups (hν : ∀ w, IsProbabilityMeasure (ν w)) (hNk : 1 < Nk)
    {A C : ℕ} (hC : GroupsProp A C)
    (Q b₀ : Fin p.C) (hdesc : forestAncestor p.lev p.par Q (p.lev b₀) = b₀)
    (hlev : p.lev b₀ ≤ p.lev Q) (hB : 0 < B (p.world Q))
    {SQ : Set Incidence} (hSm : MeasurableSet SQ) (hSQ : SQ ⊆ p.counted Q)
    {τQ : ℝ} (hτQ : 0 < τQ)
    (hfloor : ENNReal.ofReal τQ * ((ν (p.world Q)).prod volume) (p.packet Q) ≤
      ((ν (p.world Q)).prod volume) SQ)
    {g : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal} (hg : Measurable g) {rj τ h : ℝ}
    (hlaw : (((ν (p.world Q)).prod volume).restrict (E (p.world Q))).map
      (obs (B (p.world Q)) (δ Nk rj)) = (volume.prod Measure.count).withDensity g)
    (hmask : SQ ⊆ E (p.world Q) ∩
      {x | g (obs (B (p.world Q)) (δ Nk rj) x) ≤ ENNReal.ofReal (Nk ^ (-f rj + τ))})
    (hh : 0 ≤ h) (hratio : δ Nk (p.r (p.lev Q)) ≤ 2 * Nk ^ h * δ Nk rj)
    (hprof : f (p.r (p.lev Q)) - 2 * (δ₀ * L) ≤ f rj)
    (ha1 : δ Nk (p.r (p.lev Q)) ≤ δ Nk (p.r (p.lev b₀)))
    {K : ℝ} (hK2 : 2 ≤ K) (hK7 : 7 * p.κ ≤ K)
    (hKbig : p.κ * (4 * Nk ^ h + 2) * Nk ^ (τ + 2 * (δ₀ * L)) *
      (16 * (1 + (7 * p.κ) ^ 2)) ≤ K * τQ) :
    ∃ (n : ℕ) (Eg : Fin n → Set (Trajectory × ℝ)), (n : ℝ) ≤ K ^ C ∧
      (∀ i, MeasurableSet (Eg i)) ∧ (∀ i j, i ≠ j → Disjoint (Eg i) (Eg j)) ∧
      muE (ν (p.world Q)) (p.assigned Q)
          (labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).F.t₀
          (labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).F.q SQ (⋃ i, Eg i)ᶜ ≤
        ENNReal.ofReal ((K ^ A)⁻¹) * muE (ν (p.world Q)) (p.assigned Q)
          (labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).F.t₀
          (labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).F.q SQ univ ∧
      ∀ i y, y ∈ Eg i → ∀ y', y' ∈ Eg i →
        |value ((labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).normTest
            (δ Nk (p.r (p.lev b₀))) (p.test b₀))
            (pointS (labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).eb y) -
          value ((labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).normTest
            (δ Nk (p.r (p.lev b₀))) (p.test b₀))
            (pointS (labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).eb y')| ≤
          K ^ C * (δ Nk (p.r (p.lev Q)) / δ Nk (p.r (p.lev b₀)) +
            ‖nativeBase (pointS (labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀)))).eb y) -
              nativeBase (pointS (labelFrame p Q (B (p.world Q))
                (δ Nk (p.r (p.lev b₀)))).eb y')‖) := by
  set Φ := labelFrame p Q (B (p.world Q)) (δ Nk (p.r (p.lev b₀))) with hΦ
  set w := p.world Q
  set δp := δ Nk (p.r (p.lev b₀))
  set δQ := δ Nk (p.r (p.lev Q))
  have hNk0 : 0 < Nk := by linarith
  have hδ (r : ℝ) : 0 < δ Nk r := lt_of_lt_of_le (Real.rpow_pos_of_pos hNk0 _) (δ_bounds hNk r).1
  have hκ1 := hp.one_le_slack
  have hκ0 : 0 < p.κ := by linarith
  letI : IsProbabilityMeasure (ν w) := hν w
  have hq := labelFrame_q_pos hp Q (B w) δp
  have hD := labelFrame_det hp Q (B w) δp
  -- the prior and the law
  have hprior := label_prior_floor hp hNk0 Q
  have hdetQ : 0 < |(p.frame Q).det| := abs_pos.mpr (hp.chart Q).1
  have hA0 : 0 < ν w (p.assigned Q) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hprior
  have hA0t : ν w (p.assigned Q) ≠ ⊤ := measure_ne_top _ _
  set μ := muE (ν w) (p.assigned Q) Φ.F.t₀ Φ.F.q SQ with hμ
  have hpk : ((ν w).prod volume) (p.packet Q) =
      ENNReal.ofReal Φ.F.q * ν w (p.assigned Q) := by
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc, mul_comm, hΦ, labelFrame_F]
    congr 2
    rw [← sub_div]
    ring
  have hmass : μ univ = (ENNReal.ofReal Φ.F.q * ν w (p.assigned Q))⁻¹ *
      ((ν w).prod volume) SQ := by
    rw [hμ, muE_apply _ _ _ _ _ MeasurableSet.univ, preimage_univ, univ_inter]
  have hc0 : ENNReal.ofReal Φ.F.q * ν w (p.assigned Q) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hq).ne' hA0.ne'
  have hct : ENNReal.ofReal Φ.F.q * ν w (p.assigned Q) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA0t
  have hτμ : ENNReal.ofReal τQ ≤ μ univ := by
    rw [hmass, ← hpk]
    have hpkt : ((ν w).prod volume) (p.packet Q) ≠ ⊤ := by rw [hpk]; exact hct
    have hpk0 : ((ν w).prod volume) (p.packet Q) ≠ 0 := by rw [hpk]; exact hc0
    calc ENNReal.ofReal τQ = (((ν w).prod volume) (p.packet Q))⁻¹ *
          (ENNReal.ofReal τQ * ((ν w).prod volume) (p.packet Q)) := by
          rw [mul_comm (ENNReal.ofReal τQ), ← mul_assoc, ENNReal.inv_mul_cancel hpk0 hpkt,
            one_mul]
      _ ≤ _ := by gcongr
  have hμ0 : μ univ ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hτQ) hτμ).ne'
  have hsubpk : SQ ⊆ p.packet Q := fun z hz =>
    ⟨(hp.counted_support Q z (hSQ hz)).2.1, (hp.counted_support Q z (hSQ hz)).2.2.1⟩
  have hμt : μ univ ≠ ⊤ := by
    rw [hmass]
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0) ?_
    refine ne_top_of_le_ne_top ?_ (measure_mono hsubpk)
    rw [hpk]; exact hct
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hμt⟩
  -- the raw ceiling
  have hcap := pframe_raw_ceiling Φ hq hD (B w) δp (hδ _) rfl (ν w) (p.assigned Q) hA0 hA0t
    (hδ rj) hg hlaw (Mr := Nk ^ (-f rj + τ)) (by positivity) hmask
    (div_pos (hδ (p.r (p.lev Q))) (hδ (p.r (p.lev b₀))))
  have hdetD : |Φ.F.D.det| ≤ |(p.frame Q).det| := by
    rw [hΦ, labelFrame_F]
    exact (MajorFrame.abs_det (hp.chart Q).1).le
  have hν₀ : Nk ^ (-f (p.r (p.lev Q))) * |(p.frame Q).det| / p.κ ≤ (ν w (p.assigned Q)).toReal := by
    have := ENNReal.toReal_mono hA0t hprior
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hratio' : δp * (δQ / δp) ≤ 2 * Nk ^ h * δ Nk rj := by
    rw [mul_div_cancel₀ _ (hδ _).ne']
    exact hratio
  have hnum := raw_ceiling_numeric (τ := τ) (d := 0) (u := 0) (s := 0) hNk hκ1 hdetQ hdetD hν₀
    (div_pos (hδ _) (hδ _)) (hδ rj) (hδ _) hratio' hh (by simpa using hprof)
  simp only [mul_zero, neg_zero, Real.rpow_zero, mul_one] at hnum
  have hδj := hδ rj
  have hδQ0 := hδ (p.r (p.lev Q))
  have hδp0 := hδ (p.r (p.lev b₀))
  have hX0 : 0 ≤ |Φ.F.D.det| / (ν w (p.assigned Q)).toReal *
      (2 * (δp * (δQ / δp)) / δ Nk rj + 2) * Nk ^ (-f rj + τ) := by positivity
  have hD' : ENNReal.ofReal (|Φ.F.D.det| / (ν w (p.assigned Q)).toReal *
        (2 * (δp * (δQ / δp)) / δ Nk rj + 2) * Nk ^ (-f rj + τ)) *
      ENNReal.ofReal (16 * (1 + (7 * p.κ) ^ 2)) ≤ ENNReal.ofReal K * μ univ := by
    rw [← ENNReal.ofReal_mul hX0]
    calc ENNReal.ofReal (|Φ.F.D.det| / (ν w (p.assigned Q)).toReal *
          (2 * (δp * (δQ / δp)) / δ Nk rj + 2) * Nk ^ (-f rj + τ) *
          (16 * (1 + (7 * p.κ) ^ 2)))
        ≤ ENNReal.ofReal (K * τQ) := by
          apply ENNReal.ofReal_le_ofReal
          calc _ ≤ p.κ * (4 * Nk ^ h + 2) * Nk ^ (τ + 2 * (δ₀ * L)) *
                (16 * (1 + (7 * p.κ) ^ 2)) := by gcongr
            _ ≤ K * τQ := hKbig
      _ = ENNReal.ofReal K * ENNReal.ofReal τQ := ENNReal.ofReal_mul (by linarith)
      _ ≤ ENNReal.ofReal K * μ univ := by gcongr
  -- the native hypotheses almost everywhere
  have hgood7 : ∀ᵐ y ∂μ, pointS Φ.eb y ∈ goodSet (7 * p.κ) (δQ / δp)
      (Φ.normTest δp (p.test Q)) (Φ.normTest δp (p.test b₀)) := by
    apply ae_muE_of_forall _ _ _ _ hq.ne' hSm
    intro x hx
    exact label_framePoint_good hp Q b₀ hdesc hlev hB (hSQ hx)
  have htest : ∀ᵐ y ∂μ, |eval (exS Φ.eb y.1 y.2) (Φ.normTest δp (p.test Q))| ≤
      7 * p.κ * (δQ / δp) ∧
      (7 * p.κ)⁻¹ ≤ |eval (exS Φ.eb y.1 y.2) (pderiv (3 : Fin 4) (Φ.normTest δp (p.test Q)))| := by
    filter_upwards [hgood7] with y hy
    exact ⟨hy.2.1, hy.2.2.1⟩
  have hgood : ∀ᵐ y ∂μ, pointS Φ.eb y ∈ goodSet K (δQ / δp)
      (Φ.normTest δp (p.test Q)) (Φ.normTest δp (p.test b₀)) := by
    filter_upwards [hgood7] with y hy
    exact goodSet_mono (by linarith) hK7 (div_pos (hδ _) (hδ _)) hy
  have hdeg (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) :
      (Φ.normTest δp R).totalDegree ≤ 2 := (Φ.totalDegree_normTest_le δp R).trans hR
  exact hC μ hμ0 Φ.measurable_eb K (7 * p.κ) (δQ / δp) _ _ hK2 (by linarith)
    (div_pos (hδ _) (hδ _)) ((div_le_one (hδ _)).mpr ha1) (hdeg _ (hp.chart Q).2.2.2.2.1)
    (hdeg _ (hp.chart b₀).2.2.2.2.1) _ hcap hD' htest hgood

end

end

end Submission.Obl.k4_finite_affine_parent_sources
