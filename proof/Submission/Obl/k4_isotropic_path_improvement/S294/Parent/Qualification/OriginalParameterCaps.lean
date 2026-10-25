-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalParameterCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalParameterCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalParameterCaps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalParameterCaps.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterFloors2Lower


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

def originalParameterCapConstant (K Kr d : ℝ) : ℝ :=
  2*(2*Kr*K*(2+2*K)^2*(6+6*K)^d)*(K+1)

/-- Original rectangle caps and original occupation floors give both
full affine-bin mass and coefficient-ball caps. Clipping is exact on
the original support; balls are recentered at actual original lines. -/
theorem original_parameter_coefficient_caps {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (S : Set Λ) (hS : MeasurableSet S) (p K Kr d : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) (hKr : 0 ≤ Kr) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (π : (Fin 2 → ℤ) → ENNReal)
    (hcoeff : ∀ l∈S, ∀ i, |c l i| ≤ K)
    (hocc : ∀ l∈S, ENNReal.ofReal K⁻¹ ≤ volume {t | (l,t)∈E})
    (hrect : ∀ (t₀ : ℝ) (Y : Fin 2 → ℝ) (a q w : ℝ) (J : Fin 2 → ℤ), p ≤ q → p ≤ w →
      (ν.prod volume) {z | z ∈ E ∧ z.2 ∈ Icc t₀ (t₀ + p) ∧
        (∀ i, zy (c z.1) z.2 i ∈ Icc (Y i) (Y i + q)) ∧ zx (c z.1) z.2 ∈ Icc a (a + w) ∧
        vbin p (c z.1) = J} ≤ ENNReal.ofReal (Kr * p * q ^ 2 * w ^ d) * π J)
    : (∀ β J, ν (affineWorld S c p β J) ≤
        ENNReal.ofReal (originalParameterCapConstant K Kr d*p^2)*π J) ∧
      ∀ β J (b : EuclideanSpace ℝ (Fin 3)) r, p ≤ r →
        ν (affineWorld S c p β J ∩ {l | scalarCoeffPoint K (c l)∈Metric.ball b r}) ≤
          ENNReal.ofReal (originalParameterCapConstant K Kr d*p^2*r^d)*π J := by
  let A := 2*Kr*K*(2+2*K)^2*(6+6*K)^d
  have hK0 : 0 ≤ K := by linarith
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hV (l : Λ) (hl : l∈S) (i : Fin 2) : |zv (c l) i| ≤ K := by
    fin_cases i
    · exact hcoeff l hl 4
    · exact hcoeff l hl 6
  have hAC : 2*A ≤ originalParameterCapConstant K Kr d := by
    dsimp [originalParameterCapConstant]
    change 2*A ≤ 2*A*(K+1)
    nlinarith
  have hAK : A*K ≤ originalParameterCapConstant K Kr d := by
    change A*K ≤ 2*A*(K+1)
    nlinarith
  constructor
  · intro β J
    have hh := affine_bin_coefficient_cap ν hc hE hunit hS hp hp1 hK hKr hd π hV hocc hrect β J
      (b₀ := 0) (b₁ := 0) (b₂ := 0) (by simpa using hK0) (by simpa using hK0)
      (r := K) (hp1.trans hK)
    have hsub : affineWorld S c p β J ⊆
        {l | l∈S ∧ ybin p (c l)=β ∧ vbin p (c l)=J ∧
          |c l 0-0| ≤ K ∧ |c l 1-0| ≤ K ∧ |c l 2-0| ≤ K} := by
      intro l hl
      exact ⟨hl.1,hl.2.1,hl.2.2,by simpa using hcoeff l hl.1 0,
        by simpa using hcoeff l hl.1 1,by simpa using hcoeff l hl.1 2⟩
    have hpow : K^d ≤ K := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hK hd1
    apply ((measure_mono hsub).trans hh).trans
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    calc
      A*p^2*K^d ≤ A*p^2*K := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hAK (sq_nonneg p)]
  · intro β J b r hr
    let W := affineWorld S c p β J ∩ {l | scalarCoeffPoint K (c l)∈Metric.ball b r}
    by_cases hw : W.Nonempty
    · obtain ⟨l0,hl0⟩ := hw
      have hr0 : 0 < r := hp.trans_le hr
      have hcoords (l : Λ) (hl : l∈W) (i : Fin 3) :
          |scalarCoeffPoint K (c l) i-scalarCoeffPoint K (c l0) i| ≤ 2*r := by
        have hd0 : dist (scalarCoeffPoint K (c l)) (scalarCoeffPoint K (c l0)) ≤ 2*r := by
          have h1 := Metric.mem_ball.mp hl.2
          have h2 := Metric.mem_ball.mp hl0.2
          have hh := dist_triangle (scalarCoeffPoint K (c l)) b (scalarCoeffPoint K (c l0))
          rw [dist_comm b] at hh
          linarith
        have hh := PiLp.norm_apply_le (p := (2 : ENNReal))
          (scalarCoeffPoint K (c l)-scalarCoeffPoint K (c l0)) i
        exact hh.trans (by simpa only [dist_eq_norm] using hd0)
      have hscalar (l : Λ) (hl : l∈W) : ∀ i : Fin 3,
          |(![c l 0,c l 1,c l 2] : Fin 3 → ℝ) i-
            (![c l0 0,c l0 1,c l0 2] : Fin 3 → ℝ) i| ≤ 2*r := by
        intro i
        have hh := hcoords l hl i
        rw [scalarCoeffPoint_apply,scalarCoeffPoint_apply] at hh
        fin_cases i
        · change |max (-K) (min K (c l 0))-max (-K) (min K (c l0 0))| ≤ 2*r at hh
          change |c l 0-c l0 0| ≤ 2*r
          simpa only [clip_eq (hcoeff l hl.1.1 0),clip_eq (hcoeff l0 hl0.1.1 0)] using hh
        · change |max (-K) (min K (c l 1))-max (-K) (min K (c l0 1))| ≤ 2*r at hh
          change |c l 1-c l0 1| ≤ 2*r
          simpa only [clip_eq (hcoeff l hl.1.1 1),clip_eq (hcoeff l0 hl0.1.1 1)] using hh
        · change |max (-K) (min K (c l 2))-max (-K) (min K (c l0 2))| ≤ 2*r at hh
          change |c l 2-c l0 2| ≤ 2*r
          simpa only [clip_eq (hcoeff l hl.1.1 2),clip_eq (hcoeff l0 hl0.1.1 2)] using hh
      have hsub : W ⊆ {l | l∈S ∧ ybin p (c l)=β ∧ vbin p (c l)=J ∧
          |c l 0-c l0 0| ≤ 2*r ∧ |c l 1-c l0 1| ≤ 2*r ∧ |c l 2-c l0 2| ≤ 2*r} := by
        intro l hl
        exact ⟨hl.1.1,hl.1.2.1,hl.1.2.2,hscalar l hl 0,hscalar l hl 1,hscalar l hl 2⟩
      have hh := affine_bin_coefficient_cap ν hc hE hunit hS hp hp1 hK hKr hd π hV hocc hrect β J
        (b₀ := c l0 0) (hcoeff l0 hl0.1.1 1) (hcoeff l0 hl0.1.1 2) (r := 2*r) (by linarith)
      apply ((measure_mono hsub).trans hh).trans
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have h2 : (2 : ℝ)^d ≤ 2 := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hd1
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr0.le]
      calc
        A*p^2*(2^d*r^d) ≤ (2*A)*p^2*r^d := by
          nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hA0 (sq_nonneg p))
            (Real.rpow_nonneg hr0.le d))]
        _ ≤ _ := by gcongr
    · have hempty : W=∅ := Set.not_nonempty_iff_eq_empty.mp hw
      change ν W ≤ _
      rw [hempty,measure_empty]
      exact bot_le

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
