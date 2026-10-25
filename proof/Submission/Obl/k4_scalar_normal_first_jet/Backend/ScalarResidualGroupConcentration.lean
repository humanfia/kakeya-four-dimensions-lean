/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarResidualGroupConcentration.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarResidualGroupConcentration.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformResidualRange
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualCurrentCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualFitConstants
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockGroup
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockGraph
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedSupport

/-! Concentration for every substantial original residual group, with all inputs derived. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

namespace ScalarNormalHyp

theorem exists_original_residual_group_window {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsFiniteMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d H p anchor duration s : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : d ≤ 1)
    (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1) (hHp : H ≤ p)
    (hζHp : ζ ≤ H * p) (hanchor : anchor ∈ Icc (0 : ℝ) 1)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (a slope : ℝ) (hslope : |slope| ≤ K)
    (hrow : ∀ q ∈ E, |F q.2 - (a + slope * q.2)| ≤ K * H * p)
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 1) Λ ℤ (scalarBlockFitBound K) p duration)
    (bin : ℤ)
    (hprior : (scalarGroupPrior (ν.restrict ((fun l => (l, s + H * anchor)) ⁻¹' E))
      (fun l => ⌊D.scalar F l (s + H * anchor) / H⌋) bin (H ^ d)).real univ ≤ 10000 * K ^ 4)
    (hmass : (scalarBlockFitBound K)⁻¹ ≤
      ((scalarGroupPrior (ν.restrict ((fun l => (l, s + H * anchor)) ⁻¹' E))
        (fun l => ⌊D.scalar F l (s + H * anchor) / H⌋) bin (H ^ d)).prod volume).real
          (scalarLeftBlockEvent E (scalarStartingLabels D E F (s + H * anchor) H bin) s H)) :
    let c := s + H * anchor
    let νb := scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
      (fun l => ⌊D.scalar F l c / H⌋) bin (H ^ d)
    ∃ center : ℝ, duration < (νb.prod volume).real
      (scalarLeftBlockEvent E (scalarStartingLabels D E F c H bin) s H ∩
        ({l | |scalarFirstJet D F (fun _ => slope) l c - center| ≤
          p ^ ((1 - d) / 4) + scalarBlockFitBound K * p} ×ˢ univ)) := by
  let B := scalarBlockFitBound K
  let c := s + H * anchor
  let A := scalarStartingLabels D E F c H bin
  let νb := scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
    (fun l => ⌊D.scalar F l c / H⌋) bin (H ^ d)
  letI : IsFiniteMeasure νb := scalarGroupPrior_finite _ _ _ _
  let Q := scalarLeftBlockEvent E A s H
  let k := fun l => scalarFirstJet D F (fun _ => slope) l c
  let b := fun l => (D.scalar F l c - H * bin) / H - anchor * k l
  let code := fun l => (⌊D.y l c / p⌋ : ℤ)
  have hA : MeasurableSet A := scalarStartingLabels_measurable D h.event_measurable F c H bin
  have hQ : MeasurableSet Q := scalarLeftBlockEvent_measurable h.event_measurable hA s H
  have hQunit : Q ⊆ A ×ˢ Icc (0 : ℝ) 1 := scalarLeftBlockEvent_unit hH hblock
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hB1 : 1 ≤ B := (scalarBlockFitBound_bounds hK).1
  have hKB : K ≤ B := (scalarBlockFitBound_bounds hK).2.1
  have hζH : ζ ≤ H := hζHp.trans (mul_le_of_le_one_right hH.le hp1)
  have hk : Measurable k := (D.measurable_at_residual F c).sub
    (measurable_const.mul (D.measurable_at_y c))
  have hcode : Measurable code := ((D.measurable_at_y c).div_const p).floor
  have hY l (hl : l ∈ A) : |D.y l c| ≤ 2 * K := (h.active_bounds hK hl.1).2.1
  obtain ⟨J, hJ, hcover⟩ := original_residual_spatial_palette A (fun l => D.y l c) hK hp hp1 hY
  have hJbound : (J.card : ℝ) ≤ B * p ^ (-1 : ℝ) := hJ.trans
    (mul_le_mul_of_nonneg_right (scalarBlockFitBound_residual_bounds hK).2.2.1 (Real.rpow_nonneg hp.le _))
  have hν : νb.real univ ≤ B := hprior.trans (scalarBlockFitBound_bounds hK).2.2.1
  have hsupport u : IntervalAD p d B (scalarNormalizedSupport S s H bin u) :=
    CellProofs.Assouad.mono_constant hp
      (scalarNormalizedSupport_AD hζ hH hζHp h.support_AD bin u) hKB
  have hobs := original_left_residual_observations D E F s a slope bin hH hHp hp1 hK hanchor
    h.unit_time hblock h.coefficients h.row_bounded hslope hrow
  have hpoint l u (hl : (l, u) ∈ Q) :
      scalarLeftObservation D F s H bin (u, l) ∈
        scalarNormalizedSupport S s H bin u ∩ Icc (-B) B := by
    refine ⟨scalarNormalizedSupport_mem h hH bin l hl.1, ?_⟩
    exact abs_le.mp (((hobs l u hl).1).trans (scalarBlockFitBound_residual_bounds hK).2.1)
  have hmodel l u (hl : (l, u) ∈ Q) :
      |scalarLeftObservation D F s H bin (u, l) - (b l + k l * u)| ≤ B * p :=
    ((hobs l u hl).2.1).trans (mul_le_mul_of_nonneg_right
      (scalarBlockFitBound_dominates (c := 16) (m := 2) hK (by norm_num) (by norm_num) (by norm_num)) hp.le)
  have hspread l (hl : l ∈ A) l' (hl' : l' ∈ A) (he : code l = code l') : |k l - k l'| ≤ B * p := by
    have hh := original_frozen_first_jet_spread D F A c slope hK hH hHp hζH (h.row_bounded c) hslope
      (fun l hl l' hl' => same_mesh_cell_close hH (hl.2.trans hl'.2.symm))
      (fun l hl l' hl' => by
        simpa only [sub_self, abs_zero, zero_add] using h.residual_comparison (l, c) hl.1 (l', c) hl'.1)
      hl hl' he
    exact hh.trans (mul_le_mul_of_nonneg_right
      (scalarBlockFitBound_dominates (c := 7) (m := 2) hK (by norm_num) (by norm_num) (by norm_num)) hp.le)
  have hjoint u j (_hj : j ∈ J) z :
      νb.real {l | (l, u) ∈ Q ∧ code l = j ∧ (⌊scalarLeftObservation D F s H bin (u, l) / p⌋ : ℤ) = z} ≤
        B * p ^ (1 + d) := by
    have hcap t y z : ν.real {l | (l, t) ∈ E ∧ D.y l t ∈ Icc y (y + H * p) ∧
        D.scalar F l t ∈ Icc z (z + H * p)} ≤ (16 * K ^ 3) * (H * p) ^ (1 + d) := by
      simpa only [and_comm, and_left_comm, and_assoc] using h.anchor_scalar_joint_cap hK hζ hd t z y (H * p) hζHp
    have hh := original_left_residual_group_cap D ν h.event_measurable h.row_measurable s bin
      hH hH1 hp hHp hK0 (by positivity) hanchor hblock
      (fun q hq => (h.coefficients q hq).2.2.2.2) hcap u j z
    have hcoef : 25 * (1 + 2 * K) * (16 * K ^ 3) ≤ 1200 * K ^ 4 := by
      nlinarith [pow_le_pow_right₀ hK (by norm_num : (3 : ℕ) ≤ 4)]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (hcoef.trans (scalarBlockFitBound_residual_bounds hK).1) (Real.rpow_nonneg hp.le _))
  exact hconcentration νb Q A (scalarLeftObservation D F s H bin) b k code J
    (scalarNormalizedSupport S s H bin) hQ hQunit (scalarLeftObservation_measurable D h.row_measurable s H bin)
    hk hcode hν hmass hJbound (fun l u hl => hcover l hl.2) hsupport hpoint hmodel hspread hjoint

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
