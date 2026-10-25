/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNormalizedBlockFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNormalizedBlockFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarSubpowerBlockFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformRangeLocalFit

/-! The actual block construction depends only on the normalized fit property. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open WangZahlLot.Obl.wz_slab_local_linearity

theorem original_scalar_block_fit_of_normalized_fit {Λ : Type*} [MeasurableSpace Λ]
    {K p d duration : ℝ} (hK : 1 ≤ K) (hp : 0 < p) (hd : d ≤ 1)
    (hfit : OriginalScalarNormalizedFitAt (d := d) Λ (scalarBlockFitBound K) p duration) :
    OriginalScalarBlockFitAt (d := d) Λ K p duration := by
  let B := scalarBlockFitBound K
  intro D ν _ E F S ζ H s h hζ hH hH1 hHp hζH2 hblock hmass
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hKsq : K ≤ K ^ 2 := by nlinarith [hK]
  have hζH : ζ ≤ H := hζH2.trans (by nlinarith)
  have hζHp : ζ ≤ H * p := hζH2.trans (by nlinarith)
  obtain ⟨anchor, bin, hanchor, hc, hprior, hselected⟩ :=
    h.exists_original_block_search hK hζ hd hH hH1 hζH hblock hmass
  let c := s + H * anchor
  let A := scalarStartingLabels D E F c H bin
  let νb := scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
    (fun l => ⌊D.scalar F l c / H⌋) bin (H ^ d)
  let μ := scalarIntervalTime (-anchor)
  letI : IsProbabilityMeasure μ := scalarIntervalTime_probability _
  letI : IsFiniteMeasure νb := scalarGroupPrior_finite _ _ _ _
  let E' := scalarCenteredEvent E A c H
  have hA : MeasurableSet A := scalarStartingLabels_measurable D h.event_measurable F c H bin
  have hE' : MeasurableSet E' := scalarCenteredEvent_measurable h.event_measurable hA c H
  have hcblock : c ∈ Icc s (s + H) := by
    dsimp [c]
    constructor <;> nlinarith [hanchor.1, hanchor.2]
  have hE'unit : E' ⊆ Icc (-1 : ℝ) 1 ×ˢ A := scalarCenteredEvent_unit hH hcblock hblock
  obtain ⟨g, G, hgc, hnear, hf0, hf, hG, hbound, hmodel⟩ :=
    h.exists_actual_block_observations hK hH hH1 hζ.le hζH2 hc bin
  let v := scalarScaledAnchor D (K) c
  let Z := scalarBlockStart D F c H bin
  let Obs := scalarNormalizedValue D F c H bin
  let f := scalarBlockRow g F c H (K)
  let S' := scalarNormalizedSupport S c H bin
  obtain ⟨hB1, hKB, hpriorB, hmassB, hcapB, herrB, hGB, hObsB, hvB⟩ :=
    scalarBlockFitBound_bounds hK
  have hS' (u : ℝ) : IntervalAD p d (B) (S' u) := by
    exact CellProofs.Assouad.mono_constant hp
      (scalarNormalizedSupport_AD hζ hH hζHp h.support_AD bin u) hKB
  have hv : Measurable v := measurable_const.mul (D.measurable_at_y c)
  have hZ : Measurable Z := ((D.measurable_at_scalar F c).sub_const (H * bin)).div_const H
  have hObs : Measurable Obs := scalarNormalizedValue_measurable D h.row_measurable c H bin
  have hGb (x y : ℝ) : |G x - G y| ≤ B * |x - y| :=
    (hG x y).trans (by nlinarith [abs_nonneg (x - y)])
  have hvs (l : Λ) (hl : l ∈ A) : |v l| ≤ B ∧ |G (v l)| ≤ B :=
    ⟨((hbound l hl).1).trans hvB, ((hbound l hl).2.1).trans hGB⟩
  have hcurrent u l (hl : (u, l) ∈ E') : Obs (u, l) ∈ S' u ∩ Icc (-(B)) (B) := by
    have hu : |u| ≤ 1 := abs_le.mpr (hE'unit hl).1
    exact ⟨scalarNormalizedSupport_mem h hH bin l hl.1,
      abs_le.mp (((hmodel u l hu hl.2.2 hl.1).1).trans hObsB)⟩
  have hstart l (hl : l ∈ A) : Z l ∈ S' 0 ∩ Icc (-(B)) (B) := by
    have hz := (hbound l hl).2.2
    have hzbound : |Z l| ≤ B :=
      (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩).trans hB1
    refine ⟨?_, abs_le.mp hzbound⟩
    simpa only [Z, scalarBlockStart, scalarNormalizedValue, mul_zero, add_zero] using
      scalarNormalizedSupport_mem h hH bin l (show (l, c + H * 0) ∈ E from by simpa using hl.1)
  have herror u l (hl : (u, l) ∈ E') :
      |Obs (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ B * p := by
    exact ((hmodel u l (abs_le.mpr (hE'unit hl).1) hl.2.2 hl.1).2).trans
      (mul_le_mul herrB hHp hH.le (zero_le_one.trans hB1))
  have hjoint a b r (hr : p ≤ r) :
      νb.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b (b + r)} ≤ B * r ^ (1 + d) := by
    have hcap := h.starting_group_joint_cap (c := c) hK hζ hd hH hH1 (hp.trans_le hr)
      (hζHp.trans (mul_le_mul_of_nonneg_left hr hH.le)) bin a b
    exact hcap.trans (mul_le_mul_of_nonneg_right hcapB (Real.rpow_nonneg (hp.le.trans hr) _))
  have hmass' : (B)⁻¹ ≤ (μ.prod νb).real E' :=
    (scalarBlockFitBound_inverse hK).trans hselected
  obtain ⟨U, a, slope, hUm, hUunit, hUactive, hUvol, ha, hslope, hfit⟩ :=
    hfit μ νb E' A v Z Obs f G S' (S' 0) (scalarIntervalTime_le_volume _) hE' hE'unit
      hv hZ hObs hf0 hf hGb hvs hS' (hS' 0) hcurrent hstart herror hjoint hmass'
  let L := 6 * K ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hgfit u (hu : u ∈ U) :
      |(g (c + H * u) - g c) / (H * L) - (-a + -slope * u)| ≤ 13 * p := by
    have he : (g (c + H * u) - g c) / (H * L) - (-a + -slope * u) =
        -(f u - (a + slope * u)) := by
      dsimp [f, scalarBlockRow, L]
      rw [hgc]
      field_simp <;> ring
    rw [he, abs_neg]
    exact hfit u hu
  obtain ⟨hTm, hTvol, hgphysical⟩ :=
    original_affine_fit_transport hUm g c (-a) (-slope) hH hL hUvol hgfit
  let T := (fun u => c + H * u) '' U
  let a' := g c + H * L * -a - L * -slope * c
  let slope' := L * -slope
  have hTactive : T ⊆ scalarNormalTimes E := by
    rintro t ⟨u, hu, rfl⟩
    obtain ⟨l, hl⟩ := hUactive u hu
    exact ⟨l, hl.1⟩
  have hTblock : T ⊆ Icc s (s + H) := by
    rintro t ⟨u, hu, rfl⟩
    obtain ⟨l, hl⟩ := hUactive u hu
    exact (hblock hl.1).2
  have hcunit : |c| ≤ 1 := by
    have ht := h.active_unit_time hc
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hcoeff := original_affine_fit_coefficients hH.le hH1 hL.le
    (show |g c| ≤ K from by rw [hgc]; exact h.row_bounded c) hcunit
    (show |-a| ≤ 9 by simpa only [abs_neg] using ha)
    (show |-slope| ≤ 4 by simpa only [abs_neg] using hslope)
  have hab : |a'| ≤ 80 * K ^ 2 := hcoeff.2.trans (by dsimp [L]; nlinarith)
  have hsb : |slope'| ≤ 80 * K ^ 2 := hcoeff.1.trans (by dsimp [L]; nlinarith)
  refine ⟨T, a', slope', hTm, hTblock, hTactive, hTvol, hab, hsb, ?_⟩
  intro t ht
  have hng : |F t - g t| ≤ 2 * K * ζ := by
    simpa only [abs_sub_comm] using hnear t (hTactive ht)
  have hphysical := hgphysical t ht
  have hnζ := mul_le_mul_of_nonneg_left hζHp (show 0 ≤ 2 * K by positivity)
  have hnK := mul_le_mul_of_nonneg_right hKsq (mul_nonneg hH.le hp.le)
  have htriangle := abs_sub_le (F t) (g t) (a' + slope' * t)
  dsimp [L] at hphysical
  change |F t - (a' + slope' * t)| ≤ 80 * K ^ 2 * H * p
  nlinarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
