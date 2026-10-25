/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockResidualWindows.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockResidualWindows.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualGroupConcentration
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLeftBlockAnchor
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarOriginalGroupWindows
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualReadingScales

/-! Sum all original starting-bin windows inside one actual scalar block. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

namespace ScalarNormalHyp

theorem exists_original_block_residual_windows {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d H s p duration : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : d ≤ 1)
    (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1) (hHp : H ≤ p)
    (hζHp : ζ ≤ H * p) (hduration : 0 ≤ duration)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (hmass : H / K ≤ (ν.prod volume).real E)
    (a slope : ℝ) (hslope : |slope| ≤ K)
    (hrow : ∀ q ∈ E, |F q.2 - (a + slope * q.2)| ≤ K * H * p)
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 1) Λ ℤ (scalarBlockFitBound K) p duration) :
    ∃ (anchor : ℝ) (center : ℤ → ℝ) (A : Set Λ),
      anchor ∈ Icc (0 : ℝ) 1 ∧ MeasurableSet A ∧
      A ⊆ ((fun l => (l, s + H * anchor)) ⁻¹' E) ∧
      H * duration / (20000 * K ^ 6) ≤ (ν.prod volume).real (E ∩ (A ×ˢ univ)) ∧
      ∀ l ∈ A,
        |scalarFirstJet D F (fun _ => slope) l (s + H * anchor) -
          center ⌊D.scalar F l (s + H * anchor) / H⌋| ≤
            p ^ ((1 - d) / 4) + scalarBlockFitBound K * p := by
  classical
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  let B := scalarBlockFitBound K
  let C := 10000 * K ^ 4
  let c := H ^ d
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hB : 0 < B := zero_lt_one.trans_le (scalarBlockFitBound_bounds hK).1
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := Real.rpow_pos_of_pos hH d
  have hζH : ζ ≤ H := hζHp.trans (mul_le_of_le_one_right hH.le hp1)
  obtain ⟨anchor, hanchor, _, hmass₀⟩ :=
    exists_original_left_block_anchor ν h.event_measurable hKpos hH hblock hmass
  let t₀ := s + H * anchor
  let A₀ : Set Λ := (fun l => (l, t₀)) ⁻¹' E
  let code := fun l => (⌊D.scalar F l t₀ / H⌋ : ℤ)
  let k := fun l => scalarFirstJet D F (fun _ => slope) l t₀
  let Q := scalarLeftBlockEvent E A₀ s H
  have hA₀ : MeasurableSet A₀ := measurable_prodMk_right h.event_measurable
  have hQ : MeasurableSet Q := scalarLeftBlockEvent_measurable h.event_measurable hA₀ s H
  have hQunit : Q ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun q hq => ⟨mem_univ _, (scalarLeftBlockEvent_unit hH hblock hq).2⟩
  have hcode : Measurable code := ((D.measurable_at_scalar F t₀).div_const H).floor
  have hk : Measurable k := (D.measurable_at_residual F t₀).sub
    (measurable_const.mul (D.measurable_at_y t₀))
  obtain ⟨J, hJ, hcover, hpriorcap, hprior⟩ :=
    h.original_starting_group_palette (c := t₀) hK hζ hd hH hH1 hζH
  have hcellcap b (hb : b ∈ J) :
      (ν.prod scalarUnitTime).real (Q ∩ ((code ⁻¹' {b}) ×ˢ univ)) ≤ C * c := by
    have hsub : Q ∩ ((code ⁻¹' {b}) ×ˢ univ) ⊆ (A₀ ∩ code ⁻¹' {b}) ×ˢ univ :=
      fun q hq => ⟨⟨hq.1.2, hq.2.1⟩, mem_univ _⟩
    have hh := measureReal_mono (μ := ν.prod scalarUnitTime) hsub
    rw [measureReal_prod_prod, show scalarUnitTime.real univ = 1 from by simp [Measure.real], mul_one] at hh
    have hpriorEq : ν.real (A₀ ∩ code ⁻¹' {b}) = (ν.restrict A₀).real (code ⁻¹' {b}) := by
      simp only [Measure.real, Measure.restrict_apply (hcode (MeasurableSet.singleton b)), inter_comm]
    exact (hh.trans_eq hpriorEq).trans (hpriorcap b hb)
  have hselect b (hb : b ∈ J)
      (hmassb : c / B ≤ (ν.prod scalarUnitTime).real (Q ∩ ((code ⁻¹' {b}) ×ˢ univ))) :
      ∃ center : ℝ, duration < ((scalarGroupPrior (ν.restrict A₀) code b c).prod scalarUnitTime).real
        ((Q ∩ ((code ⁻¹' {b}) ×ˢ univ)) ∩
          ({l | |k l - center| ≤ p ^ ((1 - d) / 4) + B * p} ×ˢ univ)) := by
    let Aᵦ := scalarStartingLabels D E F t₀ H b
    let Qᵦ := scalarLeftBlockEvent E Aᵦ s H
    let νb := scalarGroupPrior (ν.restrict A₀) code b c
    letI : IsFiniteMeasure νb := scalarGroupPrior_finite _ _ _ _
    have hAᵦ : MeasurableSet Aᵦ := scalarStartingLabels_measurable D h.event_measurable F t₀ H b
    have hQᵦ := scalarLeftBlockEvent_measurable h.event_measurable hAᵦ s H
    have hQᵦunit : Qᵦ ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
      fun q hq => ⟨mem_univ _, (scalarLeftBlockEvent_unit hH hblock hq).2⟩
    have hQeq : Q ∩ ((code ⁻¹' {b}) ×ˢ univ) = Qᵦ := by
      ext q
      simp only [Q, Qᵦ, Aᵦ, A₀, code, scalarLeftBlockEvent, scalarStartingLabels,
        mem_inter_iff, mem_prod, mem_univ, mem_preimage, mem_setOf_eq, and_true]
      tauto
    have hmassnormal : B⁻¹ ≤ (νb.prod volume).real Qᵦ := by
      rw [← original_unit_time_prod_real νb hQᵦ hQᵦunit,
        original_scalar_group_left_mass scalarUnitTime ν A₀ code b hc hQᵦ
          (fun q hq => ⟨hq.2, mem_univ _⟩)]
      apply (le_div_iff₀ hc).mpr
      rw [hQeq] at hmassb
      have he : B⁻¹ * c = c / B := by ring
      simpa only [he] using hmassb
    obtain ⟨center, hcenter⟩ := h.exists_original_residual_group_window hK hζ hd hH hH1 hp hp1 hHp hζHp
      hanchor hblock a slope hslope hrow hconcentration b (hprior b hb) hmassnormal
    refine ⟨center, ?_⟩
    rw [hQeq]
    have hwindow : MeasurableSet {l | |k l - center| ≤ p ^ ((1 - d) / 4) + B * p} := by
      have he : {l | |k l - center| ≤ p ^ ((1 - d) / 4) + B * p} =
          (fun l => k l - center) ⁻¹' Icc (-(p ^ ((1 - d) / 4) + B * p)) (p ^ ((1 - d) / 4) + B * p) := by
        ext l
        change |k l - center| ≤ p ^ ((1 - d) / 4) + B * p ↔
          -(p ^ ((1 - d) / 4) + B * p) ≤ k l - center ∧ k l - center ≤ p ^ ((1 - d) / 4) + B * p
        exact abs_le
      rw [he]
      exact (hk.sub_const center) measurableSet_Icc
    rw [original_unit_time_prod_real νb (hQᵦ.inter (hwindow.prod MeasurableSet.univ))
      (fun q hq => hQᵦunit hq.1)]
    exact hcenter
  obtain ⟨center, W, hW, hwindow, hselected⟩ := exists_original_group_window_restriction ν scalarUnitTime A₀ hQ
    (fun q hq => ⟨hq.2, mem_univ _⟩) code hcode k hk J (fun q hq => hcover q.1 hq.2)
    hc hC hB hduration hJ hcellcap hselect
  let A := A₀ ∩ W
  have hA : MeasurableSet A := hA₀.inter hW
  have hQW : Q ∩ (W ×ˢ univ) = scalarLeftBlockEvent E A s H := by
    ext q
    simp only [Q, A, scalarLeftBlockEvent, mem_inter_iff, mem_prod, mem_univ, mem_setOf_eq, and_true]
    tauto
  have hselectedmass : duration / (20000 * K ^ 6) ≤
      (ν.prod scalarUnitTime).real (scalarLeftBlockEvent E A s H) := by
    have hbudget := scalarBlockFitBound_starting_bin_budget hK
    change C / B ≤ (K⁻¹) ^ 2 / 2 at hbudget
    change (K⁻¹) ^ 2 ≤ (ν.prod scalarUnitTime).real Q at hmass₀
    have hhalf : (K⁻¹) ^ 2 / 2 ≤ (ν.prod scalarUnitTime).real Q - C / B := by linarith
    have hh := mul_le_mul_of_nonneg_left hhalf (div_nonneg hduration hC.le)
    dsimp only [C] at hh
    rw [scalar_residual_density_identity hKpos] at hh
    exact hh.trans (by simpa only [hQW] using hselected)
  have hmassphysical : H * duration / (20000 * K ^ 6) ≤ (ν.prod volume).real (E ∩ (A ×ˢ univ)) := by
    rw [original_unit_time_prod_real ν (scalarLeftBlockEvent_measurable h.event_measurable hA s H)
      (fun q hq => ⟨mem_univ _, (scalarLeftBlockEvent_unit hH hblock hq).2⟩),
      original_left_block_event_real ν h.event_measurable hA s hH hblock] at hselectedmass
    have hh := (le_div_iff₀ hH).mp hselectedmass
    convert hh using 1 <;> ring
  refine ⟨anchor, center, A, hanchor, hA, inter_subset_left, hmassphysical, ?_⟩
  intro l hl
  exact (hwindow l hl.2).2

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
