-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2BlockWindows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2BlockWindows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2BlockWindows.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2BlockWindows.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Concentration
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLeftBlockAnchor
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarOriginalGroupWindows
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualReadingScales

set_option autoImplicit false

/-!
# First-jet windows and covers on one fitted block, version 2

The `j = 2` counterparts of x0662's and x0260's `ScalarBlockResidualWindows.lean`,
`ScalarResidualWindowTransfer.lean` and `ScalarBlockFirstJetCovers.lean` (o078, branch `x0260` at
`206ab988`), with the same proofs:

* `UpperHyp.exists_v2_block_residual_windows`: on a block `[s, s + H]` where both row components
  are affine up to `K H p`, an anchor time `t₀` and a measurable set of labels of mass
  `≥ H · duration / (400000 K⁸)` whose first jets at `t₀` lie within `p^((1-d)/4) + B p` of a
  center depending only on their scalar `H`-bin at `t₀`;
* `v2_first_jet_covers_of_block_windows`: those windows give, at every time of the block, lists
  of `≤ 1000 B²` values indexed by the current scalar `H`-bin covering the first jets within any
  `r ≥ H^((1-d)/32)` (`p = H^(1/8)`);
* `UpperHyp.exists_v2_block_first_jet_covers`: both together.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

namespace UpperHyp

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
  {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d : ℝ}

/-- **Residual windows on one block** (version 2). -/
theorem exists_v2_block_residual_windows [IsProbabilityMeasure ν] (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hζ : 0 < ζ) (hd0 : 0 ≤ d) (hd : d ≤ 1) {H s p duration : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1) (hHp : H ≤ p)
    (hζHp : ζ ≤ H * p) (hduration : 0 ≤ duration)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (hmass : H / K ≤ (ν.prod volume).real E)
    (a slope : Fin 2 → ℝ) (hslope : ∀ i, |slope i| ≤ K)
    (hrow : ∀ q ∈ E, ∀ i, |F q.2 i - (a i + slope i * q.2)| ≤ K * H * p)
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 2) Λ (Fin 2 → ℤ)
      (v2ResidualBound K) p duration) :
    ∃ (anchor : ℝ) (center : ℤ → ℝ) (A : Set Λ),
      anchor ∈ Icc (0 : ℝ) 1 ∧ MeasurableSet A ∧
      A ⊆ ((fun l => (l, s + H * anchor)) ⁻¹' E) ∧
      H * duration / (400000 * K ^ 8) ≤ (ν.prod volume).real (E ∩ (A ×ˢ univ)) ∧
      ∀ l ∈ A,
        |v2FirstJet (c l) F (fun _ => slope) (s + H * anchor) -
          center ⌊zS F (c l) (s + H * anchor) / H⌋| ≤
            p ^ ((1 - d) / 4) + v2ResidualBound K * p := by
  classical
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  let B := v2ResidualBound K
  let C := v2GroupConst K
  let cc := H ^ d
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hB : 0 < B := zero_lt_one.trans_le (v2ResidualBound_bounds hK).1
  have hC : 0 < C := by dsimp [C, v2GroupConst]; positivity
  have hc : 0 < cc := Real.rpow_pos_of_pos hH d
  have hζH : ζ ≤ H := hζHp.trans (mul_le_of_le_one_right hH.le hp1)
  obtain ⟨anchor, hanchor, _, hmass₀⟩ :=
    exists_original_left_block_anchor ν h.event_measurable hKpos hH hblock hmass
  let t₀ := s + H * anchor
  let A₀ : Set Λ := (fun l => (l, t₀)) ⁻¹' E
  let code := fun l => (⌊zS F (c l) t₀ / H⌋ : ℤ)
  let k := fun l => v2FirstJet (c l) F (fun _ => slope) t₀
  let Q := scalarLeftBlockEvent E A₀ s H
  have hA₀ : MeasurableSet A₀ := measurable_prodMk_right h.event_measurable
  have hQ : MeasurableSet Q := scalarLeftBlockEvent_measurable h.event_measurable hA₀ s H
  have hcode : Measurable code := ((measurable_zS_at h.measurable_c F t₀).div_const H).floor
  have hk : Measurable k := measurable_v2FirstJet_at h.measurable_c F _ t₀
  obtain ⟨J, hJ, hcover, hpriorcap, hprior⟩ :=
    h.v2_starting_group_palette (t₀ := t₀) hK hd0 hd hH hH1 hζH
  have hcellcap b (hb : b ∈ J) :
      (ν.prod scalarUnitTime).real (Q ∩ ((code ⁻¹' {b}) ×ˢ univ)) ≤ C * cc := by
    have hsub : Q ∩ ((code ⁻¹' {b}) ×ˢ univ) ⊆ (A₀ ∩ code ⁻¹' {b}) ×ˢ univ :=
      fun q hq => ⟨⟨hq.1.2, hq.2.1⟩, mem_univ _⟩
    have hh := measureReal_mono (μ := ν.prod scalarUnitTime) hsub (measure_ne_top _ _)
    rw [measureReal_prod_prod, show scalarUnitTime.real univ = 1 from by simp [Measure.real],
      mul_one] at hh
    have hpriorEq : ν.real (A₀ ∩ code ⁻¹' {b}) = (ν.restrict A₀).real (code ⁻¹' {b}) := by
      simp only [Measure.real, Measure.restrict_apply (hcode (MeasurableSet.singleton b)),
        inter_comm]
    exact (hh.trans_eq hpriorEq).trans (hpriorcap b hb)
  have hselect b (hb : b ∈ J)
      (hmassb : cc / B ≤ (ν.prod scalarUnitTime).real (Q ∩ ((code ⁻¹' {b}) ×ˢ univ))) :
      ∃ center : ℝ, duration <
        ((scalarGroupPrior (ν.restrict A₀) code b cc).prod scalarUnitTime).real
          ((Q ∩ ((code ⁻¹' {b}) ×ˢ univ)) ∩
            ({l | |k l - center| ≤ p ^ ((1 - d) / 4) + B * p} ×ˢ univ)) := by
    let Aᵦ := v2StartingLabels c F E t₀ H b
    let Qᵦ := scalarLeftBlockEvent E Aᵦ s H
    let νb := scalarGroupPrior (ν.restrict A₀) code b cc
    letI : IsFiniteMeasure νb := scalarGroupPrior_finite _ _ _ _
    have hAᵦ : MeasurableSet Aᵦ :=
      v2StartingLabels_measurable h.measurable_c h.event_measurable F t₀ H b
    have hQᵦ := scalarLeftBlockEvent_measurable h.event_measurable hAᵦ s H
    have hQᵦunit : Qᵦ ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
      fun q hq => ⟨mem_univ _, (scalarLeftBlockEvent_unit hH hblock hq).2⟩
    have hQeq : Q ∩ ((code ⁻¹' {b}) ×ˢ univ) = Qᵦ := by
      ext q
      simp only [Q, Qᵦ, Aᵦ, A₀, code, scalarLeftBlockEvent, v2StartingLabels,
        mem_inter_iff, mem_prod, mem_univ, mem_preimage, mem_setOf_eq, and_true,
        mem_singleton_iff]
      tauto
    have hmassnormal : B⁻¹ ≤ (νb.prod volume).real Qᵦ := by
      rw [← original_unit_time_prod_real νb hQᵦ hQᵦunit,
        original_scalar_group_left_mass scalarUnitTime ν A₀ code b hc hQᵦ
          (fun q hq => ⟨hq.2, mem_univ _⟩)]
      apply (le_div_iff₀ hc).mpr
      rw [hQeq] at hmassb
      have he : B⁻¹ * cc = cc / B := by ring
      simpa only [he] using hmassb
    obtain ⟨center, hcenter⟩ := h.exists_v2_residual_group_window hK hζ hd0 hd hH hH1 hp hp1 hHp
      hζHp hanchor hblock a slope hslope hrow hconcentration b (hprior b hb) hmassnormal
    refine ⟨center, ?_⟩
    rw [hQeq]
    have hwindow : MeasurableSet {l | |k l - center| ≤ p ^ ((1 - d) / 4) + B * p} := by
      have he : {l | |k l - center| ≤ p ^ ((1 - d) / 4) + B * p} =
          (fun l => k l - center) ⁻¹'
            Icc (-(p ^ ((1 - d) / 4) + B * p)) (p ^ ((1 - d) / 4) + B * p) := by
        ext l
        change |k l - center| ≤ p ^ ((1 - d) / 4) + B * p ↔
          -(p ^ ((1 - d) / 4) + B * p) ≤ k l - center ∧
            k l - center ≤ p ^ ((1 - d) / 4) + B * p
        exact abs_le
      rw [he]
      exact (hk.sub_const center) measurableSet_Icc
    rw [original_unit_time_prod_real νb (hQᵦ.inter (hwindow.prod MeasurableSet.univ))
      (fun q hq => hQᵦunit hq.1)]
    exact hcenter
  obtain ⟨center, W, hW, hwindow, hselected⟩ :=
    exists_original_group_window_restriction ν scalarUnitTime A₀ hQ
      (fun q hq => ⟨hq.2, mem_univ _⟩) code hcode k hk J (fun q hq => hcover q.1 hq.2)
      hc hC hB hduration hJ hcellcap hselect
  let A := A₀ ∩ W
  have hA : MeasurableSet A := hA₀.inter hW
  have hQW : Q ∩ (W ×ˢ univ) = scalarLeftBlockEvent E A s H := by
    ext q
    simp only [Q, A, scalarLeftBlockEvent, mem_inter_iff, mem_prod, mem_univ, mem_setOf_eq,
      and_true]
    tauto
  have hselectedmass : duration / (400000 * K ^ 8) ≤
      (ν.prod scalarUnitTime).real (scalarLeftBlockEvent E A s H) := by
    have hbudget := v2ResidualBound_starting_bin_budget hK
    change C / B ≤ (K⁻¹) ^ 2 / 2 at hbudget
    change (K⁻¹) ^ 2 ≤ (ν.prod scalarUnitTime).real Q at hmass₀
    have hhalf : (K⁻¹) ^ 2 / 2 ≤ (ν.prod scalarUnitTime).real Q - C / B := by linarith
    have hh := mul_le_mul_of_nonneg_left hhalf (div_nonneg hduration hC.le)
    rw [v2_residual_density_identity hKpos] at hh
    exact hh.trans (by simpa only [hQW] using hselected)
  have hmassphysical : H * duration / (400000 * K ^ 8) ≤
      (ν.prod volume).real (E ∩ (A ×ˢ univ)) := by
    rw [original_unit_time_prod_real ν (scalarLeftBlockEvent_measurable h.event_measurable hA s H)
      (fun q hq => ⟨mem_univ _, (scalarLeftBlockEvent_unit hH hblock hq).2⟩),
      original_left_block_event_real ν h.event_measurable hA s hH hblock] at hselectedmass
    have hh := (le_div_iff₀ hH).mp hselectedmass
    convert hh using 1
    ring
  refine ⟨anchor, center, A, hanchor, hA, inter_subset_left, hmassphysical, ?_⟩
  intro l hl
  exact (hwindow l hl.2).2

end UpperHyp

/-- **Covers at every time of the block from the anchor windows** (version 2). -/
theorem v2_first_jet_covers_of_block_windows {Λ : Type*} (c : Λ → Fin 7 → ℝ)
    (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (s : ℝ) (a slope : Fin 2 → ℝ)
    (A : Set Λ) (center : ℤ → ℝ) {H K B d anchor : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hB : 1 ≤ B) (hKB : 25 * K ^ 2 ≤ B)
    (hd0 : 0 ≤ d) (hd : d < 1) (hanchor : anchor ∈ Icc (0 : ℝ) 1)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (hblock : E ⊆ univ ×ˢ Icc s (s + H))
    (hcoeff : ∀ q ∈ E, ∀ e, |c q.1 e| ≤ K) (hF : ∀ t, ‖F t‖ ≤ K)
    (hslope : ∀ i, |slope i| ≤ K)
    (hrow : ∀ q ∈ E, ∀ i, |F q.2 i - (a i + slope i * q.2)| ≤ K * H * H ^ (1 / 8 : ℝ))
    (hA : A ⊆ ((fun l => (l, s + H * anchor)) ⁻¹' E))
    (hwindow : ∀ l ∈ A,
      |v2FirstJet (c l) F (fun _ => slope) (s + H * anchor) -
        center ⌊zS F (c l) (s + H * anchor) / H⌋| ≤
        (H ^ (1 / 8 : ℝ)) ^ ((1 - d) / 4) + B * H ^ (1 / 8 : ℝ)) :
    ∀ r : ℝ, H ^ ((1 - d) / 32) ≤ r →
      ∃ L : ℝ → ℤ → Finset ℝ, (∀ t z, ((L t z).card : ℝ) ≤ 1000 * B ^ 2) ∧
        ∀ l ∈ A, ∀ t, (l, t) ∈ E →
          ∃ v ∈ L t ⌊zS F (c l) t / H⌋, |v2FirstJet (c l) F (fun _ => slope) t - v| ≤ r := by
  classical
  let t₀ := s + H * anchor
  let code := fun l => (⌊zS F (c l) t₀ / H⌋ : ℤ)
  have hp : 0 < H ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hH _
  have hp1 : H ^ (1 / 8 : ℝ) ≤ 1 := Real.rpow_le_one hH.le hH1 (by norm_num)
  have hHp : H ≤ H ^ (1 / 8 : ℝ) := Real.self_le_rpow_of_le_one hH.le hH1 (by norm_num)
  have hK2 : 10 * K ^ 2 ≤ 25 * K ^ 2 := by nlinarith
  have hpoint l (hl : l ∈ A) t (ht : (l, t) ∈ E) :
      |(code l : ℝ) - (⌊zS F (c l) t / H⌋ : ℤ)| ≤ 25 * K ^ 2 + 1 ∧
      |v2FirstJet (c l) F (fun _ => slope) t - center (code l)| ≤
        (H ^ (1 / 8 : ℝ)) ^ ((1 - d) / 4) + B * H ^ (1 / 8 : ℝ) + 10 * K ^ 2 * H := by
    let u := (t - s) / H
    have hut : s + H * u = t := by simp only [u]; field_simp; ring
    have hq : (l, u) ∈ scalarLeftBlockEvent E
        {l' | (l', t₀) ∈ E ∧ (⌊zS F (c l') t₀ / H⌋ : ℤ) = code l} s H := by
      refine ⟨by simpa only [hut] using ht, hA hl, rfl⟩
    have hobs := v2_left_residual_observations c E F s a slope (code l) hH hHp hp1 hK hanchor
      hunit hblock hcoeff hF hslope hrow l u hq
    have hbound : |(zS F (c l) t - H * code l) / H| ≤ 25 * K ^ 2 := by
      simpa only [v2LeftObservation, hut] using hobs.1
    have hnear := normalized_scalar_bin_near_start hH (code l) hbound
    have hjet : |v2FirstJet (c l) F (fun _ => slope) t - v2FirstJet (c l) F (fun _ => slope) t₀| ≤
        10 * K ^ 2 * H := by
      simpa only [hut] using hobs.2.2
    refine ⟨by simpa only [abs_sub_comm] using hnear, ?_⟩
    exact (abs_sub_le _ (v2FirstJet (c l) F (fun _ => slope) t₀) _).trans
      (by linarith [hwindow l hl])
  intro r hr
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hH _).trans_le hr
  have hKB' : 23 * K ^ 2 ≤ B := by nlinarith
  have htime t : ∃ L : ℤ → Finset ℝ, (∀ z, ((L z).card : ℝ) ≤ 1000 * B ^ 2) ∧
      ∀ l ∈ {l | l ∈ A ∧ (l, t) ∈ E}, ∃ v ∈ L ⌊zS F (c l) t / H⌋,
        |v2FirstJet (c l) F (fun _ => slope) t - v| ≤ r := by
    -- the window radius and the bin distance of x0260's reading lemma, at `K' = K √(25/23)`
    have hwin : ∀ l ∈ {l | l ∈ A ∧ (l, t) ∈ E},
        |v2FirstJet (c l) F (fun _ => slope) t - center (code l)| ≤ 3 * B * r := by
      intro l hl
      have hreading := scalar_residual_window_reading_bound (K := 2 * K) hH hH1 hd0 hd hB
        (by nlinarith) hr
      have hh := (hpoint l hl.1 t hl.2).2
      have hKH : 10 * K ^ 2 * H ≤ 6 * (2 * K) ^ 2 * H := by nlinarith
      linarith
    obtain ⟨J, hJ, hcover⟩ := scalar_reading_cover_of_group_windows
      {l | l ∈ A ∧ (l, t) ∈ E} code (fun l => ⌊zS F (c l) t / H⌋)
      (fun l => v2FirstJet (c l) F (fun _ => slope) t) center
      (by positivity : 0 ≤ 25 * K ^ 2 + 1) (show 0 ≤ 3 * B by positivity) hrpos
      (fun l hl => (hpoint l hl.1 t hl.2).1) hwin
    have hcard : ∀ z, ((J z).card : ℝ) ≤ 1000 * B ^ 2 := by
      intro z
      refine (hJ z).trans ?_
      have hfirst : 2 * (25 * K ^ 2 + 1) + 3 ≤ 7 * B := by nlinarith
      have hsecond : 2 * (3 * B) + 3 ≤ 9 * B := by linarith
      have hh := mul_le_mul hfirst hsecond (by positivity : 0 ≤ 2 * (3 * B) + 3)
        (show 0 ≤ 7 * B by positivity)
      nlinarith [sq_nonneg B]
    exact scalar_interval_covers_of_grid_covers _ _ _ J hrpos hcard hcover
  choose L hLcard hLcover using htime
  exact ⟨L, hLcard, fun l hl t ht => hLcover t l ⟨hl, ht⟩⟩

namespace UpperHyp

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
  {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d : ℝ}

/-- **First-jet covers on one fitted block** (version 2). -/
theorem exists_v2_block_first_jet_covers [IsProbabilityMeasure ν] (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hζ : 0 < ζ) (hd0 : 0 ≤ d) (hd : d < 1) {H s duration : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hζHp : ζ ≤ H * H ^ (1 / 8 : ℝ)) (hduration : 0 ≤ duration)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (hmass : H / K ≤ (ν.prod volume).real E)
    (a slope : Fin 2 → ℝ) (hslope : ∀ i, |slope i| ≤ K)
    (hrow : ∀ q ∈ E, ∀ i, |F q.2 i - (a i + slope i * q.2)| ≤ K * H * H ^ (1 / 8 : ℝ))
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 2) Λ (Fin 2 → ℤ)
      (v2ResidualBound K) (H ^ (1 / 8 : ℝ)) duration) :
    ∃ A : Set Λ, MeasurableSet A ∧
      H * duration / (400000 * K ^ 8) ≤ (ν.prod volume).real (E ∩ (A ×ˢ univ)) ∧
      ∀ r : ℝ, H ^ ((1 - d) / 32) ≤ r →
        ∃ L : ℝ → ℤ → Finset ℝ,
          (∀ t z, ((L t z).card : ℝ) ≤ 1000 * (v2ResidualBound K) ^ 2) ∧
          ∀ l ∈ A, ∀ t, (l, t) ∈ E →
            ∃ v ∈ L t ⌊zS F (c l) t / H⌋,
              |v2FirstJet (c l) F (fun _ => slope) t - v| ≤ r := by
  have hp : 0 < H ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hH _
  have hp1 : H ^ (1 / 8 : ℝ) ≤ 1 := Real.rpow_le_one hH.le hH1 (by norm_num)
  have hHp : H ≤ H ^ (1 / 8 : ℝ) := Real.self_le_rpow_of_le_one hH.le hH1 (by norm_num)
  obtain ⟨anchor, center, A, hanchor, hAm, hA, hmassA, hwindow⟩ :=
    h.exists_v2_block_residual_windows hK hζ hd0 hd.le hH hH1 hp hp1 hHp hζHp hduration
      hblock hmass a slope hslope hrow hconcentration
  refine ⟨A, hAm, hmassA, ?_⟩
  have hBb := v2ResidualBound_bounds hK
  exact v2_first_jet_covers_of_block_windows c E F s a slope A center hH hH1 hK hBb.1
    hBb.2.2.2.2.1 hd0 hd hanchor h.unit_time hblock (fun q hq => h.coefficients q hq)
    h.row_bounded hslope hrow hA hwindow

end UpperHyp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
