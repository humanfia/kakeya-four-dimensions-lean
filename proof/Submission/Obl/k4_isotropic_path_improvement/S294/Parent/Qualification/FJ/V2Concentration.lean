-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Concentration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Concentration.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Concentration.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Concentration.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2ResidualCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformResidualRange
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedSupport

set_option autoImplicit false

/-!
# Concentration of the first jet in one starting group, version 2

The `j = 2` counterpart of x0662's `ScalarResidualGroupConcentration.lean` and
`ScalarResidualFitConstants.lean` (o078, branch `x0260` at `206ab988`).  Inside one normalized
starting group (labels in one scalar `H`-bin at the anchor time) x0662's dimension-generic
residual kernel `OriginalScalarResidualAt`, used with `j = 2` and the codes of the `p`-cubes of the
tangential positions at the anchor, puts more than `duration` of the normalized group mass into
one window of the first jet of radius `p^((1-d)/4) + B p`, `B = v2ResidualBound K = 10⁶ K¹⁰`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-- The bound of the residual stage in version 2. -/
def v2ResidualBound (K : ℝ) : ℝ := 1000000 * K ^ 10

theorem v2ResidualBound_dominates {K c : ℝ} {m : ℕ} (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hcupper : c ≤ 1000000) (hm : m ≤ 10) : c * K ^ m ≤ v2ResidualBound K := by
  calc
    _ ≤ c * K ^ 10 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hm) hc
    _ ≤ 1000000 * K ^ 10 := mul_le_mul_of_nonneg_right hcupper (by positivity)
    _ = _ := rfl

theorem v2ResidualBound_bounds {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ v2ResidualBound K ∧ K ≤ v2ResidualBound K ∧ v2GroupConst K ≤ v2ResidualBound K ∧
      49 * K ^ 2 ≤ v2ResidualBound K ∧ 25 * K ^ 2 ≤ v2ResidualBound K ∧
      125 * (1 + 2 * K) ^ 2 * (125 * K ^ 4) ≤ v2ResidualBound K ∧
      400000 * K ^ 8 ≤ v2ResidualBound K := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have h1 : (1 : ℝ) * K ^ 0 ≤ v2ResidualBound K :=
    v2ResidualBound_dominates hK (by norm_num) (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) * K ^ 1 ≤ v2ResidualBound K :=
    v2ResidualBound_dominates hK (by norm_num) (by norm_num) (by norm_num)
  have h3 : (200000 : ℝ) * K ^ 6 ≤ v2ResidualBound K :=
    v2ResidualBound_dominates hK (by norm_num) (by norm_num) (by norm_num)
  have h4 : (49 : ℝ) * K ^ 2 ≤ v2ResidualBound K :=
    v2ResidualBound_dominates hK (by norm_num) (by norm_num) (by norm_num)
  have h5 : (25 : ℝ) * K ^ 2 ≤ v2ResidualBound K :=
    v2ResidualBound_dominates hK (by norm_num) (by norm_num) (by norm_num)
  have h6 : (140625 : ℝ) * K ^ 6 ≤ v2ResidualBound K :=
    v2ResidualBound_dominates hK (by norm_num) (by norm_num) (by norm_num)
  have h7 : (400000 : ℝ) * K ^ 8 ≤ v2ResidualBound K :=
    v2ResidualBound_dominates hK (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_zero, pow_one, one_mul, mul_one] at h1 h2
  refine ⟨h1, h2, h3, h4, h5, ?_, h7⟩
  have hsq : (1 + 2 * K) ^ 2 ≤ 9 * K ^ 2 := by nlinarith
  calc 125 * (1 + 2 * K) ^ 2 * (125 * K ^ 4) ≤ 125 * (9 * K ^ 2) * (125 * K ^ 4) := by gcongr
    _ = 140625 * K ^ 6 := by ring
    _ ≤ _ := h6

theorem v2ResidualBound_starting_bin_budget {K : ℝ} (hK : 1 ≤ K) :
    v2GroupConst K / v2ResidualBound K ≤ (K⁻¹) ^ 2 / 2 := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hBpos : 0 < v2ResidualBound K := zero_lt_one.trans_le (v2ResidualBound_bounds hK).1
  apply (div_le_iff₀ hBpos).mpr
  have hh := mul_le_mul_of_nonneg_left (v2ResidualBound_bounds hK).2.2.2.2.2.2
    (show 0 ≤ (K⁻¹) ^ 2 / 2 by positivity)
  have he : (K⁻¹) ^ 2 / 2 * (400000 * K ^ 8) = v2GroupConst K := by
    unfold v2GroupConst; field_simp; ring
  simpa only [he] using hh

theorem v2_residual_density_identity {K ρ : ℝ} (hK : 0 < K) :
    (ρ / v2GroupConst K) * ((K⁻¹) ^ 2 / 2) = ρ / (400000 * K ^ 8) := by
  unfold v2GroupConst
  field_simp
  ring

/-- The labels of one starting bin at time `t₀`. -/
def v2StartingLabels {Λ : Type*} (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (E : Set (Λ × ℝ))
    (t₀ H : ℝ) (b : ℤ) : Set Λ :=
  {l | (l, t₀) ∈ E ∧ (⌊zS F (c l) t₀ / H⌋ : ℤ) = b}

theorem v2StartingLabels_measurable {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) {E : Set (Λ × ℝ)} (hE : MeasurableSet E) (F : ℝ → Fin 2 → ℝ)
    (t₀ H : ℝ) (b : ℤ) : MeasurableSet (v2StartingLabels c F E t₀ H b) :=
  (measurable_prodMk_right hE).inter
    (((measurable_zS_at hc F t₀).div_const H).floor (MeasurableSet.singleton b))

namespace UpperHyp

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
  {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d : ℝ}

/-- **Concentration in one substantial starting group** (version 2). -/
theorem exists_v2_residual_group_window [IsFiniteMeasure ν] (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hζ : 0 < ζ) (hd0 : 0 ≤ d) (hd : d ≤ 1) {H p anchor duration s : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1) (hHp : H ≤ p)
    (hζHp : ζ ≤ H * p) (hanchor : anchor ∈ Icc (0 : ℝ) 1)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (a slope : Fin 2 → ℝ) (hslope : ∀ i, |slope i| ≤ K)
    (hrow : ∀ q ∈ E, ∀ i, |F q.2 i - (a i + slope i * q.2)| ≤ K * H * p)
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 2) Λ (Fin 2 → ℤ)
      (v2ResidualBound K) p duration)
    (bin : ℤ)
    (hprior : (scalarGroupPrior (ν.restrict ((fun l => (l, s + H * anchor)) ⁻¹' E))
      (fun l => ⌊zS F (c l) (s + H * anchor) / H⌋) bin (H ^ d)).real univ ≤ v2GroupConst K)
    (hmass : (v2ResidualBound K)⁻¹ ≤
      ((scalarGroupPrior (ν.restrict ((fun l => (l, s + H * anchor)) ⁻¹' E))
        (fun l => ⌊zS F (c l) (s + H * anchor) / H⌋) bin (H ^ d)).prod volume).real
          (scalarLeftBlockEvent E (v2StartingLabels c F E (s + H * anchor) H bin) s H)) :
    let t₀ := s + H * anchor
    let νb := scalarGroupPrior (ν.restrict ((fun l => (l, t₀)) ⁻¹' E))
      (fun l => ⌊zS F (c l) t₀ / H⌋) bin (H ^ d)
    ∃ center : ℝ, duration < (νb.prod volume).real
      (scalarLeftBlockEvent E (v2StartingLabels c F E t₀ H bin) s H ∩
        ({l | |v2FirstJet (c l) F (fun _ => slope) t₀ - center| ≤
          p ^ ((1 - d) / 4) + v2ResidualBound K * p} ×ˢ univ)) := by
  intro t₀ νb
  let B := v2ResidualBound K
  let A := v2StartingLabels c F E t₀ H bin
  letI : IsFiniteMeasure νb := scalarGroupPrior_finite _ _ _ _
  let Q := scalarLeftBlockEvent E A s H
  let k := fun l => v2FirstJet (c l) F (fun _ => slope) t₀
  let b := fun l => (zS F (c l) t₀ - H * bin) / H - anchor * k l
  let code : Λ → Fin 2 → ℤ := fun l => fun i => ⌊zy (c l) t₀ i / p⌋
  have hA : MeasurableSet A :=
    v2StartingLabels_measurable h.measurable_c h.event_measurable F t₀ H bin
  have hQ : MeasurableSet Q := scalarLeftBlockEvent_measurable h.event_measurable hA s H
  have hQunit : Q ⊆ A ×ˢ Icc (0 : ℝ) 1 := scalarLeftBlockEvent_unit hH hblock
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hBb := v2ResidualBound_bounds hK
  have hB1 : 1 ≤ B := hBb.1
  have hKB : K ≤ B := hBb.2.1
  have hζH : ζ ≤ H := hζHp.trans (mul_le_of_le_one_right hH.le hp1)
  have hk : Measurable k := measurable_v2FirstJet_at h.measurable_c F _ t₀
  have hcode : Measurable code := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_zy_coord_at h.measurable_c t₀ i).div_const p).floor
  have hY : ∀ l ∈ A, ∀ i, |zy (c l) t₀ i| ≤ 2 * K := fun l hl => (h.active_bounds hl.1).2.1
  obtain ⟨J, hJ, hcover⟩ := v2_residual_spatial_palette A (fun l => zy (c l) t₀) hK hp hp1 hY
  have hJbound : (J.card : ℝ) ≤ B * p ^ (-(2 : ℝ)) := hJ.trans
    (mul_le_mul_of_nonneg_right hBb.2.2.2.1 (Real.rpow_nonneg hp.le _))
  have hν : νb.real univ ≤ B := hprior.trans hBb.2.2.1
  have hsupport : ∀ u, IntervalAD p d B (scalarNormalizedSupport (scalarSupport c F E) s H bin u) :=
    fun u => CellProofs.Assouad.mono_constant hp
      (scalarNormalizedSupport_AD hζ hH hζHp h.support_AD bin u) hKB
  have hobs := v2_left_residual_observations c E F s a slope bin hH hHp hp1 hK hanchor
    h.unit_time hblock (fun q hq => h.coefficients q hq) h.row_bounded hslope hrow
  have hpoint : ∀ l u, (l, u) ∈ Q →
      v2LeftObservation c F s H bin (u, l) ∈
        scalarNormalizedSupport (scalarSupport c F E) s H bin u ∩ Icc (-B) B := by
    intro l u hl
    refine ⟨⟨zS F (c l) (s + H * u), ⟨l, hl.1, rfl⟩, ?_⟩, ?_⟩
    · simp only [v2LeftObservation]; field_simp
    · exact abs_le.mp ((hobs l u hl).1.trans hBb.2.2.2.2.1)
  have hmodel : ∀ l u, (l, u) ∈ Q →
      |v2LeftObservation c F s H bin (u, l) - (b l + k l * u)| ≤ B * p := by
    intro l u hl
    refine (hobs l u hl).2.1.trans (mul_le_mul_of_nonneg_right ?_ hp.le)
    have : 15 * K ^ 2 ≤ 25 * K ^ 2 := by nlinarith
    exact this.trans hBb.2.2.2.2.1
  have hspread : ∀ l ∈ A, ∀ l' ∈ A, code l = code l' → |k l - k l'| ≤ B * p := by
    intro l hl l' hl' he
    have hS : |zS F (c l) t₀ - zS F (c l') t₀| ≤ H :=
      same_mesh_cell_close hH (hl.2.trans hl'.2.symm)
    have hR := h.residual_comparison (l, t₀) hl.1 (l', t₀) hl'.1
    simp only [sub_self, abs_zero, zero_add] at hR
    have hh := v2_frozen_first_jet_spread (c l) (c l') F t₀ slope hK hH hHp hζH (h.row_bounded t₀)
      hslope hS hR (fun i => congrFun he i)
    refine hh.trans (mul_le_mul_of_nonneg_right ?_ hp.le)
    have : 8 * K ^ 2 ≤ 25 * K ^ 2 := by nlinarith
    exact this.trans hBb.2.2.2.2.1
  have hjoint : ∀ u j, j ∈ J → ∀ z : ℤ,
      νb.real {l | (l, u) ∈ Q ∧ code l = j ∧
        (⌊v2LeftObservation c F s H bin (u, l) / p⌋ : ℤ) = z} ≤ B * p ^ (2 + d) := by
    intro u j _ z
    have hcap : ∀ t a b₀ b₁ : ℝ,
        ν.real {l | (l, t) ∈ E ∧ zy (c l) t 0 ∈ Icc b₀ (b₀ + H * p) ∧
          zy (c l) t 1 ∈ Icc b₁ (b₁ + H * p) ∧ zS F (c l) t ∈ Icc a (a + H * p)} ≤
          (125 * K ^ 4) * (H * p) ^ (2 + d) := by
      intro t a' b₀ b₁
      have hh := h.anchor_joint_cap hK hd0 hd t a' b₀ b₁ (H * p) hζHp (mul_pos hH hp)
      refine le_trans (measureReal_mono ?_ (measure_ne_top ν _)) hh
      rintro l ⟨hl, h0, h1, h2⟩
      exact ⟨hl, h2, h0, h1⟩
    have hh := v2_left_residual_group_cap c h.measurable_c ν h.event_measurable h.row_measurable
      s bin hH hH1 hp hHp hK0 (by positivity) hanchor hblock
      (fun q hq => ⟨h.coefficients q hq 4, h.coefficients q hq 6⟩) hcap u j z
    exact hh.trans (mul_le_mul_of_nonneg_right hBb.2.2.2.2.2.1 (Real.rpow_nonneg hp.le _))
  exact hconcentration νb Q A (v2LeftObservation c F s H bin) b k code J
    (scalarNormalizedSupport (scalarSupport c F E) s H bin) hQ hQunit
    (v2LeftObservation_measurable h.measurable_c h.row_measurable s H bin) hk hcode hν hmass
    hJbound (fun l u hl => hcover l (hQunit hl).1) hsupport hpoint hmodel hspread hjoint

end UpperHyp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
