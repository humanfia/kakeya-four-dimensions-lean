-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Residual, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Residual.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Residual.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Residual.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Data
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLeftBlockEvent
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry

set_option autoImplicit false

/-!
# The residual model of the first jet on one block, version 2

The `j = 2` counterparts of x0662's and x0260's `ScalarFirstJetValue.lean`,
`ScalarAffineResidualModel.lean`, `ScalarResidualBlockModel.lean` and
`ScalarResidualObservations.lean` (o078, branch `x0260` at `206ab988`); paper `tex-05`, proof of
Prop. `prop:scalar-normal`, "the residual slopes".

* `v2FirstJet c F A t = R(t) - A(t) · y(t)`, `R = x' - F · y'` (`zR`): the first jet of the
  trajectory with coefficients `c` against the time row `F` and its candidate derivative `A`;
* `v2_affine_row_residual_model`: if both components of `F` are affine up to `K H p` on a block of
  length `H`, then in the normalized time `u` the normalized scalar is affine with slope the first
  jet `R(t₀) - slope · y(t₀)` up to `15 K² p`, and the first jet moves by at most `10 K² H`;
* `v2_frozen_first_jet_spread`: two trajectories in the same scalar `H`-bin and the same `p`-cube of
  tangential positions at one time have first jets within `8 K² p` (residual comparison);
* `v2LeftObservation`, `v2_left_residual_observations`: the normalized scalar observations of a
  starting bin on the left-normalized block.

Sup norms on `Fin 2 → ℝ` throughout.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-- The first jet `R(t) - A(t) · y(t)` of the trajectory with coefficients `c`. -/
def v2FirstJet (c : Fin 7 → ℝ) (F A : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  zR F c t - A t ⬝ᵥ zy c t

theorem v2FirstJet_eq (c : Fin 7 → ℝ) (F A : ℝ → Fin 2 → ℝ) (t : ℝ) :
    v2FirstJet c F A t = c 1 + 2 * c 2 * t - (F t 0 * c 4 + F t 1 * c 6) -
      (A t 0 * (c 3 + c 4 * t) + A t 1 * (c 5 + c 6 * t)) := by
  simp only [v2FirstJet, zR, dot_two, zy_zero, zy_one, zv_zero, zv_one]

theorem measurable_v2FirstJet_at {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) (F A : ℝ → Fin 2 → ℝ) (t : ℝ) :
    Measurable (fun l => v2FirstJet (c l) F A t) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun l => c l e) :=
    fun e => (measurable_pi_apply e).comp hc
  have h1 := hcomp 1; have h2 := hcomp 2; have h3 := hcomp 3; have h4 := hcomp 4
  have h5 := hcomp 5; have h6 := hcomp 6
  simp only [v2FirstJet_eq]
  fun_prop

theorem measurable_zS_at {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) (F : ℝ → Fin 2 → ℝ) (t : ℝ) :
    Measurable (fun l => zS F (c l) t) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun l => c l e) :=
    fun e => (measurable_pi_apply e).comp hc
  have h0 := hcomp 0; have h1 := hcomp 1; have h2 := hcomp 2; have h3 := hcomp 3
  have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
  simp only [zS, zx, dot_two, zy_zero, zy_one]
  fun_prop

theorem measurable_zy_coord_at {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) (t : ℝ) (i : Fin 2) :
    Measurable (fun l => zy (c l) t i) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun l => c l e) :=
    fun e => (measurable_pi_apply e).comp hc
  have h3 := hcomp 3; have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
  fin_cases i
  · simp only [Fin.zero_eta, zy_zero]; fun_prop
  · simp only [Fin.mk_one, zy_one]; fun_prop

/-- **The affine residual model** on a block where both row components are affine. -/
theorem v2_affine_row_residual_model (c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (t₀ base : ℝ)
    (a slope : Fin 2 → ℝ) {H p K u : ℝ} (hH : 0 < H) (hHp : H ≤ p) (hp1 : p ≤ 1) (hK : 1 ≤ K)
    (hu : |u| ≤ 1) (hc : ∀ e, |c e| ≤ K) (hY : ∀ i, |zy c t₀ i| ≤ 2 * K)
    (hslope : ∀ i, |slope i| ≤ K)
    (hrow₀ : ∀ i, |F t₀ i - (a i + slope i * t₀)| ≤ K * H * p)
    (hrow : ∀ i, |F (t₀ + H * u) i - (a i + slope i * (t₀ + H * u))| ≤ K * H * p) :
    |(zS F c (t₀ + H * u) - base) / H -
      ((zS F c t₀ - base) / H + u * (zR F c t₀ - slope ⬝ᵥ zy c t₀))| ≤ 15 * K ^ 2 * p ∧
    |v2FirstJet c F (fun _ => slope) (t₀ + H * u) - v2FirstJet c F (fun _ => slope) t₀| ≤
      10 * K ^ 2 * H := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hp : 0 < p := hH.trans_le hHp
  have hKsq : K ≤ K ^ 2 := by nlinarith
  set φ : Fin 2 → ℝ := fun i => (F (t₀ + H * u) i - F t₀ i) / H with hφdef
  have hφerr : ∀ i, |φ i - u * slope i| ≤ 2 * K * p := by
    intro i
    have he : φ i - u * slope i =
        ((F (t₀ + H * u) i - (a i + slope i * (t₀ + H * u))) -
          (F t₀ i - (a i + slope i * t₀))) / H := by
      simp only [hφdef]; field_simp; ring
    rw [he, abs_div, abs_of_pos hH, div_le_iff₀ hH]
    have h1 := hrow i; have h2 := hrow₀ i
    calc |F (t₀ + H * u) i - (a i + slope i * (t₀ + H * u)) - (F t₀ i - (a i + slope i * t₀))|
        ≤ |F (t₀ + H * u) i - (a i + slope i * (t₀ + H * u))| +
            |F t₀ i - (a i + slope i * t₀)| := abs_sub _ _
      _ ≤ K * H * p + K * H * p := add_le_add h1 h2
      _ = 2 * K * p * H := by ring
  have hus : ∀ i, |u * slope i| ≤ K := by
    intro i
    rw [abs_mul]
    exact (mul_le_mul hu (hslope i) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hφ : ∀ i, |φ i| ≤ 3 * K := by
    intro i
    have h1 := hφerr i; have h2 := hus i
    have h3 : 2 * K * p ≤ 2 * K := by nlinarith
    calc |φ i| = |(φ i - u * slope i) + u * slope i| := by ring_nf
      _ ≤ |φ i - u * slope i| + |u * slope i| := abs_add_le _ _
      _ ≤ 3 * K := by linarith
  have hc2 := hc 2; have hc4 := hc 4; have hc6 := hc 6
  have hu2 : |u ^ 2| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hu
  constructor
  · have hid : (zS F c (t₀ + H * u) - base) / H -
        ((zS F c t₀ - base) / H + u * (zR F c t₀ - slope ⬝ᵥ zy c t₀)) =
        H * (u ^ 2 * c 2 - u * (φ 0 * c 4 + φ 1 * c 6)) -
          ((φ 0 - u * slope 0) * zy c t₀ 0 + (φ 1 - u * slope 1) * zy c t₀ 1) := by
      simp only [hφdef, zS, zR, zx, dot_two, zy_zero, zy_one, zv_zero, zv_one]
      field_simp
      ring
    rw [hid]
    have hA : |H * (u ^ 2 * c 2 - u * (φ 0 * c 4 + φ 1 * c 6))| ≤ H * (7 * K ^ 2) := by
      rw [abs_mul, abs_of_pos hH]
      apply mul_le_mul_of_nonneg_left _ hH.le
      have e1 : |u ^ 2 * c 2| ≤ K := by
        rw [abs_mul]; exact (mul_le_mul hu2 hc2 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      have e2 : |φ 0 * c 4| ≤ 3 * K * K := by
        rw [abs_mul]; exact mul_le_mul (hφ 0) hc4 (abs_nonneg _) (by positivity)
      have e3 : |φ 1 * c 6| ≤ 3 * K * K := by
        rw [abs_mul]; exact mul_le_mul (hφ 1) hc6 (abs_nonneg _) (by positivity)
      have e4 : |u * (φ 0 * c 4 + φ 1 * c 6)| ≤ 6 * K ^ 2 := by
        rw [abs_mul]
        calc |u| * |φ 0 * c 4 + φ 1 * c 6| ≤ 1 * (3 * K * K + 3 * K * K) :=
              mul_le_mul hu ((abs_add_le _ _).trans (add_le_add e2 e3)) (abs_nonneg _)
                zero_le_one
          _ = 6 * K ^ 2 := by ring
      calc |u ^ 2 * c 2 - u * (φ 0 * c 4 + φ 1 * c 6)|
          ≤ |u ^ 2 * c 2| + |u * (φ 0 * c 4 + φ 1 * c 6)| := abs_sub _ _
        _ ≤ 7 * K ^ 2 := by linarith
    have hB : |(φ 0 - u * slope 0) * zy c t₀ 0 + (φ 1 - u * slope 1) * zy c t₀ 1| ≤
        8 * K ^ 2 * p := by
      have e1 : |(φ 0 - u * slope 0) * zy c t₀ 0| ≤ 2 * K * p * (2 * K) := by
        rw [abs_mul]; exact mul_le_mul (hφerr 0) (hY 0) (abs_nonneg _) (by positivity)
      have e2 : |(φ 1 - u * slope 1) * zy c t₀ 1| ≤ 2 * K * p * (2 * K) := by
        rw [abs_mul]; exact mul_le_mul (hφerr 1) (hY 1) (abs_nonneg _) (by positivity)
      calc _ ≤ |(φ 0 - u * slope 0) * zy c t₀ 0| + |(φ 1 - u * slope 1) * zy c t₀ 1| :=
            abs_add_le _ _
        _ ≤ 2 * K * p * (2 * K) + 2 * K * p * (2 * K) := add_le_add e1 e2
        _ = 8 * K ^ 2 * p := by ring
    have hHp' : H * (7 * K ^ 2) ≤ 7 * K ^ 2 * p := by nlinarith
    calc _ ≤ |H * (u ^ 2 * c 2 - u * (φ 0 * c 4 + φ 1 * c 6))| +
          |(φ 0 - u * slope 0) * zy c t₀ 0 + (φ 1 - u * slope 1) * zy c t₀ 1| := abs_sub _ _
      _ ≤ 15 * K ^ 2 * p := by linarith
  · have hid : v2FirstJet c F (fun _ => slope) (t₀ + H * u) - v2FirstJet c F (fun _ => slope) t₀ =
        H * (2 * u * c 2 - φ 0 * c 4 - φ 1 * c 6 - u * slope 0 * c 4 - u * slope 1 * c 6) := by
      simp only [hφdef, v2FirstJet_eq]
      field_simp
      ring
    rw [hid, abs_mul, abs_of_pos hH, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hH.le
    have e1 : |2 * u * c 2| ≤ 2 * K := by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul hu hc2 (abs_nonneg _) zero_le_one
      linarith
    have e2 : |φ 0 * c 4| ≤ 3 * K * K := by
      rw [abs_mul]; exact mul_le_mul (hφ 0) hc4 (abs_nonneg _) (by positivity)
    have e3 : |φ 1 * c 6| ≤ 3 * K * K := by
      rw [abs_mul]; exact mul_le_mul (hφ 1) hc6 (abs_nonneg _) (by positivity)
    have e4 : |u * slope 0 * c 4| ≤ K * K := by
      rw [abs_mul]; exact mul_le_mul (hus 0) hc4 (abs_nonneg _) hK0
    have e5 : |u * slope 1 * c 6| ≤ K * K := by
      rw [abs_mul]; exact mul_le_mul (hus 1) hc6 (abs_nonneg _) hK0
    have htri : |2 * u * c 2 - φ 0 * c 4 - φ 1 * c 6 - u * slope 0 * c 4 - u * slope 1 * c 6| ≤
        |2 * u * c 2| + |φ 0 * c 4| + |φ 1 * c 6| + |u * slope 0 * c 4| + |u * slope 1 * c 6| := by
      have a1 := abs_sub (2 * u * c 2 - φ 0 * c 4 - φ 1 * c 6 - u * slope 0 * c 4)
        (u * slope 1 * c 6)
      have a2 := abs_sub (2 * u * c 2 - φ 0 * c 4 - φ 1 * c 6) (u * slope 0 * c 4)
      have a3 := abs_sub (2 * u * c 2 - φ 0 * c 4) (φ 1 * c 6)
      have a4 := abs_sub (2 * u * c 2) (φ 0 * c 4)
      linarith
    nlinarith

/-- The first jet at a labelled incidence is bounded. -/
theorem abs_v2FirstJet_le {c : Fin 7 → ℝ} {F : ℝ → Fin 2 → ℝ} {slope : Fin 2 → ℝ} {K t : ℝ}
    (hK : 1 ≤ K) (hc : ∀ e, |c e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1) (hF : ‖F t‖ ≤ K)
    (hslope : ∀ i, |slope i| ≤ K) : |v2FirstJet c F (fun _ => slope) t| ≤ 9 * K ^ 2 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hY := abs_zy_le hc ht
  have hR : |zR F c t| ≤ 3 * K + 2 * K ^ 2 := by
    have hv := norm_zv_le hc
    have h1 : |c 1 + 2 * c 2 * t| ≤ 3 * K := by
      have h1 := hc 1; have h2 := hc 2
      calc |c 1 + 2 * c 2 * t| ≤ |c 1| + |2 * c 2 * t| := abs_add_le _ _
        _ = |c 1| + 2 * |c 2| * t := by
            rw [abs_mul, abs_mul, abs_two, abs_of_nonneg ht.1]
        _ ≤ K + 2 * K * 1 := by
            have := mul_le_mul (by linarith : 2 * |c 2| ≤ 2 * K) ht.2 ht.1 (by positivity)
            linarith
        _ = 3 * K := by ring
    have h2 := abs_dot_le (F t) (zv c)
    have h3 : 2 * ‖F t‖ * ‖zv c‖ ≤ 2 * K * K :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num)) hv (norm_nonneg _) (by positivity)
    unfold zR
    calc |c 1 + 2 * c 2 * t - F t ⬝ᵥ zv c| ≤ |c 1 + 2 * c 2 * t| + |F t ⬝ᵥ zv c| := abs_sub _ _
      _ ≤ 3 * K + 2 * K ^ 2 := by nlinarith
  have hSy : |slope ⬝ᵥ zy c t| ≤ 4 * K ^ 2 := by
    rw [dot_two]
    have e1 : |slope 0 * zy c t 0| ≤ K * (2 * K) := by
      rw [abs_mul]; exact mul_le_mul (hslope 0) (hY 0) (abs_nonneg _) hK0
    have e2 : |slope 1 * zy c t 1| ≤ K * (2 * K) := by
      rw [abs_mul]; exact mul_le_mul (hslope 1) (hY 1) (abs_nonneg _) hK0
    calc _ ≤ |slope 0 * zy c t 0| + |slope 1 * zy c t 1| := abs_add_le _ _
      _ ≤ 4 * K ^ 2 := by nlinarith
  unfold v2FirstJet
  calc |zR F c t - slope ⬝ᵥ zy c t| ≤ |zR F c t| + |slope ⬝ᵥ zy c t| := abs_sub _ _
    _ ≤ 9 * K ^ 2 := by nlinarith

/-- **The residual model on the left-normalized block** `[s, s + H]`, anchored at
`t₀ = s + H · anchor`. -/
theorem v2_left_block_residual_model (c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (s : ℝ)
    (a slope : Fin 2 → ℝ) (bin : ℤ) {H p K anchor u : ℝ} (hH : 0 < H) (hHp : H ≤ p)
    (hp1 : p ≤ 1) (hK : 1 ≤ K) (hanchor : anchor ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hc : ∀ e, |c e| ≤ K) (hcunit : s + H * anchor ∈ Icc (0 : ℝ) 1)
    (hF : ‖F (s + H * anchor)‖ ≤ K) (hslope : ∀ i, |slope i| ≤ K)
    (hrow₀ : ∀ i, |F (s + H * anchor) i - (a i + slope i * (s + H * anchor))| ≤ K * H * p)
    (hrow : ∀ i, |F (s + H * u) i - (a i + slope i * (s + H * u))| ≤ K * H * p) :
    let t₀ := s + H * anchor
    let k := v2FirstJet c F (fun _ => slope) t₀
    |(zS F c (s + H * u) - H * bin) / H -
      (((zS F c t₀ - H * bin) / H - anchor * k) + u * k)| ≤ 15 * K ^ 2 * p ∧
    |v2FirstJet c F (fun _ => slope) (s + H * u) - k| ≤ 10 * K ^ 2 * H ∧
    |k| ≤ 9 * K ^ 2 := by
  intro t₀ k
  have huc : |u - anchor| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hanchor.1, hanchor.2]
  have he : t₀ + H * (u - anchor) = s + H * u := by simp only [t₀]; ring
  have hY := abs_zy_le hc hcunit
  have hmodel := v2_affine_row_residual_model c F t₀ (H * bin) a slope hH hHp hp1 hK huc hc hY
    hslope hrow₀ (by rw [he]; exact hrow)
  rw [he] at hmodel
  refine ⟨?_, hmodel.2, abs_v2FirstJet_le hK hc hcunit hF hslope⟩
  have hk : zR F c t₀ - slope ⬝ᵥ zy c t₀ = k := rfl
  rw [hk] at hmodel
  have e : (zS F c t₀ - H * bin) / H + (u - anchor) * k =
      ((zS F c t₀ - H * bin) / H - anchor * k) + u * k := by ring
  rw [← e]
  exact hmodel.1

/-- **Frozen spread of the first jet**: same scalar bin and same tangential `p`-cube at one time. -/
theorem v2_frozen_first_jet_spread (c : Fin 7 → ℝ) (c' : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (t₀ : ℝ) (slope : Fin 2 → ℝ) {K H p ζ : ℝ} (hK : 1 ≤ K) (hH : 0 < H) (hHp : H ≤ p)
    (hζH : ζ ≤ H) (hF : ‖F t₀‖ ≤ K) (hslope : ∀ i, |slope i| ≤ K)
    (hS : |zS F c t₀ - zS F c' t₀| ≤ H)
    (hR : |zR F c t₀ - zR F c' t₀| ≤
      K * (|zx c t₀ - zx c' t₀| + |zy c t₀ 0 - zy c' t₀ 0| + |zy c t₀ 1 - zy c' t₀ 1| + ζ))
    (hcode : ∀ i, (⌊zy c t₀ i / p⌋ : ℤ) = ⌊zy c' t₀ i / p⌋) :
    |v2FirstJet c F (fun _ => slope) t₀ - v2FirstJet c' F (fun _ => slope) t₀| ≤
      8 * K ^ 2 * p := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hp : 0 < p := hH.trans_le hHp
  have hy : ∀ i, |zy c t₀ i - zy c' t₀ i| ≤ p := fun i => same_mesh_cell_close hp (hcode i)
  have hF0 : |F t₀ 0| ≤ K := (abs_le_norm (F t₀) 0).trans hF
  have hF1 : |F t₀ 1| ≤ K := (abs_le_norm (F t₀) 1).trans hF
  have hx : |zx c t₀ - zx c' t₀| ≤ H + 2 * K * p := by
    have he : zx c t₀ - zx c' t₀ = (zS F c t₀ - zS F c' t₀) +
        (F t₀ 0 * (zy c t₀ 0 - zy c' t₀ 0) + F t₀ 1 * (zy c t₀ 1 - zy c' t₀ 1)) := by
      simp only [zS, dot_two]; ring
    rw [he]
    have e1 : |F t₀ 0 * (zy c t₀ 0 - zy c' t₀ 0)| ≤ K * p := by
      rw [abs_mul]; exact mul_le_mul hF0 (hy 0) (abs_nonneg _) hK0
    have e2 : |F t₀ 1 * (zy c t₀ 1 - zy c' t₀ 1)| ≤ K * p := by
      rw [abs_mul]; exact mul_le_mul hF1 (hy 1) (abs_nonneg _) hK0
    calc _ ≤ |zS F c t₀ - zS F c' t₀| +
          |F t₀ 0 * (zy c t₀ 0 - zy c' t₀ 0) + F t₀ 1 * (zy c t₀ 1 - zy c' t₀ 1)| :=
          abs_add_le _ _
      _ ≤ H + (K * p + K * p) := add_le_add hS ((abs_add_le _ _).trans (add_le_add e1 e2))
      _ = H + 2 * K * p := by ring
  have hRb : |zR F c t₀ - zR F c' t₀| ≤ 6 * K ^ 2 * p := by
    refine hR.trans ?_
    have hsum : |zx c t₀ - zx c' t₀| + |zy c t₀ 0 - zy c' t₀ 0| + |zy c t₀ 1 - zy c' t₀ 1| + ζ ≤
        4 * p + 2 * K * p := by linarith [hy 0, hy 1]
    have hKK : K * p ≤ K ^ 2 * p := mul_le_mul_of_nonneg_right (by nlinarith) hp.le
    have hKp : K * (4 * p + 2 * K * p) ≤ 6 * K ^ 2 * p := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsum hK0).trans hKp
  have hSy : |slope ⬝ᵥ (zy c t₀ - zy c' t₀)| ≤ 2 * K ^ 2 * p := by
    rw [dot_two]
    have e1 : |slope 0 * (zy c t₀ - zy c' t₀) 0| ≤ K * p := by
      rw [abs_mul, Pi.sub_apply]; exact mul_le_mul (hslope 0) (hy 0) (abs_nonneg _) hK0
    have e2 : |slope 1 * (zy c t₀ - zy c' t₀) 1| ≤ K * p := by
      rw [abs_mul, Pi.sub_apply]; exact mul_le_mul (hslope 1) (hy 1) (abs_nonneg _) hK0
    have hKp : K * p ≤ K ^ 2 * p := mul_le_mul_of_nonneg_right (by nlinarith) hp.le
    calc _ ≤ |slope 0 * (zy c t₀ - zy c' t₀) 0| + |slope 1 * (zy c t₀ - zy c' t₀) 1| :=
          abs_add_le _ _
      _ ≤ 2 * K ^ 2 * p := by linarith
  have he : v2FirstJet c F (fun _ => slope) t₀ - v2FirstJet c' F (fun _ => slope) t₀ =
      (zR F c t₀ - zR F c' t₀) - slope ⬝ᵥ (zy c t₀ - zy c' t₀) := by
    simp only [v2FirstJet, dotProduct_sub]; ring
  rw [he]
  calc _ ≤ |zR F c t₀ - zR F c' t₀| + |slope ⬝ᵥ (zy c t₀ - zy c' t₀)| := abs_sub _ _
    _ ≤ 8 * K ^ 2 * p := by linarith

/-- The normalized scalar observation `(S_l(s + H u) - H · bin) / H` on the left block. -/
def v2LeftObservation {Λ : Type*} (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (s H : ℝ) (bin : ℤ)
    (q : ℝ × Λ) : ℝ :=
  (zS F (c q.2) (s + H * q.1) - H * bin) / H

theorem v2LeftObservation_measurable {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) {F : ℝ → Fin 2 → ℝ} (hF : Measurable F) (s H : ℝ) (bin : ℤ) :
    Measurable (v2LeftObservation c F s H bin) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun q : ℝ × Λ => c q.2 e) :=
    fun e => (measurable_pi_apply e).comp (hc.comp measurable_snd)
  have hFc : ∀ i : Fin 2, Measurable (fun q : ℝ × Λ => F (s + H * q.1) i) :=
    fun i => (measurable_pi_apply i).comp
      (hF.comp (measurable_const.add (measurable_const.mul measurable_fst)))
  have h0 := hcomp 0; have h1 := hcomp 1; have h2 := hcomp 2; have h3 := hcomp 3
  have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
  have hF0 := hFc 0; have hF1 := hFc 1
  show Measurable (fun q : ℝ × Λ => (zS F (c q.2) (s + H * q.1) - H * bin) / H)
  simp only [zS, zx, dot_two, zy_zero, zy_one]
  fun_prop

/-- **The observations of one starting bin.** -/
theorem v2_left_residual_observations {Λ : Type*} (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (F : ℝ → Fin 2 → ℝ) (s : ℝ) (a slope : Fin 2 → ℝ) (bin : ℤ) {H p K anchor : ℝ}
    (hH : 0 < H) (hHp : H ≤ p) (hp1 : p ≤ 1) (hK : 1 ≤ K)
    (hanchor : anchor ∈ Icc (0 : ℝ) 1) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H))
    (hcoeff : ∀ q ∈ E, ∀ e, |c q.1 e| ≤ K) (hF : ∀ t, ‖F t‖ ≤ K) (hslope : ∀ i, |slope i| ≤ K)
    (hrow : ∀ q ∈ E, ∀ i, |F q.2 i - (a i + slope i * q.2)| ≤ K * H * p) :
    let t₀ := s + H * anchor
    let A := {l | (l, t₀) ∈ E ∧ (⌊zS F (c l) t₀ / H⌋ : ℤ) = bin}
    let k := fun l => v2FirstJet (c l) F (fun _ => slope) t₀
    let b := fun l => (zS F (c l) t₀ - H * bin) / H - anchor * k l
    ∀ l u, (l, u) ∈ scalarLeftBlockEvent E A s H →
      |v2LeftObservation c F s H bin (u, l)| ≤ 25 * K ^ 2 ∧
      |v2LeftObservation c F s H bin (u, l) - (b l + k l * u)| ≤ 15 * K ^ 2 * p ∧
      |v2FirstJet (c l) F (fun _ => slope) (s + H * u) - k l| ≤ 10 * K ^ 2 * H := by
  intro t₀ A k b l u hq
  have hu : u ∈ Icc (0 : ℝ) 1 := (scalarLeftBlockEvent_unit hH hblock hq).2
  have hA : (l, t₀) ∈ E ∧ (⌊zS F (c l) t₀ / H⌋ : ℤ) = bin := hq.2
  have hdata := v2_left_block_residual_model (c l) F s a slope bin hH hHp hp1 hK hanchor hu
    (hcoeff (l, t₀) hA.1) (hunit hA.1).2 (hF _) hslope (hrow (l, t₀) hA.1) (hrow (l, s + H * u) hq.1)
  have hk : |k l| ≤ 9 * K ^ 2 := hdata.2.2
  set Z := (zS F (c l) t₀ - H * bin) / H with hZdef
  have hZ : |Z| ≤ 1 := by
    have hh := (mesh_lower_endpoint hH hA.2).2
    rw [hZdef, abs_div, abs_of_pos hH]
    exact (div_le_iff₀ hH).mpr (by simpa only [one_mul] using hh.le)
  have huc : |u - anchor| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hanchor.1, hanchor.2]
  have hprod : |(u - anchor) * k l| ≤ 9 * K ^ 2 := by
    rw [abs_mul]; exact (mul_le_mul huc hk (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hmodel : |v2LeftObservation c F s H bin (u, l) - (b l + k l * u)| ≤ 15 * K ^ 2 * p := by
    have e : b l + k l * u = (Z - anchor * k l) + u * k l := by simp only [b, hZdef]; ring
    rw [e]
    exact hdata.1
  refine ⟨?_, hmodel, hdata.2.1⟩
  have e2 : b l + k l * u = Z + (u - anchor) * k l := by simp only [b, hZdef]; ring
  have hlin : |b l + k l * u| ≤ 1 + 9 * K ^ 2 := by
    rw [e2]; exact (abs_add_le _ _).trans (add_le_add hZ hprod)
  have hpK : 15 * K ^ 2 * p ≤ 15 * K ^ 2 := by
    have : 0 ≤ 15 * K ^ 2 := by positivity
    nlinarith
  have h1K : 1 ≤ K ^ 2 := by nlinarith
  calc |v2LeftObservation c F s H bin (u, l)|
      = |(v2LeftObservation c F s H bin (u, l) - (b l + k l * u)) + (b l + k l * u)| := by
        ring_nf
    _ ≤ |v2LeftObservation c F s H bin (u, l) - (b l + k l * u)| + |b l + k l * u| :=
        abs_add_le _ _
    _ ≤ 25 * K ^ 2 := by linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
