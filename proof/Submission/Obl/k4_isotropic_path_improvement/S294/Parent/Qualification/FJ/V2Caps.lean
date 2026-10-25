-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Caps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Caps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Caps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Caps.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Observations

set_option autoImplicit false

/-!
# The joint cap of a normalized sliced group (paper `tex-05`, display `a04:sliced-cap`)

The `j = 2` counterpart of `starting_group_joint_cap` of o078 (session x0662, branch `x0662` at
`f2bac599`, `ScalarBlockCaps.lean`).  In one sliced starting group, normalized by `H^d p`, the
labels whose scaled fitted coordinate `v = 3K² y_k(t₀)` and normalized start
`Z = (S(t₀) - H b.1)/H` lie in an `r`-square carry mass at most `250000 K⁶ r^(1+d)`, at every
`r ≥ p` (x0662's `original_normalized_sliced_cap` for `r ≤ 1`; the total group mass beyond).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The normalized sliced group prior. -/
def slicedPrior (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (E : Set (Λ × ℝ))
    (t₀ H p d : ℝ) (k : Fin 2) (b : ℤ × ℤ) : Measure Λ :=
  scalarGroupPrior (ν.restrict ((fun l => (l, t₀)) ⁻¹' E)) (slicedCode c F t₀ H p k) b
    (H ^ d * p)

theorem slicedPrior_finite (ν : Measure Λ) [IsFiniteMeasure ν] (c : Λ → Fin 7 → ℝ)
    (F : ℝ → Fin 2 → ℝ) (E : Set (Λ × ℝ)) (t₀ H p d : ℝ) (k : Fin 2) (b : ℤ × ℤ) :
    IsFiniteMeasure (slicedPrior ν c F E t₀ H p d k b) :=
  scalarGroupPrior_finite _ _ _ _

/-- **The joint cap at scales `p ≤ r ≤ 1`.** -/
theorem sliced_group_joint_cap_small {ν : Measure Λ} [IsFiniteMeasure ν] {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d H p r : ℝ} (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hH : 0 < H) (hH1 : H ≤ 1) (hHp : H ≤ p)
    (hr : 0 < r) (hr1 : r ≤ 1) (hζr : ζ ≤ H * r) (t₀ : ℝ) (k : Fin 2) (b : ℤ × ℤ) (a z : ℝ) :
    (slicedPrior ν c F E t₀ H p d k b).real
      {l | l ∈ slicedLabels c F E t₀ H p k b ∧ scaledFitted c K t₀ k l ∈ Icc a (a + r) ∧
        slicedStart c F t₀ H b l ∈ Icc z (z + r)} ≤ 15625 * K ^ 4 * r ^ (1 + d) := by
  set B := {l | l ∈ slicedLabels c F E t₀ H p k b ∧ scaledFitted c K t₀ k l ∈ Icc a (a + r) ∧
    slicedStart c F t₀ H b l ∈ Icc z (z + r)} with hBdef
  have hp : 0 < p := hH.trans_le hHp
  have hc : 0 < H ^ d * p := mul_pos (Real.rpow_pos_of_pos hH d) hp
  have hL : 1 ≤ graphScale K := by unfold graphScale; nlinarith
  have hLpos : 0 < graphScale K := by linarith
  have hBm : MeasurableSet B := by
    have hcm := h.measurable_c
    refine (slicedLabels_measurable hcm h.event_measurable F t₀ H p k b).inter
      ((((measurable_zy_at hcm t₀ k).const_mul _) measurableSet_Icc).inter
        ((((measurable_zS_at hcm F t₀).sub_const _).div_const H) measurableSet_Icc))
  have hsub : B ⊆ ((fun l => (l, t₀)) ⁻¹' E) ∩ (slicedCode c F t₀ H p k ⁻¹' {b}) :=
    fun l hl => ⟨hl.1.1, hl.1.2⟩
  rw [slicedPrior, original_scalar_group_real ν _ _ b hc hBm hsub]
  have hbox : ∀ l ∈ B,
      (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) 0 ∈
        Icc (a / graphScale K) (a / graphScale K + r) ∧
      (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) 1 ∈
        Icc (p * b.2) (p * b.2 + p) ∧
      (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) 2 ∈
        Icc (H * b.1 + H * z) (H * b.1 + H * z + H * r) := by
    intro l hl
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    obtain ⟨hlab, ⟨hv1, hv2⟩, ⟨hz1, hz2⟩⟩ := hl
    have hcode := hlab.2
    simp only [slicedCode, Prod.ext_iff] at hcode
    have hw := (mesh_lower_endpoint hp hcode.2).1
    simp only [scaledFitted] at hv1 hv2
    simp only [slicedStart] at hz1 hz2
    refine ⟨⟨(div_le_iff₀ hLpos).mpr (by linarith), ?_⟩, hw, ?_, ?_⟩
    · have h1 : a / graphScale K * graphScale K = a := div_mul_cancel₀ a hLpos.ne'
      have hrL : r ≤ graphScale K * r := by nlinarith
      nlinarith
    · have := (le_div_iff₀ hH).mp hz1; linarith
    · have := (div_le_iff₀ hH).mp hz2; linarith
  have hcube : ∀ b' : Fin 3 → ℝ,
      ν.real {l | l ∈ (fun l => (l, t₀)) ⁻¹' E ∧ ∀ i,
        (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) i ∈
          Icc (b' i) (b' i + H * r)} ≤ (125 * K ^ 4) * (H * r) ^ (2 + d) :=
    fun b' => sliced_anchor_cube_cap h hK hd0 hd t₀ k (H * r) hζr (mul_pos hH hr) b'
  have hh := original_normalized_sliced_cap ν ((fun l => (l, t₀)) ⁻¹' E) B
    (fun l => ![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀])
    ![a / graphScale K, p * b.2, H * b.1 + H * z] hH hH1 hHp hr hr1 (by positivity)
    (fun l hl => (hsub hl).1)
    (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using hbox) hcube
  calc ν.real B / (H ^ d * p) ≤ 125 * (125 * K ^ 4) * r ^ (1 + d) := hh
    _ = 15625 * K ^ 4 * r ^ (1 + d) := by ring

/-- **The joint cap at every scale `r ≥ p`.** -/
theorem sliced_group_joint_cap {ν : Measure Λ} [IsFiniteMeasure ν] {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d H p : ℝ} (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hH : 0 < H) (hH1 : H ≤ 1) (hHp : H ≤ p)
    (hζ : ζ ≤ H * p) (t₀ : ℝ) (k : Fin 2) (b : ℤ × ℤ)
    (hprior : (slicedPrior ν c F E t₀ H p d k b).real univ ≤ 250000 * K ^ 6)
    (a z r : ℝ) (hr : p ≤ r) :
    (slicedPrior ν c F E t₀ H p d k b).real
      {l | l ∈ slicedLabels c F E t₀ H p k b ∧ scaledFitted c K t₀ k l ∈ Icc a (a + r) ∧
        slicedStart c F t₀ H b l ∈ Icc z (z + r)} ≤ 250000 * K ^ 6 * r ^ (1 + d) := by
  have hp : 0 < p := hH.trans_le hHp
  have hr0 : 0 < r := hp.trans_le hr
  haveI := slicedPrior_finite ν c F E t₀ H p d k b
  have hK46 : 15625 * K ^ 4 ≤ 250000 * K ^ 6 := by
    have h46 : K ^ 4 ≤ K ^ 6 := pow_le_pow_right₀ hK (by norm_num)
    nlinarith [pow_nonneg (show (0:ℝ) ≤ K by linarith) 4]
  rcases le_or_gt r 1 with hr1 | hr1
  · have hζr : ζ ≤ H * r := hζ.trans (mul_le_mul_of_nonneg_left hr hH.le)
    refine (sliced_group_joint_cap_small h hK hd0 hd hH hH1 hHp hr0 hr1 hζr t₀ k b a z).trans ?_
    exact mul_le_mul_of_nonneg_right hK46 (Real.rpow_nonneg hr0.le _)
  · have hone : 1 ≤ r ^ (1 + d) := Real.one_le_rpow hr1.le (by linarith)
    calc _ ≤ (slicedPrior ν c F E t₀ H p d k b).real univ :=
          measureReal_mono (subset_univ _) (measure_ne_top _ _)
      _ ≤ 250000 * K ^ 6 := hprior
      _ ≤ 250000 * K ^ 6 * r ^ (1 + d) := le_mul_of_one_le_right (by positivity) hone

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
