-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Data, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Data.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Data.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Data.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCovers

set_option autoImplicit false

/-!
# Upper scalar-normal hypotheses in version 2 (`j = 2`)

The `j = 2` counterpart of `ScalarNormalHyp` of o078 (session x0662, branch `x0662` at
`f2bac599`, `ScalarNormalData.lean`), written in the coordinates of `Jets2` (`zx`, `zy`, `zv`, `zS`,
`zR`): only the upper hypotheses of paper Def. `a04:scalar-data`, which persist under every
restriction of the labels `E` (the dense mass is a separate hypothesis wherever it is used).

* `UpperHyp ν c E F K ζ d`;
* `UpperHyp.active_bounds`: coordinate bounds at labelled incidences;
* `UpperHyp.anchor_joint_cap`: the spatial cap on `(x, y₀, y₁)` gives the cap `125 K⁴ r^(2+d)` on
  boxes in the sheared coordinates `(S, y₀, y₁)` (`S = x - F · y`).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The labelled times. -/
def activeTimes (E : Set (Λ × ℝ)) : Set ℝ := {t | ∃ l, (l, t) ∈ E}

/-- The labelled scalar values at time `t`. -/
def scalarSupport (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (E : Set (Λ × ℝ)) (t : ℝ) :
    Set ℝ :=
  {s | ∃ l, (l, t) ∈ E ∧ zS F (c l) t = s}

/-- **Upper scalar-normal hypotheses, `j = 2`.** -/
structure UpperHyp (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (F : ℝ → Fin 2 → ℝ) (K ζ d : ℝ) : Prop where
  measurable_c : Measurable c
  event_measurable : MeasurableSet E
  row_measurable : Measurable F
  unit_time : E ⊆ univ ×ˢ Icc (0 : ℝ) 1
  coefficients : ∀ p ∈ E, ∀ e, |c p.1 e| ≤ K
  row_bounded : ∀ t, ‖F t‖ ≤ K
  row_comparison : ∀ p ∈ E, ∀ q ∈ E, ‖F p.2 - F q.2‖ ≤ K * (|p.2 - q.2| + ζ)
  residual_comparison : ∀ p ∈ E, ∀ q ∈ E,
    |zR F (c p.1) p.2 - zR F (c q.1) q.2| ≤
      K * (|p.2 - q.2| + |zx (c p.1) p.2 - zx (c q.1) q.2| +
        |zy (c p.1) p.2 0 - zy (c q.1) q.2 0| + |zy (c p.1) p.2 1 - zy (c q.1) q.2 1| + ζ)
  support_AD : ∀ t, IntervalAD ζ d K (scalarSupport c F E t)
  spatial_cap : ∀ t a b₀ b₁ r : ℝ, ζ ≤ r →
    ν.real {l | (l, t) ∈ E ∧ zx (c l) t ∈ Icc a (a + r) ∧ zy (c l) t 0 ∈ Icc b₀ (b₀ + r) ∧
      zy (c l) t 1 ∈ Icc b₁ (b₁ + r)} ≤ K * r ^ (2 + d)

namespace UpperHyp

variable {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ}
  {K ζ d : ℝ}

theorem active_unit_time (h : UpperHyp ν c E F K ζ d) : activeTimes E ⊆ Icc (0 : ℝ) 1 := by
  rintro t ⟨l, hl⟩
  exact (h.unit_time hl).2

theorem active_row_comparison (h : UpperHyp ν c E F K ζ d) :
    ∀ t ∈ activeTimes E, ∀ s ∈ activeTimes E, ‖F t - F s‖ ≤ K * (|t - s| + ζ) := by
  rintro t ⟨l, hl⟩ s ⟨l', hl'⟩
  exact h.row_comparison (l, t) hl (l', s) hl'

/-- The row comparison, componentwise. -/
theorem active_row_comparison_coord (h : UpperHyp ν c E F K ζ d) (i : Fin 2) :
    ∀ t ∈ activeTimes E, ∀ s ∈ activeTimes E, |F t i - F s i| ≤ K * (|t - s| + ζ) := by
  intro t ht s hs
  have := abs_le_norm (F t - F s) i
  simpa using this.trans (h.active_row_comparison t ht s hs)

theorem active_bounds (h : UpperHyp ν c E F K ζ d) {l : Λ} {t : ℝ} (hl : (l, t) ∈ E) :
    |zx (c l) t| ≤ 3 * K ∧ (∀ i, |zy (c l) t i| ≤ 2 * K) ∧ ‖zv (c l)‖ ≤ K ∧
      |zR F (c l) t| ≤ 3 * K + 2 * K ^ 2 ∧ |zS F (c l) t| ≤ 4 * K ^ 2 + 3 * K := by
  have hc := h.coefficients _ hl
  have ht := (h.unit_time hl).2
  have hF := h.row_bounded t
  have hK : 0 ≤ K := le_trans (norm_nonneg _) hF
  refine ⟨abs_zx_le hc ht, abs_zy_le hc ht, norm_zv_le hc, ?_, abs_zS_le hc ht hF⟩
  have hv := norm_zv_le hc
  have h1 : |c l 1 + 2 * c l 2 * t| ≤ 3 * K := by
    have h1 := hc 1; have h2 := hc 2
    calc |c l 1 + 2 * c l 2 * t| ≤ |c l 1| + |2 * c l 2 * t| := abs_add_le _ _
      _ = |c l 1| + 2 * |c l 2| * t := by
          rw [abs_mul, abs_mul, abs_two, abs_of_nonneg ht.1]
      _ ≤ K + 2 * K * 1 := by
          have := mul_le_mul (by linarith : 2 * |c l 2| ≤ 2 * K) ht.2 ht.1 (by positivity)
          linarith
      _ = 3 * K := by ring
  have h2 := abs_dot_le (F t) (zv (c l))
  have h3 : 2 * ‖F t‖ * ‖zv (c l)‖ ≤ 2 * K * K :=
    mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num)) hv (norm_nonneg _) (by positivity)
  unfold zR
  calc |c l 1 + 2 * c l 2 * t - F t ⬝ᵥ zv (c l)|
      ≤ |c l 1 + 2 * c l 2 * t| + |F t ⬝ᵥ zv (c l)| := abs_sub _ _
    _ ≤ 3 * K + 2 * K ^ 2 := by nlinarith

/-- **Joint cap in sheared coordinates.**  Boxes of side `r` in `(S, y₀, y₁)` at a fixed time
carry prior mass at most `125 K⁴ r^(2+d)`. -/
theorem anchor_joint_cap [IsFiniteMeasure ν] (h : UpperHyp ν c E F K ζ d) (hK : 1 ≤ K)
    (hd0 : 0 ≤ d) (hd : d ≤ 1) (t z y₀ y₁ r : ℝ) (hr : ζ ≤ r) (hr0 : 0 < r) :
    ν.real {l | (l, t) ∈ E ∧ zS F (c l) t ∈ Icc z (z + r) ∧ zy (c l) t 0 ∈ Icc y₀ (y₀ + r) ∧
      zy (c l) t 1 ∈ Icc y₁ (y₁ + r)} ≤ 125 * K ^ 4 * r ^ (2 + d) := by
  have hK0 : 0 ≤ K := by linarith
  have hF := h.row_bounded t
  have hF0 : |F t 0| ≤ K := (abs_le_norm (F t) 0).trans hF
  have hF1 : |F t 1| ≤ K := (abs_le_norm (F t) 1).trans hF
  set R := (1 + 4 * K) * r with hR
  have hrR : r ≤ R := by rw [hR]; nlinarith
  set center := z + F t 0 * y₀ + F t 1 * y₁ - 2 * K * r with hcenter
  have hsub : {l | (l, t) ∈ E ∧ zS F (c l) t ∈ Icc z (z + r) ∧ zy (c l) t 0 ∈ Icc y₀ (y₀ + r) ∧
      zy (c l) t 1 ∈ Icc y₁ (y₁ + r)} ⊆
      {l | (l, t) ∈ E ∧ zx (c l) t ∈ Icc center (center + R) ∧
        zy (c l) t 0 ∈ Icc y₀ (y₀ + R) ∧ zy (c l) t 1 ∈ Icc y₁ (y₁ + R)} := by
    rintro l ⟨hl, ⟨hs1, hs2⟩, ⟨hy01, hy02⟩, ⟨hy11, hy12⟩⟩
    have hxS : zx (c l) t = zS F (c l) t + F t 0 * zy (c l) t 0 + F t 1 * zy (c l) t 1 := by
      simp only [zS, dot_two]; ring
    have hd0' : 0 ≤ zy (c l) t 0 - y₀ := by linarith
    have hd0'' : zy (c l) t 0 - y₀ ≤ r := by linarith
    have hd1' : 0 ≤ zy (c l) t 1 - y₁ := by linarith
    have hd1'' : zy (c l) t 1 - y₁ ≤ r := by linarith
    have e0 : |F t 0 * (zy (c l) t 0 - y₀)| ≤ K * r := by
      rw [abs_mul, abs_of_nonneg hd0']
      exact mul_le_mul hF0 hd0'' hd0' hK0
    have e1 : |F t 1 * (zy (c l) t 1 - y₁)| ≤ K * r := by
      rw [abs_mul, abs_of_nonneg hd1']
      exact mul_le_mul hF1 hd1'' hd1' hK0
    rw [abs_le] at e0 e1
    refine ⟨hl, ⟨?_, ?_⟩, ⟨hy01, by linarith⟩, ⟨hy11, by linarith⟩⟩
    · rw [hxS, hcenter]; nlinarith
    · rw [hxS, hcenter, hR]; nlinarith
  have hmass := (measureReal_mono hsub (measure_ne_top ν _)).trans
    (h.spatial_cap t center y₀ y₁ R (hr.trans hrR))
  have hpow : (1 + 4 * K) ^ (2 + d) ≤ (5 * K) ^ (3 : ℝ) := by
    calc (1 + 4 * K) ^ (2 + d) ≤ (5 * K) ^ (2 + d) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ ≤ (5 * K) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply hmass.trans
  rw [hR, Real.mul_rpow (by positivity) hr0.le]
  have h3 : (5 * K) ^ (3 : ℝ) = 125 * K ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hrd : 0 ≤ r ^ (2 + d) := Real.rpow_nonneg hr0.le _
  calc K * ((1 + 4 * K) ^ (2 + d) * r ^ (2 + d)) ≤ K * ((5 * K) ^ (3 : ℝ) * r ^ (2 + d)) := by
        gcongr
    _ = 125 * K ^ 4 * r ^ (2 + d) := by rw [h3]; ring

end UpperHyp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
