-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.DenseJet.Core, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/DenseJet/Core.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/DenseJet/Core.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/DenseJet/Core.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/Core.lean
-- Earlier source attributions below are retained.
import Mathlib
import Submission.Obl.k4_quadratic_sheet_continuation.CauchyEstimates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.EighthBall
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.Propagation

/-!
# Jets of a real algebraic sheet from its values on a set of positive measure

From the sheet Remez assertion (o172): a degree-`D` sheet with a complex-smooth
extension, bounded by `v` on a measurable subset of the closed unit ball of volume at
least `θ`, has all real Fréchet jets of order at most six bounded by `K θ^(-C) v` on the
closed ball of radius two. The constants depend only on `D`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet

open Set Metric MeasureTheory
open Submission.Obl.k4_algebraic_real_jet_comparison
open scoped ContDiff ENNReal

/-- A fixed finite cover of the closed unit ball by closed balls of radius `1/8`
centered in the closed unit ball. -/
theorem exists_eighth_cover : ∃ s : Finset (EuclideanSpace ℝ (Fin 3)),
    (∀ y ∈ s, ‖y‖ ≤ 1) ∧
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ ⋃ y ∈ s, closedBall y (1 / 8) := by
  obtain ⟨t, hts, htfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨htfin.toFinset, ?_, ?_⟩
  · intro y hy
    have h := hts (htfin.mem_toFinset.mp hy)
    simpa only [mem_closedBall, dist_zero_right] using h
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨y, htfin.mem_toFinset.mpr hy, ball_subset_closedBall hxy⟩

/-- Some ball of the cover carries a proportional share of a subset of the unit ball. -/
theorem exists_heavy_eighth_ball {s : Finset (EuclideanSpace ℝ (Fin 3))}
    (hcover : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ ⋃ y ∈ s, closedBall y (1 / 8))
    {E : Set (EuclideanSpace ℝ (Fin 3))} (hE : E ⊆ closedBall 0 1) (hEne : E.Nonempty) :
    ∃ y ∈ s, volume E ≤ (s.card : ℝ≥0∞) * volume (E ∩ closedBall y (1 / 8)) := by
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hEne
    obtain ⟨y, hy, _⟩ := mem_iUnion₂.mp (hcover (hE hx))
    exact ⟨y, hy⟩
  obtain ⟨y, hy, hmax⟩ := s.exists_max_image (fun y => volume (E ∩ closedBall y (1 / 8))) hsne
  refine ⟨y, hy, ?_⟩
  have hsub : E ⊆ ⋃ z ∈ s, E ∩ closedBall z (1 / 8) := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcover (hE hx))
    exact mem_iUnion₂.mpr ⟨z, hz, hx, hxz⟩
  calc
    volume E ≤ volume (⋃ z ∈ s, E ∩ closedBall z (1 / 8)) := measure_mono hsub
    _ ≤ ∑ z ∈ s, volume (E ∩ closedBall z (1 / 8)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ s, volume (E ∩ closedBall y (1 / 8)) := Finset.sum_le_sum fun z hz => hmax z hz
    _ = (s.card : ℝ≥0∞) * volume (E ∩ closedBall y (1 / 8)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Jets of a real algebraic sheet from its values on a set of positive measure. -/
theorem core_jet_bound (hR : SheetRemezAssertion) (D : ℕ) : ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      HasSheetRelation 3 D F → ContDiffOn ℂ ∞ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (realSlice x) = (f x : ℂ)) →
      ∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (θ v : ℝ), MeasurableSet E →
        E ⊆ closedBall 0 1 → 0 < θ → θ ≤ 1 → 0 ≤ v → ENNReal.ofReal θ ≤ volume E →
        (∀ x ∈ E, |f x| ≤ v) →
        ∀ j : ℕ, j ≤ 6 → ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 2 →
          ‖iteratedFDeriv ℝ j f x‖ ≤ K * θ ^ (-C) * v := by
  obtain ⟨CR, hCR, hremez⟩ := eighth_ball_remez hR D
  obtain ⟨Cch, hCch, hchain⟩ := sheet_chain D
  obtain ⟨s, hs, hcover⟩ := exists_eighth_cover
  choose Cc hCc_pos hCc using
    Submission.Obl.k4_quadratic_sheet_continuation.exists_iteratedFDeriv_ball_bound
  let Kc : ℝ := ∑ j ∈ Finset.range 7, Cc j * 4 ^ j
  have hKc : ∀ j : ℕ, j ≤ 6 → Cc j * 4 ^ j ≤ Kc := by
    intro j hj
    apply Finset.single_le_sum (f := fun j => Cc j * 4 ^ j)
      (fun i _ => mul_nonneg (hCc_pos i).le (by positivity))
    simp only [Finset.mem_range]
    omega
  have hKc_pos : 0 < Kc := lt_of_lt_of_le (mul_pos (hCc_pos 0) (by norm_num)) (hKc 0 (by norm_num))
  let N₀ : ℝ := s.card
  obtain ⟨V₁, hV₁, hvolhalf⟩ : ∃ V₁ : ℝ, 1 ≤ V₁ ∧
      volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤ ENNReal.ofReal V₁ := by
    refine ⟨(volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2))).toReal + 1, ?_, ?_⟩
    · linarith [ENNReal.toReal_nonneg (a := volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)))]
    · have hfin : volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≠ ⊤ :=
        measure_closedBall_lt_top.ne
      calc
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) =
            ENNReal.ofReal (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2))).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
        _ ≤ ENNReal.ofReal
            ((volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2))).toReal + 1) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  have hV₁pos : 0 < V₁ := by linarith
  have hN₀0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hKpos : 0 < Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR :=
    mul_pos (mul_pos (mul_pos hKc_pos hCch) (by linarith))
      (Real.rpow_pos_of_pos (mul_pos (mul_pos two_pos (by linarith)) hV₁pos) _)
  refine ⟨Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR, CR, hKpos, hCR, ?_⟩
  intro F f hrel hF hfF E θ v hE hEsub hθ hθ1 hv hvol hbound j hj x hx
  have hF' : DifferentiableOn ℂ F (ball 0 4) := hF.differentiableOn (by simp)
  have hreal : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ < 4 → (F (realSlice z)).im = 0 := by
    intro z hz
    rw [hfF z hz, Complex.ofReal_im]
  -- the positive case
  have hpos : ∀ v' : ℝ, 0 < v' → (∀ x ∈ E, |f x| ≤ v') →
      ‖iteratedFDeriv ℝ j f x‖ ≤ Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR * θ ^ (-CR) * v' := by
    intro v' hv' hbound'
    have hEne : E.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hvol
      linarith
    obtain ⟨y, hy, hpig⟩ := exists_heavy_eighth_ball hcover hEsub hEne
    let S := E ∩ closedBall y (1 / 8)
    have hSmeas : MeasurableSet S := hE.inter measurableSet_closedBall
    have hSfin : volume S ≠ ⊤ :=
      (measure_mono (Set.inter_subset_right) |>.trans_lt measure_closedBall_lt_top).ne
    let sR : ℝ := (volume S).toReal
    have hsR : volume S = ENNReal.ofReal sR := (ENNReal.ofReal_toReal hSfin).symm
    have hN₀ : 0 ≤ N₀ := Nat.cast_nonneg _
    have hθsR : θ ≤ N₀ * sR := by
      have h := hvol.trans hpig
      rw [hsR, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hN₀ ENNReal.toReal_nonneg)).mp h
    let θ' : ℝ := θ / (2 * (N₀ + 1) * V₁)
    have hden : 0 < 2 * (N₀ + 1) * V₁ := mul_pos (mul_pos two_pos (by linarith)) hV₁pos
    have hθ' : 0 < θ' := div_pos hθ hden
    have hθ'1 : θ' ≤ 1 := by
      rw [div_le_one hden]
      nlinarith
    have hmass : ENNReal.ofReal θ' * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤
        64 * volume S := by
      calc
        ENNReal.ofReal θ' * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤
            ENNReal.ofReal θ' * ENNReal.ofReal V₁ := by gcongr
        _ = ENNReal.ofReal (θ' * V₁) := (ENNReal.ofReal_mul hθ'.le).symm
        _ ≤ ENNReal.ofReal (64 * sR) := by
          apply ENNReal.ofReal_le_ofReal
          have hsR0 : 0 ≤ sR := ENNReal.toReal_nonneg
          have h1 : θ' * V₁ = θ / (2 * (N₀ + 1)) := by
            simp only [θ']
            field_simp
          rw [h1, div_le_iff₀ (by linarith)]
          nlinarith
        _ = 64 * volume S := by
          rw [hsR, ENNReal.ofReal_mul (by norm_num)]
          norm_num
    have hSbound : ∀ z ∈ S, ‖F (realSlice z)‖ ≤ v' := by
      intro z hz
      have hz1 : ‖z‖ < 4 := by
        have := hEsub hz.1
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      rw [hfF z hz1, Complex.norm_real, Real.norm_eq_abs]
      exact hbound' z hz.1
    have hsmall := hremez F hrel hF' hreal y (hs y hy) S θ' v' hSmeas Set.inter_subset_right
      hθ' hθ'1 hv'.le hmass hSbound
    let B : ℝ := CR * θ' ^ (-CR) * v'
    have hB : 0 < B := mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hθ' _)) hv'
    have hcomplex := hchain F hrel hF' y (hs y hy) B hB hsmall x hx
    -- Cauchy estimate at the real point
    have hballsub : ball (realSlice x) (2 * (1 / 4)) ⊆ ball 0 4 := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      rw [mem_ball, dist_zero_right]
      have h1 : ‖w‖ ≤ ‖w - realSlice x‖ + ‖realSlice x‖ := by
        simpa using norm_add_le (w - realSlice x) (realSlice x)
      rw [norm_realSlice_apply] at h1
      linarith
    have hcauchy := hCc j F (realSlice x) (1 / 4) (Cch * B) (by norm_num) (mul_pos hCch hB).le
      (hF.mono hballsub) (by
        intro w hw
        apply hcomplex
        rw [mem_ball, dist_eq_norm] at hw
        linarith)
    have hrealjet := norm_iteratedFDeriv_real_le (V := ball (0 : EuclideanSpace ℝ (Fin 3)) 4)
      isOpen_ball hF isOpen_ball
      (fun z hz => by
        rw [mem_ball, dist_zero_right] at hz ⊢
        rwa [norm_realSlice_apply])
      (fun z hz => hfF z (by rwa [mem_ball, dist_zero_right] at hz)) j
      (show x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 4 by
        rw [mem_ball, dist_zero_right]; linarith)
    have hθ'pow : θ' ^ (-CR) = (2 * (N₀ + 1) * V₁) ^ CR * θ ^ (-CR) := by
      simp only [θ']
      rw [Real.div_rpow hθ.le hden.le, Real.rpow_neg hden.le, div_eq_mul_inv, inv_inv]
      ring
    calc
      ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℂ j F (realSlice x)‖ := hrealjet
      _ ≤ Cc j * (Cch * B) / (1 / 4) ^ j := hcauchy
      _ = (Cc j * 4 ^ j) * Cch * CR * θ' ^ (-CR) * v' := by
        simp only [B]
        rw [one_div, inv_pow, div_inv_eq_mul]
        ring
      _ ≤ Kc * Cch * CR * θ' ^ (-CR) * v' := by
        have h0 : 0 ≤ Cch * CR * θ' ^ (-CR) * v' :=
          (mul_pos (mul_pos (mul_pos hCch (by linarith)) (Real.rpow_pos_of_pos hθ' _)) hv').le
        have := mul_le_mul_of_nonneg_right (hKc j hj) h0
        linarith [this]
      _ = Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR * θ ^ (-CR) * v' := by
        rw [hθ'pow]
        ring
  -- conclude, also when `v = 0`
  rcases hv.lt_or_eq with hv0 | hv0
  · exact hpos v hv0 hbound
  · subst hv0
    rw [mul_zero]
    by_contra hcon
    push Not at hcon
    set a := ‖iteratedFDeriv ℝ j f x‖
    set K' := Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR * θ ^ (-CR)
    have hK'pos : 0 < K' := mul_pos hKpos (Real.rpow_pos_of_pos hθ _)
    have hpa : 0 < a / (2 * K') := div_pos hcon (mul_pos two_pos hK'pos)
    have h := hpos (a / (2 * K')) hpa (fun z hz => (hbound z hz).trans hpa.le)
    have : K' * (a / (2 * K')) = a / 2 := by field_simp
    linarith

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet
