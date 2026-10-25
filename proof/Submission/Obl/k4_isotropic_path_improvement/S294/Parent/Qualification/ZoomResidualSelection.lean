-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ZoomResidualSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ZoomResidualSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ZoomResidualSelection.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ZoomResidualSelection.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
import Submission.Lib.K4CommonLocalChoice


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

theorem measurable_zpos {Λ : Type*} [MeasurableSpace Λ]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) :
    Measurable (fun z : Λ × ℝ => zpos (c z.1) z.2) := by
  have hi (i : Fin 7) : Measurable (fun z : Λ × ℝ => c z.1 i) :=
    (measurable_pi_apply i).comp (hc.comp measurable_fst)
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_snd
  · exact ((hi 0).add ((hi 1).mul measurable_snd)).add ((hi 2).mul (measurable_snd.pow_const 2))
  · exact (hi 3).add ((hi 4).mul measurable_snd)
  · exact (hi 5).add ((hi 6).mul measurable_snd)

theorem measurable_zR {Λ : Type*} [MeasurableSpace Λ]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) {F : ℝ → Fin 2 → ℝ} (hF : Measurable F) :
    Measurable (fun z : Λ × ℝ => zR F (c z.1) z.2) := by
  have hi (i : Fin 7) : Measurable (fun z : Λ × ℝ => c z.1 i) :=
    (measurable_pi_apply i).comp (hc.comp measurable_fst)
  have hrow (i : Fin 2) : Measurable (fun z : Λ × ℝ => F z.2 i) :=
    (measurable_pi_apply i).comp (hF.comp measurable_snd)
  have h := ((hi 1).add (((hi 2).const_mul 2).mul measurable_snd)).sub
    (((hrow 0).mul (hi 4)).add ((hrow 1).mul (hi 6)))
  convert h using 1 <;> funext z <;>
    simp [zR, zv, dotProduct, Fin.sum_univ_two]

theorem residual_bound_of_original_coefficients (c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (t K : ℝ) (hK : 1 ≤ K) (ht : t ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, |c i| ≤ K) (hF : ‖F t‖ ≤ K) : |zR F c t| ≤ 5 * K ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hf (i : Fin 2) : |F t i| ≤ K := (norm_le_pi_norm _ i).trans hF
  have hv (i : Fin 2) : |zv c i| ≤ K := by fin_cases i <;> exact hc _
  have hterm (i : Fin 2) : |F t i * zv c i| ≤ K ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hf i) (hv i) (abs_nonneg _) hK0
  have hsum : |F t ⬝ᵥ zv c| ≤ 2 * K ^ 2 := by
    rw [dotProduct, Fin.sum_univ_two]
    exact (abs_add_le _ _).trans ((add_le_add (hterm 0) (hterm 1)).trans_eq (by ring))
  have hquad : |2 * c 2 * t| ≤ 2 * K := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul (hc 2) ht' (abs_nonneg _) hK0]
  have hlinear : |c 1 + 2 * c 2 * t| ≤ 3 * K :=
    (abs_add_le _ _).trans (by linarith [hc 1])
  have h := abs_sub (c 1 + 2 * c 2 * t) (F t ⬝ᵥ zv c)
  change |c 1 + 2 * c 2 * t - F t ⬝ᵥ zv c| ≤ _
  nlinarith

/-- Local residual lists produce actual residual comparison on a dense
restriction of the SAME original label event. The original product prior
is unchanged, and the exact finite-grid selection cost is recorded. -/
theorem original_zoom_residual_selection {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (F : ℝ → Fin 2 → ℝ) (hF : Measurable F) (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (K : ℝ) (hK : 1 ≤ K) (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ z ∈ E, ∀ i, |c z.1 i| ≤ K) (hrow : ∀ z ∈ E, ‖F z.2‖ ≤ K)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (lists : ℕ → ℕ)
    (A ζ : ℝ) (hA : 1 ≤ A) (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i)
    (hratio : ∀ i, i + 1 < L → s i ≤ A * s (i + 1)) (hfloor : s (L - 1) ≤ ζ)
    (hlist : ∀ i < L, ∀ n : Fin 4 → ℤ, ∃ S : Finset ℤ, S.card ≤ lists i ∧
      ∀ z ∈ E, Submission.Lib.K4CommonLocalChoice.cell (s i) (zpos (c z.1) z.2) = n →
        ⌊zR F (c z.1) z.2 / s i⌋ ∈ S) :
    ∃ E' : Set (Λ × ℝ), MeasurableSet E' ∧ E' ⊆ E ∧
      μ E ≤ (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ 4 * lists i)) * μ E' ∧
      ∀ z ∈ E', ∀ z' ∈ E', |zR F (c z.1) z.2 - zR F (c z'.1) z'.2| ≤
        2 * (A + 5 * K ^ 2) * (‖zpos (c z.1) z.2 - zpos (c z'.1) z'.2‖ + ζ) := by
  classical
  let Y (z : Λ × ℝ) : Fin 1 → ℝ := fun _ => zR F (c z.1) z.2
  have hY : Measurable Y := measurable_pi_iff.mpr (fun _ => measurable_zR hc hF)
  have hYbound : ∀ z ∈ E, ‖Y z‖ ≤ 5 * K ^ 2 := by
    intro z hz
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro _
    exact residual_bound_of_original_coefficients (c z.1) F z.2 K hK
      (htime z hz) (hcoeff z hz) (hrow z hz)
  have htuples : ∀ i < L, ∀ (ω : Unit) (n : Fin 4 → ℤ),
      ∃ S : Finset (Fin 1 → ℤ), S.card ≤ lists i ∧
        ∀ z ∈ E, () = ω → Submission.Lib.K4CommonLocalChoice.cell (s i) (zpos (c z.1) z.2) = n →
          Submission.Lib.K4CommonLocalChoice.cell (s i) (Y z) ∈ S := by
    intro i hi _ n
    obtain ⟨S, hcard, hS⟩ := hlist i hi n
    refine ⟨S.image (fun j => fun _ : Fin 1 => j), (Finset.card_image_le).trans hcard, ?_⟩
    intro z hz _ hn
    exact Finset.mem_image.mpr ⟨_, hS z hz hn, rfl⟩
  obtain ⟨E', _, hm, hsub, _, hmass, hcmp⟩ :=
    Submission.Lib.K4CommonLocalChoice.common_local_choice μ (fun _ : Λ × ℝ => ()) measurable_const
      (fun z => zpos (c z.1) z.2) (measurable_zpos hc) Y hY E hE (5 * K ^ 2)
      (by positivity) hYbound L hL s lists A hA hs0 hspos hratio htuples
  refine ⟨E', hm, hsub, ?_, ?_⟩
  · simpa using hmass ()
  · intro z hz z' hz'
    have h := hcmp z hz z' hz' rfl
    have hcoef : 0 ≤ 2 * (A + 5 * K ^ 2) := by positivity
    have h' : 2 * (A + 5 * K ^ 2) *
        (‖zpos (c z.1) z.2 - zpos (c z'.1) z'.2‖ + s (L - 1)) ≤
        2 * (A + 5 * K ^ 2) * (‖zpos (c z.1) z.2 - zpos (c z'.1) z'.2‖ + ζ) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hfloor) hcoef
    have hnorm : |zR F (c z.1) z.2 - zR F (c z'.1) z'.2| ≤ ‖Y z - Y z'‖ :=
      norm_le_pi_norm (Y z - Y z') (0 : Fin 1)
    exact hnorm.trans (h.trans h')

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
