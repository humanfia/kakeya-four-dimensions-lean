/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/AssignedArea.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.AssignedCells
import Submission.Obl.k4_scalar_heavy_intercept_selection.PlanarSupport
import Submission.Obl.k4_scalar_heavy_intercept_selection.PositiveCodes

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- The actual assigned-cell Kakeya area floor for a scalar trajectory
group. Directions, tubes, and trajectory time ceilings are constructed
from the original affine base coordinates. -/
theorem assigned_group_area_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
    (K : NNReal) (hK : 1 ≤ K) {C h b ξ η : ℝ} (hC : 0 < C)
    (hMK : FiniteMK 2 C) (hh : 0 < h) (hb : 0 < b) (hξ : 0 < ξ) (hη : 0 < η)
    (hbξ : b ≤ h * ξ)
    (u v : α → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hbu : ∀ l, |u l| ≤ (K : ℝ)) (hbv : ∀ l, |v l| ≤ (K : ℝ))
    (Λ : Set α) (hΛ : MeasurableSet Λ) (hΛμ : ∀ᵐ p ∂μ, p.1 ∈ Λ)
    (z : Fin 2 → ℝ) (phys : α × ℝ → Fin 3 → ℝ) (hphys : Measurable phys)
    (hTime : ∀ p, phys p 0 = p.2)
    (hBase : ∀ p, p.1 ∈ Λ →
      (fun i : Fin 2 => (phys p i.castSucc - z i) / h) =
        ![(p.2 - z 0) / h, u p.1 + ((p.2 - z 0) / h) * v p.1])
    (hdom : μ ≤ K • ν.prod volume)
    (hprior : (ν univ).toReal ≤ (4 * (K : ℝ) / h) * (μ univ).toReal)
    (hmass : 0 < (μ univ).toReal)
    (F : Finset (Fin 2 → ℤ))
    (hcarrier : ∀ᵐ p ∂μ,
      assignedBaseCode h b ξ z (fun j => ⌊phys p j / b⌋) ∈ F)
    (hpencil : ∀ q ∈ F, ∀ w,
      μ {p | assignedBaseCode h b ξ z (fun j => ⌊phys p j / b⌋) = q ∧ |v p.1 - w| < η} ≤
        ENNReal.ofReal (1 / 2 : ℝ) *
          μ {p | assignedBaseCode h b ξ z (fun j => ⌊phys p j / b⌋) = q}) :
    (η / ((K : ℝ) + 1) ^ 2) / (28800 * C * (K : ℝ) ^ 4 * ξ ^ 2) ≤ (F.card : ℝ) := by
  classical
  let Φ : α × ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun p => fineBasePoint h b z (fun j => ⌊phys p j / b⌋)
  let code : α × ℝ → Fin 2 → ℤ :=
    fun p => assignedBaseCode h b ξ z (fun j => ⌊phys p j / b⌋)
  let a : α → EuclideanSpace ℝ (Fin 2) := fun l => WithLp.toLp 2 ![0, u l]
  let e : α → EuclideanSpace ℝ (Fin 2) := fun l => unitBaseDirection (v l)
  let D : NNReal := NNReal.mk (3 * h * ξ) (by positivity)
  let β : ℝ := η / ((K : ℝ) + 1) ^ 2
  have hKnn₀ : (0 : NNReal) < K := zero_lt_one.trans_le hK
  have hD₀ : (0 : NNReal) < D := by change (0 : ℝ) < 3 * h * ξ; positivity
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast hKnn₀
  have hβ : 0 < β := by dsimp [β]; positivity
  have hraw : Measurable (fun p : α × ℝ => (fun j : Fin 3 => (⌊phys p j / b⌋ : ℤ))) := by
    fun_prop
  have hΦ : Measurable Φ := (measurable_fineBasePoint h b z).comp hraw
  have hcode : Measurable code := (measurable_assignedBaseCode h b ξ z).comp hraw
  have ha : Measurable a := by dsimp [a]; fun_prop
  have he : Measurable e := measurable_unitBaseDirection.comp hv
  have hnorma : ∀ l, ‖a l‖ ≤ (K : ℝ) := by
    intro l
    have hs := EuclideanSpace.real_norm_sq_eq (a l)
    simp [a, Fin.sum_univ_two] at hs
    have heq : ‖a l‖ = |u l| := (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
      (hs.trans (sq_abs (u l)).symm)
    exact heq.trans_le (hbu l)
  have hcell (p : α × ℝ) (q : Fin 2 → ℤ) :
      Φ p ∈ euclideanBaseCell ξ q ↔ code p = q := Iff.rfl
  have hcellmass (q : Fin 2 → ℤ) :
      μ {p | p.1 ∈ Λ ∧ Φ p ∈ euclideanBaseCell ξ q} = μ (code ⁻¹' {q}) := by
    apply measure_congr
    filter_upwards [hΛμ] with p hp
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, hp, true_and, hcell]
  have hpush : ∀ q ∈ F,
      (μ.restrict {p | p.1 ∈ Λ ∧ Φ p ∈ euclideanBaseCell ξ q}).map Prod.fst ≤
        (K * D) • ν.restrict Λ := by
    intro q hq
    apply map_fst_restrict_le ν μ K D hdom _
      ((measurable_fst hΛ).inter (hΦ (measurableSet_euclideanBaseCell ξ q)))
      Λ hΛ (fun _ hp => hp.1)
    intro l hl
    change volume {t | (l,t).1 ∈ Λ ∧ Φ (l,t) ∈ euclideanBaseCell ξ q} ≤
      (D : ENNReal)
    have ht := volume_assigned_time_section_le (t₀ := z 0) hh hb hξ hbξ (q 0)
      {t | (l,t).1 ∈ Λ ∧ Φ (l,t) ∈ euclideanBaseCell ξ q} (by
        intro t ht
        have hc := congrFun ((hcell (l,t) q).mp ht.2) 0
        change (⌊((b * (⌊phys (l,t) 0 / b⌋ : ℝ) - z 0) / h) / ξ⌋ : ℤ) = q 0 at hc
        simpa only [hTime] using hc)
    simpa only [D, ENNReal.ofReal_eq_coe_nnreal (by positivity : 0 ≤ 3 * h * ξ)] using ht
  have htube : ∀ q ∈ F, ∀ p : α × ℝ, p.1 ∈ Λ →
      Φ p ∈ euclideanBaseCell ξ q → ∀ x ∈ euclideanBaseCell ξ q,
        x ∈ tube (5 * ξ) (a p.1) (e p.1) := by
    intro q hq p hp hpq x hx
    exact assigned_base_cell_mem_tube hh hb hξ hbξ z (phys p)
      (u p.1) (v p.1) ((p.2 - z 0) / h) (hBase p hp) q ((hcell p q).mp hpq) x hx
  have hsum : ∑ q ∈ F,
      (μ {p | p.1 ∈ Λ ∧ Φ p ∈ euclideanBaseCell ξ q}).toReal =
        (μ univ).toReal := by
    simp_rw [hcellmass]
    exact sum_real_mass_finite_codes μ code hcode F hcarrier

  have hthin : ∀ q ∈ F, ∀ w,
      (μ.restrict {p | p.1 ∈ Λ ∧ Φ p ∈ euclideanBaseCell ξ q})
        {p | |v p.1 - w| < η} ≤
      ENNReal.ofReal (1 / 2 : ℝ) *
        μ {p | p.1 ∈ Λ ∧ Φ p ∈ euclideanBaseCell ξ q} := by
    intro q hq w
    have hEvent : MeasurableSet {p : α × ℝ | |v p.1 - w| < η} :=
      measurableSet_lt ((hv.comp measurable_fst).sub_const w).abs measurable_const
    rw [hcellmass, Measure.restrict_apply hEvent]
    apply le_trans (measure_mono ?_) (hpencil q hq w)
    intro p hp
    exact ⟨(hcell p q).mp hp.2.2, hp.1⟩

  obtain ⟨R, hER⟩ := exists_radius_euclideanBaseCells hξ F
  have harea := planar_support_floor hC.le hMK ν μ Φ hΦ a e ha he
    (fun l => norm_unitBaseDirection (v l)) hnorma (by positivity : 0 < 5 * ξ) R Λ
    hΛ F (euclideanBaseCell ξ) (fun q _ => measurableSet_euclideanBaseCell ξ q)
    (fun q hq q' hq' hqq' => euclideanBaseCell_disjoint ξ hqq') hER
    (K * D) (mul_pos hKnn₀ hD₀) hpush htube v hv hβ (sq_pos_of_pos hξ)
    (by positivity : (0 : ℝ) ≤ 4 * (K : ℝ) / h)
    (fun q _ => (volume_euclideanBaseCell hξ q).ge)
    (fun l hl l' hl' hsep => unitBaseDirection_det_lower hK₀.le (hbv l) (hbv l')
      (by simpa only [abs_sub_comm] using hsep)) hthin hsum hmass
    ((ENNReal.toReal_mono (measure_ne_top ν univ) (measure_mono (subset_univ Λ))).trans hprior)
  have hid : 4 * C * (5 * ξ) ^ 2 * (4 * (K : ℝ) / h) ^ 2 /
      (ξ ^ 2 * β * (1 / 2 : ℝ) / ((K * D : NNReal) : ℝ) ^ 2) =
      28800 * C * (K : ℝ) ^ 4 * ξ ^ 2 / β := by
    have hKD : ((K * D : NNReal) : ℝ) = (K : ℝ) * (3 * h * ξ) := rfl
    rw [hKD]
    field_simp [hh.ne', hξ.ne', hβ.ne']
    <;> ring
  rw [hid] at harea
  have hden : 0 < 28800 * C * (K : ℝ) ^ 4 * ξ ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  have ht := (le_div_iff₀ hβ).mp
    (show (1 : ℝ) ≤ ((F.card : ℝ) * (28800 * C * (K : ℝ) ^ 4 * ξ ^ 2)) / β by
      simpa only [mul_div_assoc] using harea)
  simpa only [one_mul] using ht

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
