-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeAssignedFilling, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/NativeAssignedFilling.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/NativeAssignedFilling.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeAssignedFilling.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeAssignedCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.BaseFilling
import Submission.Obl.k4_scalar_heavy_intercept_selection.AssignedCells
import Submission.Obl.k4_scalar_heavy_intercept_selection.PositiveCodes


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeAssigned

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- Actual three dimensional base filling for an original trajectory
group. Fine physical states assign the coarse cells. The original
density and prior/incidence ratio supply their time-section ceiling;
the affine trajectory supplies their tubes. -/
theorem assigned_base_filling {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
    (K : NNReal) (hK : 0 < K) {C h b ξ A ρ c : ℝ}
    (hC : 0 ≤ C) (hMK : FiniteMK 3 C) (hh : 0 < h) (hb : 0 < b) (hξ : 0 < ξ)
    (hA : 0 ≤ A) (hρ : 0 < ρ) (hc : 0 ≤ c) (hbξ : b ≤ h * ξ)
    (a v : α → EuclideanSpace ℝ (Fin 3)) (ha : Measurable a) (hv : Measurable v)
    (hv0 : ∀ l, v l ≠ 0) (anchor : ℝ) (hanchor : ∀ l, ‖a l‖ ≤ anchor)
    (Λ : Set α) (hΛ : MeasurableSet Λ) (hΛμ : ∀ᵐ p ∂μ, p.1 ∈ Λ)
    (z : Fin 3 → ℝ) (phys : α × ℝ → Fin 4 → ℝ) (hphys : Measurable phys)
    (hTime : ∀ p, phys p 0 = p.2)
    (hBase : ∀ p, p.1 ∈ Λ → ∀ i,
      (a p.1 + ((p.2 - z 0) / h) • v p.1) i = (phys p i.castSucc - z i) / h)
    (hdom : μ ≤ K • ν.prod volume)
    (hprior : (ν univ).toReal ≤ (A / h) * (μ univ).toReal)
    (hmass : 0 < (μ univ).toReal) (F : Finset (Fin 3 → ℤ))
    (hcarrier : ∀ᵐ p ∂μ, code h b ξ z (fun j => ⌊phys p j / b⌋) ∈ F)
    (hbroad : ∀ q ∈ F, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      c * (μ.restrict {p | code h b ξ z (fun j => ⌊phys p j / b⌋) = q}).real univ ≤
        (μ.restrict {p | code h b ξ z (fun j => ⌊phys p j / b⌋) = q}).real
          {p | ρ ≤ Metric.infDist (direction (v p.1)) (V : Set _)}) :
    ((ρ / 2) ^ 3 / 2 * c ^ 3) ≤
      (F.card : ℝ) * (8 * C * 7 ^ 3) ^ 2 * (3 * (K : ℝ) * A) ^ 3 * ξ ^ 3 := by
  classical
  let Φ : α × ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun p => point h b z (fun j => ⌊phys p j / b⌋)
  let label : α × ℝ → Fin 3 → ℤ :=
    fun p => code h b ξ z (fun j => ⌊phys p j / b⌋)
  let e : α → EuclideanSpace ℝ (Fin 3) := fun l => direction (v l)
  let D : NNReal := ⟨3 * h * ξ, by positivity⟩
  let enum : Fin F.card ≃ F := F.equivFin.symm
  let idx : Fin F.card → Fin 3 → ℤ := fun i => (enum i).val
  let E : Fin F.card → Set (EuclideanSpace ℝ (Fin 3)) := fun i => cell ξ (idx i)
  have hraw : Measurable (fun p : α × ℝ => fun j : Fin 4 => (⌊phys p j / b⌋ : ℤ)) := by
    fun_prop
  have hΦ : Measurable Φ := (measurable_point h b z).comp hraw
  have hlabel : Measurable label := (measurable_code h b ξ z).comp hraw
  have he : Measurable e := measurable_direction.comp hv
  have hD : 0 < D := by change (0 : ℝ) < 3 * h * ξ; positivity
  have hidx : Function.Injective idx := by
    intro i j hij
    exact enum.injective (Subtype.ext hij)
  have hcell (p : α × ℝ) (q : Fin 3 → ℤ) : Φ p ∈ cell ξ q ↔ label p = q := Iff.rfl
  have hcellmass (q : Fin 3 → ℤ) :
      μ {p | p.1 ∈ Λ ∧ Φ p ∈ cell ξ q} = μ (label ⁻¹' {q}) := by
    apply measure_congr
    filter_upwards [hΛμ] with p hp
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, hp, true_and, hcell]
  have hpush (i : Fin F.card) :
      (μ.restrict {p | p.1 ∈ Λ ∧ Φ p ∈ E i}).map Prod.fst ≤
        (K * D) • ν.restrict Λ := by
    apply map_fst_restrict_le ν μ K D hdom _
      ((measurable_fst hΛ).inter (hΦ (measurableSet_cell ξ (idx i))))
      Λ hΛ (fun _ hp => hp.1)
    intro l hl
    have ht := Submission.Obl.k4_scalar_heavy_intercept_selection.volume_assigned_time_section_le
      (t₀ := z 0) hh hb hξ hbξ (idx i 0)
      {t | (l,t).1 ∈ Λ ∧ Φ (l,t) ∈ E i} (by
        intro t ht
        have hi := congrFun ((hcell (l,t) (idx i)).mp ht.2) 0
        change (⌊((b * (⌊phys (l,t) 0 / b⌋ : ℝ) - z 0) / h) / ξ⌋ : ℤ) = idx i 0 at hi
        simpa only [hTime] using hi)
    change volume {t | l ∈ Λ ∧ Φ (l,t) ∈ cell ξ (idx i)} ≤ (D : ENNReal)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ht
  have htube (i : Fin F.card) (p : α × ℝ) (hp : p.1 ∈ Λ) (hpE : Φ p ∈ E i)
      (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ E i) :
      x ∈ tube (7 * ξ) (a p.1) (e p.1) :=
    cell_mem_tube hh hb hξ hbξ z (phys p) (a p.1) (v p.1)
      ((p.2 - z 0) / h) (hv0 p.1) (hBase p hp) (idx i) ((hcell p (idx i)).mp hpE) x hx
  have hsum : (∑ i : Fin F.card, μ.real {p | p.1 ∈ Λ ∧ Φ p ∈ E i}) = μ.real univ := by
    simp only [measureReal_def, E, hcellmass]
    have henum : (∑ i : Fin F.card, (μ (label ⁻¹' {idx i})).toReal) =
        ∑ q ∈ F, (μ (label ⁻¹' {q})).toReal := by
      rw [← Finset.sum_coe_sort F (fun q => (μ (label ⁻¹' {q})).toReal)]
      exact enum.sum_comp (fun q : F => (μ (label ⁻¹' {q.val})).toReal)
    rw [henum]
    exact Submission.Obl.k4_scalar_heavy_intercept_selection.sum_real_mass_finite_codes
      μ label hlabel F hcarrier
  have hbroad' (i : Fin F.card) (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
      (hV : Module.finrank ℝ V < 3) :
      c * μ.real {p | p.1 ∈ Λ ∧ Φ p ∈ E i} ≤
        (μ.restrict {p | p.1 ∈ Λ ∧ Φ p ∈ E i}).real
          {p | ρ ≤ Metric.infDist (e p.1) (V : Set _)} := by
    have heq : μ.restrict {p | p.1 ∈ Λ ∧ Φ p ∈ E i} =
        μ.restrict {p | label p = idx i} := by
      apply Measure.restrict_congr_set
      filter_upwards [hΛμ] with p hp
      simp only [mem_ofPred_eq, hp, true_and, E, hcell]
    have h := hbroad (idx i) (enum i).property V hV
    simpa only [heq, measureReal_def, hcellmass, E, Measure.restrict_apply_univ,
      label, e, Set.preimage, Set.mem_singleton_iff] using h
  obtain ⟨R, hR⟩ := exists_cell_radius hξ F
  have hfill := base_incidence_filling ν μ Φ hΦ a e ha he
    (fun l => norm_direction (hv0 l)) anchor hanchor Λ hΛ E
    (fun i => measurableSet_cell ξ (idx i))
    (by intro i j hij; exact cell_disjoint ξ (fun heq => hij (hidx heq))) R
    (fun i => hR (idx i) (enum i).property) ξ 7 C ρ c hξ (by norm_num) hC hMK hρ hc
    (K * D) (mul_pos hK hD) (fun i => volume_cell hξ (idx i)) hpush htube hbroad'
  rw [hsum] at hfill
  have hpriorΛ : ν.real Λ ≤ (A / h) * μ.real univ :=
    (measureReal_mono (subset_univ Λ)).trans hprior
  have hupper := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (measureReal_nonneg : 0 ≤ ν.real Λ) hpriorΛ 3)
    (show 0 ≤ (F.card : ℝ) * (8 * C * 7 ^ 3) ^ 2 * ((K * D : NNReal) : ℝ) ^ 3 by positivity)
  have hfinal := hfill.trans hupper
  have hid : (F.card : ℝ) * (8 * C * 7 ^ 3) ^ 2 * ((K * D : NNReal) : ℝ) ^ 3 *
      ((A / h) * μ.real univ) ^ 3 =
      ((F.card : ℝ) * (8 * C * 7 ^ 3) ^ 2 * (3 * (K : ℝ) * A) ^ 3 * ξ ^ 3) *
        (μ.real univ) ^ 3 := by
    change (F.card : ℝ) * (8 * C * 7 ^ 3) ^ 2 * ((K : ℝ) * (3 * h * ξ)) ^ 3 *
      ((A / h) * μ.real univ) ^ 3 = _
    field_simp
    <;> ring
  rw [hid] at hfinal
  exact (mul_le_mul_iff_left₀ (pow_pos hmass 3)).mp
    (by simpa only [mul_comm, measureReal_def] using hfinal)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeAssigned
