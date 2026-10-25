-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.BufferedPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/BufferedPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/BufferedPreparation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/BufferedPreparation.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PathAngularLoss

/- The actual native preparation data follow Native.NativePreparation,
adapted there from LOT o116/x0389/e3859a9b; the new proof retains the
explicit original omission budgets. -/

/-! A larger original mass buffer for removing all covered heavy strips.
The angular cap and every old parent reference are the existing ones. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open scoped ENNReal BigOperators

/-- Uniform preparation retains at least 11/(32*kappa) in the ORIGINAL
mixture, while satisfying the same PreparedAngularPath interface. -/
theorem ProblemData.Valid.prepare_native_angular_path_buffered {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) (κ₁ : ℝ) (m : ℕ) (hm : 0 < m)
    (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (u : T → ℝ)
    (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L) (τ : ℝ) (hτ : 0 < τ) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {q | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ q ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      ∃ Q : PreparedAngularPath d k p m H u τ,
        ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
          ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w) := by
  have hL : 0 < d.L := hd.2.2.2.1
  obtain ⟨σc, hσc, hclean⟩ := hd.cleanup_tests (fun _ : Unit => d.L) u τ hτ
    (fun _ => ⟨hL.le, le_rfl⟩) hu
  have hbad : ∀ test : Unit ⊕ T, IsPowerSmall d.N
      (fun k => ∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w
        (d.testBad (fun _ : Unit => d.L) u τ test k w)) := by
    intro test
    cases test with
    | inl _ => exact hd.pureBad_powerSmall d.L τ hL.le le_rfl hτ
    | inr t => exact hd.angularBad_powerSmall (u t) τ (hu t).1 (hu t).2 hτ
  have htotal := powerSmall_finset_sum hd.tendsto Finset.univ
    (fun (test : Unit ⊕ T) k => ∑ w, ENNReal.ofReal (d.ω k w) *
      d.μ k w (d.testBad (fun _ : Unit => d.L) u τ test k w)) (fun test _ => hbad test)
  obtain ⟨σb, hσb, hbudget⟩ := powerSmall_uniform_path_budget hd.tendsto htotal 32 (by norm_num)
  refine ⟨min σc σb, lt_min hσc hσb, ?_⟩
  filter_upwards [hclean, hbudget] with k hk hbudgetk
  intro p hp H hH hcover hmass
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  have hκc : p.κ ≤ d.N k ^ σc :=
    hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN (min_le_left _ _))
  have hκb : p.κ ≤ d.N k ^ σb :=
    hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN (min_le_right _ _))
  have hHE := hp.residual_subset_event H hcover
  have hnative := hd.clean_native_velocity k H hH
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  let H₀ : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun w =>
    nativeVelocityResidual H (d.K k) w ∩ {z | packetUnique p.lev p.γ p.F w z}
  have hH₀sub (w : Fin (d.W k)) : H₀ w ⊆ H w :=
    inter_subset_left.trans (hnative.1 w).2.1
  have hH₀ (w : Fin (d.W k)) : MeasurableSet (H₀ w) ∧ H₀ w ⊆ d.E k w :=
    ⟨(hnative.1 w).1.inter (measurableSet_packetUnique p.lev p.γ p.F hF w),
      (hH₀sub w).trans (hHE w)⟩
  have hmass_eq (w : Fin (d.W k)) : ((d.ν k w).prod volume) (H₀ w) =
      ((d.ν k w).prod volume) (H w) := by
    calc
      _ = ((d.ν k w).prod volume) (nativeVelocityResidual H (d.K k) w) := by
        apply measure_congr
        filter_upwards [hp.ae_packet_unique w] with z hz
        simp only [H₀, mem_inter_iff, mem_ofPred_eq, hz, and_true]
      _ = _ := hnative.2 w
  have hmass₀ : ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H₀ w) := by
    simpa only [hmass_eq] using hmass
  obtain ⟨hbase, hpure, hangular, _⟩ := hk p.κ hp.1 hκc H₀ hH₀ hmass₀
  let base := d.pruneTests (fun _ : Unit => d.L) u τ k H₀
  have hbaseE (w : Fin (d.W k)) : base w ⊆ d.E k w := (hbase w).2.trans (hH₀ w).2
  have hloss : (∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w
      (⋃ test, d.testBad (fun _ : Unit => d.L) u τ test k w)) ≤ ENNReal.ofReal (p.κ⁻¹ / 32) :=
    (finite_exception_mixture_bound (d.μ k) (fun w => ENNReal.ofReal (d.ω k w))
      (fun test w => d.testBad (fun _ : Unit => d.L) u τ test k w)).trans (hbudgetk p.κ hp.1 hκb)
  have hbaseStrong : ENNReal.ofReal (15 * p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (base w) := by
    have hmassμ : ENNReal.ofReal (15 * p.κ⁻¹ / 32) + ENNReal.ofReal (p.κ⁻¹ / 32) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w (H₀ w) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      have heq : 15 * p.κ⁻¹ / 32 + p.κ⁻¹ / 32 = p.κ⁻¹ / 2 := by ring
      rw [heq]
      have hμH₀ (w : Fin (d.W k)) := d.μ_apply_eq k w (hH₀ w).1 (hH₀ w).2
      simpa only [hμH₀] using hmass₀
    have hkeep := mixture_remove_budget (d.μ k) (fun w => ENNReal.ofReal (d.ω k w)) H₀
      (fun w => ⋃ test, d.testBad (fun _ : Unit => d.L) u τ test k w)
      ENNReal.ofReal_ne_top hmassμ hloss
    convert hkeep using 1
    apply Finset.sum_congr rfl
    intro w _
    change ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (base w) =
      ENNReal.ofReal (d.ω k w) * d.μ k w (base w)
    rw [d.μ_apply_eq k w (hbase w).1 (hbaseE w)]
  have hknown : ∀ w b q, q ∈ base w ∩ (if p.γ b = w then p.F b else ∅) →
      b ∈ terminalAncestorList p m w (obs (d.B k w) (δ (d.N k) d.L) q) := by
    intro w b q hq
    by_cases hb : p.γ b = w
    · have hqb : q ∈ p.F b := by simpa only [ite_eq_left hb] using hq.2
      exact hp.terminalAncestorList_mem w q ((hbase w).2 hq.1).2
        (hcover w (hH₀sub w ((hbase w).2 hq.1))) b hb hqb
    · simp only [ite_eq_right hb, mem_inter_iff, mem_empty_iff_false, and_false] at hq
  obtain ⟨A, hA, hcut, hcutloss, hdom, hcap⟩ := hd.prepare_path_angular_cut_of_list_loss k p κ₁ m s δ₀
    Mp Dp (min σc σb) hp u hu τ base (fun w => (hbase w).1) hbaseE
    (terminalAncestorList p m) (terminalAncestorList_card p m hp.2.2.2.2.2.1) hknown
    (fun w q hq => (hpure w q hq ()).1) (fun t w q hq => hangular w q hq t)
    (angularPreparationEpsilon m p.κ) (angularPreparationEpsilon_ne_zero hm hκ) ENNReal.ofReal_ne_top
  rw [angularPreparationEpsilon_budget hm hκ] at hcutloss
  have hcutmass : ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (d.pathAngularCut k p base A w) := by
    apply ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (p.κ⁻¹ / 8)) ENNReal.ofReal_ne_top
    have heq : 11 * p.κ⁻¹ / 32 + p.κ⁻¹ / 8 = 15 * p.κ⁻¹ / 32 := by ring
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), heq]
    exact hbaseStrong.trans hcutloss
  refine ⟨{
    base := base
    mask := A
    base_measurable := fun w => (hbase w).1
    base_subset := fun w => (hbase w).2.trans (hH₀sub w)
    velocity_bound := fun w q hq => (hnative.1 w).2.2 q ((hbase w).2 hq).1
    mask_measurable := hA
    residual_measurable := fun w => (hcut w).1
    residual_subset := fun w => (hcut w).2
    original_mass := (ENNReal.ofReal_le_ofReal (by nlinarith [inv_nonneg.mpr hκ.le])).trans hcutmass
    parent_domination := hdom
    angular_cap := hcap
    pointwise_pure_lower := fun w q hq => (hpure w q hq ()).1
    pointwise_pure_upper := fun w q hq => (hpure w q hq ()).2
    pointwise_angular_upper := fun t w q hq => hangular w q hq t
    base_packet_unique := fun w q hq => ((hbase w).2 hq).2 }, hcutmass⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
