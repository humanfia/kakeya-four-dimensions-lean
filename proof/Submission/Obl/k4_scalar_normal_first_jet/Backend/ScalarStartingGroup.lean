/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarStartingGroup.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarStartingGroup.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAnisotropicCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGroupNormalization
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCovers
import Mathlib.MeasureTheory.Function.Floor

/-! An actual starting scalar palette supplies one normalized original group. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

theorem original_scalar_starting_group_palette {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A : Set Λ) (hA : MeasurableSet A)
    (Y Z : Λ → ℝ) (hZ : Measurable Z) (S : Set ℝ)
    {H d B BZ Cs Cj K : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hB : 1 ≤ B)
    (hBZ : 0 < BZ) (hHBZ : H ≤ 2 * BZ) (hCs : 0 ≤ Cs) (hCj : 0 ≤ Cj)
    (hK : 0 < K) (hS : IntervalAD H d Cs S) (hY : ∀ l ∈ A, |Y l| ≤ B)
    (hsupport : ∀ l ∈ A, Z l ∈ S ∩ Icc (-BZ) BZ)
    (hjoint : ∀ a b : ℝ,
      ν.real {l | l ∈ A ∧ Y l ∈ Icc a (a + H) ∧ Z l ∈ Icc b (b + H)} ≤ Cj * H ^ (1 + d))
    (hKcount : 3 * Cs * (2 * BZ) ^ d ≤ K) (hKprior : 50 * B * Cj ≤ K) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ K / H ^ d ∧
      (∀ l ∈ A, (⌊Z l / H⌋ : ℤ) ∈ J) ∧
      (∀ b ∈ J, (ν.restrict A).real {l | (⌊Z l / H⌋ : ℤ) = b} ≤ K * H ^ d) ∧
      ∀ b ∈ J, (scalarGroupPrior (ν.restrict A) (fun l => ⌊Z l / H⌋) b (H ^ d)).real univ ≤ K := by
  have hc : 0 < H ^ d := Real.rpow_pos_of_pos hH _
  have hcode : Measurable (fun l => (⌊Z l / H⌋ : ℤ)) := (hZ.div_const H).floor
  obtain ⟨J, hcard, hcover⟩ := intervalAD_grid_list hH hHBZ hS (a := -BZ)
  have hcard' : (J.card : ℝ) ≤ K / H ^ d := by
    apply hcard.trans
    rw [Real.div_rpow (by positivity : 0 ≤ 2 * BZ) hH.le]
    calc
      _ = (3 * Cs * (2 * BZ) ^ d) / H ^ d := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hKcount hc.le
  have hcover' : ∀ l ∈ A, (⌊Z l / H⌋ : ℤ) ∈ J := by
    intro l hl
    obtain ⟨hs, hlo, hhi⟩ := hsupport l hl
    exact hcover _ ⟨hs, hlo, by linarith⟩
  have hcap : ∀ b ∈ J, (ν.restrict A).real {l | (⌊Z l / H⌋ : ℤ) = b} ≤ K * H ^ d := by
    intro b hb
    let C := A ∩ {l | (⌊Z l / H⌋ : ℤ) = b}
    have hCsub : C ⊆ A := inter_subset_left
    have hbox : ∀ l ∈ C,
        (![Y l, Z l] : Fin 2 → ℝ) 0 ∈ Icc (-B) (-B + (2 * B) * 1) ∧
        (![Y l, Z l] : Fin 2 → ℝ) 1 ∈ Icc (H * b) (H * b + H * 1) := by
      intro l hl
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hy := abs_le.mp (hY l hl.1)
      have hz := (mesh_lower_endpoint hH hl.2).1
      exact ⟨⟨hy.1, by nlinarith [hy.2]⟩,
        by simpa only [mul_one] using hz⟩
    have hcube : ∀ a : Fin 2 → ℝ,
        ν.real {l | l ∈ A ∧ ∀ i, (![Y l, Z l] : Fin 2 → ℝ) i ∈ Icc (a i) (a i + H * 1)} ≤
          Cj * (H * 1) ^ (1 + d) := by
      intro a
      simpa only [Fin.forall_fin_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one] using hjoint (a 0) (a 1)
    have hh := original_normalized_scalar_cap_enlarged ν A C (fun l => ![Y l, Z l]) ![-B, H * b]
      hH hH1 (L := 2 * B) (by linarith) (r := 1) (by norm_num) hCj hCsub hbox hcube
    have hraw : ν.real C ≤ K * H ^ d := by
      apply (div_le_iff₀ hc).mp at hh
      have hcoef : 25 * (2 * B) * Cj * (1 : ℝ) ^ (1 + d) ≤ K := by
        simpa only [Real.one_rpow, mul_one] using (show 25 * (2 * B) * Cj ≤ K by nlinarith)
      exact hh.trans (mul_le_mul_of_nonneg_right hcoef hc.le)
    change (ν.restrict A).real ((fun l => (⌊Z l / H⌋ : ℤ)) ⁻¹' {b}) ≤ K * H ^ d
    rw [Measure.real, Measure.restrict_apply (hcode (MeasurableSet.singleton b))]
    simpa [C, Measure.real, Set.preimage, inter_comm] using hraw
  refine ⟨J, hcard', hcover', hcap, ?_⟩
  intro b hb
  rw [scalarGroupPrior_real _ _ _ hc MeasurableSet.univ, univ_inter]
  exact (div_le_iff₀ hc).mpr (hcap b hb)

theorem exists_original_scalar_starting_group {Θ Λ : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [IsFiniteMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) (A : Set Λ) (hA : MeasurableSet A)
    (hEA : E ⊆ univ ×ˢ A) (Y Z : Λ → ℝ) (hZ : Measurable Z) (S : Set ℝ)
    {H d B BZ Cs Cj K δ : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hB : 1 ≤ B)
    (hBZ : 0 < BZ) (hHBZ : H ≤ 2 * BZ) (hCs : 0 ≤ Cs) (hCj : 0 ≤ Cj)
    (hK : 0 < K) (hδ : 0 < δ) (hmass : δ ≤ (μ.prod ν).real E)
    (hS : IntervalAD H d Cs S) (hY : ∀ l ∈ A, |Y l| ≤ B)
    (hsupport : ∀ l ∈ A, Z l ∈ S ∩ Icc (-BZ) BZ)
    (hjoint : ∀ a b : ℝ,
      ν.real {l | l ∈ A ∧ Y l ∈ Icc a (a + H) ∧ Z l ∈ Icc b (b + H)} ≤ Cj * H ^ (1 + d))
    (hKcount : 3 * Cs * (2 * BZ) ^ d ≤ K) (hKprior : 50 * B * Cj ≤ K) :
    ∃ b : ℤ,
      (scalarGroupPrior (ν.restrict A) (fun l => ⌊Z l / H⌋) b (H ^ d)).real univ ≤ K ∧
      δ / K ≤ (μ.prod (scalarGroupPrior (ν.restrict A) (fun l => ⌊Z l / H⌋) b (H ^ d))).real
        (E ∩ (univ ×ˢ {l | ⌊Z l / H⌋ = b})) := by
  have hc : 0 < H ^ d := Real.rpow_pos_of_pos hH _
  have hcode : Measurable (fun l => (⌊Z l / H⌋ : ℤ)) := (hZ.div_const H).floor
  obtain ⟨J, hcard', hcover', hcap, _⟩ :=
    original_scalar_starting_group_palette ν A hA Y Z hZ S hH hH1 hB hBZ hHBZ
      hCs hCj hK hS hY hsupport hjoint hKcount hKprior
  have hprod : μ.prod (ν.restrict A) = (μ.prod ν).restrict (univ ×ˢ A) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := μ) (ν := ν) univ A)
  have hmass' : δ ≤ (μ.prod (ν.restrict A)).real E := by
    simpa only [hprod, Measure.real, Measure.restrict_apply hE, inter_eq_left.mpr hEA] using hmass
  obtain ⟨b, hb, hprior, hgroup⟩ := exists_original_normalized_scalar_group μ (ν.restrict A)
    hE (fun l => ⌊Z l / H⌋) hcode J hc hK hδ (fun p hp => hcover' p.2 (hEA hp).2) hmass' hcard' hcap
  refine ⟨b, hprior, ?_⟩
  change δ / K ≤ (μ.prod (scalarGroupPrior (ν.restrict A) (fun l => (⌊Z l / H⌋ : ℤ)) b (H ^ d))).real
    (E ∩ (univ ×ˢ ((fun l => (⌊Z l / H⌋ : ℤ)) ⁻¹' {b})))
  rw [original_scalar_group_mass μ (ν.restrict A) (fun l => (⌊Z l / H⌋ : ℤ)) b hc
    (hE.inter (MeasurableSet.univ.prod (hcode (MeasurableSet.singleton b))))]
  rw [original_scalar_group_mass μ (ν.restrict A) (fun l => (⌊Z l / H⌋ : ℤ)) b hc hE] at hgroup
  simpa only [inter_assoc, inter_self] using hgroup

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
