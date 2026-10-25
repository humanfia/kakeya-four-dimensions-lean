-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeFamilyMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeFamilyMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeFamilyMass.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeFamilyMass.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeFamilyMass.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeConditionalOmissions

/-! Relative selections under original current-parent posteriors retain the
same fraction of the original weighted family mass. This permits summing
narrow-state floors without charging the number of states or packets. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

/-- This is an exact identity under the original weighted law, before the
single prepared normalizer is applied. -/
theorem PreparedAngularPath.packet_family_original_mass_eq (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i : ℕ)
    (D : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hD : ∀ b, MeasurableSet (D b))
    (hsub : ∀ b, D b ⊆ Q.residual (p.γ b) ∩ p.F b) :
    (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.packetFamilyResidual i D w)) =
      ∑ b, if p.lev b = i then ENNReal.ofReal (d.ω k (p.γ b)) *
        (ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) * Q.currentParentLaw b univ) else 0 := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hcurD (b : Fin p.C) : Q.currentParentLaw b (D b) = ((d.ν k (p.γ b)).prod volume) (D b) := by
    rw [Q.current_parent_eq_original hHE hF b, Measure.restrict_apply (hD b), inter_eq_left.mpr (hsub b)]
  have hcond (b : Fin p.C) :
      ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) * Q.currentParentLaw b univ =
        ((d.ν k (p.γ b)).prod volume) (D b) := by
    have htop : Q.currentParentLaw b univ ≠ ∞ := by
      apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞)
      rw [currentParentLaw, Measure.restrict_apply_univ]
      exact (measure_mono (subset_univ _)).trans (hd.selected_incidence_mass_le_one k _)
    simpa only [univ_inter, hcurD b] using
      ProbabilityTheory.cond_mul_eq_inter' (μ := Q.currentParentLaw b) MeasurableSet.univ htop (D b)
  let ids := Finset.univ.filter (fun b => p.lev b = i)
  have hsum := weighted_packet_union_mass (fun w => (d.ν k w).prod volume)
    (fun w => ENNReal.ofReal (d.ω k w)) p.γ D ids (fun b _ => hD b) (by
      intro b hb b' hb' hne hγ
      exact (hp.packet_aedisjoint b b' hne
        ((Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hb').2.symm) hγ).mono
          (fun _ hz => (hsub b hz).2) (fun _ hz => (hsub b' hz).2))
  have heq (w : Fin (d.W k)) : Q.packetFamilyResidual i D w =
      {z | ∃ b ∈ ids, p.γ b = w ∧ z ∈ D b} := by
    ext z
    simp only [packetFamilyResidual, ids, mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [← heq] at hsum
  rw [hsum]
  simp only [ids, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp only [hcond]

/-- A relative floor in every ORIGINAL current posterior sums to the same
relative floor in the ORIGINAL weighted mixture, with no parent factor. -/
theorem PreparedAngularPath.relative_family_original_mass_le (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i : ℕ)
    (U V : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hU : ∀ b, MeasurableSet (U b)) (hV : ∀ b, MeasurableSet (V b))
    (hUsub : ∀ b, U b ⊆ Q.residual (p.γ b) ∩ p.F b)
    (hVsub : ∀ b, V b ⊆ Q.residual (p.γ b) ∩ p.F b)
    (θ : ENNReal)
    (hfloor : ∀ b, p.lev b = i → θ * ProbabilityTheory.cond (Q.currentParentLaw b) univ (U b) ≤
      ProbabilityTheory.cond (Q.currentParentLaw b) univ (V b)) :
    θ * (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.packetFamilyResidual i U w)) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.packetFamilyResidual i V w) := by
  rw [Q.packet_family_original_mass_eq hd hp hHE i U hU hUsub,
    Q.packet_family_original_mass_eq hd hp hHE i V hV hVsub, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : p.lev b = i
  · simp only [hb, ite_true]
    calc
      _ = ENNReal.ofReal (d.ω k (p.γ b)) *
          ((θ * ProbabilityTheory.cond (Q.currentParentLaw b) univ (U b)) * Q.currentParentLaw b univ) := by ring
      _ ≤ _ := mul_le_mul le_rfl (mul_le_mul (hfloor b hb) le_rfl zero_le zero_le) zero_le zero_le
  · simp only [hb, ite_false, mul_zero]
    exact le_rfl

/-- The SAME relative floor holds under the SINGLE prepared law, without
conditioning on a new retained family. -/
theorem PreparedAngularPath.relative_family_prepared_mass_le (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i : ℕ)
    (U V : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hU : ∀ b, MeasurableSet (U b)) (hV : ∀ b, MeasurableSet (V b))
    (hUsub : ∀ b, U b ⊆ Q.residual (p.γ b) ∩ p.F b)
    (hVsub : ∀ b, V b ⊆ Q.residual (p.γ b) ∩ p.F b)
    (θ : ENNReal)
    (hfloor : ∀ b, p.lev b = i → θ * ProbabilityTheory.cond (Q.currentParentLaw b) univ (U b) ≤
      ProbabilityTheory.cond (Q.currentParentLaw b) univ (V b)) :
    θ * Q.law (labelledSupport (Q.packetFamilyResidual i U)) ≤
      Q.law (labelledSupport (Q.packetFamilyResidual i V)) := by
  have hformula (D : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (hD : ∀ b, MeasurableSet (D b))
      (hsub : ∀ b, D b ⊆ Q.residual (p.γ b) ∩ p.F b) :
      Q.law (labelledSupport (Q.packetFamilyResidual i D)) =
        (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.packetFamilyResidual i D w)) /
          ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w) := by
    have hmeas := measurableSet_labelledSupport (Q.packetFamilyResidual i D)
      (Q.measurableSet_packetFamilyResidual i D hD)
    have hinter (w : Fin (d.W k)) : Q.residual w ∩
        {z | (w, z) ∈ labelledSupport (Q.packetFamilyResidual i D)} = Q.packetFamilyResidual i D w :=
      inter_eq_right.mpr (Q.packetFamilyResidual_subset i D hsub w)
    change preparedResidualLaw (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual _ = _
    rw [preparedResidualLaw_apply _ _ _ _ hmeas]
    simp only [hinter]
  rw [hformula U hU hUsub, hformula V hV hVsub]
  change θ * (_ / _) ≤ _ / _
  simpa only [div_eq_mul_inv, mul_assoc] using
    ENNReal.div_le_div_right (Q.relative_family_original_mass_le hd hp hHE i U V hU hV hUsub hVsub θ hfloor) _

/-- Undo the single normalization after a prepared family floor. The original
world weights and source measures appear unchanged in the conclusion. -/
theorem PreparedAngularPath.original_floor_of_prepared_family (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i : ℕ)
    (D : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hD : ∀ b, MeasurableSet (D b))
    (hsub : ∀ b, D b ⊆ Q.residual (p.γ b) ∩ p.F b)
    {a : ℝ} (hfloor : ENNReal.ofReal a ≤ Q.law (labelledSupport (Q.packetFamilyResidual i D))) :
    ENNReal.ofReal ((p.κ⁻¹ / 8) * a) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.packetFamilyResidual i D w) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  have hmeas := measurableSet_labelledSupport (Q.packetFamilyResidual i D)
    (Q.measurableSet_packetFamilyResidual i D hD)
  have htop : (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w)) ≠ ∞ := by
    rw [← labelledResidual_univ]
    exact ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞) (Q.original_total_le_one hd hHE)
  have hinter (w : Fin (d.W k)) : Q.residual w ∩
      {z | (w, z) ∈ labelledSupport (Q.packetFamilyResidual i D)} = Q.packetFamilyResidual i D w :=
    inter_eq_right.mpr (Q.packetFamilyResidual_subset i D hsub w)
  have hh := prepared_cut_original_floor (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
    (labelledSupport (Q.packetFamilyResidual i D)) hmeas (by positivity) htop Q.original_mass hfloor
  simpa only [hinter] using hh

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
