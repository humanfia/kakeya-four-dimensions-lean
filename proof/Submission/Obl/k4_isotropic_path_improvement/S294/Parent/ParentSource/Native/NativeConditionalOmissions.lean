-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeConditionalOmissions, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeConditionalOmissions.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeConditionalOmissions.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeConditionalOmissions.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeConditionalOmissions.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.CoarsePacketWitness

/-! Uniform omissions under the fixed current-parent posteriors sum under
one prepared law. Every charge is to the original parent measure. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

def PreparedAngularPath.packetFamilyResidual (_Q : PreparedAngularPath d k p m H u τ) (i : ℕ)
    (D : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (w : Fin (d.W k)) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {z | ∃ b, p.lev b = i ∧ p.γ b = w ∧ z ∈ D b}

theorem PreparedAngularPath.measurableSet_packetFamilyResidual (i : ℕ)
    (D : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hD : ∀ b, MeasurableSet (D b)) (w : Fin (d.W k)) :
    MeasurableSet (Q.packetFamilyResidual i D w) := by
  classical
  have heq : Q.packetFamilyResidual i D w =
      ⋃ b : Fin p.C, if p.lev b = i ∧ p.γ b = w then D b else ∅ := by
    ext z
    simp only [packetFamilyResidual, mem_ofPred_eq, mem_iUnion]
    aesop
  rw [heq]
  exact MeasurableSet.iUnion (fun b => by split <;> simp_all)

theorem PreparedAngularPath.packetFamilyResidual_subset (i : ℕ)
    (D : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hD : ∀ b, D b ⊆ Q.residual (p.γ b) ∩ p.F b) (w : Fin (d.W k)) :
    Q.packetFamilyResidual i D w ⊆ Q.residual w := by
  rintro z ⟨b, _, hbw, hz⟩
  simpa only [hbw] using (hD b hz).1

/-- No count of parents appears: each conditional omission is charged to
its ORIGINAL current-parent mass, and those masses form an exact partition. -/
theorem PreparedAngularPath.conditional_omission_original_mass_le (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m)
    (D : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hD : ∀ b, MeasurableSet (D b))
    (hsub : ∀ b, D b ⊆ Q.residual (p.γ b) ∩ p.F b)
    (ε : ENNReal)
    (hcap : ∀ b, p.lev b = i → ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) ≤ ε) :
    (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.packetFamilyResidual i D w)) ≤
      ε * labelledResidual (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual univ := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hcur (b : Fin p.C) : Q.currentParentLaw b univ =
      ((d.ν k (p.γ b)).prod volume) (Q.residual (p.γ b) ∩ p.F b) := by
    rw [Q.current_parent_eq_original hHE hF b, Measure.restrict_apply_univ]
  have hparent (b : Fin p.C) (hbi : p.lev b = i) :
      ((d.ν k (p.γ b)).prod volume) (D b) ≤ ε * Q.currentParentLaw b univ := by
    have htop : Q.currentParentLaw b univ ≠ ∞ := by
      apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞)
      rw [currentParentLaw, Measure.restrict_apply_univ]
      exact (measure_mono (subset_univ _)).trans (hd.selected_incidence_mass_le_one k _)
    have hmult : ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) *
        Q.currentParentLaw b univ ≤ ε * Q.currentParentLaw b univ :=
      mul_le_mul (hcap b hbi) le_rfl zero_le zero_le
    rw [ProbabilityTheory.cond_mul_eq_inter' MeasurableSet.univ htop, univ_inter] at hmult
    rw [Q.current_parent_eq_original hHE hF b] at hmult ⊢
    simpa only [Measure.restrict_apply (hD b), inter_eq_left.mpr (hsub b)] using hmult
  let ids := Finset.univ.filter (fun b => p.lev b = i)
  have hsum := weighted_packet_union_mass (fun w => (d.ν k w).prod volume)
    (fun w => ENNReal.ofReal (d.ω k w)) p.γ D ids (fun b _ => hD b) (by
      intro b hb b' hb' hne hγ
      have hbi := (Finset.mem_filter.mp hb).2
      have hb'i := (Finset.mem_filter.mp hb').2
      exact (hp.packet_aedisjoint b b' hne (hbi.trans hb'i.symm) hγ).mono
        (fun _ hz => (hsub b hz).2) (fun _ hz => (hsub b' hz).2))
  have heq (w : Fin (d.W k)) : Q.packetFamilyResidual i D w =
      {z | ∃ b ∈ ids, p.γ b = w ∧ z ∈ D b} := by
    ext z
    simp only [packetFamilyResidual, ids, mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
      true_and]
  simp_rw [← heq] at hsum
  have htotal := hp.residual_mass_eq_sum Q.residual Q.residual_measurable
    (fun w => (Q.residual_subset w).trans ((Q.base_subset w).trans (hH w))) i hi
  calc
    _ = ∑ b ∈ ids, ENNReal.ofReal (d.ω k (p.γ b)) * ((d.ν k (p.γ b)).prod volume) (D b) := hsum
    _ ≤ ∑ b ∈ ids, ENNReal.ofReal (d.ω k (p.γ b)) * (ε * Q.currentParentLaw b univ) :=
      Finset.sum_le_sum (fun b hb => mul_le_mul le_rfl
        (hparent b (Finset.mem_filter.mp hb).2) zero_le zero_le)
    _ = ε * ∑ b ∈ ids, ENNReal.ofReal (d.ω k (p.γ b)) * Q.currentParentLaw b univ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ε * labelledResidual (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual univ := by
      congr 1
      rw [labelledResidual_univ, htotal]
      simp only [ids, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp_all only

/-- A uniform conditional fraction costs the SAME fraction under the ONE
prepared law; its normalizer and original world weights cancel exactly. -/
theorem PreparedAngularPath.conditional_omission_prepared_mass_le (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m)
    (D : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hD : ∀ b, MeasurableSet (D b))
    (hsub : ∀ b, D b ⊆ Q.residual (p.γ b) ∩ p.F b)
    (ε : ENNReal)
    (hcap : ∀ b, p.lev b = i → ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) ≤ ε) :
    Q.law (labelledSupport (Q.packetFamilyResidual i D)) ≤ ε := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  have hpos : 0 < labelledResidual (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual univ :=
    by
      rw [labelledResidual_univ]
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity : 0 < p.κ⁻¹ / 8)) Q.original_mass
  have htop := ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞) (Q.original_total_le_one hd hHE)
  have hmeas := measurableSet_labelledSupport (Q.packetFamilyResidual i D)
    (Q.measurableSet_packetFamilyResidual i D hD)
  have hinter (w : Fin (d.W k)) : Q.residual w ∩
      {z | (w, z) ∈ labelledSupport (Q.packetFamilyResidual i D)} = Q.packetFamilyResidual i D w :=
    inter_eq_right.mpr (Q.packetFamilyResidual_subset i D hsub w)
  change preparedResidualLaw (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual _ ≤ ε
  rw [preparedResidualLaw_apply _ _ _ _ hmeas]
  simp only [hinter]
  rw [← labelledResidual_univ (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual]
  calc
    _ ≤ (ε * labelledResidual (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual univ) /
      labelledResidual (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual univ :=
        ENNReal.div_le_div_right (Q.conditional_omission_original_mass_le hd hp hHE hH i hi D hD hsub ε hcap) _
    _ = ε := by
      rw [div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hpos.ne' htop, mul_one]

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
