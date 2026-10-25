-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeLightParents, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeLightParents.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeLightParents.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeLightParents.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeLightParents.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeParentCaps

/-! Omit light coarse parents after the window is chosen, while retaining all
old probability references. The cost is paid in the original weighted law. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

noncomputable def PreparedAngularPath.lightParents (i : ℕ) (θ : ENNReal) : Finset (Fin p.C) := by
  classical
  exact Finset.univ.filter (fun b => p.lev b = i ∧
    ¬ θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ)

def PreparedAngularPath.lightParentResidual (i : ℕ) (θ : ENNReal) (w : Fin (d.W k)) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {z | ∃ b ∈ Q.lightParents i θ, p.γ b = w ∧ z ∈ Q.residual (p.γ b) ∩ p.F b}

theorem PreparedAngularPath.light_parent_subset (i : ℕ) (θ : ENNReal) (w : Fin (d.W k)) :
    Q.lightParentResidual i θ w ⊆ Q.residual w := by
  rintro z ⟨b, _, hbw, hz⟩
  simpa only [hbw] using hz.1

theorem PreparedAngularPath.measurableSet_lightParentResidual
    (hF : ∀ b, MeasurableSet (p.F b)) (i : ℕ) (θ : ENNReal) (w : Fin (d.W k)) :
    MeasurableSet (Q.lightParentResidual i θ w) := by
  classical
  have heq : Q.lightParentResidual i θ w =
      ⋃ b : Fin p.C, if b ∈ Q.lightParents i θ ∧ p.γ b = w then Q.residual (p.γ b) ∩ p.F b else ∅ := by
    ext z
    constructor
    · rintro ⟨b, hb, hbw, hz⟩
      apply mem_iUnion.mpr
      have hh : b ∈ Q.lightParents i θ ∧ p.γ b = w := ⟨hb, hbw⟩
      exact ⟨b, by simpa only [ite_eq_left hh] using hz⟩
    · intro hz
      obtain ⟨b, hb⟩ := mem_iUnion.mp hz
      split_ifs at hb with hbw
      · exact ⟨b, hbw.1, hbw.2, hb⟩
      · exact False.elim hb
  rw [heq]
  apply MeasurableSet.iUnion
  intro b
  split
  · exact (Q.residual_measurable _).inter (hF b)
  · exact MeasurableSet.empty

theorem PreparedAngularPath.nonlight_parent_floor (i : ℕ) (θ : ENNReal) (b : Fin p.C)
    (hbi : p.lev b = i) (hb : b ∉ Q.lightParents i θ) :
    θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ := by
  classical
  by_contra hn
  exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbi, hn⟩)

/-- All omitted parents at the chosen level cost at most `θ` in ORIGINAL
weighted incidence mass. The reference budget is fixed before the window. -/
theorem PreparedAngularPath.light_parent_original_mass_le (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i : ℕ) (θ : ENNReal) :
    (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.lightParentResidual i θ w)) ≤ θ := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hcur (b : Fin p.C) : Q.currentParentLaw b univ =
      ((d.ν k (p.γ b)).prod volume) (Q.residual (p.γ b) ∩ p.F b) := by
    rw [Q.current_parent_eq_original hHE hF b, Measure.restrict_apply_univ]
  have hsum := weighted_packet_union_mass (fun w => (d.ν k w).prod volume)
    (fun w => ENNReal.ofReal (d.ω k w)) p.γ (fun b => Q.residual (p.γ b) ∩ p.F b)
    (Q.lightParents i θ) (fun b _ => (Q.residual_measurable _).inter (hF b)) (by
      intro b hb b' hb' hne hγ
      have hbi := (Finset.mem_filter.mp hb).2.1
      have hb'i := (Finset.mem_filter.mp hb').2.1
      exact (hp.packet_aedisjoint b b' hne (hbi.trans hb'i.symm) hγ).mono
        inter_subset_right inter_subset_right)
  change (∑ w, ENNReal.ofReal (d.ω k w) *
    ((d.ν k w).prod volume) (Q.lightParentResidual i θ w)) = _ at hsum
  have hl := light_packet_mass_le
    (fun b => if p.lev b = i then ENNReal.ofReal (d.ω k (p.γ b)) else 0)
    (fun b => d.pathAngularReference k p Q.base Q.mask b univ)
    (fun b => Q.currentParentLaw b univ) θ (Q.reference_level_budget hd hp i)
  calc
    _ = ∑ b ∈ Q.lightParents i θ, ENNReal.ofReal (d.ω k (p.γ b)) * Q.currentParentLaw b univ := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro b _
      rw [hcur b]
    _ = ∑ b, if θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ
        then 0 else (if p.lev b = i then ENNReal.ofReal (d.ω k (p.γ b)) else 0) *
          Q.currentParentLaw b univ := by
      rw [lightParents, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : p.lev b = i <;>
        by_cases hh : θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ <;>
        simp [hb, hh]
    _ ≤ θ := hl

/-- The same omission costs at most `8κθ` under the single prepared law.
This is a bound on an event of that law, not a replacement probability law. -/
theorem PreparedAngularPath.light_parent_prepared_mass_le (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i : ℕ) (θ : ENNReal) :
    Q.law (labelledSupport (Q.lightParentResidual i θ)) ≤ θ * ENNReal.ofReal (8 * p.κ) := by
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hD := measurableSet_labelledSupport (Q.lightParentResidual i θ)
    (Q.measurableSet_lightParentResidual hF i θ)
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  have hfloor : 0 < p.κ⁻¹ / 8 := by positivity
  have hinter (w : Fin (d.W k)) : Q.residual w ∩
      {x | (w, x) ∈ labelledSupport (Q.lightParentResidual i θ)} = Q.lightParentResidual i θ w :=
    inter_eq_right.mpr (Q.light_parent_subset i θ w)
  change preparedResidualLaw (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual _ ≤ _
  rw [preparedResidualLaw_apply _ _ _ _ hD]
  simp only [hinter, div_eq_mul_inv]
  have hi : (ENNReal.ofReal (p.κ⁻¹ / 8))⁻¹ = ENNReal.ofReal (8 * p.κ) := by
    rw [← ENNReal.ofReal_inv_of_pos hfloor]
    congr 1
    simp [inv_div, div_inv_eq_mul]
  calc
    _ ≤ θ * (ENNReal.ofReal (p.κ⁻¹ / 8))⁻¹ :=
      mul_le_mul (Q.light_parent_original_mass_le hd hp hHE i θ)
        (ENNReal.inv_le_inv.mpr Q.original_mass) zero_le zero_le
    _ = _ := by rw [hi]

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
