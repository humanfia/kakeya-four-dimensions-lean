-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.LocalReferences, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/LocalReferences.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/LocalReferences.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ReferenceVolumes

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W}
  {Nk L κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
  {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
  {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
  (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem Native.PathData.Valid.packet_incidence_sum_le
    (old : Fin p.C) (mid : ℕ) (S : Finset (Fin p.C))
    (hS : ∀ b ∈ S, p.lev b = mid ∧ p.γ b = p.γ old ∧ p.F b ⊆ p.F old) :
    (∑ b ∈ S, ((ν (p.γ old)).prod volume) (p.F b)) ≤
      ((ν (p.γ old)).prod volume) (p.F old) := by
  classical
  let μ : Measure Ev := (ν (p.γ old)).prod volume
  have hpack := hp.2.2.2.2.2.2.2
  have hdisjA := hp.2.2.2.2.2.2.1
  have hmeas (b : Fin p.C) : MeasurableSet (p.F b) := by
    obtain ⟨-, -, hch⟩ := hpack b
    exact hch.2.2.2.2.2.2.2.1
  have hdisj : (S : Set (Fin p.C)).Pairwise (Function.onFun (AEDisjoint μ) p.F) := by
    intro b hb c hc hne
    obtain ⟨hlb, hγb, -⟩ := hS b hb
    obtain ⟨hlc, hγc, -⟩ := hS c hc
    obtain ⟨-, -, hchb⟩ := hpack b
    obtain ⟨-, -, hchc⟩ := hpack c
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hFb, -⟩ := hchb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hFc, -⟩ := hchc
    by_cases hj : p.j b = p.j c
    · exact Broad.aedisjoint_of_lines
        (hdisjA b c hne (hlb.trans hlc.symm) (hγb.trans hγc.symm) hj)
        (fun q hq => (hFb q hq).2.1) (fun q hq => (hFc q hq).2.1)
    · apply Broad.aedisjoint_of_blocks (T := p.T mid) hj
      · intro q hq
        rw [← hlb]
        exact (hFb q hq).2.2.1
      · intro q hq
        rw [← hlc]
        exact (hFc q hq).2.2.1
  rw [← measure_biUnion_finset₀ hdisj (fun b _ => (hmeas b).nullMeasurableSet)]
  exact measure_mono (iUnion₂_subset (fun b hb => (hS b hb).2.2))

/-- All full fine references inside one original old packet are paid by
that packet's SAME full reference, with only the two saturation factors. -/
theorem Native.PathData.Valid.local_reference_sum_le
    (hN : 0 < Nk) (old : Fin p.C) (mid : ℕ) (S : Finset (Fin p.C))
    (hS : ∀ b ∈ S, p.lev b = mid ∧ p.γ b = p.γ old ∧ p.F b ⊆ p.F old) :
    (∑ b ∈ S, ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹) * ν (p.γ old) (p.A b)) ≤
      ENNReal.ofReal (p.κ ^ 2) *
        (ν (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hpoint (b : Fin p.C) (hb : b ∈ S) :
      ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹) * ν (p.γ old) (p.A b) ≤
        ENNReal.ofReal (p.κ ^ 2) * ((ν (p.γ old)).prod volume) (p.F b) := by
    have hprior := (hp.assignment_mass_bounds hN b).2
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfloor, -⟩ := hch
    rw [(hS b hb).1, (hS b hb).2.1] at hprior hfloor
    calc
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹) *
          ENNReal.ofReal (p.κ * Nk ^ (-f (p.r mid)) * |(p.Q b).det|) :=
        mul_le_mul' le_rfl hprior
      _ = ENNReal.ofReal (p.κ ^ 2) *
          ENNReal.ofReal (Nk ^ (-f (p.r mid)) * |(p.Q b).det| / ((2 : ℝ) ^ p.T mid * p.κ)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp [hκ.ne']
      _ ≤ _ := mul_le_mul' le_rfl hfloor
  have hceil : ((ν (p.γ old)).prod volume) (p.F old) ≤
      ν (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹) := by
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 old
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
    exact Broad.prod_le_prior_mul_block
      (fun q (hq : q ∈ p.F old) => ⟨(hF q hq).2.1, (hF q hq).2.2.1⟩)
  calc
    _ ≤ ∑ b ∈ S, ENNReal.ofReal (p.κ ^ 2) * ((ν (p.γ old)).prod volume) (p.F b) :=
      Finset.sum_le_sum hpoint
    _ = ENNReal.ofReal (p.κ ^ 2) * (∑ b ∈ S, ((ν (p.γ old)).prod volume) (p.F b)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (p.κ ^ 2) * ((ν (p.γ old)).prod volume) (p.F old) :=
      mul_le_mul' le_rfl (hp.packet_incidence_sum_le old mid S hS)
    _ ≤ _ := mul_le_mul' le_rfl hceil

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
