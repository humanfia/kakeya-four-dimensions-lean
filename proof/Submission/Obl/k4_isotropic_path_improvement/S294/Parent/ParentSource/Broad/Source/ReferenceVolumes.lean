-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ReferenceVolumes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ReferenceVolumes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ReferenceVolumes.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.ChildCount
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PathBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path

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

/-- Exact original reference volumes sum using the incidence floors.
Neither a frame condition number nor a rounded width exponent enters. -/
theorem Native.PathData.Valid.reference_volume_sum_le
    (hN : 0 < Nk) (old : Fin p.C) [IsFiniteMeasure (ν (p.γ old))]
    (mid : ℕ) (S : Finset (Fin p.C))
    (hS : ∀ b ∈ S, p.lev b = mid ∧ p.γ b = p.γ old ∧ p.F b ⊆ p.F old) :
    (∑ b ∈ S, ((2 : ℝ) ^ p.T mid)⁻¹ * |(p.Q b).det|) ≤
      p.κ ^ 2 * Nk ^ (f (p.r mid) - f (p.r (p.lev old))) *
        (((2 : ℝ) ^ p.T (p.lev old))⁻¹ * |(p.Q old).det|) := by
  classical
  let μ : Measure Ev := (ν (p.γ old)).prod volume
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hpack := hp.2.2.2.2.2.2.2
  have hdisjA := hp.2.2.2.2.2.2.1
  have hceil : μ (p.F old) ≤ ENNReal.ofReal
      (p.κ * Nk ^ (-f (p.r (p.lev old))) * |(p.Q old).det| *
        ((2 : ℝ) ^ p.T (p.lev old))⁻¹) := by
    obtain ⟨-, -, hch⟩ := hpack old
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -, hupper, -⟩ := hch
    have hh := Broad.prod_le_prior_mul_block (ν := ν (p.γ old))
      (fun q (hq : q ∈ p.F old) => ⟨(hF q hq).2.1, (hF q hq).2.2.1⟩)
    refine hh.trans ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' hupper le_rfl
  have hfinite : μ (p.F old) ≠ ∞ := ne_of_lt (hceil.trans_lt ENNReal.ofReal_lt_top)
  have hchildFinite (b : Fin p.C) (hb : b ∈ S) : μ (p.F b) ≠ ∞ :=
    ne_of_lt ((measure_mono (hS b hb).2.2).trans_lt (lt_top_iff_ne_top.mpr hfinite))
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
  have hsum : (∑ b ∈ S, μ (p.F b)) ≤ μ (p.F old) := by
    rw [← measure_biUnion_finset₀ hdisj (fun b _ => (hmeas b).nullMeasurableSet)]
    exact measure_mono (iUnion₂_subset (fun b hb => (hS b hb).2.2))
  have hsumReal : (∑ b ∈ S, μ.real (p.F b)) ≤ μ.real (p.F old) := by
    have hh := ENNReal.toReal_mono hfinite hsum
    rw [ENNReal.toReal_sum (fun b hb => hchildFinite b hb)] at hh
    exact hh
  have hfloor (b : Fin p.C) (hb : b ∈ S) :
      (Nk ^ (-f (p.r mid)) / p.κ) *
        (((2 : ℝ) ^ p.T mid)⁻¹ * |(p.Q b).det|) ≤ μ.real (p.F b) := by
    obtain ⟨hl, hγ, -⟩ := hS b hb
    obtain ⟨-, -, hch⟩ := hpack b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfl, -⟩ := hch
    rw [hl, hγ] at hfl
    have hh := ENNReal.toReal_mono (hchildFinite b hb) hfl
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    have heq : (Nk ^ (-f (p.r mid)) / p.κ) *
        (((2 : ℝ) ^ p.T mid)⁻¹ * |(p.Q b).det|) =
        Nk ^ (-f (p.r mid)) * |(p.Q b).det| / ((2 : ℝ) ^ p.T mid * p.κ) := by
      field_simp
    rw [heq]
    exact hh
  have hceilReal : μ.real (p.F old) ≤
      p.κ * Nk ^ (-f (p.r (p.lev old))) * |(p.Q old).det| *
        ((2 : ℝ) ^ p.T (p.lev old))⁻¹ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hceil
    rw [ENNReal.toReal_ofReal (show 0 ≤ p.κ * Nk ^ (-f (p.r (p.lev old))) *
      |(p.Q old).det| * ((2 : ℝ) ^ p.T (p.lev old))⁻¹ by positivity)] at hh
    exact hh
  have hscaled : (Nk ^ (-f (p.r mid)) / p.κ) *
      (∑ b ∈ S, ((2 : ℝ) ^ p.T mid)⁻¹ * |(p.Q b).det|) ≤
      p.κ * Nk ^ (-f (p.r (p.lev old))) * |(p.Q old).det| *
        ((2 : ℝ) ^ p.T (p.lev old))⁻¹ := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum (fun b hb => hfloor b hb)).trans (hsumReal.trans hceilReal)
  have hfactor : 0 < Nk ^ (-f (p.r mid)) / p.κ := by positivity
  apply (mul_le_mul_iff_right₀ hfactor).mp
  have hpower : Nk ^ (f (p.r mid) - f (p.r (p.lev old))) * Nk ^ (-f (p.r mid)) =
      Nk ^ (-f (p.r (p.lev old))) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  refine hscaled.trans_eq ?_
  calc
    _ = p.κ * (Nk ^ (f (p.r mid) - f (p.r (p.lev old))) * Nk ^ (-f (p.r mid))) *
        |(p.Q old).det| * ((2 : ℝ) ^ p.T (p.lev old))⁻¹ := by rw [hpower]
    _ = _ := by field_simp [hκ.ne']

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
