-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OriginalPath, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/OriginalPath.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.PotentialFits
import Submission.Obl.k4_finite_positive_mixed_cover_realization.Path
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketCoverage
import Submission.Obl.k4_finite_affine_parent_sources.SourceSet
import Submission.Obl.k4_scalar_normalized_exact_refinement.Mass

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set

noncomputable section

namespace OriginalPath

abbrev Data := Submission.Obl.k4_finite_positive_mixed_cover_realization.PathData

/-- Read the same arrays through the accepted affine-parent API. -/
def affineData {W : ℕ} (p : Data W) :
    Submission.Obl.k4_finite_affine_parent_sources.PathData W :=
  ⟨p.r, p.T, p.nw, p.κ, p.C, p.lev, p.par, p.world, p.bin, p.center,
    p.velocity, p.frame, p.test, p.assigned, p.counted, p.lists⟩

/-- The accepted original-path API is exactly the frozen zero-narrowness
path used here, with the original arrays unchanged. -/
theorem valid_iff {W : ℕ} (p : Data W) (Nk L : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Ln) (E : Fin W → Set Ev) (B : Fin W → ℝ)
    (f : ℝ → ℝ) (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ)
    (Mp Dp : ℕ) (σ : ℝ) :
    p.Valid 0 Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ ↔
      path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ
        p.r p.T p.nw p.κ p.C p.lev p.par p.world p.bin p.center p.velocity
        p.frame p.test p.assigned p.counted p.lists := Iff.rfl

abbrev AtLevel {W : ℕ} (p : Data W) (i : ℕ) := {b : Fin p.C // p.lev b = i}

section Path

variable {W m Mp Dp : ℕ} {p : Data W} {Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
    {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid 0 Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem affine_valid : (affineData p).Valid 0 Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ := hp

/-- Every counted event is bounded by its full original assignment and
physical block length. -/
theorem counted_le_reference (b : Fin p.C) :
    ((ν (p.world b)).prod volume) (p.counted b) ≤
      ENNReal.ofReal (PotentialFits.clock (p.T (p.lev b))) *
        ν (p.world b) (p.assigned b) := by
  apply Submission.Obl.k4_scalar_normalized_exact_refinement.selected_mass_le_assignment
    (ν (p.world b)) ((ν (p.world b)).prod volume) le_rfl (p.assigned b) (p.counted b)
    ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
    (PotentialFits.clock (p.T (p.lev b)))
  intro z hz
  have hs := hp.counted_support b z hz
  refine ⟨hs.2.1, hs.2.2.1.1, ?_⟩
  convert hs.2.2.1.2 using 1 <;> simp only [PotentialFits.clock] <;> ring

/-- Positivity is inherited from the accepted counted-mass theorem and
the original assignment bound; no posterior reference is introduced. -/
theorem reference_pos (hNk : 0 < Nk) (b : Fin p.C)
    [IsFiniteMeasure (ν (p.world b))] :
    0 < ENNReal.ofReal (PotentialFits.clock (p.T (p.lev b))) *
      ν (p.world b) (p.assigned b) := by
  letI : IsFiniteMeasure (ν ((affineData p).world b)) := by
    change IsFiniteMeasure (ν (p.world b))
    infer_instance
  have hpos := Submission.Obl.k4_finite_affine_parent_sources.counted_toReal_pos
    (affine_valid hp) hNk b
  change 0 < (((ν (p.world b)).prod volume) (p.counted b)).toReal at hpos
  have hne : ((ν (p.world b)).prod volume) (p.counted b) ≠ 0 := by
    intro h
    simp only [h, ENNReal.toReal_zero, lt_self_iff_false] at hpos
  exact (pos_iff_ne_zero.mpr hne).trans_le (counted_le_reference hp b)

/-- Full original assignments at one level, multiplied by their physical
block length, have total mixture mass at most one. The accepted assignment
budget is used before selecting any residual packet. -/
theorem reference_budget (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1) (i : ℕ) :
    (∑ b : AtLevel p i, ENNReal.ofReal (ω (p.world b.1)) *
      (ENNReal.ofReal (PotentialFits.clock (p.T i)) * ν (p.world b.1) (p.assigned b.1))) ≤ 1 := by
  classical
  let jt : AtLevel p i → Fin (2 ^ p.T i) := fun b =>
    ⟨p.bin b.1, by simpa only [b.2] using hp.label_bin b.1⟩
  have hbudget := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
    ν ω (fun b : AtLevel p i => p.world b.1) jt (fun b => p.assigned b.1)
    hν hω hsum (fun b => by
      rcases hp.chart b.1 with ⟨_, _, _, _, _, _, hA, _⟩
      exact hA)
    (fun b b' hne hw hj => hp.assignment_disjoint b.1 b'.1
      (fun h => hne (Subtype.ext h)) (b.2.trans b'.2.symm) hw (congrArg Fin.val hj))
  simp only [Fintype.card_fin] at hbudget
  calc
    _ = ENNReal.ofReal (PotentialFits.clock (p.T i)) *
        ∑ b : AtLevel p i, ENNReal.ofReal (ω (p.world b.1)) * ν (p.world b.1) (p.assigned b.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ac_rfl
    _ ≤ ENNReal.ofReal (PotentialFits.clock (p.T i)) * ((2 ^ p.T i : ℕ) : ENNReal) :=
      mul_le_mul' le_rfl hbudget
    _ = 1 := by
      have hcast : ((2 ^ p.T i : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ p.T i) := by
        norm_cast
      rw [hcast, PotentialFits.clock, ENNReal.ofReal_inv_of_pos (by positivity)]
      exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

/-- The original ancestor inclusions cover every terminal residual at every
earlier level, before imposing any later analytical conditions. -/
theorem covered_at_level (H : Fin W → Set Ev) (i : ℕ) (hi : i < m)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.world b = w ∧ z ∈ p.counted b}) :
    ∀ w, H w ⊆ {z | ∃ b : AtLevel p i, p.world b.1 = w ∧ z ∈ p.counted b.1} := by
  intro w z hz
  obtain ⟨b, hlast, hw, hb⟩ := hH w hz
  obtain ⟨ha, haw, hsub⟩ := hp.ancestor b i (by omega)
  exact ⟨⟨_, ha⟩, haw.trans hw, hsub hb⟩

/-- A positive terminal residual selects an actual old packet relative to
its full original `clock * prior(assignment)` reference. The selection uses
the accepted original-packet lemma, with no normalized posterior. -/
theorem exists_dense_packet (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1)
    (H : Fin W → Set Ev) (hHm : ∀ w, MeasurableSet (H w))
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.world b = w ∧ z ∈ p.counted b})
    (hmass : ENNReal.ofReal (p.κ⁻¹ / 4) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w))
    (i : ℕ) (hi : i < m) :
    ∃ b : Fin p.C, p.lev b = i ∧ 0 < ω (p.world b) ∧
      ENNReal.ofReal (p.κ⁻¹ / 8) *
        (ENNReal.ofReal (PotentialFits.clock (p.T i)) * ν (p.world b) (p.assigned b)) ≤
          ((ν (p.world b)).prod volume) (H (p.world b) ∩ p.counted b) := by
  classical
  let μ : Fin W → Measure Ev := fun w => ((ν w).prod volume).restrict (H w)
  have hcover w : μ w {z | ∃ b : AtLevel p i, p.world b.1 = w ∧ z ∈ p.counted b.1}ᶜ = 0 := by
    apply measure_mono_null (compl_subset_compl.mpr (covered_at_level hp H i hi hH w))
    simp only [μ, Measure.restrict_apply (hHm w).compl, compl_inter_self, measure_empty]
  have hκpos : 0 < p.κ := zero_lt_one.trans_le hp.one_le_slack
  have hmass' : ENNReal.ofReal (p.κ⁻¹ / 8) < ∑ w, ENNReal.ofReal (ω w) * μ w univ := by
    calc
      _ < ENNReal.ofReal (p.κ⁻¹ / 4) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by
          have : 0 < p.κ⁻¹ := inv_pos.mpr hκpos
          linarith)
      _ ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w) := hmass
      _ = _ := by simp only [μ, Measure.restrict_apply_univ]
  obtain ⟨b, hw, hselected⟩ :=
    Submission.Obl.k4_scalar_grid_cartesian_field.exists_original_packet_with_retained_mass
      μ (fun w => ENNReal.ofReal (ω w)) (fun b : AtLevel p i => p.world b.1)
      (fun b => p.counted b.1)
      (fun b => ENNReal.ofReal (PotentialFits.clock (p.T i)) * ν (p.world b.1) (p.assigned b.1))
      (ENNReal.ofReal (p.κ⁻¹ / 8)) (reference_budget hp hν hω hsum i) hcover hmass'
  refine ⟨b.1, b.2, ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hw), ?_⟩
  have hFm : MeasurableSet (p.counted b.1) := by
    rcases hp.chart b.1 with ⟨_, _, _, _, _, _, _, hF, _⟩
    exact hF
  simpa only [μ, Measure.restrict_apply hFm, inter_comm] using hselected

end Path

end OriginalPath

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
