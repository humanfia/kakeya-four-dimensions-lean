-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedMass.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedMass.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedMass.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedAtlas
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path

/-! A successful original residual is covered by the merged finite-format
incidences. Their mass is measured in the original worlds, independently of
the fixed posterior law used to construct the heavy net. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators RealInnerProductSpace

namespace StripRefinement

variable {α : Type} [Fintype α] {W T : ℕ}
  (d : StripRefinement α) (p : α → StripParent W T)

theorem original_residual_covered_by_merged_incidence {N κ depth w : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hr : 0 < d.radius)
    (hn : ∀ b i, ‖d.normal b i‖ = 1) (hbins : κ ≤ (d.bins : ℝ) * d.radius)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcover : ∀ γ, H γ ⊆ {x | ∃ b, (p b).world = γ ∧ x ∈ (p b).incidences ∧
      packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity x.1 ∈
        ⋃ j, affineStrip (d.normal b j) (d.offset b j) w ∧
      ∀ q : StripCodeLabel d.radius (d.normal b) (d.offset b),
        packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity x.1 ∈
          mergedStripCell d.radius (d.normal b) (d.offset b) w q → x ∈ success b q.val}) :
    ∀ γ, H γ ⊆ {x | ∃ a : d.MergedLabel,
      (p a.1).world = γ ∧ x ∈ d.mergedIncidence p w success a} := by
  intro γ x hx
  obtain ⟨b, hγ, hF, hV, hsuccess⟩ := hcover γ hx
  rcases hold b with ⟨_, _, _, _, _, _, _, _, _, hgeo, hinc, _⟩
  have hq : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hmid : (p b).start + ((2 : ℝ) ^ T)⁻¹ / 2 ∈
      Set.Icc (((p b).timeIndex : ℝ) / (2 : ℝ) ^ T)
        ((((p b).timeIndex : ℝ) + 1) / (2 : ℝ) ^ T) := by
    change _ ∈ Set.Icc (p b).start _
    have hend : (((p b).timeIndex : ℝ) + 1) / (2 : ℝ) ^ T =
        (p b).start + ((2 : ℝ) ^ T)⁻¹ := by unfold StripParent.start; ring
    rw [hend]
    constructor <;> linarith
  have hpart := iUnion_mergedStripAssignment (p b).trajectories
    (packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity)
    (fun l => packetPosition (p b).frame (p b).center (p b).velocity l
      ((p b).start + ((2 : ℝ) ^ T)⁻¹ / 2)) (d.normal b) (d.offset b) w hr (hn b)
    (fun l hl => ((hgeo l hl).2.2 _ hmid).1.trans hbins)
  have hA : x.1 ∈ ⋃ q : StripCodeLabel d.radius (d.normal b) (d.offset b) ×
      {z : ℤ // z ∈ stripBinRange d.bins},
      d.mergedAssignment p w ⟨b, q⟩ := by
    dsimp only [mergedAssignment]
    rw [hpart]
    exact ⟨(hinc x hF).2.1, hV⟩
  obtain ⟨q, hA⟩ := Set.mem_iUnion.mp hA
  exact ⟨⟨b, q⟩, hγ, ⟨hF, hA⟩, hsuccess q.1 hA.1.2⟩

theorem weighted_merged_mass_le
    (μ : Fin W → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ω : Fin W → ℝ) (w : ℝ)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcover : ∀ γ, H γ ⊆ {x | ∃ a : d.MergedLabel,
      (p a.1).world = γ ∧ x ∈ d.mergedIncidence p w success a}) :
    (∑ γ, ENNReal.ofReal (ω γ) * μ γ (H γ)) ≤
      ∑ a : d.MergedLabel, ENNReal.ofReal (ω (p a.1).world) *
        μ (p a.1).world (d.mergedIncidence p w success a) := by
  classical
  have h := weighted_residual_mass_le_sum μ ω (fun _a : d.MergedLabel => 0)
    (fun a => (p a.1).world) (d.mergedIncidence p w success) H 0 (fun γ x hx => by
      obtain ⟨a, hγ, ha⟩ := hcover γ hx
      exact ⟨a, rfl, hγ, ha⟩)
  calc
    _ ≤ ∑ a : d.MergedLabel, ENNReal.ofReal (ω (p a.1).world) *
        μ (p a.1).world (H (p a.1).world ∩ d.mergedIncidence p w success a) := by
      simpa only [ite_true] using h
    _ ≤ _ := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (measure_mono inter_subset_right) zero_le)

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
