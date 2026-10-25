-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.SetAdapter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.SetInterface
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.StandardGeometry

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

open Set Metric

/-- Adapt the counting formulation of Proposition 8.9 to the finite kernel
used in the AD reduction. Half the epsilon absorbs the constant packing loss. -/
theorem separated_kernel_of_set_statement (h : SeparatedSetStatement) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ θ d : ℝ, 0 < θ ∧ 0 < d ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → SeparatedDichotomyAt δ θ ε := by
  intro ε hε hε1
  let Fr := fun (δ C : ℝ) (X : Set Plane) => X.Finite ∧
    (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧
    ∀ (x : Plane) (r : ℝ), δ ≤ r →
      ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard
  obtain ⟨θ, d, hθ, hd, H⟩ := h Fr rfl (ε / 2) (by positivity)
  obtain ⟨s, hs, hs1, hsmall⟩ :=
    exists_monomial_bound 25 (a := ε - 1) (b := ε / 2 - 1) (by linarith)
  refine ⟨θ, min d s, hθ, lt_min hd hs, ?_⟩
  intro δ hδ hδsmall S T U hSn hTn hUn hSs hTs hUs hSF hTF hUF hgeom K hKne hKsub hKden
  have hδs := hδsmall.trans (min_le_right d s)
  have hδ1 := hδs.trans hs1
  have hFr (V : Finset Plane) (hn : ∀ x ∈ V, ‖x‖ ≤ 4)
      (hs : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → δ ≤ dist x y)
      (hF : ClosedFiniteFrostman δ (δ ^ (-θ)) V) : Fr δ (δ ^ (-θ)) ↑V := by
    refine ⟨V.finite_toSet, fun x hx => ⟨hn x hx, fun y hy hxy => hs x hx y hy hxy⟩, ?_⟩
    simpa only [ClosedFiniteFrostman, Set.ncard_coe_finset] using hF
  obtain ⟨hA, hB, hC, hBC⟩ := hgeom.separated_small_sets
  have hKset : (↑K : Set Triple) ⊆ (↑S : Set Plane) ×ˢ ((↑T : Set Plane) ×ˢ (↑U : Set Plane)) := by
    intro p hp
    simpa only [Set.mem_prod, Finset.mem_coe, Finset.mem_product] using hKsub hp
  have hKD : δ ^ θ * (↑S : Set Plane).ncard * (↑T : Set Plane).ncard *
      (↑U : Set Plane).ncard ≤ ((↑K : Set Triple).ncard : ℝ) := by
    simpa only [Set.ncard_coe_finset] using hKden
  rcases H δ hδ (hδsmall.trans (min_le_left _ _)) ↑S ↑T ↑U ↑K
      (hFr S hSn hSs hSF) (hFr T hTn hTs hTF) (hFr U hUn hUs hUF)
      hA hB hC hBC hKset hKne hKD with hl | hg
  · left
    exact lineConclusion_of_strip_counts hδ S.finite_toSet T.finite_toSet hSs hTs
      (hsmall δ hδ hδs) hl
  · right
    have hgain : ProjectionGain δ θ (ε / 2) (↑K : Set Triple) := hg
    exact hgain.mono_epsilon hδ hδ1 hθ.le (by linarith)

/-- Complete final reduction in the exact interface chosen for the split. -/
theorem ad_dichotomy_from_set_statement (h : SeparatedSetStatement) :
    ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ F G : Set Plane,
        InUnitSquare F → InUnitSquare G → AD δ (δ ^ (-η)) F → AD δ (δ ^ (-η)) G →
          LineConclusion δ ε F G ∨ ProjectionConclusion δ η ε F G :=
  reduce_to_separated_dichotomy (separated_kernel_of_set_statement h)

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
