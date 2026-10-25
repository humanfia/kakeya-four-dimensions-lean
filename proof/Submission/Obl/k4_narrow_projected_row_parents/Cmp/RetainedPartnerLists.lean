/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/RetainedPartnerLists.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.OriginalGraphTube
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.StoredSheetLists

/-! Forward and reverse lists on the ball where comparison gives uniform agreement. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal Classical

noncomputable section

def QuarterListBound {n₁ n₂ : ℕ} (a L d : ℝ)
    (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) : Prop :=
  ∀ R : ℝ, a ≤ R →
    (∀ i, ((Finset.univ.filter fun j : Fin n₂ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
      ‖f₂ j (emb x) - f₁ i (emb x)‖ ≤ R).card : ℝ) ≤ L * (R / a) ^ d) ∧
    (∀ j, ((Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
      ‖f₁ i (emb x) - f₂ j (emb x)‖ ≤ R).card : ℝ) ≤ L * (R / a) ^ d)

/-- Stored original witnesses also count sheets on the quarter ball. The source
lies in the eighth ball almost everywhere; its null complement is removed only
from the witnesses used in the counting proof, preserving every stored floor. -/
theorem stored_quarter_sheet_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (mesh : ComparisonMesh μ)
    {n : ℕ} (W : Fin n → Set Ω) (hW : ∀ i, MeasurableSet (W i))
    (hdisj : Pairwise (fun i j => Disjoint (W i) (W j)))
    (signal : Ω → ℝ) (hs : Measurable signal)
    (f : Fin n → EuclideanSpace ℝ (Fin 3) → ℂ)
    (ref : EuclideanSpace ℝ (Fin 3) → ℂ) (K : NNReal)
    (href : LipschitzOnWith K ref (closedBall 0 (1 / 2)))
    {a R B F T d : ℝ} (ha : 0 < a) (hR : a ≤ R) (hB : 0 < B)
    (hF : 0 < F) (hT : 0 < T) (palette : ℝ≥0∞) (hp : palette ≠ 0) (hpt : palette ≠ ⊤)
    (hresolve : (K : ℝ) * mesh.diameter ≤ R)
    (hvolume : (∑ _q : Fin mesh.n, mesh.vol) ≤ 1)
    (hfloor : ∀ i, ENNReal.ofReal (T / F) * palette ≤ μ (W i))
    (hfit : ∀ i p, p ∈ W i → ‖(signal p : ℂ) - f i (mesh.base p)‖ ≤ a)
    (hnative : ∀ q j, μ {p | mesh.code p = q ∧ ⌊signal p / R⌋ = j} ≤
      (ENNReal.ofReal (B * T * (R / a) ^ d) * palette) * mesh.vol) :
    ((Finset.univ.filter fun i : Fin n => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
      ‖f i x - ref x‖ ≤ R).card : ℝ) ≤ (14 * B) * F * (R / a) ^ d := by
  let E : Set Ω := {p | ‖mesh.base p‖ ≤ 1 / 8}
  have hE : MeasurableSet E := measurableSet_le mesh.measurable_base.norm measurable_const
  have hEa : ∀ᵐ p ∂μ, p ∈ E := mesh.original.mono fun p hp => hp.1
  let W' : Fin n → Set Ω := fun i => W i ∩ E
  have hmass (i : Fin n) : μ (W' i) = μ (W i) := by
    apply measure_congr
    filter_upwards [hEa] with p hp
    simp only [W', mem_inter_iff, hp, and_true]
  have hfloor' (i : Fin n) : ENNReal.ofReal (T / F) * palette ≤ μ (W' i) := by
    rw [hmass]
    exact hfloor i
  have hfit' (i : Fin n) (p : Ω) (hpw : p ∈ W' i) :
      ‖mesh.base p‖ ≤ (1 : ℝ) / 4 ∧ ‖(signal p : ℂ) - f i (mesh.base p)‖ ≤ a :=
    ⟨hpw.2.trans (by norm_num), hfit i p hpw.1⟩
  have htube := original_graph_tube_cap μ mesh signal hs ref K href (ha.trans_le hR)
    hresolve hvolume (ENNReal.ofReal (B * T * (R / a) ^ d) * palette) hnative
  have hcap : μ {p | ‖mesh.base p‖ ≤ 1 / 4 ∧ ‖(signal p : ℂ) - ref (mesh.base p)‖ ≤ 2 * R} ≤
      ENNReal.ofReal ((14 * B) * T * (R / a) ^ d) * palette := by
    have hsub : {p | ‖mesh.base p‖ ≤ 1 / 4 ∧ ‖(signal p : ℂ) - ref (mesh.base p)‖ ≤ 2 * R} ⊆
        {p | ‖mesh.base p‖ ≤ 1 / 2 ∧ ‖(signal p : ℂ) - ref (mesh.base p)‖ ≤ 2 * R} :=
      fun p hp => ⟨hp.1.trans (by norm_num), hp.2⟩
    refine (measure_mono hsub).trans (htube.trans_eq ?_)
    rw [← ENNReal.ofReal_ofNat 14, ← mul_assoc,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 14)]
    congr 2
    ring
  exact stored_sheet_list_count μ W'
    (fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left)
    (fun i => (hW i).inter hE) mesh.base (fun p => (signal p : ℂ)) f ref
    ha hR hF (by positivity) hT palette hp hpt hfloor' hfit' hcap

/-- A retained incidence relation with uniform quarter-ball agreement has both
forward and reverse partner bounds from the corresponding original sheet lists. -/
theorem retained_partner_list_bounds {Ω : Type*} {n₁ n₂ : ℕ}
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂) (G : Set Ω)
    (f₁ : Fin n₁ → EuclideanSpace ℝ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℝ (Fin 3) → ℂ) {M B : ℝ}
    (hagreement : ∀ p ∈ G, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
      ‖f₁ (i₁ p) x - f₂ (i₂ p) x‖ ≤ M)
    (hforward : ∀ i, ((Finset.univ.filter fun j : Fin n₂ =>
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 → ‖f₂ j x - f₁ i x‖ ≤ M).card : ℝ) ≤ B)
    (hreverse : ∀ j, ((Finset.univ.filter fun i : Fin n₁ =>
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 → ‖f₁ i x - f₂ j x‖ ≤ M).card : ℝ) ≤ B) :
    (∀ i, ((Finset.univ.filter fun j : Fin n₂ => ∃ p ∈ G, i₁ p = i ∧ i₂ p = j).card : ℝ) ≤ B) ∧
    (∀ j, ((Finset.univ.filter fun i : Fin n₁ => ∃ p ∈ G, i₁ p = i ∧ i₂ p = j).card : ℝ) ≤ B) := by
  constructor
  · intro i
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hforward i)
    intro j hj
    obtain ⟨p, hp, h₁, h₂⟩ := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro x hx
    have h := hagreement p hp x hx
    rw [h₁, h₂, norm_sub_rev] at h
    exact h
  · intro j
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hreverse j)
    intro i hi
    obtain ⟨p, hp, h₁, h₂⟩ := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro x hx
    simpa only [h₁, h₂] using hagreement p hp x hx

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
