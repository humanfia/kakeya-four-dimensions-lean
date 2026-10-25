-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/JetLabels.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/JetLabels.lean (namespace renamed).

import Submission.Lib.K4QuadraticSheets.JetBins
import Submission.Lib.K4IncidenceWitnesses
import Submission.Lib.K4MeshListRecovery.PosteriorLists

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Finset MeasureTheory

section Bins

variable {ι α : Type*} [Fintype ι]

/-- A finite vector of real jets quantized at coordinate-dependent widths. -/
noncomputable def binVector (width : ι → ℝ) (jet : α → ι → ℝ) (a : α) : ι → ℤ :=
  fun i => ⌊jet a i / width i⌋

/-- Equal labels control every recorded jet. -/
theorem jet_gap_of_binVector_eq {width : ι → ℝ} (hw : ∀ i, 0 < width i)
    {jet : α → ι → ℝ} {a b : α} (h : binVector width jet a = binVector width jet b) (i : ι) :
    |jet a i - jet b i| < width i :=
  Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq (hw i) (congrFun h i)

/-- A finite-jet lower norm comparison passes to all members of one label. -/
theorem gap_le_of_binVector_eq {width : ι → ℝ} (hw : ∀ i, 0 < width i)
    {jet : α → ι → ℝ} {a b : α} (h : binVector width jet a = binVector width jet b)
    {c gap : ℝ} (hc : 0 < c) (hcompare : c * gap ≤ ∑ i, |jet a i - jet b i|) :
    gap ≤ (∑ i, width i) / c := by
  apply (le_div_iff₀ hc).mpr
  rw [mul_comm]
  exact hcompare.trans (sum_le_sum fun i _ => (jet_gap_of_binVector_eq hw h i).le)

/-- Close jet vectors lie in neighboring integer bins. -/
theorem binVector_near {width : ι → ℝ} (hw : ∀ i, 0 < width i)
    {jet : α → ι → ℝ} {a b : α} (h : ∀ i, |jet a i - jet b i| ≤ width i) :
    ∀ i, |binVector width jet a i - binVector width jet b i| ≤ 1 := by
  intro i
  exact Submission.Lib.K4QuadraticSheets.floor_sub_le_one_of_abs_le (hw i) (h i)

end Bins

section FiniteLabels

variable {ι α : Type*} [Fintype ι] [Fintype α]

/-- Only the finitely many labels actually occurring in the candidate family are kept. -/
noncomputable def binLabels (width : ι → ℝ) (jet : α → ι → ℝ) : Finset (ι → ℤ) := by
  classical
  exact univ.image (binVector width jet)

noncomputable def mergedLabel (width : ι → ℝ) (jet : α → ι → ℝ) (a : α) :
    binLabels width jet := by
  classical
  exact ⟨binVector width jet a, mem_image.mpr ⟨a, mem_univ a, rfl⟩⟩

/-- A representative is chosen for a merged jet label, rather than retaining its raw
candidate index as part of the output label. -/
noncomputable def binRepresentative (width : ι → ℝ) (jet : α → ι → ℝ)
    (b : binLabels width jet) : α := by
  classical
  exact Classical.choose (mem_image.mp b.property)

theorem binRepresentative_spec (width : ι → ℝ) (jet : α → ι → ℝ)
    (b : binLabels width jet) : binVector width jet (binRepresentative width jet b) = b.val := by
  classical
  exact (Classical.choose_spec (mem_image.mp b.property)).2

theorem same_label_as_representative (width : ι → ℝ) (jet : α → ι → ℝ) (a : α) :
    binVector width jet a =
      binVector width jet (binRepresentative width jet (mergedLabel width jet a)) := by
  rw [binRepresentative_spec]
  rfl

end FiniteLabels

section Neighbors

variable {ι : Type*} [Fintype ι]

/-- Neighbor labels in an arbitrary finite set of realized integer vectors. -/
noncomputable def neighboringLabels (s : Finset (ι → ℤ)) (b : s) : Finset s := by
  classical
  exact univ.filter fun a => ∀ i, |a.val i - b.val i| ≤ 1

theorem card_neighboringLabels (s : Finset (ι → ℤ)) (b : s) :
    (neighboringLabels s b).card ≤ 7 ^ Fintype.card ι := by
  classical
  let P : Finset (ι → ℤ) := (neighboringLabels s b).image Subtype.val
  have hdiam (p : ι → ℤ) (hp : p ∈ P) (q : ι → ℤ) (hq : q ∈ P) (i : ι) :
      |(p i : ℝ) - (q i : ℝ)| ≤ 2 := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
    obtain ⟨a', ha', rfl⟩ := mem_image.mp hq
    have hh := (mem_filter.mp ha).2 i
    have hh' := (mem_filter.mp ha').2 i
    have h₁ : |(a.val i : ℝ) - (b.val i : ℝ)| ≤ 1 := by exact_mod_cast hh
    have h₂ : |(a'.val i : ℝ) - (b.val i : ℝ)| ≤ 1 := by exact_mod_cast hh'
    calc
      _ ≤ |(a.val i : ℝ) - (b.val i : ℝ)| + |(b.val i : ℝ) - (a'.val i : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ 2 := by rw [abs_sub_comm (b.val i : ℝ)]; linarith
  have hc := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter P
    (by norm_num : (0 : ℝ) ≤ 2) hdiam
  have hcard : P.card = (neighboringLabels s b).card :=
    card_image_of_injective _ Subtype.val_injective
  rw [hcard] at hc
  norm_num at hc
  exact_mod_cast hc

/-- Measurable posterior maximization gives a uniformly bounded list of merged labels,
preserving the full unnormalized mass of neighboring-pair agreement. -/
theorem recover_merged_neighbor_mass {X : Type*} [MeasurableSpace X]
    (s : Finset (ι → ℤ)) (μ : Measure X) (p : X → s → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a))
    (hpint : ∀ a, Integrable (fun x => p x a) μ) (hpnonneg : ∀ x a, 0 ≤ p x a)
    (mass : ℝ) (hpair : mass ≤ ∫ x,
      (∑ b, p x b * ∑ a ∈ neighboringLabels s b, p x a) / (∑ a, p x a) ∂μ) :
    ∃ L : X → Finset s, Submission.Lib.K4OriginalLists.MeasurableLists L ∧
      (∀ x, (L x).card ≤ 7 ^ Fintype.card ι) ∧
      mass ≤ ∫ x, ∑ a ∈ L x, p x a ∂μ := by
  obtain ⟨L, hm, hcard, hmass⟩ :=
    Submission.Lib.K4MeshListRecovery.recover_neighbor_density_mass μ p hpmeas hpint hpnonneg
      univ (7 ^ Fintype.card ι) (neighboringLabels s)
      (fun b => ⟨subset_univ _, card_neighboringLabels s b⟩) mass hpair
  exact ⟨L, hm, fun x => (hcard x).2, hmass⟩

end Neighbors

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
