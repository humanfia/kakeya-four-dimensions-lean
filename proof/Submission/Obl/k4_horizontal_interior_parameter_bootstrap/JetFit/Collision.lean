import Mathlib

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# Collision counting

* `collision_lower`: if the values of a bin map on `W` lie in `B`, then
  `ν(W)² ≤ |B| · (ν ⊗ ν){(l,l') ∈ W×W : same bin}` (Cauchy–Schwarz over the bins);
* `collision_eq_sum`: the collision measure is the sum of the squared bin masses.
-/

open MeasureTheory

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*}

/-- The collision set of a bin map on `W`. -/
def collSet (W : Set Ω) (f : Ω → ℤ) : Set (Ω × Ω) := {p | p.1 ∈ W ∧ p.2 ∈ W ∧ f p.1 = f p.2}

theorem collSet_eq_biUnion (W : Set Ω) (f : Ω → ℤ) (B : Finset ℤ) (hB : ∀ l ∈ W, f l ∈ B) :
    collSet W f = ⋃ b ∈ B, (W ∩ f ⁻¹' {b}) ×ˢ (W ∩ f ⁻¹' {b}) := by
  ext ⟨l, l'⟩
  simp only [collSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
  constructor
  · rintro ⟨hl, hl', hf⟩
    exact ⟨f l, hB l hl, ⟨hl, rfl⟩, ⟨hl', hf.symm⟩⟩
  · rintro ⟨b, -, ⟨hl, hb⟩, ⟨hl', hb'⟩⟩
    exact ⟨hl, hl', hb.trans hb'.symm⟩

variable [MeasurableSpace Ω]

theorem measurableSet_collSet {W : Set Ω} (hW : MeasurableSet W) {f : Ω → ℤ} (hf : Measurable f) :
    MeasurableSet (collSet W f) := by
  have h1 : MeasurableSet {p : Ω × Ω | p.1 ∈ W} := measurable_fst hW
  have h2 : MeasurableSet {p : Ω × Ω | p.2 ∈ W} := measurable_snd hW
  have h3 : MeasurableSet {p : Ω × Ω | f p.1 = f p.2} :=
    measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd)
  exact h1.inter (h2.inter h3)

theorem collision_eq_sum (ν : Measure Ω) [SFinite ν] {W : Set Ω} (hW : MeasurableSet W)
    {f : Ω → ℤ} (hf : Measurable f) (B : Finset ℤ) (hB : ∀ l ∈ W, f l ∈ B) :
    (ν.prod ν) (collSet W f) = ∑ b ∈ B, ν (W ∩ f ⁻¹' {b}) ^ 2 := by
  rw [collSet_eq_biUnion W f B hB, measure_biUnion_finset]
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Measure.prod_prod, sq]
  · intro b _ b' _ hbb'
    refine Set.disjoint_left.2 ?_
    rintro ⟨l, l'⟩ ⟨⟨_, hb⟩, _⟩ ⟨⟨_, hb'⟩, _⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb hb'
    exact hbb' (hb.symm.trans hb')
  · intro b _
    exact (hW.inter (hf (measurableSet_singleton b))).prod (hW.inter (hf (measurableSet_singleton b)))

theorem measure_eq_sum_bins (ν : Measure Ω) {W : Set Ω} (hW : MeasurableSet W)
    {f : Ω → ℤ} (hf : Measurable f) (B : Finset ℤ) (hB : ∀ l ∈ W, f l ∈ B) :
    ν W = ∑ b ∈ B, ν (W ∩ f ⁻¹' {b}) := by
  have hW' : W = ⋃ b ∈ B, W ∩ f ⁻¹' {b} := by
    ext l
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop]
    exact ⟨fun hl => ⟨f l, hB l hl, hl, rfl⟩, fun ⟨_, _, hl, _⟩ => hl⟩
  conv_lhs => rw [hW']
  rw [measure_biUnion_finset]
  · intro b _ b' _ hbb'
    refine Set.disjoint_left.2 ?_
    rintro l ⟨_, hb⟩ ⟨_, hb'⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb hb'
    exact hbb' (hb.symm.trans hb')
  · intro b _
    exact hW.inter (hf (measurableSet_singleton b))

/-- Cauchy–Schwarz over the bins: `ν(W)² ≤ |B| · (ν ⊗ ν)(collisions)`. -/
theorem collision_lower (ν : Measure Ω) [IsFiniteMeasure ν] {W : Set Ω} (hW : MeasurableSet W)
    {f : Ω → ℤ} (hf : Measurable f) (B : Finset ℤ) (hB : ∀ l ∈ W, f l ∈ B) :
    ν W ^ 2 ≤ (B.card : ENNReal) * (ν.prod ν) (collSet W f) := by
  rw [collision_eq_sum ν hW hf B hB, measure_eq_sum_bins ν hW hf B hB]
  have hfin : ∀ b ∈ B, ν (W ∩ f ⁻¹' {b}) ≠ ⊤ := fun b _ => measure_ne_top ν _
  -- work in `ℝ≥0`
  set g : ℤ → NNReal := fun b => (ν (W ∩ f ⁻¹' {b})).toNNReal with hg
  have hcoe : ∀ b ∈ B, ν (W ∩ f ⁻¹' {b}) = (g b : ENNReal) := fun b hb => by
    simp [hg, ENNReal.coe_toNNReal (hfin b hb)]
  have e1 : ∑ b ∈ B, ν (W ∩ f ⁻¹' {b}) = ∑ b ∈ B, (g b : ENNReal) := Finset.sum_congr rfl hcoe
  have e2 : ∑ b ∈ B, ν (W ∩ f ⁻¹' {b}) ^ 2 = ∑ b ∈ B, (g b : ENNReal) ^ 2 :=
    Finset.sum_congr rfl (fun b hb => by rw [hcoe b hb])
  rw [e1, e2]
  have key := sq_sum_le_card_mul_sum_sq (s := B) (f := g)
  have := ENNReal.coe_le_coe.2 key
  push_cast at this
  exact this

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
