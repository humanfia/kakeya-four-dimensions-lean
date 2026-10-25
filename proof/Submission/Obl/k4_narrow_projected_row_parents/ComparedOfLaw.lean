import Submission.Obl.k4_narrow_projected_row_parents.CompareMap

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type} [MeasurableSpace α]

theorem measurable_ccode {b : α → Fin 6 → ℝ} (hb : Measurable b) (q χ g m : ℝ) :
    Measurable (fun z : α × ℝ => ccode q χ g m (b z.1) z.2) := by
  unfold ccode
  fun_prop

/-- A dense comparison sublaw with almost-everywhere partner lists gives the
pointwise retained event required by `Compared`. -/
noncomputable def compared_of_ae {a : PreparedModel α} {k : ℕ} {s q χ g m M : ℝ}
    {n : ℕ} (C : Fin n → Set α) (hC : ∀ i, MeasurableSet (C i))
    (ζ : Measure (α × ℝ)) (hζ : ζ ≤ a.rho k) (hmass : ENNReal.ofReal M⁻¹ ≤ ζ univ)
    (lab : α → Fin n) (hlab : Measurable lab)
    (tru : α × ℝ → Fin (a.n k s)) (htru : Measurable tru)
    (hW : ∀ Q, MeasurableSet (a.B k s Q ×ˢ a.block k s Q))
    (hb : Measurable (a.b k))
    (partners : Fin (a.n k s) → (Fin 5 → ℤ) → Finset (Fin n))
    (hcard : ∀ Q code, ((partners Q code).card : ℝ) ≤ M)
    (hcurrent : ∀ᵐ z ∂ζ, z.1 ∈ C (lab z.1) ∧
      z ∈ a.B k s (tru z) ×ˢ a.block k s (tru z) ∧
      lab z.1 ∈ partners (tru z) (ccode q χ g m (a.b k z.1) z.2)) :
    Compared a k s C q χ g m M := by
  classical
  let R : Set (α × ℝ) := {z | z.1 ∈ C (lab z.1) ∧
      z ∈ a.B k s (tru z) ×ˢ a.block k s (tru z) ∧
      lab z.1 ∈ partners (tru z) (ccode q χ g m (a.b k z.1) z.2)}
  have hL : MeasurableSet {z : α × ℝ | z.1 ∈ C (lab z.1)} := by
    have heq : {z : α × ℝ | z.1 ∈ C (lab z.1)} =
        ⋃ i : Fin n, ((C i ×ˢ univ) ∩ {z | lab z.1 = i}) := by
      ext z
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_prod, mem_univ, and_true]
      constructor
      · intro hz; exact ⟨lab z.1, hz, rfl⟩
      · rintro ⟨i, hz, hi⟩; simpa only [hi] using hz
    rw [heq]
    exact MeasurableSet.iUnion fun i => ((hC i).prod MeasurableSet.univ).inter
      (measurableSet_eq_fun (hlab.comp measurable_fst) measurable_const)
  have hT : MeasurableSet {z | z ∈ a.B k s (tru z) ×ˢ a.block k s (tru z)} := by
    have heq : {z | z ∈ a.B k s (tru z) ×ˢ a.block k s (tru z)} =
        ⋃ Q : Fin (a.n k s), ((a.B k s Q ×ˢ a.block k s Q) ∩ {z | tru z = Q}) := by
      ext z
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · intro hz; exact ⟨tru z, hz, rfl⟩
      · rintro ⟨Q, hz, hQ⟩; simpa only [hQ] using hz
    rw [heq]
    exact MeasurableSet.iUnion fun Q => (hW Q).inter
      (measurableSet_eq_fun htru measurable_const)
  have hP : MeasurableSet {z : α × ℝ |
      lab z.1 ∈ partners (tru z) (ccode q χ g m (a.b k z.1) z.2)} := by
    let S : Set (Fin (a.n k s) × (Fin 5 → ℤ) × Fin n) := {x | x.2.2 ∈ partners x.1 x.2.1}
    have hS : MeasurableSet S := (Set.to_countable S).measurableSet
    exact hS.preimage (htru.prodMk ((measurable_ccode hb q χ g m).prodMk (hlab.comp measurable_fst)))
  have hR : MeasurableSet R := hL.inter (hT.inter hP)
  have hReq : ζ R = ζ univ := by
    apply measure_congr
    filter_upwards [hcurrent] with z hz
    exact propext ⟨fun _ => trivial, fun _ => hz⟩
  exact {
    R := R
    measurable_R := hR
    mass := hmass.trans (hReq.symm.le.trans (hζ R))
    lab := lab
    lab_mem := fun z hz => hz.1
    tru := tru
    tru_mem := fun z hz => hz.2.1
    partners := partners
    partners_card := hcard
    partners_mem := fun z hz => hz.2.2 }

end Submission.Obl.k4_narrow_projected_row_parents
