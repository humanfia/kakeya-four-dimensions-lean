/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- An almost-everywhere conditional failure cap bounds the failure
probability of the corresponding actual full-history trajectory step. -/
theorem trajectory_bad_step_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Ω) Ω)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ)
    (R : Set ((((i : Finset.Iic n) → Ω)) × Ω)) (hR : MeasurableSet R)
    (ε : ENNReal)
    (hbad : ∀ᵐ h ∂(Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map (Preorder.frestrictLe n),
      κ n h (Prod.mk h ⁻¹' Rᶜ) ≤ ε) :
    (Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ)
      {x | (Preorder.frestrictLe n x, x (n + 1)) ∉ R} ≤ ε := by
  have hp : Measurable (fun x : ℕ → Ω => (Preorder.frestrictLe n x, x (n + 1))) := by fun_prop
  calc
    _ = ((Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map
        (fun x => (Preorder.frestrictLe n x, x (n + 1)))) Rᶜ :=
      (Measure.map_apply hp hR.compl).symm
    _ = (((Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map
        (Preorder.frestrictLe n)) ⊗ₘ κ n) Rᶜ := by
      rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ : ℕ => Ω)]
    _ = ∫⁻ h, κ n h (Prod.mk h ⁻¹' Rᶜ)
        ∂(Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map (Preorder.frestrictLe n) :=
      Measure.compProd_apply hR.compl
    _ ≤ ∫⁻ _ : ((i : Finset.Iic n) → Ω), ε
        ∂(Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map (Preorder.frestrictLe n) :=
      lintegral_mono_ae hbad
    _ = ε := by simp

/-- Initial and conditional full-past failure budgets leave an explicit
mass of successful paths. The transition events may depend on every earlier
state; no independence or post-success conditioning is required. -/
theorem trajectory_good_steps_mass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Ω) Ω)
    [∀ n, IsMarkovKernel (κ n)] (N : ℕ) (G : Set Ω)
    (R : (n : ℕ) → Set ((((i : Finset.Iic n) → Ω)) × Ω))
    (hR : ∀ n, MeasurableSet (R n)) (ε : Fin N → ENNReal)
    (hbad : ∀ k : Fin N, ∀ᵐ h ∂(Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ).map
        (Preorder.frestrictLe (k : ℕ)),
      κ k h (Prod.mk h ⁻¹' (R k)ᶜ) ≤ ε k) :
    (1 : ENNReal) ≤ (Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ)
        {x | x 0 ∈ G ∧ ∀ k : Fin N, (Preorder.frestrictLe (k : ℕ) x, x (k + 1)) ∈ R k} +
      (Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ) {x | x 0 ∉ G} + ∑ k, ε k := by
  classical
  let Q := Kernel.trajMeasure (X := fun _ : ℕ => Ω) P κ
  let good := {x : ℕ → Ω | x 0 ∈ G ∧
    ∀ k : Fin N, (Preorder.frestrictLe (k : ℕ) x, x (k + 1)) ∈ R k}
  let bad (k : Fin N) := {x : ℕ → Ω |
    (Preorder.frestrictLe (k : ℕ) x, x (k + 1)) ∉ R k}
  have hb : ∀ k : Fin N, Q (bad k) ≤ ε k := fun k =>
    trajectory_bad_step_mass_le P κ k (R k) (hR k) (ε k) (hbad k)
  have hsum : Q (⋃ k : Fin N, bad k) ≤ ∑ k, ε k :=
    (measure_iUnion_fintype_le Q bad).trans (Finset.sum_le_sum (fun k _ => hb k))
  have hcover : (univ : Set (ℕ → Ω)) ⊆ good ∪ ({x | x 0 ∉ G} ∪ ⋃ k : Fin N, bad k) := by
    intro x _
    by_cases h0 : x 0 ∈ G
    · by_cases hs : ∀ k : Fin N, (Preorder.frestrictLe (k : ℕ) x, x (k + 1)) ∈ R k
      · exact Or.inl ⟨h0, hs⟩
      · obtain ⟨k, hk⟩ := not_forall.mp hs
        exact Or.inr (Or.inr (mem_iUnion.mpr ⟨k,hk⟩))
    · exact Or.inr (Or.inl h0)
  calc
    _ = Q univ := by simp [Q]
    _ ≤ Q (good ∪ ({x | x 0 ∉ G} ∪ ⋃ k : Fin N, bad k)) := measure_mono hcover
    _ ≤ Q good + Q ({x | x 0 ∉ G} ∪ ⋃ k : Fin N, bad k) := measure_union_le _ _
    _ ≤ Q good + (Q {x | x 0 ∉ G} + Q (⋃ k : Fin N, bad k)) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ ≤ Q good + (Q {x | x 0 ∉ G} + ∑ k, ε k) :=
      add_le_add le_rfl (add_le_add le_rfl hsum)
    _ = _ := by rw [add_assoc]

end Submission.Lib.K4PolynomialNorming

