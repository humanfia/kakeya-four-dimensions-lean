import Submission.Obl.k4_horizontal_strict_parameter_step.CandidateLayer
import Submission.Obl.k4_horizontal_strict_parameter_step.FloorFamilies
import Submission.Obl.k4_horizontal_strict_parameter_step.Interface

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/CandidateFloors.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- Restoring floors is a finite-measure operation after the analytic chart calls.
Its only numerical requirement is that the total floor cost fits below the retained mass. -/
theorem CandidateLayer.restore_floors {α : Type} [MeasurableSpace α]
    {N : ℕ → ℝ} {d e₀ ε D a M m Q : ℝ} {k : ℕ}
    {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ} {ρ : Measure (α × ℝ)}
    (H : CandidateLayer α ρ (π k) (b k) d (N k ^ (-e₀)) D a M m Q)
    (hN : 0 < N k) (ha : 0 ≤ a) (hQ : 0 ≤ Q) (hm : 0 < m)
    (hM : M ≤ N k ^ ε) (hfit : 2 ≤ N k ^ ε)
    (hgap : N k ^ (-ε) + N k ^ (-ε) * Q < m) :
    ∃ (σ : Measure (α × ℝ)) (n : ℕ) (A : Fin n → Set α)
      (q : Fin n → Fin 3 → ℤ) (h : Fin n → Fin 6 → ℝ),
      σ ≤ ρ ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ σ univ ∧
        LayerAt N d e₀ π b k ε σ D a n A q h := by
  classical
  let U : Set α := ⋃ i, H.A i
  let V : Set (α × ℝ) := U ×ˢ Icc (0 : ℝ) 1
  let μ := ρ.restrict V
  let E : Fin H.n → Set (α × ℝ) := fun i => H.A i ×ˢ Icc (0 : ℝ) 1
  let W : Fin H.n → ENNReal := fun i => ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) *
    π k (Ico ((H.q i 0 : ℝ) * N k ^ (-e₀)) (((H.q i 0 : ℝ) + 1) * N k ^ (-e₀)))
  have hU : MeasurableSet U := MeasurableSet.iUnion H.measurable
  have hV : MeasurableSet V := hU.prod measurableSet_Icc
  have hE : ∀ i, MeasurableSet (E i) := fun i => (H.measurable i).prod measurableSet_Icc
  have hEV : {p | ∃ i, p ∈ E i} = V := by ext p; simp [E, V, U]
  have hcover : μ {p | ∃ i, p ∈ E i}ᶜ = 0 := by
    change ρ.restrict V {p | ∃ i, p ∈ E i}ᶜ = 0
    rw [hEV, Measure.restrict_apply hV.compl, compl_inter_self, measure_empty]
  have hmass : ENNReal.ofReal m ≤ μ univ := by
    rw [show μ univ = ρ V from Measure.restrict_apply_univ V]
    exact H.mass
  have hfactor (i : Fin H.n) : W i = ENNReal.ofReal (N k ^ (-ε)) *
      (ENNReal.ofReal (D ^ 2 * a ^ d) *
        π k (Ico ((H.q i 0 : ℝ) * N k ^ (-e₀)) (((H.q i 0 : ℝ) + 1) * N k ^ (-e₀)))) := by
    have heq : D ^ 2 * a ^ d / N k ^ ε = N k ^ (-ε) * (D ^ 2 * a ^ d) := by
      rw [Real.rpow_neg hN.le, div_eq_mul_inv]
      ring
    dsimp only [W]
    rw [heq, ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), mul_assoc]
  have hbudget : (∑ i, W i) ≤ ENNReal.ofReal (N k ^ (-ε) * Q) := by
    simp_rw [hfactor]
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left H.budget zero_le).trans_eq
      (ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)).symm
  have hreserve : ENNReal.ofReal (N k ^ (-ε)) + ∑ i, W i < μ univ := by
    calc
      _ ≤ ENNReal.ofReal (N k ^ (-ε)) + ENNReal.ofReal (N k ^ (-ε) * Q) := add_le_add le_rfl hbudget
      _ = ENNReal.ofReal (N k ^ (-ε) + N k ^ (-ε) * Q) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg hN.le _) (by positivity)).symm
      _ < ENNReal.ofReal m := (ENNReal.ofReal_lt_ofReal_iff hm).mpr hgap
      _ ≤ μ univ := hmass
  obtain ⟨σ, n, e, hσ, hσmass, hfloors, hσcover⟩ :=
    exists_common_floored_families (J := Unit) (ι := fun _ => Fin H.n) μ
      (fun _ i => E i) (fun _ i => hE i) (fun _ i => W i)
      (ENNReal.ofReal (N k ^ (-ε))) (fun _ => hcover) (by simpa using hreserve)
  refine ⟨σ, n (), (fun i => H.A (e () i)), (fun i => H.q (e () i)),
    (fun i => H.h (e () i)), hσ.trans Measure.restrict_le_self, hσmass, ?_⟩
  refine ⟨(fun i => H.measurable _), (fun i j hij => H.disjoint _ _ ((e ()).injective.ne hij)), ?_, ?_⟩
  · intro i
    refine ⟨H.grid (e () i), ?_, ?_, (hfloors () i).2⟩
    · intro t ht p hp q hq
      exact (H.norm (e () i) t ht p hp q hq).trans hM
    · intro l hl t ht
      have hh := H.fit (e () i) l hl t ht
      exact hh.trans (mul_le_mul_of_nonneg_right hfit ha)
  · apply measure_mono_null (μ := σ) (t := {p | ∃ i, p ∈ E (e () i)}ᶜ) ?_ (hσcover ())
    intro p hp he
    obtain ⟨i, hi⟩ := he
    exact hp ⟨i, hi.1⟩

end

end Submission.Obl.k4_horizontal_strict_parameter_step
