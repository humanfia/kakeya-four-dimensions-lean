import Submission.Obl.k4_subcritical_chart_projection.Packets
import Submission.Obl.k4_subcritical_chart_projection.LayerDefs

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory
open scoped ENNReal BigOperators
open Submission.Obl.k4_horizontal_supercritical_three_projections
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Restoring the Scalar denominator gives the physical reference at the
requested depth, with exactly the two Scalar losses. -/
theorem restored_reference_identity (π : Measure ℝ) {N χ D s₀ depth d τ : ℝ}
    (hN : 0 < N) (q : Fin 3 → ℤ) :
    chartReference π χ D (N ^ (-s₀)) d q * (N ^ (-(depth - s₀))) ^ d * N ^ (-τ) / N ^ τ =
      chartReference π χ D (N ^ (-depth)) d q / N ^ (2 * τ) := by
  have hs : (N ^ (-s₀)) ^ d * (N ^ (-(depth - s₀))) ^ d = (N ^ (-depth)) ^ d := by
    rw [← Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _),
      ← Real.rpow_add hN]
    congr 2
    ring
  have ht : N ^ (-τ) / N ^ τ = (N ^ (2 * τ))⁻¹ := by
    rw [← Real.rpow_sub hN, ← Real.rpow_neg hN.le]
    congr 1
    ring
  unfold chartReference
  calc
    _ = ((π (Ico ((q 0 : ℝ) * χ) (((q 0 : ℝ) + 1) * χ))).toReal * D ^ 2) *
        ((N ^ (-s₀)) ^ d * (N ^ (-(depth - s₀))) ^ d) * (N ^ (-τ) / N ^ τ) := by ring
    _ = _ := by rw [hs, ht]; ring

/-- Flatten every packet in every retained chart into a single finite
corrected layer, retaining full coverage and every restored floor. -/
theorem layer_of_corrected_chart_packets {α : Type} [MeasurableSpace α]
    {N d κ s₀ M ξ τ : ℝ} (hN : 1 ≤ N) (hτ : 0 ≤ τ)
    (depth : Fin 3 → ℝ) (h : Fin 3)
    (ν : Measure α) [IsFiniteMeasure ν] (ρ ζ : Measure (α × ℝ))
    (π : Measure ℝ) (b : α → Fin 6 → ℝ)
    (C : Charts b ρ π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀))
      (N ^ (-(20 * s₀))) d (N ^ ξ) (N ^ (-ξ))
      (fun h => N ^ (-(depth h - s₀))))
    (S : Finset (Fin C.n))
    (F : (i : S) → ScalarPackets N d (depth h - s₀) (20 * s₀)
      (chartReference π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀)) d (C.q i.val) /
        (ν (C.G i.val)).toReal) τ (chartLaw ν ζ (C.G i.val))
      (fun l => scalarCoefficients (N ^ (-(2 * κ * s₀))) (N ^ (-s₀))
        (C.q i.val 1) (C.q i.val 2) (C.g i.val) (b l)))
    (hν : ∀ i : S, ν (C.G i.val) ≠ 0)
    (hpalette : ∀ i : S, 0 < π (Ico ((C.q i.val 0 : ℝ) * N ^ (-M))
      (((C.q i.val 0 : ℝ) + 1) * N ^ (-M))))
    (hsub : ∀ (i : S) (j : Fin (F i).n), (F i).A j ⊆ C.G i.val)
    (hmass : ENNReal.ofReal (N ^ (-2 * τ)) ≤
      ζ {p | ∃ (i : S) (j : Fin (F i).n), p.1 ∈ (F i).A j}) :
    ∃ L : CorrectedLayer α,
      L.Certified b (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-s₀)) (N ^ ξ)
        (240 * (N ^ τ) ^ 5) (N ^ τ * N ^ (-(depth h - s₀))) ∧
      (∀ i, 0 < π (Ico ((L.q i 0 : ℝ) * N ^ (-M))
        (((L.q i 0 : ℝ) + 1) * N ^ (-M)))) ∧
      (∀ i, ENNReal.ofReal
        (chartReference π (N ^ (-M)) (N ^ (-(2 * κ * s₀))) (N ^ (-depth h)) d (L.q i) /
          N ^ (2 * τ)) ≤ ζ (L.A i ×ˢ Icc (0 : ℝ) 1)) ∧
      ENNReal.ofReal (N ^ (-2 * τ)) ≤ ζ {p | ∃ i, p.1 ∈ L.A i} := by
  classical
  let J := (i : S) × Fin (F i).n
  let e := (Fintype.equivFin J).symm
  let L : CorrectedLayer α := {
    n := Fintype.card J
    A := fun j => (F (e j).1).A (e j).2
    q := fun j => C.q (e j).1.val
    g := fun j => C.g (e j).1.val
    P := fun j => ((F (e j).1).candidate (e j).2).P }
  have hdisj : Pairwise (fun ij ij' : J =>
      Disjoint ((F ij.1).A ij.2) ((F ij'.1).A ij'.2)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    by_cases hi : i = i'
    · subst i'
      exact (F i).disjoint j j' (fun hj => hij (by subst j'; rfl))
    · have hne : i.val ≠ i'.val := fun heq => hi (Subtype.ext heq)
      exact (C.disjoint i.val i'.val hne).mono (hsub i j) (hsub i' j')
  refine ⟨L, ?_, fun j => hpalette (e j).1, ?_, ?_⟩
  · refine {
      measurable := fun j => (F (e j).1).measurable (e j).2
      disjoint := fun j j' hj => hdisj (fun heq => hj (e.injective heq))
      bins := fun j l hl => C.bins (e j).1.val l (hsub _ _ hl)
      norm := fun j => C.norm (e j).1.val
      degree := fun j => ((F (e j).1).candidate (e j).2).degree
      coeff := fun j mon => ((F (e j).1).candidate (e j).2).coeff_bound hN hτ mon
      fit := ?_ }
    intro j l hl t ht
    have hf := (F (e j).1).fit (e j).2 l hl t ht
    simpa only [scalarCoefficients_x, scalarCoefficients_y] using hf
  · intro j
    have hr := ((F (e j).1).restore ν ζ (C.G (e j).1.val) (hν (e j).1) _).1 (e j).2
    rw [restored_reference_identity π (by linarith : 0 < N)] at hr
    exact hr
  · have heq : {p : α × ℝ | ∃ j, p.1 ∈ L.A j} =
        {p | ∃ (i : S) (j : Fin (F i).n), p.1 ∈ (F i).A j} := by
      ext p
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨(e j).1, (e j).2, hj⟩
      · rintro ⟨i, j, hj⟩
        refine ⟨e.symm ⟨i, j⟩, ?_⟩
        change p.1 ∈ (F (e (e.symm ⟨i, j⟩)).1).A (e (e.symm ⟨i, j⟩)).2
        rw [e.apply_symm_apply]
        exact hj
    rw [heq]
    exact hmass

end Submission.Obl.k4_subcritical_chart_projection
