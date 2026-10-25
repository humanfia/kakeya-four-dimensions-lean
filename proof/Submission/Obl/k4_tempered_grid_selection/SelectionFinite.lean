import Mathlib

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set
open scoped ENNReal

/-- A bounded real interval admits a finite quantizer at every positive accuracy.
No regularity of the quantizer is required: it will be applied to countable labels. -/
theorem exists_interval_quantizer (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ (c : Fin n → ℝ) (q : ℝ → Fin n),
      (∀ i, |c i| ≤ C) ∧ ∀ x, |x| ≤ C → |x - c (q x)| < δ := by
  classical
  obtain ⟨s, hs, hfin, hcover⟩ :=
    (isCompact_Icc : IsCompact (Icc (-C) C)).finite_cover_balls hδ
  have hzero : (0 : ℝ) ∈ Icc (-C) C := ⟨by linarith, hC⟩
  have hex (x : ℝ) (hx : |x| ≤ C) : ∃ y : s, |x - y.1| < δ := by
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (abs_le.mp hx))
    exact ⟨⟨y, hy⟩, by simpa only [Metric.mem_ball, Real.dist_eq] using hxy⟩
  have hne : Nonempty s := by
    obtain ⟨y, _⟩ := hex 0 (by simpa using hC)
    exact ⟨y⟩
  letI : Fintype s := hfin.fintype
  letI : Nonempty s := hne
  have hchoice (x : ℝ) : ∃ y : s, |x| ≤ C → |x - y.1| < δ := by
    by_cases hx : |x| ≤ C
    · obtain ⟨y, hy⟩ := hex x hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨Classical.arbitrary s, fun h => (hx h).elim⟩
  choose q hq using hchoice
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, Fintype.card_pos, (fun i => (e.symm i).1),
    (fun x => e (q x)), ?_, ?_⟩
  · intro i
    exact abs_le.mpr (hs (e.symm i).2)
  · intro x hx
    simpa only [Equiv.symm_apply_apply] using hq x hx

/-- A heaviest finite type of a bounded family retains at least the reciprocal
of a constant number of classes. The constant is independent of the functions,
measure, label map, and resolution. -/
theorem finite_type_selection (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) (m : ℕ) :
    ∃ B : ℕ, 0 < B ∧ ∀ (Ω Λ : Type*) [MeasurableSpace Ω]
      (μ : Measure Ω) (label : Ω → Λ) (f : ℕ → Λ → ℝ),
      (∀ j z, |f j z| ≤ C) →
      ∃ (T : Set Λ) (a : ℕ → ℝ),
        (∀ j, |a j| ≤ C) ∧
        (∀ z ∈ T, ∀ j < m, |f j z - a j| < δ) ∧
        μ univ ≤ (B : ℝ≥0∞) * μ (label ⁻¹' T) := by
  classical
  obtain ⟨n, hn, c, q, hc, hq⟩ := exists_interval_quantizer C δ hC hδ
  refine ⟨n ^ m, pow_pos hn _, ?_⟩
  intro Ω Λ _ μ label f hf
  let code (z : Λ) : Fin m → Fin n := fun j => q (f j z)
  let fiber (t : Fin m → Fin n) : Set Ω := label ⁻¹' {z | code z = t}
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image Finset.univ
    (fun t : Fin m → Fin n => μ (fiber t)) Finset.univ_nonempty
  let a (j : ℕ) : ℝ := if hj : j < m then c (t ⟨j, hj⟩) else 0
  refine ⟨{z | code z = t}, a, ?_, ?_, ?_⟩
  · intro j
    dsimp [a]
    split_ifs
    · exact hc _
    · simpa using hC
  · intro z hz j hj
    have heq : q (f j z) = t ⟨j, hj⟩ := congrFun hz ⟨j, hj⟩
    simpa only [a, dif_pos hj, heq] using hq (f j z) (hf j z)
  · have hcover : (univ : Set Ω) = ⋃ t : Fin m → Fin n, fiber t := by
      ext x
      simp only [mem_univ, mem_iUnion, fiber, mem_preimage, mem_setOf_eq,
        true_iff]
      exact ⟨code (label x), rfl⟩
    calc
      μ univ ≤ ∑ t : Fin m → Fin n, μ (fiber t) := by
        rw [hcover]
        exact measure_iUnion_fintype_le μ fiber
      _ ≤ ∑ _t : Fin m → Fin n, μ (fiber t) :=
        Finset.sum_le_sum fun t' _ => ht t' (Finset.mem_univ _)
      _ = ((n ^ m : ℕ) : ℝ≥0∞) * μ (label ⁻¹' {z | code z = t}) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, fiber]

end Submission.Obl.k4_tempered_grid_selection
