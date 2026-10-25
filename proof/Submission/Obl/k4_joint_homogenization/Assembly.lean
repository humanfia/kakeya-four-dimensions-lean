import Submission.Obl.k4_joint_homogenization.Interface

namespace Submission.Obl.k4_joint_homogenization

/-- Passing to a subsequence preserves the polynomial-format witnesses. -/
theorem format_comp {N K : ℕ → ℝ}
    {ν : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (h : Format N K ν E) (ψ : ℕ → ℕ) :
    Format (fun k => N (ψ k)) (fun k => K (ψ k))
      (fun k => ν (ψ k)) (fun k => E (ψ k)) := by
  obtain ⟨M, D, h⟩ := h
  exact ⟨M, D, fun k => h (ψ k)⟩

/-- Subpower losses remain subpower along a strictly increasing subsequence. -/
theorem subpower_comp {N K : ℕ → ℝ} (h : Subpower N K)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    Subpower (fun k => N (ψ k)) (fun k => K (ψ k)) := by
  refine ⟨fun k => h.1 (ψ k), ?_⟩
  intro ε hε
  exact hψ.tendsto_atTop.eventually (h.2 ε hε)

/-- The retained law has mass at most one, since its times lie in [0,1]. -/
theorem law_le_one {N K : ℕ → ℝ}
    {ν : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (h : Format N K ν E) : ∀ k, Law ν E k Set.univ ≤ 1 := by
  obtain ⟨M, D, h⟩ := h
  intro k
  obtain ⟨hprob, _, _, htime, _, _, _, _⟩ := h k
  let _ := hprob
  change (((ν k).prod MeasureTheory.volume).restrict (E k)) Set.univ ≤ 1
  rw [MeasureTheory.Measure.restrict_apply_univ]
  calc
    _ ≤ ((ν k).prod MeasureTheory.volume)
        (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := MeasureTheory.measure_mono htime
    _ = 1 := by simp

/-- The format's last conjunct is the required lower mass bound. -/
theorem law_mass_lower {N K : ℕ → ℝ}
    {ν : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (h : Format N K ν E) :
    ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ Law ν E k Set.univ := by
  obtain ⟨M, D, h⟩ := h
  intro k
  exact (h k).2.2.2.2.2.2.2

end Submission.Obl.k4_joint_homogenization
