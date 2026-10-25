import Submission.Obl.k4_scalar_grid_cartesian_field.QualifiedSelection
import Submission.Obl.k4_scalar_grid_cartesian_field.NonsteepSelection

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- Qualified nonsteep original world pieces with the original coefficient support and mass floor. -/
noncomputable def cleanPartsAt (data : Data) (M : ℕ)
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (data.W k) → Set Incidence) (B : ℝ) (H : ℕ → ℝ)
    (ε Q : ℝ) (k : ℕ) : Prop :=
  ∃ Good : Fin (data.W k) → Set Incidence,
    (∀ g, MeasurableSet (Good g) ∧ Good g ⊆ E k g ∧ ∀ x ∈ Good g,
      (∀ e, |x.1.2 e| ≤ data.K k) ∧ x ∉ unqualified data M G E B ε k g ∧
        x ∉ steepWorld data k g Q) ∧
    ENNReal.ofReal (1 / (4 * H k)) ≤
      ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (Good g)

/-- Relative qualification deletion and an absolute small steep loss can be combined
without demanding a convergence rate of the former against a subpower sequence. -/
theorem clean_parts_of_qualified {data : Data} (hb : baseHyp data) {k M : ℕ}
    (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (data.W k) → Set Incidence) {B : ℝ} (H : ℕ → ℝ)
    {ε Q : ℝ} (hH : 1 ≤ H k) (hq : qualifiedPartsAt data M G E B H ε k)
    (hbadmeas : ∀ g : Fin (data.W k), MeasurableSet (steepWorld data k g Q))
    (hbad : (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (steepWorld data k g Q)) ≤
      ENNReal.ofReal (1 / (8 * H k))) : cleanPartsAt data M G E B H ε Q k := by
  classical
  obtain ⟨Good, hGood, hmass⟩ := hq
  let C : Set Incidence := {x | ∀ e, |x.1.2 e| ≤ data.K k}
  let Cut : Fin (data.W k) → Set Incidence := fun g => (Good g \ steepWorld data k g Q) ∩ C
  have hC : MeasurableSet C := (measurableSet_coefficient_bound (data.K k)).preimage measurable_fst
  have hnull (g : Fin (data.W k)) : data.ρ k g Cᶜ = 0 := ae_iff.mp (original_incidence_coefficients data hb k g)
  have hHpos : 0 < H k := by linarith
  refine ⟨Cut, ?_, ?_⟩
  · intro g
    refine ⟨((hGood g).1.diff (hbadmeas g)).inter hC, ?_, ?_⟩
    · exact fun x hx => (hGood g).2.1 hx.1.1
    · intro x hx
      exact ⟨hx.2, (hGood g).2.2 x hx.1.1, hx.1.2⟩
  · have hbudget : (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (Good g)) ≤
        (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (Cut g)) +
          ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (steepWorld data k g Q) := by
      calc
        _ = ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (Good g ∩ C) := by
          apply Finset.sum_congr rfl
          intro g _
          rw [measure_inter_conull (hnull g)]
        _ ≤ ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) *
            (data.ρ k g (Cut g) + data.ρ k g (steepWorld data k g Q)) := by
          apply Finset.sum_le_sum
          intro g _
          apply mul_le_mul' le_rfl
          apply (measure_mono (t := Cut g ∪ steepWorld data k g Q) ?_).trans (measure_union_le _ _)
          intro x hx
          by_cases hxs : x ∈ steepWorld data k g Q
          · exact Or.inr hxs
          · exact Or.inl ⟨⟨hx.1, hxs⟩, hx.2⟩
        _ = _ := by simp only [mul_add, Finset.sum_add_distrib]
    have hfloor : ENNReal.ofReal (1 / (4 * H k)) + ENNReal.ofReal (1 / (4 * H k)) ≤
        ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (Good g) := by
      convert hmass using 1
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 1 / (4 * H k)) (by positivity : 0 ≤ 1 / (4 * H k))]
      congr 1
      ring
    have hcost : (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * data.ρ k g (steepWorld data k g Q)) ≤
        ENNReal.ofReal (1 / (4 * H k)) := hbad.trans (ENNReal.ofReal_le_ofReal (by
      apply one_div_le_one_div_of_le (by positivity : 0 < 4 * H k)
      linarith))
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
      (hfloor.trans (hbudget.trans (add_le_add le_rfl hcost)))

end Submission.Obl.k4_scalar_grid_cartesian_field
