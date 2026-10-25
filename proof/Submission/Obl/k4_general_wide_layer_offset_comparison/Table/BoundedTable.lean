import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.Assemble
import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.DomainBudgets
import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.FinalBudgets

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent.GoodTableData

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {r u v m H₀ H : ℝ}

/-- The original fine-domain budgets pay for the entire realized table.
The budget uses only intrinsic losses, before choosing the final fiber radius. -/
theorem exists_budgeted_table (t : p.GoodTableData k r u v m H₀ H)
    (hH2 : 2 ≤ H) (hH₀ : 1 ≤ H₀) (hH₀H : H₀ ≤ H) (h3H₀ : 3 * H₀ ≤ H)
    (h10K : 10 * p.K k ≤ H) (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 ≤ p.d)
    (hKnat : 0 ≤ t.Knat)
    (hcoarse : tableCoarseBudget (p.K k) t.Knat ≤ H ^ 4)
    (hfine : tableFineBudget (p.K k) H₀ p.d t.δ⁻¹ ≤ H ^ 4)
    (hoff : tableOffsetBudget (p.K k) H₀ p.d t.δ⁻¹ ≤ H ^ 10)
    (hrev : tableReverseBudget (p.K k) H₀ p.d t.Knat t.δ⁻¹ ≤ H ^ 4)
    (hshort : ∀ a, (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) ≤ (t.layers a).β)
    (hβg : ∀ a, (t.layers a).β ≤ p.N k ^ (-p.ℓ * r)) :
    ∃ table : p.ComparisonTable k r u v m H
        (tableReferenceBudget (p.K k) H₀ p.d t.Knat t.δ⁻¹), table.law = t.law := by
  classical
  have hN := N_pos t
  have hq : 0 < (2 : ℝ) ^ (-(p.T k r : ℤ)) := by positivity
  have hq1 : (2 : ℝ) ^ (-(p.T k r : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hsdepth (c : Fin 2) : (![r, r + u, r + v] : Fin 3 → ℝ) c.succ =
      r + (![u, v] : Fin 2 → ℝ) c := by fin_cases c <;> rfl
  have hmenus (c : Fin 2) :
      ∃ D : Fin (t.layers c.succ).count → Finset (ℤ × ℤ × ℤ),
      (∀ i l, l ∈ (t.layers c.succ).C i → ∀ s ∈ Icc (0 : ℝ) 1,
        movingDomainCode ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
          ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
          (p.b k l 1) (p.b k l 4) s ∈ D i) ∧
      (∑ i, ∑ _q ∈ D i,
        ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
          (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
          (p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c)) ^ p.d) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (t.layers c.succ).tag i 0}) ≤
        ENNReal.ofReal (240 * H₀ ^ 3) := by
    have hvalid : (t.layers c.succ).Valid p k (r + (![u, v] : Fin 2 → ℝ) c) m H₀ := by
      rw [← hsdepth c]
      exact t.layer_valid c.succ
    obtain ⟨D, hD, hb⟩ := (t.layers c.succ).reference_domain_menus p hN hvalid hH₀
      hq hq1 (by positivity) (hshort c.succ) (hβg c.succ)
    refine ⟨D, hD, ?_⟩
    simpa only [neg_add, sub_eq_add_neg] using hb
  choose domains hdom hbudget using hmenus
  have hrev' : 16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat ≤ H ^ 4 := by
    simpa only [tableReverseBudget, div_eq_mul_inv] using hrev
  let table := t.toTable hH2 hH₀ hH₀H h3H₀ h10K hu hv hd hKnat
    hcoarse hfine hoff hrev' domains hdom (240 * H₀ ^ 3) hbudget
  have hR : (4 * p.K k + 5) * (6 * p.K k + 5) * t.Knat *
      (16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat) * (240 * H₀ ^ 3) =
      tableReferenceBudget (p.K k) H₀ p.d t.Knat t.δ⁻¹ := by
    unfold tableReferenceBudget tableCoarseBudget tableReverseBudget
    rw [div_eq_mul_inv]
  have htransport {R R' : ℝ} (h : R = R') (s : p.ComparisonTable k r u v m H R) :
      (h ▸ s).law = s.law := by subst R'; rfl
  exact ⟨hR ▸ table, (htransport hR table).trans rfl⟩

end Parent.GoodTableData
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
