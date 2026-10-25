import Submission.Obl.k4_finite_width_path_realization.Forests

namespace Submission.Obl.k4_finite_width_path_realization

open MeasureTheory Filter

/-- Bin selection only reindexes full witnesses; its fixed fractional mass loss
is absorbed by multiplying slack by a fixed positive integer. -/
theorem select_forest_widths (sel : ForestWidthSelectionExpanded) (m M : ℕ)
    (ε : ℝ) (hm : 0 < m) (hε : 0 < ε) :
    ∃ B : ℕ, 0 < B ∧ ∀ {p : Data}, p.Valid → ∀ {k M' D : ℕ}
      (a : Forest p k) (r : ℕ → ℝ) (w q : ℝ), 0 ≤ q →
      a.Core M' D m r → a.Prepared r → a.Budget → a.LowerWidths M r w q →
      ∃ (b : Forest p k) (nw : ℕ → ℝ), b.κ = (B : ℝ) * a.κ ∧ b.T = a.T ∧
        b.Core M' D m r ∧ b.Prepared r ∧
        (∀ z, p.N k ^ (-b.width z) = |Matrix.det (b.Q z)| * (4 : ℝ) ^ b.T (b.lev z)) ∧
        (∀ z, |b.width z - nw (b.lev z)| ≤ ε) ∧
        (∀ i, i < m → w * r i - (m : ℝ) * (q + 2 * ε) ≤ nw i ∧
          nw i + w * (r (m - 1) - r i) - (m : ℝ) * (q + 2 * ε) ≤ nw (m - 1)) := by
  obtain ⟨B, hB, hselect⟩ := sel m M ε hm hε
  refine ⟨B, hB, fun {p} hp {k M' D} a r w q hq ha hprepared hbudget hwidth => ?_⟩
  have hpos : 0 < a.layerMass (m - 1) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (inv_pos.mpr (by linarith [ha.1])))
      (ha.2.2.2.1 _ (by omega))
  obtain ⟨C', e, par', nw, hC, hpar, hbin, hmass, hlower⟩ :=
    hselect a.C a.lev a.par a.width a.mass r w q hq
      (fun z => ⟨(ha.2.2.2.2.2 z).1, (hwidth z).1⟩)
      (fun z hz => ((ha.2.2.2.2.2 z).2.2.2 hz).1)
      hbudget.1 hbudget.2 hpos (fun z => (hwidth z).2.2)
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hκ : a.κ ≤ (B : ℝ) * a.κ := by nlinarith [ha.1]
  have hmass' (i : ℕ) (hi : i < m) :
      ENNReal.ofReal (((B : ℝ) * a.κ)⁻¹) ≤
        ∑ z, if a.lev (e z) = i then a.mass (e z) else 0 := by
    have heq : ENNReal.ofReal (((B : ℝ) * a.κ)⁻¹) =
        ENNReal.ofReal a.κ⁻¹ / (B : ENNReal) := by
      rw [show ((B : ℝ) * a.κ)⁻¹ = a.κ⁻¹ / (B : ℝ) by simp [div_eq_mul_inv, mul_comm]]
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < B)]
      simp
    rw [heq]
    exact (ENNReal.div_le_div_right (ha.2.2.2.1 _ (by omega)) _).trans (hmass i hi)
  let b := a.reindex e par' ((B : ℝ) * a.κ)
  refine ⟨b, nw, rfl, rfl, ha.reindex hp e par' hC hκ hpar hmass',
    hprepared.reindex hp e par' hκ, ?_, hbin, hlower⟩
  exact fun z => (hwidth (e z)).2.1

end Submission.Obl.k4_finite_width_path_realization
