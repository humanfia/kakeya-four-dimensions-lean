import Submission.Obl.k4_scalar_grid_cartesian_field.QualifiedPart

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- The frozen real bad-mass ratio gives a relative original ENNReal mass bound. -/
theorem eventually_relative_mass_small (bad total : ℕ → ENNReal)
    (htop : ∀ k, total k ≠ ⊤) (hbad : ∀ k, bad k ≤ total k)
    (hpos : ∀ᶠ k in atTop, 0 < total k)
    (hlim : Tendsto (fun k => (bad k).toReal / (total k).toReal) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, bad k ≤ ENNReal.ofReal ε * total k := by
  filter_upwards [hpos, hlim.eventually (gt_mem_nhds hε)] with k hk hratio
  have hbadtop : bad k ≠ ⊤ := ne_top_of_le_ne_top (htop k) (hbad k)
  have hreal : 0 < (total k).toReal := ENNReal.toReal_pos hk.ne' (htop k)
  have hbound : (bad k).toReal ≤ ε * (total k).toReal :=
    ((div_lt_iff₀ hreal).mp hratio).le
  calc
    _ = ENNReal.ofReal (bad k).toReal := (ENNReal.ofReal_toReal hbadtop).symm
    _ ≤ ENNReal.ofReal (ε * (total k).toReal) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := by rw [ENNReal.ofReal_mul hε.le, ENNReal.ofReal_toReal (htop k)]

/-- Deleting at most one quarter of a finite original mass retains at least half. -/
theorem half_mass_of_quarter_bad {total good bad : ENNReal}
    (htop : total ≠ ⊤) (hgood : good ≤ total) (hbad : bad ≤ total)
    (hcover : total ≤ good + bad) (hsmall : bad ≤ ENNReal.ofReal (1 / 4 : ℝ) * total) :
    ENNReal.ofReal (1 / 2 : ℝ) * total ≤ good := by
  have hgtop : good ≠ ⊤ := ne_top_of_le_ne_top htop hgood
  have hbtop : bad ≠ ⊤ := ne_top_of_le_ne_top htop hbad
  have hsumtop : good + bad ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hgtop, hbtop⟩
  have hc : total.toReal ≤ good.toReal + bad.toReal := by
    have hc' := ENNReal.toReal_mono hsumtop hcover
    rwa [ENNReal.toReal_add hgtop hbtop] at hc'
  have hs : bad.toReal ≤ (1 / 4 : ℝ) * total.toReal := by
    have hs' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) hsmall
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)] using hs'
  have hreal : (1 / 2 : ℝ) * total.toReal ≤ good.toReal := by
    linarith [ENNReal.toReal_nonneg (a := total)]
  calc
    _ = ENNReal.ofReal ((1 / 2 : ℝ) * total.toReal) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.ofReal_toReal htop]
    _ ≤ ENNReal.ofReal good.toReal := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal hgtop

/-- Finite weighted families preserve a measurable bad-set deletion budget. -/
theorem weighted_measurable_qualified_parts {Ω G : Type*} [MeasurableSpace Ω] [Fintype G]
    (ρ : G → Measure Ω) (weight : G → ENNReal) (E Bad : G → Set Ω)
    (hE : ∀ g, MeasurableSet (E g)) :
    ∃ Good : G → Set Ω, (∀ g, MeasurableSet (Good g) ∧ Good g ⊆ E g ∧
      ∀ p ∈ Good g, p ∉ Bad g) ∧
      (∑ g, weight g * ρ g (E g)) ≤
        (∑ g, weight g * ρ g (Good g)) + ∑ g, weight g * (ρ g).restrict (E g) (Bad g) := by
  classical
  choose Good hGood using fun g => measurable_part_avoiding_bad
    ((ρ g).restrict (E g)) (E g) (Bad g) (hE g)
  refine ⟨Good, (fun g => ⟨(hGood g).1, (hGood g).2.1, (hGood g).2.2.1⟩), ?_⟩
  have hbound (g : G) : ρ g (E g) ≤ ρ g (Good g) + (ρ g).restrict (E g) (Bad g) := by
    have h := (hGood g).2.2.2
    rw [Measure.restrict_apply (hE g), inter_self,
      Measure.restrict_apply (hGood g).1, inter_eq_left.mpr (hGood g).2.1] at h
    exact h
  calc
    _ ≤ ∑ g, weight g * (ρ g (Good g) + (ρ g).restrict (E g) (Bad g)) :=
      Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (hbound g)
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib]

end Submission.Obl.k4_scalar_grid_cartesian_field
