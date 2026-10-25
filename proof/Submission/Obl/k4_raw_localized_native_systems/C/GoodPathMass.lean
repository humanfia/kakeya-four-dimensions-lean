import Submission.Obl.k4_raw_localized_native_systems.C.Q2Path

/-
Adapted from this LOT tree, o178, session x0596, `GoodPathMass.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The good path loses only exceptional mass

The path of a chart system in one world (its selected incidences at their own
block index) differs from the good path only by incidences that are atypical at
the terminal or zero depth, bad for the terminal angular cap, or violate the
native bounds or position/velocity bounds.  The last two are null when the slack
dominates the problem's `K`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- The full path of a chart system in one world. -/
def fullPath (a : Atlas p k) (γ : Fin (p.W k)) : Set Point :=
  {q | ∃ b, TagPred a γ q b ∧ q ∈ a.F b}

/-- The incidences of short-axis charts (major axis below `lam`) that are angular-good. -/
def shortPath (a : Atlas p k) (γ : Fin (p.W k)) (u τ lam : ℝ) : Set Point :=
  {q | (∃ b, TagPred a γ q b ∧ q ∈ a.F b ∧ ‖longCol (a.Q b)‖ < lam) ∧ AngGood p k γ u τ q}

/-- Angular-cap failures at width `u`. -/
def angFail (p : Data) (k : ℕ) (γ : Fin (p.W k)) (u τ : ℝ) : Set Point :=
  {q | ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) <
    p.G k γ u (jointObs (p.B k γ) (p.N k) p.L u q)}

/-- Typicality failures at depth `r`. -/
def typFail (p : Data) (k : ℕ) (γ : Fin (p.W k)) (r τ : ℝ) : Set Point :=
  {q | p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q) < ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ∨
    ENNReal.ofReal (p.N k ^ (-p.f r + τ)) < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}

/-- Native and position bounds hold almost everywhere for the selected law. -/
theorem ae_native_selected (hp : Valid p) (γ : Fin (p.W k)) {κ' : ℝ} (hK : p.K k ≤ κ') :
    ∀ᵐ q ∂ selected p k γ, NativeOK p k γ κ' q ∧ ‖y q.1 0‖ + ‖v q.1‖ ≤ κ' := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  obtain ⟨hprob, hBpos, -, -, -, -, -, hEm, hEsub, -, -, hae, hfloor⟩ := (hfmt k).2.2.2.1 γ
  have hK1 : 1 ≤ p.K k := hp.slack_ge_one k
  have hκ0 : 0 < κ' := by linarith
  -- the line bounds hold for ν-a.e. line, hence for a.e. incidence
  have hline : ∀ᵐ q ∂ selected p k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖y q.1 t‖ + ‖v q.1‖ ≤ p.K k ∧ |MvPolynomial.eval (x q.1 t) (p.P k γ)| ≤ p.K k ∧
      |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv 3 (p.P k γ))| ≤ p.K k * p.B k γ ∧
      |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.P k γ)))| ≤
        p.K k * p.B k γ ^ 2 := by
    have h1 : ∀ᵐ q ∂ (p.ν k γ).prod (volume : Measure ℝ), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖y q.1 t‖ + ‖v q.1‖ ≤ p.K k ∧ |MvPolynomial.eval (x q.1 t) (p.P k γ)| ≤ p.K k ∧
        |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv 3 (p.P k γ))| ≤ p.K k * p.B k γ ∧
        |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.P k γ)))| ≤
          p.K k * p.B k γ ^ 2 := by
      rw [ae_iff] at hae ⊢
      have hset : {q : Point | ¬ ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖y q.1 t‖ + ‖v q.1‖ ≤ p.K k ∧ |MvPolynomial.eval (x q.1 t) (p.P k γ)| ≤ p.K k ∧
          |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv 3 (p.P k γ))| ≤ p.K k * p.B k γ ∧
          |MvPolynomial.eval (x q.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.P k γ)))| ≤
            p.K k * p.B k γ ^ 2} =
          {l : Line | ¬ ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖y l t‖ + ‖v l‖ ≤ p.K k ∧ |MvPolynomial.eval (x l t) (p.P k γ)| ≤ p.K k ∧
          |MvPolynomial.eval (x l t) (MvPolynomial.pderiv 3 (p.P k γ))| ≤ p.K k * p.B k γ ∧
          |MvPolynomial.eval (x l t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.P k γ)))| ≤
            p.K k * p.B k γ ^ 2} ×ˢ Set.univ := by
        ext q; simp
      rw [hset, Measure.prod_prod, hae, zero_mul]
    exact ae_restrict_of_ae h1
  have hsel : ∀ᵐ q ∂ selected p k γ, q ∈ p.E k γ := ae_restrict_mem hEm
  filter_upwards [hline, hfloor, hsel] with q hq hfl hqE
  have ht : q.2 ∈ Set.Icc (0 : ℝ) 1 := (Set.mem_prod.1 (hEsub hqE)).2
  obtain ⟨h1, h2, h3, h4⟩ := hq q.2 ht
  have h0 := (hq 0 ⟨le_rfl, zero_le_one⟩).1
  have hxq : x q.1 q.2 = x q.1 q.2 := rfl
  refine ⟨⟨h2.trans hK, ?_, ?_, ?_⟩, h0.trans hK⟩
  · exact h3.trans (mul_le_mul_of_nonneg_right hK (hBpos).le)
  · exact h4.trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))
  · refine le_trans ?_ hfl
    exact div_le_div_of_nonneg_left hBpos.le (by linarith) hK

/-- The full path is covered by the good path and the exceptional sets. -/
theorem fullPath_subset (a : Atlas p k) (γ : Fin (p.W k)) (u τ κ' lam : ℝ) :
    fullPath a γ ⊆ goodPath a γ u τ κ' lam ∪ angFail p k γ u τ ∪ typFail p k γ p.L τ ∪
      typFail p k γ 0 τ ∪ {q | ¬ (NativeOK p k γ κ' q ∧ ‖y q.1 0‖ + ‖v q.1‖ ≤ κ')} ∪
        shortPath a γ u τ lam := by
  intro q hq
  by_cases hang : q ∈ angFail p k γ u τ
  · left; left; left; left; right; exact hang
  by_cases htL : q ∈ typFail p k γ p.L τ
  · left; left; left; right; exact htL
  by_cases ht0 : q ∈ typFail p k γ 0 τ
  · left; left; right; exact ht0
  have hgood : AngGood p k γ u τ q := by
    refine ⟨?_, ?_⟩
    · simp only [angFail, Set.mem_setOf_eq, not_lt] at hang; exact hang
    · simp only [typFail, Set.mem_setOf_eq, not_or, not_lt] at htL; exact htL.1
  by_cases hn : NativeOK p k γ κ' q ∧ ‖y q.1 0‖ + ‖v q.1‖ ≤ κ'
  · obtain ⟨b, hb, hF⟩ := hq
    by_cases hlong : lam ≤ ‖longCol (a.Q b)‖
    · left; left; left; left; left
      refine ⟨⟨b, hb, hF, hlong⟩, hgood, ?_, hn.1, hn.2⟩
      simp only [typFail, Set.mem_setOf_eq, not_or, not_lt] at ht0; exact ht0.2
    · right
      exact ⟨⟨b, hb, hF, lt_of_not_ge hlong⟩, hgood⟩
  · left; right; exact hn

/-- **Path mass versus good-path mass, in one world.** -/
theorem fullPath_mass_le (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k)) {u τ κ' lam : ℝ}
    (hK : p.K k ≤ κ')
    {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex) :
    ((p.ν k γ).prod volume) (fullPath a γ) ≤
      ((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam) + selected p k γ (angFail p k γ u τ) +
        selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ) +
          selected p k γ (shortPath a γ u τ lam) := by
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hEm : MeasurableSet (p.E k γ) := ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.1
  have hpathE : fullPath a γ ⊆ p.E k γ := by
    intro q hq
    obtain ⟨b, hb, hF⟩ := hq
    have := (hc.selected b hF).1
    rwa [hb.1] at this
  have hnull : selected p k γ {q | ¬ (NativeOK p k γ κ' q ∧ ‖y q.1 0‖ + ‖v q.1‖ ≤ κ')} = 0 := by
    have := ae_native_selected hp γ hK
    rw [ae_iff] at this
    exact this
  -- the full path lives in E, so its prior mass is its selected mass
  have heq : ((p.ν k γ).prod volume) (fullPath a γ) = selected p k γ (fullPath a γ) := by
    unfold selected priorMass
    rw [Measure.restrict_apply' hEm, Set.inter_eq_left.2 hpathE]
  rw [heq]
  calc selected p k γ (fullPath a γ)
      ≤ selected p k γ (goodPath a γ u τ κ' lam ∪ angFail p k γ u τ ∪ typFail p k γ p.L τ ∪
          typFail p k γ 0 τ ∪ {q | ¬ (NativeOK p k γ κ' q ∧ ‖y q.1 0‖ + ‖v q.1‖ ≤ κ')} ∪
            shortPath a γ u τ lam) :=
        measure_mono (fullPath_subset a γ u τ κ' lam)
    _ ≤ selected p k γ (goodPath a γ u τ κ' lam) + selected p k γ (angFail p k γ u τ) +
          selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ) +
          selected p k γ {q | ¬ (NativeOK p k γ κ' q ∧ ‖y q.1 0‖ + ‖v q.1‖ ≤ κ')} +
          selected p k γ (shortPath a γ u τ lam) := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ _ := by
        rw [hnull, add_zero]
        have hres : selected p k γ (goodPath a γ u τ κ' lam) ≤
            ((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam) := by
          unfold selected priorMass
          exact Measure.restrict_le_self _
        exact add_le_add (add_le_add (add_le_add (add_le_add hres le_rfl) le_rfl) le_rfl) le_rfl

end

end Submission.Obl.k4_raw_localized_native_systems.C
