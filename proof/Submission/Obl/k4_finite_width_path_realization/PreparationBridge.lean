import Submission.Obl.k4_finite_width_path_realization.Forests

namespace Submission.Obl.k4_finite_width_path_realization

open Filter MeasureTheory

/-- The concrete preparation interface applied to the same supplied forest. -/
theorem prepare_forests (prep : ForestPreparationExpanded) {p : Data} (hp : p.Valid)
    (m : ℕ) (r : ℕ → ℝ) (hm : 0 < m)
    (hr : ∀ i, i < m → 0 < r i ∧ r i ≤ p.L) (M D : ℕ) :
    ∃ M' D' : ℕ, ∀ σ : ℝ, 0 < σ → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ k in atTop, ∀ (a : Forest p k) (w q : ℝ),
        (∀ i, i < m → (2 : ℝ) ^ a.T i ≤ p.N k ^ M) →
        a.Core M D m r → a.κ ≤ p.N k ^ ρ → a.LowerWidths M r w q →
        ∃ b : Forest p k, b.κ = p.N k ^ σ ∧ b.T = a.T ∧
          b.Core M' D' m r ∧ b.Prepared r ∧ b.Budget ∧ b.LowerWidths M r w q := by
  obtain ⟨M', D', _, _, hs⟩ := prep p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E
    p.P p.B p.f p.g p.G hp m r hm hr M D
  refine ⟨M', D', fun σ hσ => ?_⟩
  obtain ⟨ρ, hρ, _, hk⟩ := hs σ hσ
  refine ⟨ρ, hρ, hk.mono fun k hprep a w q hT ha hκ hwidth => ?_⟩
  have ha' := ha.mono hp hκ
  obtain ⟨C', e, par', F', lst, hC, hcore, hsub, hlst, hupper, hfin, hbudget⟩ :=
    hprep a.T a.C a.lev a.par a.γ a.j a.c a.u a.Q a.R a.A a.F hT ha'
  let b : Forest p k := ⟨p.N k ^ σ, a.T, C', a.lev ∘ e, par', a.γ ∘ e,
    a.j ∘ e, a.c ∘ e, a.u ∘ e, a.Q ∘ e, a.R ∘ e, a.A ∘ e, F', a.width ∘ e, lst⟩
  refine ⟨b, rfl, rfl, hcore, ⟨hlst, hupper⟩, ⟨hfin, hbudget⟩, ?_⟩
  dsimp only [Forest.LowerWidths, b, Function.comp_apply]
  intro z
  refine ⟨(hwidth (e z)).1, (hwidth (e z)).2.1, (hwidth (e z)).2.2.1, ?_⟩
  intro hz
  rw [(hsub z).2 hz]
  exact (hwidth (e z)).2.2.2 hz

end Submission.Obl.k4_finite_width_path_realization
