import Submission.Obl.k4_finite_width_output_exclusion.Models

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

lemma Valid.scale_ge_two {p : Data} (hp : Valid p) (k : ℕ) : 2 ≤ p.N k := hp.1 k
lemma Valid.scale_pos {p : Data} (hp : Valid p) (k : ℕ) : 0 < p.N k := by
  linarith [hp.scale_ge_two k]
lemma Valid.scale_ge_one {p : Data} (hp : Valid p) (k : ℕ) : 1 ≤ p.N k := by
  linarith [hp.scale_ge_two k]
lemma Valid.scale_tendsto {p : Data} (hp : Valid p) : Tendsto p.N atTop atTop := hp.2.1
lemma Valid.slack_ge_one {p : Data} (hp : Valid p) (k : ℕ) : 1 ≤ p.K k := hp.2.2.1.1 k
lemma Valid.slack_subpower {p : Data} (hp : Valid p) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε := hp.2.2.1.2 ε hε
lemma Valid.length_pos {p : Data} (hp : Valid p) : 0 < p.L := hp.2.2.2.1

lemma Valid.B_pos {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) :
    0 < p.B k γ := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  exact ((hfmt k).2.2.2.1 γ).2.1

lemma cost_iff (p : Data) (h : ℝ) : Cost p h ↔
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧
        ∃ a : Atlas p k, (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M D κ := by
  classical
  constructor
  · rintro ⟨M, D, ht⟩
    refine ⟨M, D, fun ε hε => (ht ε hε).mono ?_⟩
    rintro k ⟨κ, hκ, hKκ, hκε, T, C, γ, j, c, u, Q, R, A, F, hT, hC, hd, hc, hm⟩
    exact ⟨κ, hκ, hKκ, hκε,
      ⟨T, C, γ, j, c, u, Q, R, A, F, fun _ _ => ∅⟩, hT, hC, hd, hc, hm⟩
  · rintro ⟨M, D, ht⟩
    refine ⟨M, D, fun ε hε => (ht ε hε).mono ?_⟩
    rintro k ⟨κ, hκ, hKκ, hκε, a, hT, hC, hd, hc, hm⟩
    exact ⟨κ, hκ, hKκ, hκε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F,
      hT, hC, hd, hc, hm⟩

lemma narrow_iff (p : Data) (h w : ℝ) : Narrow p h w ↔
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧
        ∃ a : Atlas p k, (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧
          (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w + ε)) ∧
          a.TrueAt M D κ := by
  classical
  constructor
  · rintro ⟨M, D, ht⟩
    refine ⟨M, D, fun ε hε => (ht ε hε).mono ?_⟩
    rintro k ⟨κ, hκ, hKκ, hκε, T, C, γ, j, c, u, Q, R, A, F,
      hT, hw, hC, hd, hc, hm⟩
    exact ⟨κ, hκ, hKκ, hκε,
      ⟨T, C, γ, j, c, u, Q, R, A, F, fun _ _ => ∅⟩, hT, hw, hC, hd, hc, hm⟩
  · rintro ⟨M, D, ht⟩
    refine ⟨M, D, fun ε hε => (ht ε hε).mono ?_⟩
    rintro k ⟨κ, hκ, hKκ, hκε, a, hT, hw, hC, hd, hc, hm⟩
    exact ⟨κ, hκ, hKκ, hκε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F,
      hT, hw, hC, hd, hc, hm⟩

lemma horizon_eq (p : Data) : Horizon p = sInf {h : ℝ | Cost p h} := rfl

end
end Submission.Obl.k4_finite_width_output_exclusion
