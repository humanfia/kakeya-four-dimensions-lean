import Submission.Obl.k4_raw_critical_segment_forests.RawOneLayer
import Submission.Obl.k4_raw_critical_segment_forests.ForestMono

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Whole-label selection with a possibly smaller selected incidence set. -/
structure Forest.Selection {p : Data} {k : ℕ} (a : Forest p k) where
  C : ℕ
  emb : Fin C ↪ Fin a.C
  par : Fin C → Fin C
  F : Fin C → Set Point

/-- Geometry and full trajectory assignments of retained labels are fixed. -/
abbrev Forest.Selection.forest {p : Data} {k : ℕ} {a : Forest p k}
    (sel : a.Selection) (κ : ℝ) : Forest p k where
  κ := κ
  T := a.T
  C := sel.C
  lev b := a.lev (sel.emb b)
  par := sel.par
  γ b := a.γ (sel.emb b)
  j b := a.j (sel.emb b)
  c b := a.c (sel.emb b)
  u b := a.u (sel.emb b)
  Q b := a.Q (sel.emb b)
  R b := a.R (sel.emb b)
  A b := a.A (sel.emb b)
  F := sel.F

/-- The mass ceiling and own-depth observation knowledge obtained by preparation. -/
def Forest.Prepared {p : Data} {k : ℕ} (a : Forest p k) (r : ℕ → ℝ)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)) : Prop :=
  (∀ i γ o, ((lst i γ o).card : ℝ) ≤ a.κ) ∧
  (∀ b, p.ν k (a.γ b) (a.A b) ≤
    ENNReal.ofReal (a.κ * p.N k ^ (-p.f (r (a.lev b))) * |Matrix.det (a.Q b)|) ∧
    ∀ z ∈ a.F b, b ∈ lst (a.lev b) (a.γ b)
      (obs (p.B k (a.γ b)) (δ (p.N k) (r (a.lev b))) z))

/-- The frozen preparation hypothesis, packaged using finite forest data.
The unused finite child-mass conclusions of that hypothesis are omitted here. -/
def Preparation : Prop :=
  ∀ p : Data, Valid p → ∀ (m : ℕ) (r : ℕ → ℝ), 0 < m →
    (∀ i, i < m → 0 < r i ∧ r i ≤ p.L) → ∀ M D : ℕ,
    ∃ M' D' : ℕ, M ≤ M' ∧ D ≤ D' ∧
      ∀ σ : ℝ, 0 < σ → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ σ ∧
        ∀ᶠ k in atTop, ∀ a : Forest p k,
          a.κ = p.N k ^ ρ → (∀ i, i < m → (2 : ℝ) ^ a.T i ≤ p.N k ^ M) →
          a.Core M D m r →
          ∃ (sel : a.Selection)
            (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin sel.C)),
            sel.C ≤ a.C ∧ (sel.forest (p.N k ^ σ)).Core M' D' m r ∧
            (∀ b, sel.F b ⊆ a.F (sel.emb b) ∧
              (0 < a.lev (sel.emb b) → sel.emb (sel.par b) = a.par (sel.emb b))) ∧
            (sel.forest (p.N k ^ σ)).Prepared r lst

lemma rawData_select {p : Data} {kr w ε q σ : ℝ} {m M M' D' k : ℕ}
    {s r : ℕ → ℝ} {a : Forest p k} {width : Fin a.C → ℝ}
    (hM : M ≤ M') (sel : a.Selection)
    (hcore : (sel.forest (p.N k ^ σ)).Core M' D' m r)
    (hparent : ∀ b, 0 < a.lev (sel.emb b) →
      sel.emb (sel.par b) = a.par (sel.emb b))
    (htime : ∀ i, i < m → p.N k ^ (kr * s i - ε) ≤ (2 : ℝ) ^ a.T i ∧
      (2 : ℝ) ^ a.T i ≤ p.N k ^ (kr * s i + ε) ∧ (2 : ℝ) ^ a.T i ≤ p.N k ^ M)
    (hwidth : ∀ b, |width b| ≤ (M : ℝ) ∧
      p.N k ^ (-width b) = |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T (a.lev b) ∧
      (a.lev b = 0 → w * r 0 - q ≤ width b) ∧
      (0 < a.lev b → width (a.par b) +
        w * (r (a.lev b) - r (a.lev (a.par b))) - q ≤ width b))
    (hN : 1 ≤ p.N k) :
    (sel.forest (p.N k ^ σ)).RawData (fun b => width (sel.emb b))
      kr w ε q σ m s r M' D' := by
  refine ⟨le_rfl, hcore, ?_, ?_⟩
  · intro i hi
    exact ⟨(htime i hi).1, (htime i hi).2.1,
      (htime i hi).2.2.trans (pow_le_pow_right₀ hN hM)⟩
  · intro b
    refine ⟨(hwidth (sel.emb b)).1.trans (by exact_mod_cast hM),
      (hwidth (sel.emb b)).2.1, (hwidth (sel.emb b)).2.2.1, ?_⟩
    intro hlev
    have hpar := hparent b hlev
    change width (sel.emb (sel.par b)) +
      w * (r (a.lev (sel.emb b)) - r (a.lev (sel.emb (sel.par b)))) - q ≤ width (sel.emb b)
    rw [hpar]
    exact (hwidth (sel.emb b)).2.2.2 hlev

/-- Prepare an entire frequent forest family on one subsequence with vanishing
slack. The format is fixed before the diagonal and all lists refer to the
actual chosen forests. -/
theorem prepared_raw_sequence (hprep : Preparation)
    {p : Data} (hp : Valid p) {kr w ε q : ℝ} {m M D : ℕ} {s r : ℕ → ℝ}
    (hm : 0 < m) (hr : ∀ i, i < m → 0 < r i ∧ r i ≤ p.L)
    (hfamily : ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop, RawAt p kr w ε q σ m s r M D k) :
    ∃ M' D' : ℕ, M ≤ M' ∧ D ≤ D' ∧
      ∃ (φ : ℕ → ℕ) (a : (n : ℕ) → Forest p (φ n))
        (width : (n : ℕ) → Fin (a n).C → ℝ)
        (lst : (n : ℕ) → ℕ → Fin (p.W (φ n)) → Observation → Finset (Fin (a n).C)),
        StrictMono φ ∧ ∀ n,
          (a n).RawData (width n) kr w ε q (1 / ((n : ℝ) + 1)) m s r M' D' ∧
          (a n).Prepared r (lst n) := by
  classical
  obtain ⟨M', D', hM, hD, hprep⟩ := hprep p hp m r hm hr M D
  have hfreq (n : ℕ) : ∃ᶠ k in atTop,
      ∃ (a : Forest p k) (width : Fin a.C → ℝ)
        (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)),
        a.RawData width kr w ε q (1 / ((n : ℝ) + 1)) m s r M' D' ∧ a.Prepared r lst := by
    have hσ : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨ρ, hρ, hρσ, hlate⟩ := hprep _ hσ
    apply ((hfamily ρ hρ).and_eventually hlate).mono
    rintro k ⟨⟨a, width, hκ, hcore, htime, hwidth⟩, hlatek⟩
    let a₀ := a.reslack (p.N k ^ ρ)
    have hcore₀ : a₀.Core M D m r := hcore.mono hp le_rfl le_rfl hκ
    obtain ⟨sel, lst, hC, hcore', hsub, hprepared⟩ :=
      hlatek a₀ rfl (fun i hi => (htime i hi).2.2) hcore₀
    refine ⟨sel.forest (p.N k ^ (1 / ((n : ℝ) + 1))),
      fun b => width (sel.emb b), lst, ?_, hprepared⟩
    exact rawData_select (a := a₀) (width := width) hM sel hcore'
      (fun b hb => (hsub b).2 hb) htime hwidth (hp.scale_ge_one k)
  obtain ⟨φ, hφ, hs⟩ := extraction_forall_of_frequently hfreq
  choose a width lst hcert using hs
  exact ⟨M', D', hM, hD, φ, a, width, lst, hφ, hcert⟩

end
end Submission.Obl.k4_raw_critical_segment_forests
