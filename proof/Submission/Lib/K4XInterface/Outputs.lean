import Mathlib
import Submission.Lib.K4XInterface.Charts

/-!
# Building outputs of the frozen interface X

* `gchart_reframe`: a path chart with a new frame `Q₂ = f⁻¹` given by bounded row functionals
  on sub-assignments in format, keeping its test, depth and block (the strip conversion of
  paper Prop. 4.11 produces exactly such charts).
* `XOutput`: the frozen conclusion of X at a sample (an excluded improvement), written with
  `gchart`, `gobs`, `gδ`. Inside the frozen statement of o107, after introducing the grid,
  the problem, the complexity bounds, `τ`, `σ`, `k₀`, the sample and the path, the goal is
  `XOutput W ω ν E B N L Δ κ₁ m r T nw Mi Di τ k` by `change` (checked).
* `xOutput_of_family`: any finite family of output charts with a bound on the number of charts
  of one world met by one terminal observation gives `XOutput`; the lists and the `Fin`
  indexing are built here.
-/

namespace Submission.Lib.K4XInterface

open MeasureTheory

/-- A path chart re-framed by row functionals `f` (`Q₂ = f⁻¹`), on measurable sub-assignments in
format: the test, depth and block are kept (paper Prop. 4.11, strip conversion). -/
theorem gchart_reframe {Nk : ℝ} {M M' D D' : ℕ} {κ κ' : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A A' : Set (ℕ × (Fin 6 → ℝ))}
    {F F' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex) (hNk : 1 ≤ Nk) (hM : M ≤ M')
    (hD : D ≤ D') (hκ : 0 < κ) (hκκ : κ ≤ κ') (hBv : 0 ≤ Bv)
    (f : Matrix (Fin 2) (Fin 2) ℝ) (hf : f.det ≠ 0) (c₂ u₂ : EuclideanSpace ℝ (Fin 2))
    {a b : ℝ} (hab : a + b ≤ κ')
    (hrows : ∀ l ∈ A', ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T),
      |f 0 0 * (gy l t - c₂ - t • u₂) 0 + f 0 1 * (gy l t - c₂ - t • u₂) 1| ≤ a ∧
      |f 1 0 * (gy l t - c₂ - t • u₂) 0 + f 1 1 * (gy l t - c₂ - t • u₂) 1| ≤ b)
    (hcu : ‖c₂‖ + ‖u₂‖ ≤ Nk ^ M')
    (hfr : (∑ e : Fin 2, ∑ e' : Fin 2, (|f⁻¹ e e'| + |(f⁻¹)⁻¹ e e'|)) ≤ Nk ^ M')
    (hfs : (∑ e : Fin 2, ∑ e' : Fin 2, |f⁻¹ e e'|) ≤ κ' / (2 : ℝ) ^ T)
    (hA : A' ⊆ A) (hF : F' ⊆ F) (hF'A' : ∀ p ∈ F', p.1 ∈ A')
    (hmA : MeasurableSet A') (hmF : MeasurableSet F')
    (hfmt : ∀ i, gfmt 6 (Nk ^ M') D' {x | (i, x) ∈ A'} ∧
      gfmt 7 (Nk ^ M') D' {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F'})
    (hex : ex') : gchart Nk M' D' κ' T j r Bv Ev c₂ u₂ f⁻¹ R A' F' ex' := by
  have hm := gchart_mono h hNk hM hD hκ hκκ hBv (fun _ => hex)
  obtain ⟨-, -, -, -, hdeg, hcoef, -, -, -, hAl, hFp, -⟩ := hm
  have hdet : (f⁻¹).det ≠ 0 := by
    rw [det_inv_fin2]
    exact inv_ne_zero hf
  refine ⟨hdet, hcu, hfr, hfs, hdeg, hcoef, hmA, hmF, hfmt, ?_, ?_, hex⟩
  · intro l hl
    obtain ⟨h1, h2, h3⟩ := hAl l (hA hl)
    refine ⟨h1, h2, fun t ht => ⟨?_, (h3 t ht).2⟩⟩
    rw [inv_inv_of_det_ne_zero f hf]
    obtain ⟨r0, r1⟩ := hrows l hl t ht
    exact (norm_le_of_rows f _ r0 r1).trans hab
  · intro p hp
    obtain ⟨b1, -, b3, b4⟩ := hFp p (hF hp)
    exact ⟨b1, hF'A' p hp, b3, b4⟩

/-- The frozen output of the interface X at sample `k` (an excluded improvement), with the
frozen lambdas replaced by `gchart`, `gobs`, `gδ`. -/
def XOutput (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ)
    (N : ℕ → ℝ) (L Δ κ₁ : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (Mi Di : ℕ)
    (τ : ℝ) (k : ℕ) : Prop :=
  ∃ (r₂ : ℝ) (T₂ C₂ : ℕ) (γ₂ : Fin C₂ → Fin (W k)) (j₂ : Fin C₂ → Fin (2 ^ T₂))
    (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2)) (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ)
    (R₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ) (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ)))
    (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst₂ : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
    r₂ + Δ * L ≤ L ∧
    ((Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ N k ^ (κ₁ * Δ * L / 2)) ∨ ∃ i, i < m ∧
      ((r i + Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * N k ^ (κ₁ * Δ * L / 2)) ∨
        (r₂ = r i ∧ T₂ = T i ∧
          ∀ b, |Matrix.det (Q₂ b)| * (4 : ℝ) ^ T₂ ≤ N k ^ (-(nw i + Δ * L))))) ∧
    (C₂ : ℝ) ≤ N k ^ Mi ∧
    (∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b')) ∧
    (∀ γ₁ o, ((lst₂ γ₁ o).card : ℝ) ≤ N k ^ τ) ∧
    (∀ b, gchart (N k) Mi Di (N k ^ τ) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B k (γ₂ b)) (E k (γ₂ b))
      (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b)
      (∀ p ∈ F₂ b, b ∈ lst₂ (γ₂ b) (gobs (B k (γ₂ b)) (gδ (N k) L) p))) ∧
    ENNReal.ofReal (N k ^ (-τ)) ≤
      ∑ b, ENNReal.ofReal (ω k (γ₂ b)) * ((ν k (γ₂ b)).prod volume) (F₂ b)

open Classical in
/-- Assembling an excluded improvement from any finite family of charts: the lists are the
charts of a world met by an observation, so it suffices to bound that multiplicity. -/
theorem xOutput_of_family {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : (k : ℕ) → Fin (W k) → ℝ}
    {N : ℕ → ℝ} {L Δ κ₁ : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {Mi Di : ℕ}
    {τ : ℝ} {k : ℕ} {ι : Type} [Fintype ι] (r₂ : ℝ) (T₂ : ℕ) (γ₂ : ι → Fin (W k))
    (j₂ : ι → Fin (2 ^ T₂)) (c₂ u₂ : ι → EuclideanSpace ℝ (Fin 2))
    (Q₂ : ι → Matrix (Fin 2) (Fin 2) ℝ) (R₂ : ι → MvPolynomial (Fin 4) ℝ)
    (A₂ : ι → Set (ℕ × (Fin 6 → ℝ))) (F₂ : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hdepth : r₂ + Δ * L ≤ L)
    (himp : (Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ N k ^ (κ₁ * Δ * L / 2)) ∨ ∃ i, i < m ∧
      ((r i + Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * N k ^ (κ₁ * Δ * L / 2)) ∨
        (r₂ = r i ∧ T₂ = T i ∧
          ∀ b, |Matrix.det (Q₂ b)| * (4 : ℝ) ^ T₂ ≤ N k ^ (-(nw i + Δ * L)))))
    (hcard : (Fintype.card ι : ℝ) ≤ N k ^ Mi)
    (hdisj : ∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b'))
    (hmult : ∀ γ₁ o, ((Finset.univ.filter (fun b => γ₂ b = γ₁ ∧
      ∃ p ∈ F₂ b, gobs (B k γ₁) (gδ (N k) L) p = o)).card : ℝ) ≤ N k ^ τ)
    (hchart : ∀ b, gchart (N k) Mi Di (N k ^ τ) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B k (γ₂ b))
      (E k (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) True)
    (hmass : ENNReal.ofReal (N k ^ (-τ)) ≤
      ∑ b, ENNReal.ofReal (ω k (γ₂ b)) * ((ν k (γ₂ b)).prod volume) (F₂ b)) :
    XOutput W ω ν E B N L Δ κ₁ m r T nw Mi Di τ k := by
  set e := Fintype.equivFin ι
  let lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin (Fintype.card ι)) :=
    fun γ₁ o => (Finset.univ.filter (fun b => γ₂ b = γ₁ ∧
      ∃ p ∈ F₂ b, gobs (B k γ₁) (gδ (N k) L) p = o)).map e.toEmbedding
  refine ⟨r₂, T₂, Fintype.card ι, γ₂ ∘ e.symm, j₂ ∘ e.symm, c₂ ∘ e.symm, u₂ ∘ e.symm,
    Q₂ ∘ e.symm, R₂ ∘ e.symm, A₂ ∘ e.symm, F₂ ∘ e.symm, lst, hdepth, ?_, hcard, ?_, ?_, ?_, ?_⟩
  · rcases himp with h | ⟨i, hi, h | ⟨h1, h2, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, Or.inl h⟩
    · exact Or.inr ⟨i, hi, Or.inr ⟨h1, h2, fun b => h3 (e.symm b)⟩⟩
  · intro b b' hbb' hγ hj
    exact hdisj (e.symm b) (e.symm b') (fun h => hbb' (e.symm.injective h)) hγ hj
  · intro γ₁ o
    simp only [lst, Finset.card_map]
    exact hmult γ₁ o
  · intro b
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hchart (e.symm b)
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
    intro p hp
    simp only [lst, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply]
    exact ⟨e.symm b, ⟨rfl, p, hp, rfl⟩, e.apply_symm_apply b⟩
  · calc ENNReal.ofReal (N k ^ (-τ)) ≤ _ := hmass
      _ = ∑ b, ENNReal.ofReal (ω k ((γ₂ ∘ e.symm) b)) *
            ((ν k ((γ₂ ∘ e.symm) b)).prod volume) ((F₂ ∘ e.symm) b) :=
          (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

end Submission.Lib.K4XInterface
