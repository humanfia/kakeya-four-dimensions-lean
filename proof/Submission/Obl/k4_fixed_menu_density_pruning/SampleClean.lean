import Submission.Obl.k4_fixed_menu_density_pruning.Interface

/-!
# The per-sample interface of o209

`SampleClean` is the deterministic statement about ONE late sample that the outer layer
(`Outer.lean`) reduces o209 to: from the path, the unpacked greedy cover (`gcBody`) and
small upper pure-density tails (`upperTail`, each at most `Nk ^ (-ε) / 48`) at the three
fixed depths used by `CleanCover` (the candidate depth `menuDepth L (s i) h δ₀`, the old
depth `menuDepth L (s i) 0 δ₀` and the terminal depth `L`), it gives `CleanCover`.

`gcBody` and `greedyCover_iff_gcBody` follow o194/x0672 (commit 69d09a7b, `Outer.lean`).
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_fixed_menu_density_pruning

open MeasureTheory

noncomputable section

/-- The body of `greedyCover` at fixed witnesses `i h n old R' A' V`. -/
def gcBody (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (B : Fin W → ℝ) (d₁ ρ gain : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Mg Dg : ℕ) (ε : ℝ)
    (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) : Prop :=
i < m∧ gain ≤ h∧ h ≤ 1/8∧ (∃ z:ℕ,h=gain+(z:ℝ)*(ρ*gain))∧ r i+2*h*L ≤ L∧ (n:ℝ) ≤ Nk^Mg∧ (∀ a,lev (old a)=i∧ 0 < ν (γ (old a)) (A (old a))∧ (R' a).totalDegree ≤ 2∧ (∀ e,|(R' a).coeff e| ≤ Nk^Mg)∧ MeasurableSet (A' a)∧ A' a ⊆ A (old a)∧ (∀ q,fmt 6 (Nk^Mg) Dg {z | (q,z) ∈ A' a})∧ (∀ l ∈ A' a,∀ t ∈ Set.Icc ((j (old a):ℝ)/(2:ℝ)^T i) (((j (old a):ℝ)+1)/(2:ℝ)^T i),|MvPolynomial.eval (x l t) (R' a)| ≤ Nk^(4*ρ*gain*L+4*ε)*δ Nk (r i+h*L)∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (R' a))| ≤ Nk^(4*ρ*gain*L+4*ε)*B (γ (old a))∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (R' a)))| ≤ Nk^(4*ρ*gain*L+4*ε)*B (γ (old a))^2/δ Nk (r i+h*L))∧ MeasurableSet (V a)∧ V a ⊆ {p | (∃ b:Fin C,lev b=m - 1∧ γ b=γ (old a)∧ p ∈ F b)∧ p.1 ∈ A' a∧ p.2 ∈ Set.Icc ((j (old a):ℝ)/(2:ℝ)^T i) (((j (old a):ℝ)+1)/(2:ℝ)^T i)∧ B (γ (old a))/Nk^(4*ρ*gain*L+4*ε) ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3:Fin 4) (R' a))|}∧ ENNReal.ofReal (Nk^(-((d₁*h+4*ρ*gain)*L) - 4*ε)/(2:ℝ)^T i)*ν (γ (old a)) (A (old a)) ≤ ((ν (γ (old a))).prod MeasureTheory.volume) (V a))∧ (∀ a a',a ≠ a'→ old a=old a'→ Disjoint (A' a) (A' a'))∧ (∀ b:Fin C,((Finset.univ.filter (fun a=>old a=b)).card:ℝ) ≤ Nk^((d₁*h+4*ρ*gain)*L+4*ε))∧ (∀ a a',a ≠ a'→ γ (old a)=γ (old a')→ Disjoint (V a) (V a'))∧ ENNReal.ofReal (Nk^(-ε)) ≤ ∑ a,ENNReal.ofReal (ω (γ (old a)))*((ν (γ (old a))).prod MeasureTheory.volume) (V a)

theorem greedyCover_iff_gcBody (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ) (d₁ ρ gain : ℝ) (m : ℕ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Mg Dg : ℕ) (ε : ℝ) :
    greedyCover Nk L W ω ν B d₁ ρ gain m r T C lev γ j A F Mg Dg ε ↔
      ∃ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
        (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
        gcBody Nk L W ω ν B d₁ ρ gain m r T C lev γ j A F Mg Dg ε i h n old R' A' V :=
  Iff.rfl

/-- The weighted original mass of the upper pure-density exception at depth `q`, with
tolerance `τ`, of one sample. -/
def upperTail (Nk : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (τ q : ℝ) : ENNReal :=
  ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w))
    {p | ENNReal.ofReal (Nk ^ (-f q + τ)) < g w q (obs (B w) (δ Nk q) p)}

/-- **The per-sample cleaning statement.** One late sample `Nk` of the frozen problem (its
scalar data, its pure-density laws `g` at every depth in `[0, L]`), a path, the unpacked
greedy cover with witnesses `i h n old R' A' V`, and upper pure-density tails at most
`Nk ^ (-ε) / 48` at the candidate depth `menuDepth L (s i) h δ₀`, the old depth
`menuDepth L (s i) 0 δ₀` and the terminal depth `L` give the clean cover. -/
def SampleClean : Prop :=
  ∀ (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (d₁ κ₁ ρ gain δ₀ τ ε σ : ℝ) (m : ℕ) (s : ℕ → ℝ) (Mp Dp Mg Dg : ℕ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ) (lev : Fin C → ℕ)
    (par : Fin C → Fin C) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    2 ≤ Nk → 0 < L → 0 ≤ d₁ → d₁ < 1 → 0 < ρ → ρ ≤ 1 / 4 → 0 < gain → gain ≤ 1 / 8 →
    0 < δ₀ → δ₀ ≤ ρ * gain → 0 < τ → 0 < ε →
    (∀ w, 0 ≤ ω w) → (∑ w, ω w) = 1 →
    (∀ w, IsProbabilityMeasure (ν w) ∧ 0 < B w ∧ MeasurableSet (E w) ∧
      E w ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) →
    (∀ w q, 0 ≤ q → q ≤ L → Measurable (g w q) ∧
      (((ν w).prod volume).restrict (E w)).map (obs (B w) (δ Nk q)) =
        (volume.prod Measure.count).withDensity (g w q)) →
    path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
    gcBody Nk L W ω ν B d₁ ρ gain m r T C lev γ j A F Mg Dg ε i h n old R' A' V →
    upperTail Nk W ω ν E B f g τ (menuDepth L (s i) h δ₀) ≤
      ENNReal.ofReal (Nk ^ (-ε) / 48) →
    upperTail Nk W ω ν E B f g τ (menuDepth L (s i) 0 δ₀) ≤
      ENNReal.ofReal (Nk ^ (-ε) / 48) →
    upperTail Nk W ω ν E B f g τ L ≤ ENNReal.ofReal (Nk ^ (-ε) / 48) →
    CleanCover Nk L W ω ν B f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε

end

end Submission.Obl.k4_fixed_menu_density_pruning
