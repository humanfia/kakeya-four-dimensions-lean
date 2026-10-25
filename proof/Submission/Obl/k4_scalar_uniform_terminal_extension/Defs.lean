import Mathlib
import ChallengeDeps

/-!
Readable names for the frozen tuple and chart predicates of o132.
The definitions below are mere abbreviations of the frozen statement.
-/

namespace Submission.Obl.k4_scalar_uniform_terminal_extension

open MeasureTheory

abbrev Trajectory := ℕ × (Fin 5 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Observation := (Fin 2 → ℝ) × ℤ
abbrev AngularObservation := Observation × ℤ

abbrev Problem := Σ W : ℕ → ℕ,
  (ℕ → ℝ) × (ℕ → ℝ) × ℕ × ℕ × ℝ × ℝ × ℝ × ℝ ×
  ((k : ℕ) → Fin (W k) → ℝ) ×
  ((k : ℕ) → Fin (W k) → Measure Trajectory) ×
  ((k : ℕ) → Fin (W k) → Set Incidence) ×
  ((k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal) ×
  ((k : ℕ) → Fin (W k) → ℝ → AngularObservation → ENNReal) × (ℝ → ℝ)

abbrev W (p : Problem) := p.1
abbrev N (p : Problem) := p.2.1
abbrev K (p : Problem) := p.2.2.1
abbrev M (p : Problem) := p.2.2.2.1
abbrev D (p : Problem) := p.2.2.2.2.1
abbrev L (p : Problem) := p.2.2.2.2.2.1
abbrev d (p : Problem) := p.2.2.2.2.2.2.1
abbrev S (p : Problem) := p.2.2.2.2.2.2.2.1
abbrev U (p : Problem) := p.2.2.2.2.2.2.2.2.1
abbrev ω (p : Problem) := p.2.2.2.2.2.2.2.2.2.1
abbrev ν (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.1
abbrev E (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.1
abbrev ρ (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev ρa (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev f (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2

def y (l : Trajectory) (t : ℝ) : ℝ := l.2 0 + t * l.2 1
def x (l : Trajectory) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

noncomputable def mu : (p : Problem) → (k : ℕ) → Fin (W p k) → Measure Incidence :=
  (fun p k a => (((ν p) k a).prod MeasureTheory.volume).restrict ((E p) k a))

def I : (T : ℕ) → Fin (2 ^ T) → Set ℝ :=
  (fun T j => Set.Icc (((j:ℕ):ℝ) / (2:ℝ) ^ T) ((((j:ℕ):ℝ) + 1) / (2:ℝ) ^ T))

def Format : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  (fun n B D A => ∃ k:ℕ,(k:ℝ) ≤ B ∧
    ∃ p:Fin k → MvPolynomial (Fin n) ℝ,(∀ j,(p j).totalDegree ≤ D ∧
    ∀ b,|(p j).coeff b| ≤ B) ∧
    ∃ S:Set (Fin k → SignType),A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S})

def Exact : Problem → Prop :=
  (fun edc => ((∀ k,2 ≤ (N edc) k) ∧
    Filter.Tendsto (N edc) Filter.atTop Filter.atTop ∧
    ((∀ k,1 ≤ (K edc) k) ∧
    ∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,(K edc) k ≤ (N edc) k ^ ε) ∧
    1 ≤ (M edc) ∧
    1 ≤ (D edc) ∧
    0 < (L edc) ∧
    0 ≤ (d edc) ∧
    (d edc) < 1 ∧
    0 < (S edc) ∧
    0 < (U edc)) ∧
    ((∀ k,((W edc) k:ℝ) ≤ (N edc) k ^ ((M edc):ℝ) ∧
    (∀ γ,0 ≤ (ω edc) k γ) ∧
    (∑ γ,(ω edc) k γ) = 1 ∧
    (∀ γ,MeasureTheory.IsProbabilityMeasure ((ν edc) k γ) ∧
    (∃ n:ℕ,(n:ℝ) ≤ (N edc) k ^ ((M edc):ℝ) ∧
    ∃ (h:Fin n → ℝ) (i:Fin n → ℕ) (B:Fin n → Set (Fin 5 → ℝ)),(∀ j,0 ≤ h j ∧
    h j ≤ (N edc) k ^ ((M edc):ℝ) ∧
    (i j:ℝ) ≤ (N edc) k ^ ((M edc):ℝ) ∧
    Format 5 ((N edc) k ^ ((M edc):ℝ)) (D edc) (B j) ∧
    (∀ b ∈ B j,∀ e,|b e| ≤ (N edc) k ^ ((M edc):ℝ))) ∧
    (ν edc) k γ = ∑ j,ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j,b)) (MeasureTheory.volume.restrict (B j))) ∧
    (∀ᵐ l ∂(ν edc) k γ,∀ e,|l.2 e| ≤ (K edc) k) ∧
    MeasurableSet ((E edc) k γ) ∧
    (E edc) k γ ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1 ∧
    (∀ p ∈ (E edc) k γ,(p.1.1:ℝ) ≤ (N edc) k ^ ((M edc):ℝ)) ∧
    (∀ i:ℕ,Format 6 ((N edc) k ^ ((M edc):ℝ)) (D edc) {b:Fin 6 → ℝ | ((i,fun e:Fin 5 => b e.castSucc),b 5) ∈ (E edc) k γ})) ∧
    ENNReal.ofReal (((K edc) k)⁻¹) ≤ ∑ γ,ENNReal.ofReal ((ω edc) k γ) * (mu edc) k γ Set.univ)) ∧
    ((∀ k γ r,0 ≤ r → r ≤ (L edc) → Measurable ((ρ edc) k γ r) ∧
    MeasureTheory.Measure.map (fun p => ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ))) ((mu edc) k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity ((ρ edc) k γ r))) ∧
    ((∀ k γ u,0 < u → u ≤ (U edc) → Measurable ((ρa edc) k γ u) ∧
    MeasureTheory.Measure.map (fun p => (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-(L edc)))⌋:ℤ)),(⌊p.1.2 1 / ((N edc) k ^ (-u))⌋:ℤ))) ((mu edc) k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity ((ρa edc) k γ u))) ∧
    ((∀ r s:ℝ,0 ≤ r → r ≤ s → s ≤ (L edc) → 0 ≤ (f edc) s - (f edc) r ∧
    (f edc) s - (f edc) r ≤ s - r)) ∧
    ((∀ r τ:ℝ,0 ≤ r → r ≤ (L edc) → 0 < τ → ∃ c:ℝ,0 < c ∧
    ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal ((ω edc) k γ) * (mu edc) k γ {p | (ρ edc) k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ)) < ENNReal.ofReal ((N edc) k ^ (-(f edc) r - τ))∨ENNReal.ofReal ((N edc) k ^ (-(f edc) r + τ)) < (ρ edc) k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ))}) ≤ ENNReal.ofReal ((N edc) k ^ (-c)))) ∧
    ((∀ r:ℝ,0 ≤ r → r ≤ (L edc) → (f edc) (L edc) - (f edc) r ≤ (d edc) * ((L edc) - r))) ∧
    ((∀ u τ:ℝ,0 < u → u ≤ (U edc) → 0 < τ → ∃ c:ℝ,0 < c ∧
    ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal ((ω edc) k γ) * (mu edc) k γ {p | ENNReal.ofReal ((N edc) k ^ (-(f edc) (L edc) - (S edc) * u + τ)) < (ρa edc) k γ u (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-(L edc)))⌋:ℤ)),(⌊p.1.2 1 / ((N edc) k ^ (-u))⌋:ℤ))}) ≤ ENNReal.ofReal ((N edc) k ^ (-c)))))

def ChartData : (p : Problem) → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → (k : ℕ) → (T n : ℕ) → (Fin n → Fin (W p k)) → (Fin n → Fin (2 ^ T)) → (Fin n → Set Trajectory) → (Fin n → Set Incidence) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → MvPolynomial (Fin 2) ℝ) → (Fin (W p k) → Observation → Finset (Fin n)) → Prop :=
  (fun p B r b h ε isTrue k T n γ j A C u v J P Λ => (2:ℝ) ^ T ≤ (N p) k ^ h ∧
    (n:ℝ) ≤ (N p) k ^ (B:ℝ) ∧
    (∀ i,MeasurableSet (A i) ∧
    MeasurableSet (C i)) ∧
    (∀ i i',i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧
    (∀ i,C i ⊆ (E p) k (γ i) ∩ (A i ×ˢ I T (j i))) ∧
    (∀ i,0 < mu p k (γ i) (C i) ∧
    0 < J i ∧
    (J i)⁻¹ ≤ (N p) k ^ (B:ℝ) ∧
    J i ≤ (N p) k ^ ε / (2:ℝ) ^ T ∧
    |u i| + |v i| ≤ (N p) k ^ ε ∧
    (P i).totalDegree ≤ 2 ∧
    (∀ a,|(P i).coeff a| ≤ (N p) k ^ (B:ℝ)) ∧
    (∀ l ∈ A i,(l.1:ℝ) ≤ (N p) k ^ (B:ℝ) ∧
    ∀ e,|l.2 e| ≤ (N p) k ^ ε) ∧
    (∀ z:ℕ,Format 5 ((N p) k ^ (B:ℝ)) B {a | (z,a) ∈ A i}) ∧
    (∀ z:ℕ,Format 6 ((N p) k ^ (B:ℝ)) B {a | ((z,fun e:Fin 5 => a e.castSucc),a 5) ∈ C i}) ∧
    (∀ l ∈ A i,∀ t ∈ I T (j i),|y l t - u i - t * v i| ≤ (N p) k ^ ε * J i ∧
    |x l t - MvPolynomial.eval ![t,y l t] (P i)| ≤ (N p) k ^ ε * (N p) k ^ (-r)) ∧
    (isTrue = true → ENNReal.ofReal ((N p) k ^ (-(f p) r) * J i / ((N p) k ^ ε * (2:ℝ) ^ T)) ≤ mu p k (γ i) (C i))) ∧
    (∀ a z,((Λ a z).card:ℝ) ≤ (N p) k ^ ε) ∧
    (∀ a i,MeasurableSet {z | i ∈ Λ a z}) ∧
    (∀ i,mu p k (γ i) {q | q ∈ C i ∧
    i ∉ Λ (γ i) ((![q.2,y q.1 q.2]:Fin 2 → ℝ),(⌊x q.1 q.2 / ((N p) k ^ (-b))⌋:ℤ))} = 0) ∧
    ENNReal.ofReal ((N p) k ^ (-ε)) ≤ ∑ a:Fin ((W p) k),ENNReal.ofReal ((ω p) k a) * mu p k a {q | ∃ i,γ i = a ∧
    q ∈ C i})

def Chart : Problem → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → ℕ → Prop :=
  (fun p B r b h ε isTrue k => ∃ (T n:ℕ) (γ:Fin n → Fin ((W p) k)) (j:Fin n → Fin (2 ^ T)) (A:Fin n → Set (ℕ×(Fin 5 → ℝ))) (C:Fin n → Set ((ℕ×(Fin 5 → ℝ))×ℝ)) (u v J:Fin n → ℝ) (P:Fin n → MvPolynomial (Fin 2) ℝ) (Λ:Fin ((W p) k) → ((Fin 2 → ℝ)×ℤ) → Finset (Fin n)),ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)

def Known : Problem → ℝ → ℝ → ℝ → Prop :=
  (fun p r b h => 0 ≤ h ∧
    ∃ B:ℕ,1 ≤ B ∧
    ∀ ε:ℝ,0 < ε → ∃ᶠ k in Filter.atTop,Chart p B r b (h + ε) ε false k)

def Cost : Problem → ℝ → Prop :=
  (fun p h => 0 ≤ h ∧
    ∃ B:ℕ,1 ≤ B ∧
    ∀ ε:ℝ,0 < ε → ∃ᶠ k in Filter.atTop,Chart p B (L p) (L p) (h + ε) ε true k)

def TCM : Prop := (∀ (D J:ℕ),1 ≤ D → D < J → ∀ d:ℝ,0 ≤ d → d < 1 → ∃ η:ℝ,0 < η∧∃ N₀:ℝ,2 ≤ N₀∧∀ N:ℝ,N₀ ≤ N → ∀ (n₁ n₂:ℕ) (f₁:Fin n₁ → ℝ → ℝ) (f₂:Fin n₂ → ℝ → ℝ) (π₁:Fin n₁ → ℝ) (π₂:Fin n₂ → ℝ) (μ:MeasureTheory.Measure ((Fin n₁×Fin n₂)×ℝ)),(n₁:ℝ) ≤ N ^ (d + η) → (n₂:ℝ) ≤ N ^ (d + η) → (∀ i:Fin n₁,ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1:ℝ) 2)) → (∀ i:Fin n₂,ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1:ℝ) 2)) → (∀ (i:Fin n₁) (j:ℕ),j ≤ J + 1 → ∀ t ∈ Set.Icc (0:ℝ) 1,|iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i:Fin n₂) (j:ℕ),j ≤ J + 1 → ∀ t ∈ Set.Icc (0:ℝ) 1,|iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i:Fin n₁,0 ≤ π₁ i) → (∀ i:Fin n₂,0 ≤ π₂ i) → (∑ i:Fin n₁,π₁ i) = 1 → (∑ i:Fin n₂,π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i:Fin n₁) (E:Set ℝ),MeasurableSet E → μ {p | p.1.1 = i∧p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i:Fin n₂) (E:Set ℝ),MeasurableSet E → μ {p | p.1.2 = i∧p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0:ℝ) 1∧|f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η)∧∃ j:ℕ,1 ≤ j∧j ≤ D∧N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0)

def Extension : Prop :=
  ∀ d₀ S₀ η : ℝ, 0 ≤ d₀ → d₀ < 1 → 0 < S₀ → 0 < η →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ p : Problem,
      Exact p → d p ≤ d₀ → S p = S₀ → U p = η * L p →
      ∀ h e : ℝ, 0 < h → Cost p h → 0 < e → e < h → e < c * L p →
      ∃ r : ℝ, 0 < r ∧ r < L p ∧ L p - r ≤ C * e ∧ Known p r (L p) (h - e)

end Submission.Obl.k4_scalar_uniform_terminal_extension
