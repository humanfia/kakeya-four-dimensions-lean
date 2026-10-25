import Mathlib
import ChallengeDeps

/-! Names for the literal lambda definitions in the frozen statement. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

abbrev Trajectory := ℕ × (Fin 5 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Observation := (Fin 2 → ℝ) × ℤ

abbrev Data := (Σ W:ℕ → ℕ,(ℕ → ℝ)×(ℕ → ℝ)×ℕ×ℕ×ℝ×ℝ×ℝ×ℝ×((k:ℕ) → Fin (W k) → ℝ)×((k:ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ×(Fin 5 → ℝ)))×((k:ℕ) → Fin (W k) → Set ((ℕ×(Fin 5 → ℝ))×ℝ))×((k:ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ)×ℤ) → ENNReal)×((k:ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ)×ℤ)×ℤ) → ENNReal)×(ℝ → ℝ))

abbrev worlds (p : Data) : ℕ → ℕ := p.1
abbrev N (p : Data) : ℕ → ℝ := p.2.1
abbrev K (p : Data) : ℕ → ℝ := p.2.2.1
abbrev M (p : Data) : ℕ := p.2.2.2.1
abbrev D (p : Data) : ℕ := p.2.2.2.2.1
abbrev L (p : Data) : ℝ := p.2.2.2.2.2.1
abbrev d (p : Data) : ℝ := p.2.2.2.2.2.2.1
abbrev S (p : Data) : ℝ := p.2.2.2.2.2.2.2.1
abbrev U (p : Data) : ℝ := p.2.2.2.2.2.2.2.2.1
abbrev weight (p : Data) : (k : ℕ) → Fin (worlds p k) → ℝ := p.2.2.2.2.2.2.2.2.2.1
abbrev prior (p : Data) : (k : ℕ) → Fin (worlds p k) → Measure Trajectory := p.2.2.2.2.2.2.2.2.2.2.1
abbrev event (p : Data) : (k : ℕ) → Fin (worlds p k) → Set Incidence := p.2.2.2.2.2.2.2.2.2.2.2.1
abbrev density (p : Data) : (k : ℕ) → Fin (worlds p k) → ℝ → Observation → ENNReal := p.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev angularDensity (p : Data) : (k : ℕ) → Fin (worlds p k) → ℝ → (Observation × ℤ) → ENNReal := p.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev profile (p : Data) : ℝ → ℝ := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2

noncomputable def mu : (p:Data) → (k:ℕ) → Fin ((p).1 k) → MeasureTheory.Measure (Incidence) :=
  fun p k a => (((prior p) k a).prod MeasureTheory.volume).restrict ((event p) k a)

noncomputable def y : (Trajectory) → ℝ → ℝ :=
  fun l t => l.2 0 + t * l.2 1

noncomputable def x : (Trajectory) → ℝ → ℝ :=
  fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

noncomputable def I : (T:ℕ) → Fin (2 ^ T) → Set ℝ :=
  fun T j => Set.Icc (((j:ℕ):ℝ) / (2:ℝ) ^ T) ((((j:ℕ):ℝ) + 1) / (2:ℝ) ^ T)

noncomputable def Format : (n:ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  fun n B D A => ∃ k:ℕ,(k:ℝ) ≤ B∧∃ p:Fin k → MvPolynomial (Fin n) ℝ,(∀ j,(p j).totalDegree ≤ D∧∀ b,|(p j).coeff b| ≤ B)∧∃ S:Set (Fin k → SignType),A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S}

noncomputable def Exact : Data → Prop :=
  fun edc => ((∀ k,2 ≤ (N edc) k)∧Filter.Tendsto (N edc) Filter.atTop Filter.atTop∧((∀ k,1 ≤ (K edc) k)∧∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,(K edc) k ≤ (N edc) k ^ ε)∧1 ≤ (M edc)∧1 ≤ (D edc)∧0 < (L edc)∧0 ≤ (d edc)∧(d edc) < 1∧0 < (S edc)∧0 < (U edc))∧((∀ k,(((edc).1) k:ℝ) ≤ (N edc) k ^ ((M edc):ℝ)∧(∀ γ,0 ≤ (weight edc) k γ)∧(∑ γ,(weight edc) k γ) = 1∧(∀ γ,MeasureTheory.IsProbabilityMeasure ((prior edc) k γ)∧(∃ n:ℕ,(n:ℝ) ≤ (N edc) k ^ ((M edc):ℝ)∧∃ (h:Fin n → ℝ) (i:Fin n → ℕ) (B:Fin n → Set (Fin 5 → ℝ)),(∀ j,0 ≤ h j∧h j ≤ (N edc) k ^ ((M edc):ℝ)∧(i j:ℝ) ≤ (N edc) k ^ ((M edc):ℝ)∧Format 5 ((N edc) k ^ ((M edc):ℝ)) (D edc) (B j)∧(∀ b ∈ B j,∀ e,|b e| ≤ (N edc) k ^ ((M edc):ℝ)))∧(prior edc) k γ = ∑ j,ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j,b)) (MeasureTheory.volume.restrict (B j)))∧(∀ᵐ l ∂(prior edc) k γ,∀ e,|l.2 e| ≤ (K edc) k)∧MeasurableSet ((event edc) k γ)∧(event edc) k γ ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1∧(∀ p ∈ (event edc) k γ,(p.1.1:ℝ) ≤ (N edc) k ^ ((M edc):ℝ))∧(∀ i:ℕ,Format 6 ((N edc) k ^ ((M edc):ℝ)) (D edc) {b:Fin 6 → ℝ | ((i,fun e:Fin 5 => b e.castSucc),b 5) ∈ (event edc) k γ}))∧ENNReal.ofReal (((K edc) k)⁻¹) ≤ ∑ γ,ENNReal.ofReal ((weight edc) k γ) * (mu edc) k γ Set.univ))∧((∀ k γ r,0 ≤ r → r ≤ (L edc) → Measurable ((density edc) k γ r)∧MeasureTheory.Measure.map (fun p => ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ))) ((mu edc) k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity ((density edc) k γ r)))∧((∀ k γ u,0 < u → u ≤ (U edc) → Measurable ((angularDensity edc) k γ u)∧MeasureTheory.Measure.map (fun p => (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-(L edc)))⌋:ℤ)),(⌊p.1.2 1 / ((N edc) k ^ (-u))⌋:ℤ))) ((mu edc) k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity ((angularDensity edc) k γ u)))∧((∀ r s:ℝ,0 ≤ r → r ≤ s → s ≤ (L edc) → 0 ≤ (profile edc) s - (profile edc) r∧(profile edc) s - (profile edc) r ≤ s - r))∧((∀ r τ:ℝ,0 ≤ r → r ≤ (L edc) → 0 < τ → ∃ c:ℝ,0 < c∧∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal ((weight edc) k γ) * (mu edc) k γ {p | (density edc) k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ)) < ENNReal.ofReal ((N edc) k ^ (-(profile edc) r - τ))∨ENNReal.ofReal ((N edc) k ^ (-(profile edc) r + τ)) < (density edc) k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ))}) ≤ ENNReal.ofReal ((N edc) k ^ (-c))))∧((∀ r:ℝ,0 ≤ r → r ≤ (L edc) → (profile edc) (L edc) - (profile edc) r ≤ (d edc) * ((L edc) - r)))∧((∀ u τ:ℝ,0 < u → u ≤ (U edc) → 0 < τ → ∃ c:ℝ,0 < c∧∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal ((weight edc) k γ) * (mu edc) k γ {p | ENNReal.ofReal ((N edc) k ^ (-(profile edc) (L edc) - (S edc) * u + τ)) < (angularDensity edc) k γ u (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-(L edc)))⌋:ℤ)),(⌊p.1.2 1 / ((N edc) k ^ (-u))⌋:ℤ))}) ≤ ENNReal.ofReal ((N edc) k ^ (-c))))

noncomputable def ChartData : (p:Data) → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → (k:ℕ) → (T n:ℕ) → (Fin n → Fin ((p).1 k)) → (Fin n → Fin (2 ^ T)) → (Fin n → Set (Trajectory)) → (Fin n → Set (Incidence)) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → MvPolynomial (Fin 2) ℝ) → (Fin ((p).1 k) → (Observation) → Finset (Fin n)) → Prop :=
  fun p B r b h ε isTrue k T n γ j A C u v J P Λ => (2:ℝ) ^ T ≤ (N p) k ^ h∧(n:ℝ) ≤ (N p) k ^ (B:ℝ)∧(∀ i,MeasurableSet (A i)∧MeasurableSet (C i))∧(∀ i i',i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))∧(∀ i,C i ⊆ (event p) k (γ i) ∩ (A i ×ˢ I T (j i)))∧(∀ i,0 < mu p k (γ i) (C i)∧0 < J i∧(J i)⁻¹ ≤ (N p) k ^ (B:ℝ)∧J i ≤ (N p) k ^ ε / (2:ℝ) ^ T∧|u i| + |v i| ≤ (N p) k ^ ε∧(P i).totalDegree ≤ 2∧(∀ a,|(P i).coeff a| ≤ (N p) k ^ (B:ℝ))∧(∀ l ∈ A i,(l.1:ℝ) ≤ (N p) k ^ (B:ℝ)∧∀ e,|l.2 e| ≤ (N p) k ^ ε)∧(∀ z:ℕ,Format 5 ((N p) k ^ (B:ℝ)) B {a | (z,a) ∈ A i})∧(∀ z:ℕ,Format 6 ((N p) k ^ (B:ℝ)) B {a | ((z,fun e:Fin 5 => a e.castSucc),a 5) ∈ C i})∧(∀ l ∈ A i,∀ t ∈ I T (j i),|y l t - u i - t * v i| ≤ (N p) k ^ ε * J i∧|x l t - MvPolynomial.eval ![t,y l t] (P i)| ≤ (N p) k ^ ε * (N p) k ^ (-r))∧(isTrue = true → ENNReal.ofReal ((N p) k ^ (-(profile p) r) * J i / ((N p) k ^ ε * (2:ℝ) ^ T)) ≤ mu p k (γ i) (C i)))∧(∀ a z,((Λ a z).card:ℝ) ≤ (N p) k ^ ε)∧(∀ a i,MeasurableSet {z | i ∈ Λ a z})∧(∀ i,mu p k (γ i) {q | q ∈ C i∧i ∉ Λ (γ i) ((![q.2,y q.1 q.2]:Fin 2 → ℝ),(⌊x q.1 q.2 / ((N p) k ^ (-b))⌋:ℤ))} = 0)∧ENNReal.ofReal ((N p) k ^ (-ε)) ≤ ∑ a:Fin ((p).1 k),ENNReal.ofReal ((weight p) k a) * mu p k a {q | ∃ i,γ i = a∧q ∈ C i}

noncomputable def Chart : Data → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → ℕ → Prop :=
  fun p B r b h ε isTrue k => ∃ (T n:ℕ) (γ:Fin n → Fin ((p).1 k)) (j:Fin n → Fin (2 ^ T)) (A:Fin n → Set (Trajectory)) (C:Fin n → Set (Incidence)) (u v J:Fin n → ℝ) (P:Fin n → MvPolynomial (Fin 2) ℝ) (Λ:Fin ((p).1 k) → (Observation) → Finset (Fin n)),ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ

noncomputable def Cost : Data → ℝ → Prop :=
  fun p h => 0 ≤ h∧∃ B:ℕ,1 ≤ B∧∀ ε:ℝ,0 < ε → ∃ᶠ k in Filter.atTop,Chart p B (L p) (L p) (h + ε) ε true k

noncomputable def Initial : Prop :=
  ∀ p:Data,Exact p → Cost p (L p)

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
