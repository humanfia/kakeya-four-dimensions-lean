import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_scalar_chart_normalization

open MeasureTheory Filter
open scoped ENNReal Topology

abbrev Problem := (Σ W:ℕ → ℕ,(ℕ → ℝ)×(ℕ → ℝ)×ℕ×ℕ×ℝ×ℝ×ℝ×ℝ×((k:ℕ) → Fin (W k) → ℝ)×((k:ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ×(Fin 5 → ℝ)))×((k:ℕ) → Fin (W k) → Set ((ℕ×(Fin 5 → ℝ))×ℝ))×((k:ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ)×ℤ) → ENNReal)×((k:ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ)×ℤ)×ℤ) → ENNReal)×(ℝ → ℝ))


namespace Problem

abbrev N (p : Problem) := p.2.1
abbrev K (p : Problem) := p.2.2.1
abbrev M (p : Problem) := p.2.2.2.1
abbrev D (p : Problem) := p.2.2.2.2.1
abbrev L (p : Problem) := p.2.2.2.2.2.1
abbrev d (p : Problem) := p.2.2.2.2.2.2.1
abbrev S (p : Problem) := p.2.2.2.2.2.2.2.1
abbrev U (p : Problem) := p.2.2.2.2.2.2.2.2.1
abbrev w (p : Problem) := p.2.2.2.2.2.2.2.2.2.1
abbrev nu (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.1
abbrev E (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.1
abbrev rho (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev rhoA (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev f (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Problem

noncomputable def mu : (p:Problem) → (k:ℕ) → Fin ((p).1 k) → MeasureTheory.Measure ((ℕ×(Fin 5 → ℝ))×ℝ) :=
  (fun p k a => ((p.nu k a).prod MeasureTheory.volume).restrict (p.E k a))

noncomputable def y : (ℕ×(Fin 5 → ℝ)) → ℝ → ℝ :=
  (fun l t => l.2 0 + t * l.2 1)

noncomputable def x : (ℕ×(Fin 5 → ℝ)) → ℝ → ℝ :=
  (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4)

noncomputable def I : (T:ℕ) → Fin (2 ^ T) → Set ℝ :=
  (fun T j => Set.Icc (((j:ℕ):ℝ) / (2:ℝ) ^ T) ((((j:ℕ):ℝ) + 1) / (2:ℝ) ^ T))

noncomputable def Format : (n:ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  (fun n B D A => ∃ k:ℕ,(k:ℝ) ≤ B ∧
    ∃ p:Fin k → MvPolynomial (Fin n) ℝ,(∀ j,(p j).totalDegree ≤ D ∧
    ∀ b,|(p j).coeff b| ≤ B) ∧
    ∃ S:Set (Fin k → SignType),A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S})

noncomputable def Exact : Problem → Prop :=
  (fun edc => ((∀ k,2 ≤ edc.N k) ∧
    Filter.Tendsto edc.N Filter.atTop Filter.atTop ∧
    ((∀ k,1 ≤ edc.K k) ∧
    ∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,edc.K k ≤ edc.N k ^ ε) ∧
    1 ≤ edc.M ∧
    1 ≤ edc.D ∧
    0 < edc.L ∧
    0 ≤ edc.d ∧
    edc.d < 1 ∧
    0 < edc.S ∧
    0 < edc.U) ∧
    ((∀ k,(((edc).1) k:ℝ) ≤ edc.N k ^ (edc.M:ℝ) ∧
    (∀ γ,0 ≤ edc.w k γ) ∧
    (∑ γ,edc.w k γ) = 1 ∧
    (∀ γ,MeasureTheory.IsProbabilityMeasure (edc.nu k γ) ∧
    (∃ n:ℕ,(n:ℝ) ≤ edc.N k ^ (edc.M:ℝ) ∧
    ∃ (h:Fin n → ℝ) (i:Fin n → ℕ) (B:Fin n → Set (Fin 5 → ℝ)),(∀ j,0 ≤ h j ∧
    h j ≤ edc.N k ^ (edc.M:ℝ) ∧
    (i j:ℝ) ≤ edc.N k ^ (edc.M:ℝ) ∧
    Format 5 (edc.N k ^ (edc.M:ℝ)) edc.D (B j) ∧
    (∀ b ∈ B j,∀ e,|b e| ≤ edc.N k ^ (edc.M:ℝ))) ∧
    edc.nu k γ = ∑ j,ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j,b)) (MeasureTheory.volume.restrict (B j))) ∧
    (∀ᵐ l ∂edc.nu k γ,∀ e,|l.2 e| ≤ edc.K k) ∧
    MeasurableSet (edc.E k γ) ∧
    edc.E k γ ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1 ∧
    (∀ p ∈ edc.E k γ,(p.1.1:ℝ) ≤ edc.N k ^ (edc.M:ℝ)) ∧
    (∀ i:ℕ,Format 6 (edc.N k ^ (edc.M:ℝ)) edc.D {b:Fin 6 → ℝ | ((i,fun e:Fin 5 => b e.castSucc),b 5) ∈ edc.E k γ})) ∧
    ENNReal.ofReal ((edc.K k)⁻¹) ≤ ∑ γ,ENNReal.ofReal (edc.w k γ) * (mu edc) k γ Set.univ)) ∧
    ((∀ k γ r,0 ≤ r → r ≤ edc.L → Measurable (edc.rho k γ r) ∧
    MeasureTheory.Measure.map (fun p => ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-r))⌋:ℤ))) ((mu edc) k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (edc.rho k γ r))) ∧
    ((∀ k γ u,0 < u → u ≤ edc.U → Measurable (edc.rhoA k γ u) ∧
    MeasureTheory.Measure.map (fun p => (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-edc.L))⌋:ℤ)),(⌊p.1.2 1 / (edc.N k ^ (-u))⌋:ℤ))) ((mu edc) k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (edc.rhoA k γ u))) ∧
    ((∀ r s:ℝ,0 ≤ r → r ≤ s → s ≤ edc.L → 0 ≤ edc.f s - edc.f r ∧
    edc.f s - edc.f r ≤ s - r)) ∧
    ((∀ r τ:ℝ,0 ≤ r → r ≤ edc.L → 0 < τ → ∃ c:ℝ,0 < c ∧
    ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal (edc.w k γ) * (mu edc) k γ {p | edc.rho k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-r))⌋:ℤ)) < ENNReal.ofReal (edc.N k ^ (-edc.f r - τ))∨ENNReal.ofReal (edc.N k ^ (-edc.f r + τ)) < edc.rho k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-r))⌋:ℤ))}) ≤ ENNReal.ofReal (edc.N k ^ (-c)))) ∧
    ((∀ r:ℝ,0 ≤ r → r ≤ edc.L → edc.f edc.L - edc.f r ≤ edc.d * (edc.L - r))) ∧
    ((∀ u τ:ℝ,0 < u → u ≤ edc.U → 0 < τ → ∃ c:ℝ,0 < c ∧
    ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal (edc.w k γ) * (mu edc) k γ {p | ENNReal.ofReal (edc.N k ^ (-edc.f edc.L - edc.S * u + τ)) < edc.rhoA k γ u (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-edc.L))⌋:ℤ)),(⌊p.1.2 1 / (edc.N k ^ (-u))⌋:ℤ))}) ≤ ENNReal.ofReal (edc.N k ^ (-c)))))

noncomputable def ChartData : (p:Problem) → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → (k:ℕ) → (T n:ℕ) → (Fin n → Fin ((p).1 k)) → (Fin n → Fin (2 ^ T)) → (Fin n → Set (ℕ×(Fin 5 → ℝ))) → (Fin n → Set ((ℕ×(Fin 5 → ℝ))×ℝ)) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → MvPolynomial (Fin 2) ℝ) → (Fin ((p).1 k) → ((Fin 2 → ℝ)×ℤ) → Finset (Fin n)) → Prop :=
  (fun p B r b h ε isTrue k T n γ j A C u v J P Λ => (2:ℝ) ^ T ≤ p.N k ^ h ∧
    (n:ℝ) ≤ p.N k ^ (B:ℝ) ∧
    (∀ i,MeasurableSet (A i) ∧
    MeasurableSet (C i)) ∧
    (∀ i i',i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧
    (∀ i,C i ⊆ p.E k (γ i) ∩ (A i ×ˢ I T (j i))) ∧
    (∀ i,0 < mu p k (γ i) (C i) ∧
    0 < J i ∧
    (J i)⁻¹ ≤ p.N k ^ (B:ℝ) ∧
    J i ≤ p.N k ^ ε / (2:ℝ) ^ T ∧
    |u i| + |v i| ≤ p.N k ^ ε ∧
    (P i).totalDegree ≤ 2 ∧
    (∀ a,|(P i).coeff a| ≤ p.N k ^ (B:ℝ)) ∧
    (∀ l ∈ A i,(l.1:ℝ) ≤ p.N k ^ (B:ℝ) ∧
    ∀ e,|l.2 e| ≤ p.N k ^ ε) ∧
    (∀ z:ℕ,Format 5 (p.N k ^ (B:ℝ)) B {a | (z,a) ∈ A i}) ∧
    (∀ z:ℕ,Format 6 (p.N k ^ (B:ℝ)) B {a | ((z,fun e:Fin 5 => a e.castSucc),a 5) ∈ C i}) ∧
    (∀ l ∈ A i,∀ t ∈ I T (j i),|y l t - u i - t * v i| ≤ p.N k ^ ε * J i ∧
    |x l t - MvPolynomial.eval ![t,y l t] (P i)| ≤ p.N k ^ ε * p.N k ^ (-r)) ∧
    (isTrue = true → ENNReal.ofReal (p.N k ^ (-p.f r) * J i / (p.N k ^ ε * (2:ℝ) ^ T)) ≤ mu p k (γ i) (C i))) ∧
    (∀ a z,((Λ a z).card:ℝ) ≤ p.N k ^ ε) ∧
    (∀ a i,MeasurableSet {z | i ∈ Λ a z}) ∧
    (∀ i,mu p k (γ i) {q | q ∈ C i ∧
    i ∉ Λ (γ i) ((![q.2,y q.1 q.2]:Fin 2 → ℝ),(⌊x q.1 q.2 / (p.N k ^ (-b))⌋:ℤ))} = 0) ∧
    ENNReal.ofReal (p.N k ^ (-ε)) ≤ ∑ a:Fin ((p).1 k),ENNReal.ofReal (p.w k a) * mu p k a {q | ∃ i,γ i = a ∧
    q ∈ C i})

noncomputable def Chart : Problem → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → ℕ → Prop :=
  (fun p B r b h ε isTrue k => ∃ (T n:ℕ) (γ:Fin n → Fin ((p).1 k)) (j:Fin n → Fin (2 ^ T)) (A:Fin n → Set (ℕ×(Fin 5 → ℝ))) (C:Fin n → Set ((ℕ×(Fin 5 → ℝ))×ℝ)) (u v J:Fin n → ℝ) (P:Fin n → MvPolynomial (Fin 2) ℝ) (Λ:Fin ((p).1 k) → ((Fin 2 → ℝ)×ℤ) → Finset (Fin n)),ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)

noncomputable def Known : Problem → ℝ → ℝ → ℝ → Prop :=
  (fun p r b h => 0 ≤ h ∧
    ∃ B:ℕ,1 ≤ B ∧
    ∀ ε:ℝ,0 < ε → ∃ᶠ k in Filter.atTop,Chart p B r b (h + ε) ε false k)

noncomputable def Cost : Problem → ℝ → Prop :=
  (fun p h => 0 ≤ h ∧
    ∃ B:ℕ,1 ≤ B ∧
    ∀ ε:ℝ,0 < ε → ∃ᶠ k in Filter.atTop,Chart p B p.L p.L (h + ε) ε true k)

noncomputable def Horizon : Problem → ℝ :=
  (fun p => sInf {h:ℝ | Cost p h})

noncomputable def Initial : Prop :=
  (∀ p:Problem,Exact p → Cost p p.L)

noncomputable def Refinement : Problem → Problem → ℝ → ℝ → ℝ → Prop :=
  (fun p q r b h => ∃ (φ:ℕ → ℕ) (ε:ℕ → ℝ) (B:ℕ) (T:ℕ → ℕ) (γ:(k:ℕ) → Fin ((q).1 k) → Fin ((p).1 (φ k))) (j:(k:ℕ) → Fin ((q).1 k) → Fin (2 ^ T k)) (A:(k:ℕ) → Fin ((q).1 k) → Set (ℕ×(Fin 5 → ℝ))) (C:(k:ℕ) → Fin ((q).1 k) → Set ((ℕ×(Fin 5 → ℝ))×ℝ)) (u v J:(k:ℕ) → Fin ((q).1 k) → ℝ) (P:(k:ℕ) → Fin ((q).1 k) → MvPolynomial (Fin 2) ℝ) (Λ:(k:ℕ) → Fin ((p).1 (φ k)) → ((Fin 2 → ℝ)×ℤ) → Finset (Fin ((q).1 k))) (θ:(k:ℕ) → Fin ((q).1 k) → (ℕ×(Fin 5 → ℝ)) → (ℕ×(Fin 5 → ℝ))),(fun dt:ℕ → ℝ => (fun t₀:(k:ℕ) → Fin ((q).1 k) → ℝ => StrictMono φ ∧
    (∀ k,0 < ε k) ∧
    Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    1 ≤ B ∧
    (∀ k,q.N k = p.N (φ k) ∧
    ChartData p B r b (h + ε k) (ε k) false (φ k) (T k) ((q).1 k) (γ k) (j k) (A k) (C k) (u k) (v k) (J k) (P k) (Λ k)) ∧
    (∀ k i,Measurable (θ k i) ∧
    (∀ l,(θ k i l).1 = l.1) ∧
    (∀ l t,y (θ k i l) ((t - t₀ k i) / dt k) = (y l t - u k i - t * v k i) / J k i) ∧
    (∀ l t,x (θ k i l) ((t - t₀ k i) / dt k) = (x l t - MvPolynomial.eval ![t,y l t] (P k i)) / p.N (φ k) ^ (-r)) ∧
    q.nu k i = (p.nu (φ k) (γ k i) (A k i))⁻¹ • MeasureTheory.Measure.map (θ k i) ((p.nu (φ k) (γ k i)).restrict (A k i)) ∧
    mu q k i = (ENNReal.ofReal (dt k) * p.nu (φ k) (γ k i) (A k i))⁻¹ • MeasureTheory.Measure.map (fun z => (θ k i z.1,(z.2 - t₀ k i) / dt k)) ((mu p (φ k) (γ k i)).restrict (C k i))) ∧
    (∀ k,(fun Z:ℝ => 0 < Z ∧
    ∀ i,q.w k i = (p.w (φ k) (γ k i) * dt k * (p.nu (φ k) (γ k i) (A k i)).toReal) / Z) (∑ i:Fin ((q).1 k),p.w (φ k) (γ k i) * dt k * (p.nu (φ k) (γ k i) (A k i)).toReal)))
  (fun k i => (((j k i:Fin (2 ^ T k)):ℕ):ℝ) * dt k)) (fun k => ((2:ℝ) ^ T k)⁻¹))

noncomputable def Calculus : Prop :=
  ((∀ (p:Problem) (α:ℝ),Exact p → 0 < α → ∃ q:Problem,Exact q ∧
    q.L = p.L / α ∧
    q.d = p.d ∧
    q.S = p.S ∧
    q.U = p.U / α ∧
    Horizon q = Horizon p / α ∧
    ∀ r:ℝ,0 ≤ r → r ≤ q.L → q.f r - q.f 0 = (p.f (α * r) - p.f 0) / α) ∧
    (∀ (p:Problem) (r d':ℝ),Exact p → 0 < r → r < p.L → 0 ≤ d' → d' < 1 → (∀ s:ℝ,0 ≤ s → s ≤ r → p.f r - p.f s ≤ d' * (r - s)) → ∃ q:Problem,Exact q ∧
    q.L = r ∧
    q.d = d' ∧
    q.S = p.S ∧
    q.U = p.U * r / p.L ∧
    (∀ s:ℝ,0 ≤ s → s ≤ r → q.f s - q.f 0 = p.f s - p.f 0) ∧
    (∀ h:ℝ,Cost q h → Known p r r h)) ∧
    (∀ (p:Problem) (r b h d':ℝ),Exact p → 0 ≤ r → r < p.L → r ≤ b → b ≤ p.L → 0 ≤ d' → d' < 1 → (∀ s:ℝ,r ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ d' * (p.L - s)) → Known p r b h → ∃ q:Problem,Exact q ∧
    q.L = p.L - r ∧
    q.d = d' ∧
    q.S = p.S ∧
    q.U = p.U * (p.L - r) / p.L ∧
    Refinement p q r b h ∧
    Horizon p ≤ h + Horizon q ∧
    (∀ s:ℝ,0 ≤ s → s ≤ q.L → q.f q.L - q.f s ≤ p.f p.L - p.f (r + s)) ∧
    (b = r → ∀ s:ℝ,0 ≤ s → s ≤ q.L → q.f s - q.f 0 = p.f (r + s) - p.f r)))

end Submission.Obl.k4_scalar_chart_normalization
