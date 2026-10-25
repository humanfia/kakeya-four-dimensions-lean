import Mathlib
import ChallengeDeps

/-! Names for the literal scalar fields and predicates of o166. The four
proposed children expand these definitions using closed lambda applications. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Stages

noncomputable section

def Data :=
  (Σ W:ℕ → ℕ,(ℕ → ℝ)×(ℕ → ℝ)×ℕ×ℕ×ℝ×ℝ×ℝ×ℝ×((k:ℕ) → Fin (W k) → ℝ)×((k:ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ×(Fin 5 → ℝ)))×((k:ℕ) → Fin (W k) → Set ((ℕ×(Fin 5 → ℝ))×ℝ))×((k:ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ)×ℤ) → ENNReal)×((k:ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ)×ℤ)×ℤ) → ENNReal)×(ℝ → ℝ))

def W : Data → ℕ → ℕ :=
  (fun p => p.1)

def N : Data → ℕ → ℝ :=
  (fun p => p.2.1)

def K : Data → ℕ → ℝ :=
  (fun p => p.2.2.1)

def M : Data → ℕ :=
  (fun p => p.2.2.2.1)

def D : Data → ℕ :=
  (fun p => p.2.2.2.2.1)

def L : Data → ℝ :=
  (fun p => p.2.2.2.2.2.1)

def d : Data → ℝ :=
  (fun p => p.2.2.2.2.2.2.1)

def S : Data → ℝ :=
  (fun p => p.2.2.2.2.2.2.2.1)

def U : Data → ℝ :=
  (fun p => p.2.2.2.2.2.2.2.2.1)

def omega : (p : Data) → (k : ℕ) → Fin (W p k) → ℝ :=
  (fun p => p.2.2.2.2.2.2.2.2.2.1)

def nu : (p : Data) → (k : ℕ) → Fin (W p k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ)) :=
  (fun p => p.2.2.2.2.2.2.2.2.2.2.1)

def E : (p : Data) → (k : ℕ) → Fin (W p k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  (fun p => p.2.2.2.2.2.2.2.2.2.2.2.1)

def rho : (p : Data) → (k : ℕ) → Fin (W p k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal :=
  (fun p => p.2.2.2.2.2.2.2.2.2.2.2.2.1)

def rhoA : (p : Data) → (k : ℕ) → Fin (W p k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal :=
  (fun p => p.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

def f : Data → ℝ → ℝ :=
  (fun p => p.2.2.2.2.2.2.2.2.2.2.2.2.2.2)

def pack : (Σ W:ℕ → ℕ,(ℕ → ℝ)×(ℕ → ℝ)×ℕ×ℕ×ℝ×ℝ×ℝ×ℝ×((k:ℕ) → Fin (W k) → ℝ)×((k:ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ×(Fin 5 → ℝ)))×((k:ℕ) → Fin (W k) → Set ((ℕ×(Fin 5 → ℝ))×ℝ))×((k:ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ)×ℤ) → ENNReal)×((k:ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ)×ℤ)×ℤ) → ENNReal)×(ℝ → ℝ)) → Data :=
  (fun p => p)

def mu : (p:Data) → (k:ℕ) → Fin ((W p) k) → MeasureTheory.Measure ((ℕ×(Fin 5 → ℝ))×ℝ) :=
  (fun p k a => (((nu p) k a).prod MeasureTheory.volume).restrict ((E p) k a))

def y : (ℕ×(Fin 5 → ℝ)) → ℝ → ℝ :=
  (fun l t => l.2 0 + t * l.2 1)

def x : (ℕ×(Fin 5 → ℝ)) → ℝ → ℝ :=
  (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4)

def I : (T:ℕ) → Fin (2 ^ T) → Set ℝ :=
  (fun T j => Set.Icc (((j:ℕ):ℝ) / (2:ℝ) ^ T) ((((j:ℕ):ℝ) + 1) / (2:ℝ) ^ T))

def Format : (n:ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  (fun n B D A => ∃ k:ℕ,(k:ℝ) ≤ B∧∃ p:Fin k → MvPolynomial (Fin n) ℝ,(∀ j,(p j).totalDegree ≤ D∧∀ b,|(p j).coeff b| ≤ B)∧∃ S:Set (Fin k → SignType),A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S})

def RawScalar : Data → Prop :=
  (fun edc => ((∀ k,2 ≤ (N edc) k) ∧ Filter.Tendsto (N edc) Filter.atTop Filter.atTop ∧ ((∀ k,1 ≤ (K edc) k) ∧ ∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,(K edc) k ≤ (N edc) k ^ ε) ∧ 1 ≤ (M edc) ∧ 1 ≤ (D edc) ∧ 0 < (L edc) ∧ 0 ≤ (d edc) ∧ (d edc) < 1 ∧ 0 < (S edc) ∧ 0 < (U edc)) ∧ ((∀ k,(((W edc)) k:ℝ) ≤ (N edc) k ^ ((M edc):ℝ) ∧ (∀ γ,0 ≤ (omega edc) k γ) ∧ (∑ γ,(omega edc) k γ) = 1 ∧ (∀ γ,MeasureTheory.IsProbabilityMeasure ((nu edc) k γ) ∧ (∃ n:ℕ,(n:ℝ) ≤ (N edc) k ^ ((M edc):ℝ) ∧ ∃ (h:Fin n → ℝ) (i:Fin n → ℕ) (B:Fin n → Set (Fin 5 → ℝ)),(∀ j,0 ≤ h j ∧ h j ≤ (N edc) k ^ ((M edc):ℝ) ∧ (i j:ℝ) ≤ (N edc) k ^ ((M edc):ℝ) ∧ Format 5 ((N edc) k ^ ((M edc):ℝ)) (D edc) (B j) ∧ (∀ b ∈ B j,∀ e,|b e| ≤ (N edc) k ^ ((M edc):ℝ))) ∧ (nu edc) k γ = ∑ j,ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j,b)) (MeasureTheory.volume.restrict (B j))) ∧ (∀ᵐ l ∂(nu edc) k γ,∀ e,|l.2 e| ≤ (K edc) k) ∧ MeasurableSet ((E edc) k γ) ∧ (E edc) k γ ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1 ∧ (∀ p ∈ (E edc) k γ,(p.1.1:ℝ) ≤ (N edc) k ^ ((M edc):ℝ)) ∧ (∀ i:ℕ,Format 6 ((N edc) k ^ ((M edc):ℝ)) (D edc) {b:Fin 6 → ℝ | ((i,fun e:Fin 5 => b e.castSucc),b 5) ∈ (E edc) k γ})) ∧ ENNReal.ofReal (((K edc) k)⁻¹) ≤ ∑ γ,ENNReal.ofReal ((omega edc) k γ) * (mu edc) k γ Set.univ)))

def PureProfile : Data → Prop :=
  (fun edc => ((∀ k γ r,0 ≤ r → r ≤ (L edc) → Measurable ((rho edc) k γ r) ∧ MeasureTheory.Measure.map (fun p => ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ))) ((mu edc) k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity ((rho edc) k γ r))) ∧ ((∀ r s:ℝ,0 ≤ r → r ≤ s → s ≤ (L edc) → 0 ≤ (f edc) s - (f edc) r ∧ (f edc) s - (f edc) r ≤ s - r)) ∧ ((∀ r τ:ℝ,0 ≤ r → r ≤ (L edc) → 0 < τ → ∃ c:ℝ,0 < c ∧ ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal ((omega edc) k γ) * (mu edc) k γ {p | (rho edc) k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ)) < ENNReal.ofReal ((N edc) k ^ (-(f edc) r - τ))∨ENNReal.ofReal ((N edc) k ^ (-(f edc) r + τ)) < (rho edc) k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋:ℤ))}) ≤ ENNReal.ofReal ((N edc) k ^ (-c)))))

def JointLaw : Data → Prop :=
  (fun edc : Data => ((∀ k γ u,0 < u → u ≤ (U edc) → Measurable ((rhoA edc) k γ u) ∧ MeasureTheory.Measure.map (fun p => (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-(L edc)))⌋:ℤ)),(⌊p.1.2 1 / ((N edc) k ^ (-u))⌋:ℤ))) ((mu edc) k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity ((rhoA edc) k γ u))))

def TailCap : Data → Prop :=
  (fun edc : Data => ((∀ r:ℝ,0 ≤ r → r ≤ (L edc) → (f edc) (L edc) - (f edc) r ≤ (d edc) * ((L edc) - r))))

def AngularCap : Data → Prop :=
  (fun edc : Data => ((∀ u τ:ℝ,0 < u → u ≤ (U edc) → 0 < τ → ∃ c:ℝ,0 < c ∧ ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal ((omega edc) k γ) * (mu edc) k γ {p | ENNReal.ofReal ((N edc) k ^ (-(f edc) (L edc) - (S edc) * u + τ)) < (rhoA edc) k γ u (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / ((N edc) k ^ (-(L edc)))⌋:ℤ)),(⌊p.1.2 1 / ((N edc) k ^ (-u))⌋:ℤ))}) ≤ ENNReal.ofReal ((N edc) k ^ (-c)))))

def Exact : Data → Prop :=
  (fun edc : Data => RawScalar edc ∧ PureProfile edc ∧ JointLaw edc ∧ TailCap edc ∧ AngularCap edc)

def ChartData : (p:Data) → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → (k:ℕ) → (T n:ℕ) → (Fin n → Fin ((W p) k)) → (Fin n → Fin (2 ^ T)) → (Fin n → Set (ℕ×(Fin 5 → ℝ))) → (Fin n → Set ((ℕ×(Fin 5 → ℝ))×ℝ)) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → MvPolynomial (Fin 2) ℝ) → (Fin ((W p) k) → ((Fin 2 → ℝ)×ℤ) → Finset (Fin n)) → Prop :=
  (fun p B r b h ε isTrue k T n γ j A C u v J P Λ => (2:ℝ) ^ T ≤ (N p) k ^ h∧(n:ℝ) ≤ (N p) k ^ (B:ℝ)∧(∀ i,MeasurableSet (A i)∧MeasurableSet (C i))∧(∀ i i',i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))∧(∀ i,C i ⊆ (E p) k (γ i) ∩ (A i ×ˢ I T (j i)))∧(∀ i,0 < mu p k (γ i) (C i)∧0 < J i∧(J i)⁻¹ ≤ (N p) k ^ (B:ℝ)∧J i ≤ (N p) k ^ ε / (2:ℝ) ^ T∧|u i| + |v i| ≤ (N p) k ^ ε∧(P i).totalDegree ≤ 2∧(∀ a,|(P i).coeff a| ≤ (N p) k ^ (B:ℝ))∧(∀ l ∈ A i,(l.1:ℝ) ≤ (N p) k ^ (B:ℝ)∧∀ e,|l.2 e| ≤ (N p) k ^ ε)∧(∀ z:ℕ,Format 5 ((N p) k ^ (B:ℝ)) B {a | (z,a) ∈ A i})∧(∀ z:ℕ,Format 6 ((N p) k ^ (B:ℝ)) B {a | ((z,fun e:Fin 5 => a e.castSucc),a 5) ∈ C i})∧(∀ l ∈ A i,∀ t ∈ I T (j i),|y l t - u i - t * v i| ≤ (N p) k ^ ε * J i∧|x l t - MvPolynomial.eval ![t,y l t] (P i)| ≤ (N p) k ^ ε * (N p) k ^ (-r))∧(isTrue = true → ENNReal.ofReal ((N p) k ^ (-(f p) r) * J i / ((N p) k ^ ε * (2:ℝ) ^ T)) ≤ mu p k (γ i) (C i)))∧(∀ a z,((Λ a z).card:ℝ) ≤ (N p) k ^ ε)∧(∀ a i,MeasurableSet {z | i ∈ Λ a z})∧(∀ i,mu p k (γ i) {q | q ∈ C i∧i ∉ Λ (γ i) ((![q.2,y q.1 q.2]:Fin 2 → ℝ),(⌊x q.1 q.2 / ((N p) k ^ (-b))⌋:ℤ))} = 0)∧ENNReal.ofReal ((N p) k ^ (-ε)) ≤ ∑ a:Fin ((W p) k),ENNReal.ofReal ((omega p) k a) * mu p k a {q | ∃ i,γ i = a∧q ∈ C i})

def Chart : Data → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → ℕ → Prop :=
  (fun p B r b h ε isTrue k => ∃ (T n:ℕ) (γ:Fin n → Fin ((W p) k)) (j:Fin n → Fin (2 ^ T)) (A:Fin n → Set (ℕ×(Fin 5 → ℝ))) (C:Fin n → Set ((ℕ×(Fin 5 → ℝ))×ℝ)) (u v J:Fin n → ℝ) (P:Fin n → MvPolynomial (Fin 2) ℝ) (Λ:Fin ((W p) k) → ((Fin 2 → ℝ)×ℤ) → Finset (Fin n)),ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)

def Known : Data → ℝ → ℝ → ℝ → Prop :=
  (fun p r b h => 0 ≤ h∧∃ B:ℕ,1 ≤ B∧∀ ε:ℝ,0 < ε → ∃ᶠ k in Filter.atTop,Chart p B r b (h + ε) ε false k)

def Refinement : Data → Data → ℝ → ℝ → ℝ → Prop :=
  (fun p q r b h => ∃ (φ:ℕ → ℕ) (ε:ℕ → ℝ) (B:ℕ) (T:ℕ → ℕ) (γ:(k:ℕ) → Fin ((W q) k) → Fin ((W p) (φ k))) (j:(k:ℕ) → Fin ((W q) k) → Fin (2 ^ T k)) (A:(k:ℕ) → Fin ((W q) k) → Set (ℕ×(Fin 5 → ℝ))) (C:(k:ℕ) → Fin ((W q) k) → Set ((ℕ×(Fin 5 → ℝ))×ℝ)) (u v J:(k:ℕ) → Fin ((W q) k) → ℝ) (P:(k:ℕ) → Fin ((W q) k) → MvPolynomial (Fin 2) ℝ) (Λ:(k:ℕ) → Fin ((W p) (φ k)) → ((Fin 2 → ℝ)×ℤ) → Finset (Fin ((W q) k))) (θ:(k:ℕ) → Fin ((W q) k) → (ℕ×(Fin 5 → ℝ)) → (ℕ×(Fin 5 → ℝ))),(fun dt:ℕ → ℝ => (fun t₀:(k:ℕ) → Fin ((W q) k) → ℝ => StrictMono φ∧(∀ k,0 < ε k)∧Filter.Tendsto ε Filter.atTop (nhds 0)∧1 ≤ B∧(∀ k,(N q) k = (N p) (φ k)∧ChartData p B r b (h + ε k) (ε k) false (φ k) (T k) ((W q) k) (γ k) (j k) (A k) (C k) (u k) (v k) (J k) (P k) (Λ k))∧(∀ k i,Measurable (θ k i)∧(∀ l,(θ k i l).1 = l.1)∧(∀ l t,y (θ k i l) ((t - t₀ k i) / dt k) = (y l t - u k i - t * v k i) / J k i)∧(∀ l t,x (θ k i l) ((t - t₀ k i) / dt k) = (x l t - MvPolynomial.eval ![t,y l t] (P k i)) / (N p) (φ k) ^ (-r))∧(nu q) k i = ((nu p) (φ k) (γ k i) (A k i))⁻¹ • MeasureTheory.Measure.map (θ k i) (((nu p) (φ k) (γ k i)).restrict (A k i))∧mu q k i = (ENNReal.ofReal (dt k) * (nu p) (φ k) (γ k i) (A k i))⁻¹ • MeasureTheory.Measure.map (fun z => (θ k i z.1,(z.2 - t₀ k i) / dt k)) ((mu p (φ k) (γ k i)).restrict (C k i)))∧(∀ k,(fun Z:ℝ => 0 < Z∧∀ i,(omega q) k i = ((omega p) (φ k) (γ k i) * dt k * ((nu p) (φ k) (γ k i) (A k i)).toReal) / Z) (∑ i:Fin ((W q) k),(omega p) (φ k) (γ k i) * dt k * ((nu p) (φ k) (γ k i) (A k i)).toReal))) (fun k i => (((j k i:Fin (2 ^ T k)):ℕ):ℝ) * dt k)) (fun k => ((2:ℝ) ^ T k)⁻¹))

def PureHomogenization : Prop :=
  (∀ p : Data, RawScalar p → ∃ (φ : ℕ → ℕ) (K' : ℕ → ℝ) (M' D' : ℕ) (E' : (k : ℕ) → Fin (W p (φ k)) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (ρ' : (k : ℕ) → Fin (W p (φ k)) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal) (F : ℝ → ℝ), (fun q : Data => StrictMono φ ∧ (∀ k γ, E' k γ ⊆ E p (φ k) γ) ∧ RawScalar q ∧ PureProfile q) (pack ⟨(fun k => W p (φ k)), (fun k => N p (φ k)), K', M', D', L p, d p, S p, U p, (fun k => omega p (φ k)), (fun k => nu p (φ k)), E', ρ', (fun _ _ _ _ => 0), F⟩))

def withJoint : (p : Data) → ((k : ℕ) → Fin (W p k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) → Data :=
  (fun p a => pack ⟨W p, N p, K p, M p, D p, L p, d p, S p, U p, omega p, nu p, E p, rho p, a, f p⟩)

def RawRefinement : Prop :=
  ∀ (p : Data) (r b h d' : ℝ), RawScalar p → 0 ≤ r → r < L p → r ≤ b → b ≤ L p → 0 ≤ d' → d' < 1 → Known p r b h → ∃ q : Data, RawScalar q ∧ L q = L p - r ∧ d q = d' ∧ S q = S p ∧ U q = U p * (L p - r) / L p ∧ Refinement p q r b h

def PureRestriction : Prop :=
  PureHomogenization → ∀ (p q : Data) (r b h : ℝ), RawScalar p → RawScalar q → 0 ≤ r → r < L p → r ≤ b → b ≤ L p → Refinement p q r b h → ∃ q' : Data, RawScalar q' ∧ PureProfile q' ∧ L q' = L q ∧ d q' = d q ∧ S q' = S q ∧ U q' = U q ∧ Refinement p q' r b h

def RelativeProfiles : Prop :=
  ∀ (p q : Data) (r b h : ℝ), Exact p → RawScalar q → PureProfile q → 0 ≤ r → r < L p → r ≤ b → b ≤ L p → L q = L p - r → Refinement p q r b h → (∀ s : ℝ, 0 ≤ s → s ≤ L q → f q (L q) - f q s ≤ f p (L p) - f p (r + s)) ∧ (b = r → ∀ s : ℝ, 0 ≤ s → s ≤ L q → f q s - f q 0 = f p (r + s) - f p r)

def AngularTransfer : Prop :=
  ∀ (p q : Data) (r b h : ℝ), Exact p → RawScalar q → PureProfile q → 0 ≤ r → r < L p → r ≤ b → b ≤ L p → L q = L p - r → S q = S p → U q = U p * (L p - r) / L p → Refinement p q r b h → ∃ a : (k : ℕ) → Fin (W q k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal, JointLaw (withJoint q a) ∧ AngularCap (withJoint q a)

def Goal : Prop :=
  PureHomogenization → ∀ (p : Data) (r b h d' : ℝ), Exact p → 0 ≤ r → r < L p → r ≤ b → b ≤ L p → 0 ≤ d' → d' < 1 → (∀ s : ℝ, r ≤ s → s ≤ L p → f p (L p) - f p s ≤ d' * (L p - s)) → Known p r b h → ∃ q : Data, Exact q ∧ L q = L p - r ∧ d q = d' ∧ S q = S p ∧ U q = U p * (L p - r) / L p ∧ Refinement p q r b h ∧ (∀ s : ℝ, 0 ≤ s → s ≤ L q → f q (L q) - f q s ≤ f p (L p) - f p (r + s)) ∧ (b = r → ∀ s : ℝ, 0 ≤ s → s ≤ L q → f q s - f q 0 = f p (r + s) - f p r)

end

end Submission.Obl.k4_scalar_normalized_exact_refinement.Stages
