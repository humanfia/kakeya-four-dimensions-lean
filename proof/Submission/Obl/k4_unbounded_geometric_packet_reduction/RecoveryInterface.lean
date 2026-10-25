import Submission.Lib.K4XInterface.Basic

/-! Named copies of the scalar-law predicates in the frozen o178 statement. -/

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open Submission.Lib.K4XInterface

set_option linter.unusedVariables false

noncomputable section

def PairedFullTimeBinning : Prop :=
  ∃ C:ℕ,2 ≤ C∧∀ (α:Type) [MeasurableSpace α] (ν:MeasureTheory.Measure α) (E:Set (α × ℝ)) (b v:α→ EuclideanSpace ℝ (Fin 2)) (n:ℕ) (normal:Fin n→ EuclideanSpace ℝ (Fin 2)) (intercept speed:Fin n→ ℝ) (tag:α × ℝ→ Fin n) (O:α × ℝ→ EuclideanSpace ℝ (Fin 3) × ℤ) (lst:(EuclideanSpace ℝ (Fin 3) × ℤ)→ Finset (Fin n)) (K H g:ℝ),MeasureTheory.IsProbabilityMeasure ν→ MeasurableSet E→ E ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1→ Measurable b→ Measurable v→ Measurable tag→ Measurable O→ (∀ i,‖normal i‖ = 1∧ |intercept i| + |speed i| ≤ K)→ (∀ o,((lst o).card:ℝ) ≤ K)→ (∀ i,MeasurableSet {o | i ∈ lst o})→ (∀ p ∈ E,tag p ∈ lst (O p)∧‖b p.1‖ + ‖v p.1‖ ≤ K∧ |inner ℝ (normal (tag p)) (b p.1) - intercept (tag p)| ≤ K * g∧ |inner ℝ (normal (tag p)) (v p.1) - speed (tag p)| ≤ K * g)→ 2 ≤ K→ (C:ℝ) * K ^ 2 ≤ H→ 0 < g→ g * H ^ 2 ≤ 1→ (fun (μ:MeasureTheory.Measure (α × ℝ)) (pair:MeasureTheory.Measure (α × (ℝ × ℝ))) (bin:Fin n→ Fin 4→ ℤ) => 0 < μ Set.univ→ pair {p | (p.1,p.2.1) ∈ E∧(p.1,p.2.2) ∈ E∧g * H < min ‖normal (tag (p.1,p.2.1)) - normal (tag (p.1,p.2.2))‖ ‖normal (tag (p.1,p.2.1)) + normal (tag (p.1,p.2.2))‖} ≤ ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4)→ ∃ (t₀:ℝ) (m:ℕ) (rep:Fin m→ Fin n) (A:Fin m→ Set α) (L:(EuclideanSpace ℝ (Fin 3) × ℤ)→ Finset (Fin m)),t₀ ∈ Set.Icc (0:ℝ) 1∧(m:ℝ) ≤ ((C:ℝ) * K / (g * H ^ 2)) ^ C∧Function.Injective (fun i => bin (rep i))∧(∀ i,A i = {l | (l,t₀) ∈ E∧bin (tag (l,t₀)) = bin (rep i)})∧(∀ i,MeasurableSet (A i))∧(∀ i j,i ≠ j→ Disjoint (A i) (A j))∧(∀ i l,l ∈ A i→ ∀ t ∈ Set.Icc (0:ℝ) 1,|inner ℝ (normal (rep i)) (b l + t • v l) - intercept (rep i) - t * speed (rep i)| ≤ (C:ℝ) * K * (g * H ^ 2))∧(∀ o,((L o).card:ℝ) ≤ (C:ℝ) * K)∧(∀ i,MeasurableSet {o | i ∈ L o})∧ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4) ≤ μ {p | ∃ i,p.1 ∈ A i∧i ∈ L (O p)}) ((ν.prod MeasureTheory.volume).restrict E) (ν.prod (MeasureTheory.volume.prod MeasureTheory.volume)) (fun i => ![⌊normal i 0 / (g * H ^ 2)⌋,⌊normal i 1 / (g * H ^ 2)⌋,⌊intercept i / (g * H ^ 2)⌋,⌊speed i / (g * H ^ 2)⌋])

def StableNativeOscillation : Prop :=
  ∀ A:ℕ,∃ C:ℕ,1 ≤ C∧∀ (K a:ℝ) (P S:MvPolynomial (Fin 4) ℝ) (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 4))),2 ≤ K→ 0 < a→ a ≤ 1→ P.totalDegree ≤ 2→ S.totalDegree ≤ 2→ MeasureTheory.IsProbabilityMeasure μ→ (fun base:EuclideanSpace ℝ (Fin 4)→ EuclideanSpace ℝ (Fin 3) => MeasureTheory.Measure.map base μ ≤ ENNReal.ofReal K • MeasureTheory.volume→ (∀ᵐ p ∂μ,‖base p‖ ≤ K∧ |MvPolynomial.eval (fun i => p i) P| ≤ K * a∧K⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) P)|∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) P)| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) P))| ≤ K / a∧ |MvPolynomial.eval (fun i => p i) S| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) S)| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) S))| ≤ K)→ ∃ (n:ℕ) (E:Fin n→ Set (EuclideanSpace ℝ (Fin 4))),(n:ℝ) ≤ K ^ C∧(∀ i,MeasurableSet (E i))∧(∀ i j,i ≠ j→ Disjoint (E i) (E j))∧μ (⋃ i,E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹)∧∀ i p,p ∈ E i→ ∀ q,q ∈ E i→ |MvPolynomial.eval (fun j => p j) S - MvPolynomial.eval (fun j => q j) S| ≤ K ^ C * (a + ‖base p - base q‖)) (fun p => WithLp.toLp 2 ![p 0,p 1,p 2])

def scalarY : ∀ (b:Fin 5→ ℝ) (t:ℝ),ℝ :=
  fun b t => b 0 + t * b 1

def scalarZ : ∀ (b:Fin 5→ ℝ) (t σ:ℝ),Fin 2→ ℤ :=
  fun b t σ => ![⌊t / σ⌋,⌊scalarY b t / σ⌋]

def scalarX : ∀ (b:Fin 5→ ℝ) (t:ℝ),ℝ :=
  fun b t => b 2 + t * b 3 + t ^ 2 * b 4

def ScalarAdmissible : ∀ {α:Type} [MeasurableSpace α] (N η d s m C S U c:ℝ) (ν:MeasureTheory.Measure α) (b:α→ Fin 5→ ℝ) (μ:MeasureTheory.Measure (α × ℝ)),Prop :=
  fun {α} [inst₀:MeasurableSpace α] N η d s m C S U c ν b μ => Measurable b∧MeasureTheory.IsProbabilityMeasure ν∧μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume)∧μ (Set.univ ×ˢ Set.Icc (0:ℝ) 1)ᶜ = 0∧(∀ l i,|b l i| ≤ N ^ η)∧N ^ (-C) ≤ c∧c ≤ N ^ C∧(∀ (r:ℝ) (q:Fin 2→ ℤ) (j:ℤ),0 ≤ r→ r ≤ s→ μ {p | scalarZ (b p.1) p.2 (N ^ (-m)) = q∧⌊scalarX (b p.1) p.2 / N ^ (-r)⌋ = j} ≤ ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d))∧(∃ F:Finset ((Fin 2→ ℤ) × ℤ),(F.card:ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ η * c⁻¹ * (N ^ (-s)) ^ (-d)∧∀ᵐ p ∂μ,(scalarZ (b p.1) p.2 (N ^ (-m)),⌊scalarX (b p.1) p.2 / N ^ (-s)⌋) ∈ F)∧(∀ (r:ℝ) (q:Fin 2→ ℤ) (j k:ℤ),0 < r→ r ≤ U→ μ {p | scalarZ (b p.1) p.2 (N ^ (-m)) = q∧⌊scalarX (b p.1) p.2 / N ^ (-s)⌋ = j∧⌊b p.1 1 / N ^ (-r)⌋ = k} ≤ ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * c * (N ^ (-s)) ^ d * N ^ (-S * r)))

def ProjectedScalarLaw : ∀ (N η d s m S U:ℝ) (ν:MeasureTheory.Measure (ℕ × (Fin 6→ ℝ))) (μ:MeasureTheory.Measure ((ℕ × (Fin 6→ ℝ)) × ℝ)) (b:(ℕ × (Fin 6→ ℝ))→ Fin 5→ ℝ),Prop :=
  fun N η d s m S U ν μ b => ScalarAdmissible N η d s m 1 S U 1 ν b μ∧∀ (r:ℝ) (j:ℤ) (E:Set (EuclideanSpace ℝ (Fin 2))),0 ≤ r→ r ≤ s→ MeasurableSet E→ μ {p | WithLp.toLp 2 ![p.2,scalarY (b p.1) p.2] ∈ E∧⌊scalarX (b p.1) p.2 / (N ^ (-r))⌋ = j} ≤ ENNReal.ofReal (N ^ η * (N ^ (-r)) ^ d) * MeasureTheory.volume E

def FixedBudgetRecovery : Prop :=
  ∀ d s m S U:ℝ,0 ≤ d→ d < 1→ 0 < s→ s < 1→ s < m→ 0 < S→ 0 < U→ U < m→ ∃ c:ℝ,0 < c∧c < min s 1∧∃ M D:ℕ,1 ≤ M∧∀ ε:ℝ,0 < ε→ ε ≤ 1→ ∃ η:ℝ,0 < η∧∃ N₀:ℝ,2 ≤ N₀∧∀ N:ℝ,N₀ ≤ N→ ∀ (ν:MeasureTheory.Measure (ℕ × (Fin 6→ ℝ))) (μ:MeasureTheory.Measure ((ℕ × (Fin 6→ ℝ)) × ℝ)) (b:(ℕ × (Fin 6→ ℝ))→ Fin 5→ ℝ) (O:((ℕ × (Fin 6→ ℝ)) × ℝ)→ EuclideanSpace ℝ (Fin 3) × ℤ) (base:(EuclideanSpace ℝ (Fin 3) × ℤ)→ EuclideanSpace ℝ (Fin 2)) (signal:(EuclideanSpace ℝ (Fin 3) × ℤ)→ ℝ),ProjectedScalarLaw N η d s m S U ν μ b→ ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ→ Measurable O→ Measurable base→ Measurable signal→ (∀ᵐ p ∂μ,base (O p) = WithLp.toLp 2 ![p.2,scalarY (b p.1) p.2]∧ |scalarX (b p.1) p.2 - signal (O p)| ≤ N ^ (-1 + η))→ ∃ (n:ℕ) (P:Fin n→ MvPolynomial (Fin 2) ℝ) (A:Fin n→ Set (Fin 5→ ℝ)) (lst:(EuclideanSpace ℝ (Fin 3) × ℤ)→ Finset (Fin n)),(n:ℝ) ≤ N ^ (d * s + ε)∧(∀ i,(P i).totalDegree ≤ 2∧(∀ e,|(P i).coeff e| ≤ N ^ ε)∧MeasurableSet (A i)∧gfmt 5 (N ^ M) D (A i)∧∀ z ∈ A i,∀ t ∈ Set.Icc (0:ℝ) 1,|scalarX z t - MvPolynomial.eval ![t,scalarY z t] (P i)| ≤ N ^ (-c))∧(∀ i j,i ≠ j→ Disjoint (A i) (A j))∧(∀ o,(lst o).card ≤ M)∧(∀ i,MeasurableSet {o | i ∈ lst o})∧ENNReal.ofReal (1 / 2:ℝ) * μ Set.univ ≤ μ {p | ∃ i,b p.1 ∈ A i∧i ∈ lst (O p)}

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
