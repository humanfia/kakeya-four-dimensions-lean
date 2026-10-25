import Submission.Obl.k4_finite_width_output_exclusion.Models

/-! Names for the immediately applied lambdas of the frozen o197 statement.
The trajectory, problem, chart, horizon, and narrowness predicates are imported
from accepted o153. No hypotheses or conclusions are changed. -/

namespace Submission.Obl.k4_unbounded_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option linter.unusedVariables false
set_option maxRecDepth 4096

def toE : ℝ → ENNReal :=
  fun r₉:ℝ => ENNReal.ofReal r₉

def initialRaw : Prop :=
  ∀ N K L d S η W ω ν E P B f g G,prob N K L d S η W ω ν E P B f g G → ∀ h:ℝ,L < h → term N K L W ω ν E B f h

def widthRaw : ∀ (ds kr S η:ℝ),Prop :=
  fun ds kr S η => ∃ a w:ℝ,0 < a ∧ 0 ≤ w ∧ ∀ t:ℝ,0 < t → ∃ N K d W ω ν E P B f g G,prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < H N K 1 W ω ν E B f ∧ ¬ nt N K 1 W ω ν E B f (kr + a) w

def scalarY : ∀ (b:Fin 5→ ℝ) (t:ℝ),ℝ :=
  fun b t => b 0 + t * b 1

def scalarX : ∀ (b:Fin 5→ ℝ) (t:ℝ),ℝ :=
  fun b t => b 2 + t * b 3 + t ^ 2 * b 4

def nativeCoeff : ∀ (P:MvPolynomial (Fin 4) ℝ) (t₀ q a:ℝ) (v:Fin 3 → ℝ) (A:Set (ℕ × (Fin 6 → ℝ))) (l:(ℕ × (Fin 6 → ℝ))),Fin 5 → ℝ :=
  fun P t₀ q a v A l => @ite (Fin 5 → ℝ) (l ∈ A) (Classical.propDecidable _) (((fun Y => ((fun X => ![Y t₀,Y (t₀ + q) - Y t₀,X t₀,4 * X (t₀ + q / 2) - 3 * X t₀ - X (t₀ + q),2 * (X (t₀ + q) + X t₀ - 2 * X (t₀ + q / 2))]) (fun t:ℝ => MvPolynomial.eval (x l t) P))) (fun t:ℝ => a + ∑ i:Fin 3,v i * x l t i.castSucc))) 0

def BasicScalarLaw : ∀ (N χ d s m S U:ℝ) (ν:MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (μ:MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (b:(ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ),Prop :=
  fun N χ d s m S U ν μ b => Measurable b ∧ MeasureTheory.IsProbabilityMeasure ν ∧ μ ≤ toE (N ^ χ) • (ν.prod MeasureTheory.volume) ∧ μ (Set.univ ×ˢ Set.Icc (0:ℝ) 1)ᶜ = 0 ∧ (∀ l i,|b l i| ≤ N ^ χ)

def base4 : ∀ (p:EuclideanSpace ℝ (Fin 4)),EuclideanSpace ℝ (Fin 3) :=
  fun p => WithLp.toLp 2 ![p 0,p 1,p 2]

def SupportCertificate : ∀ (N χ d s m:ℝ) (C:ℕ) (R:Fin C → ENNReal) (μ:Fin C → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (b:Fin C → (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ),Prop :=
  fun N χ d s m C R μ b => ∃ (J:ℕ) (w:Fin J → ENNReal) (Λ:Fin J → MeasureTheory.Measure (EuclideanSpace ℝ (Fin 4))) (P S:Fin J → MvPolynomial (Fin 4) ℝ) (tag:Fin C → ((ℕ × (Fin 6 → ℝ)) × ℝ) → Fin J) (A:Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (z:Fin C → Fin J → ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 4)),(∑ e,w e) ≤ 1 ∧ 2 ≤ N ^ χ ∧ (∀ e,MeasureTheory.IsProbabilityMeasure (Λ e) ∧ (P e).totalDegree ≤ 2 ∧ (S e).totalDegree ≤ 2 ∧ MeasureTheory.Measure.map base4 (Λ e) ≤ toE (N ^ χ) • MeasureTheory.volume ∧ ∀ᵐ p ∂Λ e,‖base4 p‖ ≤ N ^ χ ∧ |MvPolynomial.eval (fun i => p i) (P e)| ≤ N ^ χ * N ^ (-s + χ) ∧ (N ^ χ)⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (P e))| ∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (P e))| ≤ N ^ χ ∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (P e)))| ≤ N ^ χ / N ^ (-s + χ) ∧ |MvPolynomial.eval (fun i => p i) (S e)| ≤ N ^ χ ∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (S e))| ≤ N ^ χ ∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) (S e)))| ≤ N ^ χ) ∧ (∀ a,0 < R a ∧ Measurable (tag a) ∧ MeasurableSet (A a) ∧ μ a (A a)ᶜ = 0 ∧ ∀ e,Measurable (z a e)) ∧ (∀ e,(∑ a,R a • MeasureTheory.Measure.map (z a e) ((μ a).restrict {p | p ∈ A a ∧ tag a p = e})) ≤ w e • Λ e) ∧ (∀ a p,p ∈ A a → scalarX (b a p.1) p.2 = MvPolynomial.eval (fun i => z a (tag a p) p i) (S (tag a p))) ∧ (∀ a t y,((@Finset.filter (Fin J) (fun e => ∃ p ∈ A a,|p.2 - t| ≤ N ^ (-m) ∧ |scalarY (b a p.1) p.2 - y| ≤ N ^ (-m) ∧ tag a p = e) (fun e => Classical.propDecidable _) (Finset.univ:Finset (Fin J))).card:ℝ) ≤ N ^ (d * s + χ)) ∧ ∀ a p,p ∈ A a → ∀ p',p' ∈ A a → tag a p = tag a p' → |p.2 - p'.2| ≤ N ^ (-m) → |scalarY (b a p.1) p.2 - scalarY (b a p'.1) p'.2| ≤ N ^ (-m) → ‖base4 (z a (tag a p) p) - base4 (z a (tag a p) p')‖ ≤ N ^ (-s + χ)

def NativeSample : ∀ (p₀:Bool) (N K:ℝ) (W:ℕ) (ω:Fin W → ℝ) (ν:Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E:Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (P:Fin W → MvPolynomial (Fin 4) ℝ) (B:Fin W → ℝ) (M D:ℕ) (a₀ w loss h χ d s m S U:ℝ),Prop :=
  fun p₀ N K W ω ν E P B M D a₀ w loss h χ d s m S U => ∃ (T C:ℕ) (γ:Fin C → Fin W) (j:Fin C → Fin (2 ^ T)) (c u:Fin C → EuclideanSpace ℝ (Fin 2)) (Q:Fin C → Matrix (Fin 2) (Fin 2) ℝ) (A:Fin C → Set (ℕ × (Fin 6 → ℝ))) (F:Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst:Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)) (α₀:Fin C → ℝ) (v₀:Fin C → Fin 3 → ℝ) (law:Fin C → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Y₁:Fin C → (EuclideanSpace ℝ (Fin 3) × ℤ) → EuclideanSpace ℝ (Fin 2)) (X₁:Fin C → (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ),((fun (q:ℝ) => ((fun t₀ => ((fun e₀ => ((fun b₁ => ((fun r₀ => ((fun R => K ≤ N ^ loss ∧ (2:ℝ) ^ T ≤ N ^ (h + loss) ∧ (C:ℝ) ≤ N ^ M ∧ (∀ a a',a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a')) ∧ (∀ w o,((lst w o).card:ℝ) ≤ N ^ loss) ∧ (∀ w a,MeasurableSet {o | a ∈ lst w o}) ∧ (∀ a,chart N M D (N ^ loss) T ((j a:ℕ):ℝ) 0 (B (γ a)) (E (γ a)) (c a) (u a) (Q a) (P (γ a)) (A a) (F a) (∀ p ∈ F a,a ∈ lst (γ a) (obs (B (γ a)) (δ N 1) p))) ∧ (∀ a,|α₀ a| ≤ N ^ M ∧ (∀ i,|v₀ a i| ≤ N ^ M) ∧ |q⁻¹| ≤ N ^ M) ∧ (∑ a,R a) ≤ 1 ∧ (∀ a,BasicScalarLaw N χ d s m S U ((ν (γ a) (A a))⁻¹ • (ν (γ a)).restrict (A a)) (law a) (b₁ a) ∧ toE (N ^ (-χ)) ≤ law a Set.univ ∧ Measurable (Y₁ a) ∧ Measurable (X₁ a) ∧ (∀ᵐ z ∂law a,Y₁ a (obs (B (γ a)) (δ N 1) (e₀ a z)) = WithLp.toLp 2 ![z.2,scalarY (b₁ a z.1) z.2] ∧ |scalarX (b₁ a z.1) z.2 - X₁ a (obs (B (γ a)) (δ N 1) (e₀ a z))| ≤ N ^ (-1 + χ)) ∧ (∀ᵐ z ∂law a,z.1 ∈ A a) ∧ r₀ a • MeasureTheory.Measure.map (e₀ a) (law a) ≤ ((ν (γ a)).prod MeasureTheory.volume).restrict (F a)) ∧ toE (N ^ (-loss)) ≤ ∑ a,R a * law a Set.univ ∧ SupportCertificate N χ d s m C R law b₁ ∧ (if false then True else T = 0 ∧ (∀ a,v₀ a 0 = 0 ∧ (v₀ a 1) ^ 2 + (v₀ a 2) ^ 2 = 1) ∧ (∃ g:ℝ,0 < g ∧ g ≤ N ^ (-w) ∧ ∀ a,Q a = ![![v₀ a 1,-g * v₀ a 2],![v₀ a 2,g * v₀ a 1]]) ∧ (∑ a,toE (ω (γ a)) * ((ν (γ a)).prod MeasureTheory.volume) (F a)) ≤ (∑ a,R a * law a Set.univ) + toE (N ^ (-a₀)))) (fun a => toE (ω (γ a)) * r₀ a))) (fun a => toE q * ν (γ a) (A a)))) (fun a => nativeCoeff (P (γ a)) (t₀ a) q (α₀ a) (v₀ a) (A a)))) (fun a (z:((ℕ × (Fin 6 → ℝ)) × ℝ)) => (z.1,t₀ a + q * z.2)))) (fun a => ((j a:ℕ):ℝ) / (2:ℝ) ^ T))) (1 / (2:ℝ) ^ T))

def NativeAvailable : ∀ (p₀:Bool) (ds kr S η s m U χ w h t:ℝ),Prop :=
  fun p₀ ds kr S η s m U χ w h t => ∃ N K d W ω ν E P B f g G,prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < H N K 1 W ω ν E B f ∧ ∃ (a₀:ℝ) (M D:ℕ),0 < a₀ ∧ ∀ loss:ℝ,0 < loss → ∃ᶠ k in Filter.atTop,NativeSample p₀ (N k) (K k) (W k) (ω k) (ν k) (E k) (P k) (B k) M D a₀ w loss h χ ds s m (S / 2) U

def LocalizedSystems : ∀ (ds kr S η:ℝ),Prop :=
  fun ds kr S η => ∃ s m U:ℝ,0 < s ∧ s < 1 ∧ s < m ∧ 0 < U ∧ U < m ∧ ∀ χ w t:ℝ,0 < χ → 0 < w → 0 < t → NativeAvailable false ds kr S η s m U χ w 1 t

def Statement : Prop :=
  initialRaw → ∀ ds kr S η:ℝ,0 < S → 0 < η → es ds kr S η → ¬ widthRaw ds kr S η → LocalizedSystems ds kr S η

end
end Submission.Obl.k4_unbounded_localized_native_systems
