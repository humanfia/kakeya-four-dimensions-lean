import Mathlib
import ChallengeDeps

/-!
# Explicit terminal-chart interface for the split of o018

`TerminalChartAssertion` expands the version-2 data and asserts true
terminal systems at every positive upper time exponent, on a subsequence.
It is a proposition defined entirely in Mathlib vocabulary. The frozen
children fully expand its body; they do not refer to this declaration.

The local abbreviations evaluate six trajectory coefficients (`z`, `y`,
`v`), encode Boolean combinations of bounded-degree polynomial sign tests
(`fmt`), take an indexed coefficient slice (`slice`), and quantify every
subpower tolerance explicitly (`sub`). The input laws keep the prior
independent of time. Observation densities and all exceptional masses
are unnormalized within each world. World weights enter the sums only.

The output assigns whole trajectories disjointly per world/time interval,
selects subsets of the original incidences, and measures packet masses
using the unchanged original product priors. Its per-packet inequality is
exactly the true floor after multiplication by the dyadic time length.
Further selections and strictly increasing subsequences are explicit.
See the submitted PROOF.md for the mapping to Definitions 2.1, 2.2, 2.6,
2.8 and 2.14 of the supplied paper and for the horizon-zero equivalence.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_framework_from_matching_clustering_conic

/-- Every tempered homogeneous version-2 cap-class problem has true terminal
chart systems at arbitrarily small positive upper time exponents. -/
def TerminalChartAssertion : Prop :=
let C := ℕ × (Fin 6 → ℝ);
let O := EuclideanSpace ℝ (Fin 3) × ℤ;
let z : C → ℝ → Fin 4 → ℝ := fun l t => ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5];
let y : C → ℝ → EuclideanSpace ℝ (Fin 2) := fun l t => WithLp.toLp 2 ![z l t 1, z l t 2];
let v : C → EuclideanSpace ℝ (Fin 2) := fun l => WithLp.toLp 2 ![l.2 3, l.2 4];
let fmt := fun (e D : ℕ) (H : ℝ) (A : Set (Fin e → ℝ)) => ∃ m : ℕ, (m : ℝ) ≤ H ∧ ∃ p : Fin m → MvPolynomial (Fin e) ℝ, (∀ i, (p i).totalDegree ≤ D) ∧ ∃ b : (Fin m → Bool) → Bool, ∀ x, x ∈ A ↔ b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true;
let slice := fun (A : Set (C × ℝ)) (i : ℕ) => {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ A};
let sub := fun (N K : ℕ → ℝ) => (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε;
∀ N K : ℕ → ℝ, (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → sub N K →
∀ L d S η : ℝ, 0 < L → 0 < d → d < 1 → 0 < S → 0 < η →
∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
(ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure C)
(E : (k : ℕ) → Fin (W k) → Set (C × ℝ))
(P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
(B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ),
let a := fun k r => (2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ));
let μ := fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ);
let obs := fun k γ r (p : C × ℝ) => ((WithLp.toLp 2 ![p.2, z p.1 p.2 1, z p.1 p.2 2] : EuclideanSpace ℝ (Fin 3)), ⌊B k γ * z p.1 p.2 3 / a k r⌋);
let ang := fun k γ u (p : C × ℝ) => (obs k γ L p, fun j : Fin 2 => ⌊v p.1 j / a k u⌋);
∀ (g : (k : ℕ) → Fin (W k) → ℝ → O → ENNReal)
(G : (k : ℕ) → Fin (W k) → ℝ → (O × (Fin 2 → ℤ)) → ENNReal),
(∃ M D : ℕ, ∀ k,
 (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧
 (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧
 (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)),
 (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ fmt 6 D (N k ^ M) (A j) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧
 ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧
 MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, fmt 7 D (N k ^ M) (slice (E k γ) i)) ∧
 (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖y l t‖ + ‖v l‖ ≤ K k ∧ |MvPolynomial.eval (z l t) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (z l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (z l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧
 (∀ᵐ p ∂μ k γ, B k γ / K k ≤ |MvPolynomial.eval (z p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧
 ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * μ k γ Set.univ) →
(∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (obs k γ r) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) →
(∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (ang k γ u) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) →
(∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) →
(∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * μ k γ {p | g k γ r (obs k γ r p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r (obs k γ r p)}) ≤ ENNReal.ofReal (N k ^ (-c))) →
(∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) →
(∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * μ k γ {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u (ang k γ u p)}) ≤ ENNReal.ofReal (N k ^ (-c))) →
∀ h : ℝ, 0 < h → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
∃ M D : ℕ, ∃ K' : ℕ → ℝ, sub (fun k => N (ψ k)) K' ∧ (∀ k, K (ψ k) ≤ K' k) ∧
∃ T C' : ℕ → ℕ,
∃ (γ : (k : ℕ) → Fin (C' k) → Fin (W (ψ k)))
(j : (k : ℕ) → Fin (C' k) → Fin (2 ^ T k))
(c u : (k : ℕ) → Fin (C' k) → EuclideanSpace ℝ (Fin 2))
(Q : (k : ℕ) → Fin (C' k) → Matrix (Fin 2) (Fin 2) ℝ)
(R : (k : ℕ) → Fin (C' k) → MvPolynomial (Fin 4) ℝ)
(A : (k : ℕ) → Fin (C' k) → Set C)
(F : (k : ℕ) → Fin (C' k) → Set (C × ℝ)),
let I := fun k b => Set.Icc (((j k b : ℕ) : ℝ) / (2 : ℝ) ^ T k) ((((j k b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k);
let m := fun k b => ((ν (ψ k) (γ k b)).prod MeasureTheory.volume) (F k b);
∀ k, (2 : ℝ) ^ T k ≤ N (ψ k) ^ h ∧ (C' k : ℝ) ≤ N (ψ k) ^ M ∧
(∀ b b', b ≠ b' → γ k b = γ k b' → j k b = j k b' → Disjoint (A k b) (A k b')) ∧
(∀ b, Matrix.det (Q k b) ≠ 0 ∧ ‖c k b‖ + ‖u k b‖ ≤ N (ψ k) ^ M ∧
 (∑ e : Fin 2, ∑ e' : Fin 2, (|Q k b e e'| + |(Q k b)⁻¹ e e'|)) ≤ N (ψ k) ^ M ∧
 (∑ e : Fin 2, ∑ e' : Fin 2, |Q k b e e'|) ≤ K' k / (2 : ℝ) ^ T k ∧ (R k b).totalDegree ≤ 2 ∧ (∀ e, |(R k b).coeff e| ≤ N (ψ k) ^ M) ∧
 MeasurableSet (A k b) ∧ MeasurableSet (F k b) ∧ (∀ i, fmt 6 D (N (ψ k) ^ M) {x | (i, x) ∈ A k b} ∧ fmt 7 D (N (ψ k) ^ M) (slice (F k b) i)) ∧
 (∀ l ∈ A k b, (l.1 : ℝ) ≤ N (ψ k) ^ M ∧ (∀ e, |l.2 e| ≤ N (ψ k) ^ M) ∧ ∀ t ∈ I k b,
 ‖Matrix.toEuclideanLin ((Q k b)⁻¹) (y l t - c k b - t • u k b)‖ ≤ K' k ∧
 |MvPolynomial.eval (z l t) (R k b)| ≤ K' k * a (ψ k) L ∧
 |MvPolynomial.eval (z l t) (MvPolynomial.pderiv (3 : Fin 4) (R k b))| ≤ K' k * B (ψ k) (γ k b) ∧
 |MvPolynomial.eval (z l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R k b)))| ≤ K' k * (B (ψ k) (γ k b)) ^ 2 / a (ψ k) L) ∧
 (∀ p ∈ F k b, p ∈ E (ψ k) (γ k b) ∧ p.1 ∈ A k b ∧ p.2 ∈ I k b ∧ B (ψ k) (γ k b) / K' k ≤ |MvPolynomial.eval (z p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R k b))|) ∧
 ENNReal.ofReal (N (ψ k) ^ (-f L) * |Matrix.det (Q k b)| / ((2 : ℝ) ^ T k * K' k)) ≤ m k b) ∧
ENNReal.ofReal ((K' k)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω (ψ k) (γ k b)) * m k b

end Submission.Obl.k4_framework_from_matching_clustering_conic
