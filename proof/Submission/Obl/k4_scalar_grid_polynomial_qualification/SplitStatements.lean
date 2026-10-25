import Submission.Obl.k4_scalar_grid_polynomial_qualification.Assembly
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Interface

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

/-- Mathlib-only expansion of the scalar-normal higher-jet input.
The conjunction record in Jets.Interface is curried explicitly here. -/
def HigherJetInput : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ M : ℕ, 2 ≤ M → ∀ c_h : ℝ, 0 < c_h →
  ∃ c_ζ : ℝ, 0 < c_ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ,
  ∀ N : ℝ, N₀ ≤ N →
  ∀ (Λ : Type) [MeasurableSpace Λ] (ν : MeasureTheory.Measure Λ)
    (c : Λ → Fin 5 → ℝ) (E : Set (Λ × ℝ)) (F : ℝ → ℝ)
    (piece : ℝ → Λ → Fin 5 → ℤ) (K ζ : ℝ) (T : ℕ),
  (fun (zx : (Fin 5 → ℝ) → ℝ → ℝ) =>
  (fun (zy : (Fin 5 → ℝ) → ℝ → ℝ) =>
  (fun (scalar : (Fin 5 → ℝ) → ℝ → ℝ) =>
  (fun (resid : (Fin 5 → ℝ) → ℝ → ℝ) =>
  (fun (pos : (Fin 5 → ℝ) → ℝ → Fin 3 → ℝ) =>
  (fun (h : ℝ) =>
  K ≤ N ^ α → N ^ (-c_h) / K ≤ h → h ≤ K * N ^ (-c_h) → ζ ≤ h ^ c_ζ →
  MeasureTheory.IsProbabilityMeasure ν → 1 ≤ K → 0 < ζ → ζ ≤ 1 →
  Measurable c → MeasurableSet E → Measurable F → (∀ r, Measurable (piece r)) →
  (∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1) →
  (∀ p ∈ E, ∀ e, |c p.1 e| ≤ K) → (∀ p ∈ E, |F p.2| ≤ K) →
  ENNReal.ofReal K⁻¹ ≤ (ν.prod MeasureTheory.volume) E →
  (∀ t r R a : ℝ, ζ ≤ r → r ≤ R → ∃ (m : ℕ) (z : Fin m → ℝ),
    {s : ℝ | ∃ l, (l,t) ∈ E ∧ scalar (c l) t = s} ∩ Set.Icc a (a + R) ⊆
      ⋃ i, Metric.closedBall (z i) r ∧ (m : ℝ) ≤ K * (R / r) ^ d) →
  (∀ t a b q : ℝ, ζ ≤ q → q ≤ 1 →
    ν {l | (l,t) ∈ E ∧ zx (c l) t ∈ Set.Ico a (a + q) ∧
      zy (c l) t ∈ Set.Ico b (b + q)} ≤ ENNReal.ofReal (K * q ^ (1 + d))) →
  (∀ p ∈ E, ∀ p' ∈ E, |F p.2 - F p'.2| ≤ K * (|p.2 - p'.2| + ζ)) →
  (∀ p ∈ E, ∀ p' ∈ E, |resid (c p.1) p.2 - resid (c p'.1) p'.2| ≤
    K * (‖pos (c p.1) p.2 - pos (c p'.1) p'.2‖ + ζ)) →
  (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∀ l l', piece r l = piece r l' → ‖c l - c l'‖ ≤ r) →
  (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∀ (b : Fin 5 → ℤ) (t a a' q : ℝ), ζ ≤ q → q ≤ r →
    ν {l | piece r l = b ∧ (l,t) ∈ E ∧ zx (c l) t ∈ Set.Ico a (a + q) ∧
      zy (c l) t ∈ Set.Ico a' (a' + q)} ≤
        ENNReal.ofReal (K * (q / r) ^ (1 + d)) * ν {l | piece r l = b}) →
  ∃ p ∈ E, ∃ P : Polynomial ℝ, P.natDegree ≤ M ∧ (∀ i, |P.coeff i| ≤ N ^ ε) ∧
    |F p.2 - P.eval p.2| ≤ h ^ ((M : ℝ) + 1 / 8) ∧
    ENNReal.ofReal (h * N ^ (-ε)) ≤ MeasureTheory.volume {t : ℝ |
      t ∈ Set.Icc (((⌊p.2 * (2 : ℝ) ^ T⌋ : ℤ) : ℝ) / (2 : ℝ) ^ T)
        ((((⌊p.2 * (2 : ℝ) ^ T⌋ : ℤ) : ℝ) + 1) / (2 : ℝ) ^ T) ∧
      (p.1,t) ∈ E ∧ |F t - P.eval t| ≤ h ^ ((M : ℝ) + 1 / 8)}) (((2 : ℝ) ^ T)⁻¹)) (fun a t => ![t, zx a t, zy a t])) (fun a t => a 1 + 2 * a 2 * t - F t * a 4)) (fun a t => zx a t - F t * zy a t)) (fun a t => a 3 + a 4 * t)) (fun a t => a 0 + a 1 * t + a 2 * t ^ 2)

/-- The explicit raw-array form of polynomial discovery. Its shared context
is the obligation's own frozen context, and its conclusion is SlackDiscovery. -/
def DiscoveryInput : Prop :=
  (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening r (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤ ENNReal.ofReal (C * r ^ n * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) → ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ S : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ) (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))) (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ), (fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => (fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => (fun (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun (z : ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℤ) => (fun (phys : ℕ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 3 → ℤ) => (fun (coeff : ℕ → ℝ → (ℕ × (Fin 5 → ℝ)) → Fin 5 → ℤ) => (fun (vel : ℕ → ℝ → ℤ → Set ℝ) => (fun (rowbin : ℕ → ℝ → (Fin 2 → ℝ) → Fin 2 → ℤ) => (fun (subpower : (ℕ → ℝ) → Prop) => (fun (prepData : (ℕ → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (fun (graphData : ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → ℝ → (ℕ → ℝ) → ℝ → ((k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) =>    (∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧ (∀ g, MeasureTheory.IsProbabilityMeasure (ν k g) ∧ MeasureTheory.IsProbabilityMeasure (π k g) ∧ (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧ ρ k g ≤ ENNReal.ofReal (K k) • ((ν k g).prod MeasureTheory.volume) ∧ ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∀ c : ℤ, π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-S * b))) ∧ (∀ (q : Fin 2 → ℤ) (a : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧ (∀ (q : Fin 2 → ℤ) (a c : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a ∧ (⌊p.1.2 1 / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) * π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i)) ∧ (∀ i i', i ≠ i' → γ k s i = γ k s i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (N k ^ (-d * s) / (K k * (2 : ℝ) ^ T k s)) ≤ ν k (γ k s i) (A k s i) ∧ ν k (γ k s i) (A k s i) ≤ ENNReal.ofReal (K k * N k ^ (-d * s) / (2 : ℝ) ^ T k s) ∧ ENNReal.ofReal ((K k * (2 : ℝ) ^ T k s)⁻¹) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) (A k s i ×ˢ I (T k s) (j k s i)) ∧ |u k s i| + |v k s i| ≤ K k ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ t ∈ I (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2, |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s] (F k s i)| ≤ K k) ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |y l t - u k s i - t * v k s i| ≤ K k / (2 : ℝ) ^ T k s ∧ |x l t - MvPolynomial.eval ![t, y l t] (F k s i)| ≤ K k * N k ^ (-s))) ∧ (∀ g : Fin (W k), ρ k g {p | ∃ i, γ k s i = g ∧ p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i)}ᶜ = 0)) → ∀ (H₀ : ℕ → ℝ) (θ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E₀ : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), prepData H₀ θ E₀ →
  ∀ M : ℕ, 2 ≤ M → ∀ L : ℝ, 0 < L → ∃ L' : ℝ, L ≤ L' ∧ 0 < L' ∧
  ∀ (H : ℕ → ℝ) (B : ℝ)
    (G : (k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)),
  graphData E₀ L' H B G E →
  (fun (h : ℕ → ℝ) =>
  (fun (row : (k : ℕ) → Fin (W k) → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℝ) =>
  (fun (fitWith : (k : ℕ) → Fin (n k 1) → ℝ → ℝ → ℝ →
      ((ℕ × (Fin 5 → ℝ)) × ℝ) → (Fin 2 → Polynomial ℝ) → Prop) =>
  (fun (rationalFit : ℝ → (k : ℕ) → Fin (n k 1) → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Prop) =>
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ φ : ℕ → ℕ,
    Filter.Tendsto φ Filter.atTop Filter.atTop →
    (∀ k, δ ≤
      (∑ g : Fin (W (φ k)), ENNReal.ofReal (ω (φ k) g) *
        (ρ (φ k) g).restrict (E (φ k) g) {p | ∃ i : Fin (n (φ k) 1),
          γ (φ k) 1 i = g ∧ p.1 ∈ A (φ k) 1 i ∧
          p.2 ∈ I (T (φ k) 1) (j (φ k) 1 i) ∧ ¬ rationalFit ε (φ k) i p}).toReal /
      (∑ g : Fin (W (φ k)), ENNReal.ofReal (ω (φ k) g) *
        (ρ (φ k) g).restrict (E (φ k) g) Set.univ).toReal) →
    ∃ (k : ℕ) (i : Fin (n (φ k) 1)) (p : ((ℕ × (Fin 5 → ℝ)) × ℝ))
      (P : Fin 2 → Polynomial ℝ),
      (p.1 ∈ A (φ k) 1 i ∧ p.2 ∈ I (T (φ k) 1) (j (φ k) 1 i)) ∧
      ¬ rationalFit ε (φ k) i p ∧
      fitWith (φ k) i (N (φ k) ^ (ε / 2)) (h (φ k) ^ M / 2)
        (h (φ k) * N (φ k) ^ (-(ε / 2))) p P) (fun ε k i p => ∃ Q : Fin 2 → Polynomial ℚ,
      fitWith k i (N k ^ ε) (h k ^ M) (h k * N k ^ (-ε)) p
        (fun e => (Q e).map (algebraMap ℚ ℝ)))) (fun k i C δ τ p P =>
      (∀ e, (P e).natDegree ≤ M ∧ ∀ a : ℕ, |(P e).coeff a| ≤ C) ∧
      (∀ e, |row k (γ k 1 i) p e - (P e).eval p.2| ≤ δ) ∧
      ENNReal.ofReal τ ≤ MeasureTheory.volume {t : ℝ |
        (p.1,t) ∈ E k (γ k 1 i) ∧ t ∈ I (T k 1) (j k 1 i) ∧
        ∀ e, |row k (γ k 1 i) (p.1,t) e - (P e).eval t| ≤ δ})) (fun k g p => G k g (phys k B p))) (fun k => ((2 : ℝ) ^ T k 1)⁻¹)) (fun E₀ L H B G E => subpower H ∧ L + 10 ≤ B ∧ (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ ∧ ∀ g : Fin (W k), MeasurableSet (E k g) ∧ E k g ⊆ E₀ k g ∧ (∀ p ∈ E k g, (∀ e : Fin 2, |G k g (phys k B p) e| ≤ H k) ∧ |p.1.2 3 + 2 * p.2 * p.1.2 4 - G k g (phys k B p) 0 - G k g (phys k B p) 1 * p.1.2 1| ≤ H k * N k ^ (-L)) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → r ≤ L → ∀ q : Fin 3 → ℤ, ({v : Fin 2 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ rowbin k r (G k g (phys k B p)) = v} ≠ 0}.ncard : ℝ) ≤ H k) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (c : ℤ), (ρ k g).restrict (E k g) {p | phys k B p = q ∧ p.1.2 1 ∈ vel k r c} ≤ ENNReal.ofReal (H k) * (ρ k g).restrict (E k g) {p | phys k B p = q} * π k g (vel k r c))))) (fun H θ E => subpower H ∧ ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧ (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ ∧ ∀ g : Fin (W k), θ k g ≤ ν k g ∧ θ k g Set.univ ≤ 1 ∧ MeasurableSet (E k g) ∧ (∀ p ∈ E k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H k) ∧ (∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ H k) ∧ ENNReal.ofReal ((H k)⁻¹) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ≤ (ρ k g).restrict (E k g) ∧ (ρ k g).restrict (E k g) ≤ ENNReal.ofReal (H k) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) → Set.Finite {q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q} ≠ 0} ∧ ({q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q} ≠ 0}.ncard : ℝ) ≤ H k * N k ^ ((2 + d) * r) ∧ (∀ r₀ : ℝ, R⁻¹ ≤ r₀ → r₀ ≤ r → (∃ m : ℕ, r₀ = (m : ℝ) / (M k : ℝ)) → ∀ q₀ : Fin 3 → ℤ, ({q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ phys k r₀ p = q₀} ≠ 0}.ncard : ℝ) ≤ H k * N k ^ ((2 + d) * (r - r₀))) ∧ (∀ q : Fin 5 → ℤ, (ρ k g).restrict (E k g) {p | coeff k r p.1 = q} ≠ 0 → ENNReal.ofReal (N k ^ (-(1 + d) * r) / H k) * π k g (vel k r (q 1)) ≤ θ k g {l | coeff k r l = q} ∧ θ k g {l | coeff k r l = q} ≤ ENNReal.ofReal (H k * N k ^ (-(1 + d) * r)) * π k g (vel k r (q 1))) ∧ (∀ (q : Fin 3 → ℤ) (c : ℤ), ({b : Fin 5 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ coeff k r p.1 1 = c ∧ coeff k r p.1 = b} ≠ 0}.ncard : ℝ) ≤ H k)) ∧ (∀ (r s b t : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∃ m₁ m₂ m₃ : ℕ, r = (m₁ : ℝ) / (M k : ℝ) ∧ s = (m₂ : ℝ) / (M k : ℝ) ∧ b = (m₃ : ℝ) / (M k : ℝ)) → ∀ (q a c : ℤ), θ k g {l | (l,t) ∈ E k g ∧ (⌊y l t / (N k ^ (-r))⌋ : ℤ) = q ∧ (⌊x l t / (N k ^ (-s))⌋ : ℤ) = a ∧ l.2 1 ∈ vel k b c} ≤ ENNReal.ofReal (H k * N k ^ (-r - d * s)) * π k g (vel k b c))))) (fun H => (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ N k ^ ε)) (fun k r v e => (⌊v e / (N k ^ (-r))⌋ : ℤ))) (fun k r c => {v : ℝ | (⌊v / (N k ^ (-r))⌋ : ℤ) = c})) (fun k r l e => (⌊l.2 e / (N k ^ (-r))⌋ : ℤ))) (fun k r p e => (⌊(![p.2, y p.1 p.2, x p.1 p.2] : Fin 3 → ℝ) e / (N k ^ (-r))⌋ : ℤ))) (fun B r p e => (⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋ : ℤ))) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4)) (fun l t => l.2 0 + t * l.2 1)

/-- This conditional implication is the Section 6 child; Section 5 is a
literal hypothesis supplied by the other child. -/
def DiscoveryFromHigherJets : Prop := HigherJetInput → DiscoveryInput

end Submission.Obl.k4_scalar_grid_polynomial_qualification
