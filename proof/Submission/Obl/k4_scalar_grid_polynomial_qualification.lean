import Mathlib
import ChallengeDeps
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Rounding
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Residual
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Table
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Packets
import Submission.Obl.k4_scalar_grid_polynomial_qualification.StripFilling
import Submission.Obl.k4_scalar_grid_polynomial_qualification.StripCount
import Submission.Obl.k4_scalar_grid_polynomial_qualification.FitNumerics
import Submission.Obl.k4_scalar_grid_polynomial_qualification.TimeRow
import Submission.Obl.k4_scalar_grid_polynomial_qualification.SplitGlue
import Submission.Obl.k4_scalar_grid_polynomial_qualification.SlowGrid
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Subgrid
import Submission.Obl.k4_scalar_grid_polynomial_qualification.RelativeEntropy
import Submission.Obl.k4_scalar_grid_polynomial_qualification.TestedEntropy
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ParameterRefinement
import Submission.Obl.k4_scalar_grid_polynomial_qualification.SpatialCaps
import Submission.Obl.k4_scalar_grid_polynomial_qualification.CoefficientZoom
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ZoomCaps
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ExponentGrid
import Submission.Obl.k4_scalar_grid_polynomial_qualification.GraphSelection
import Submission.Obl.k4_scalar_grid_polynomial_qualification.OriginalRows
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ResidualRenewal
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Breadth
import Submission.Obl.k4_scalar_grid_polynomial_qualification.PlanarLines
import Submission.Obl.k4_scalar_grid_polynomial_qualification.PlanarBreadth
import Submission.Obl.k4_scalar_grid_polynomial_qualification.NormalStrips
import Submission.Obl.k4_scalar_grid_polynomial_qualification.OriginalParameterCaps
import Submission.Obl.k4_scalar_grid_polynomial_qualification.CurveCells
import Submission.Obl.k4_scalar_grid_polynomial_qualification.StripDuration
import Submission.Obl.k4_scalar_grid_polynomial_qualification.BaseCells
import Submission.Obl.k4_scalar_grid_polynomial_qualification.PaletteUnion
import Submission.Obl.k4_scalar_grid_polynomial_qualification.AssignedStripFilling
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ScalarFitTransfer
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ScalarFitNumerics
import Submission.Obl.k4_scalar_grid_polynomial_qualification.OriginalPhysicalSupport
import Submission.Obl.k4_scalar_grid_polynomial_qualification.NormalCellLists
import Submission.Obl.k4_scalar_grid_polynomial_qualification.PhysicalBandCount
import Submission.Obl.k4_scalar_grid_polynomial_qualification.PaletteListCount
import Submission.Obl.k4_scalar_grid_polynomial_qualification.OriginalWorldChoice
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ScalarCovering
import Submission.Obl.k4_scalar_grid_polynomial_qualification.OriginalParameterLists
import Submission.Obl.k4_scalar_grid_polynomial_qualification.EntryReferences
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ResidualZoom
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ZoomEntryPreparation
import Submission.Obl.k4_scalar_grid_polynomial_qualification.ZoomIncidenceCaps
set_option linter.unusedVariables false

open Submission.Obl.k4_scalar_grid_polynomial_qualification

/-!
# `Submission.k4_scalar_grid_polynomial_qualification`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_scalar_grid_polynomial_qualification`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_scalar_grid_polynomial_qualification/`
belong to this obligation.
-/

theorem Submission.k4_scalar_grid_polynomial_qualification : (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening r (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤ ENNReal.ofReal (C * r ^ n * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) → ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ S : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ) (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))) (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ), (fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => (fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => (fun (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun (z : ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℤ) => (fun (phys : ℕ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 3 → ℤ) => (fun (coeff : ℕ → ℝ → (ℕ × (Fin 5 → ℝ)) → Fin 5 → ℤ) => (fun (vel : ℕ → ℝ → ℤ → Set ℝ) => (fun (rowbin : ℕ → ℝ → (Fin 2 → ℝ) → Fin 2 → ℤ) => (fun (subpower : (ℕ → ℝ) → Prop) => (fun (prepData : (ℕ → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (fun (graphData : ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → ℝ → (ℕ → ℝ) → ℝ → ((k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (fun (graphOracle : ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (fun (fit : (k : ℕ) → ℕ → ((k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin (n k 1) → Prop) => (fun (qualOracle : ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧ (∀ g, MeasureTheory.IsProbabilityMeasure (ν k g) ∧ MeasureTheory.IsProbabilityMeasure (π k g) ∧ (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧ ρ k g ≤ ENNReal.ofReal (K k) • ((ν k g).prod MeasureTheory.volume) ∧ ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∀ c : ℤ, π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-S * b))) ∧ (∀ (q : Fin 2 → ℤ) (a : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧ (∀ (q : Fin 2 → ℤ) (a c : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a ∧ (⌊p.1.2 1 / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) * π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i)) ∧ (∀ i i', i ≠ i' → γ k s i = γ k s i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (N k ^ (-d * s) / (K k * (2 : ℝ) ^ T k s)) ≤ ν k (γ k s i) (A k s i) ∧ ν k (γ k s i) (A k s i) ≤ ENNReal.ofReal (K k * N k ^ (-d * s) / (2 : ℝ) ^ T k s) ∧ ENNReal.ofReal ((K k * (2 : ℝ) ^ T k s)⁻¹) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) (A k s i ×ˢ I (T k s) (j k s i)) ∧ |u k s i| + |v k s i| ≤ K k ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ t ∈ I (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2, |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s] (F k s i)| ≤ K k) ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |y l t - u k s i - t * v k s i| ≤ K k / (2 : ℝ) ^ T k s ∧ |x l t - MvPolynomial.eval ![t, y l t] (F k s i)| ≤ K k * N k ^ (-s))) ∧ (∀ g : Fin (W k), ρ k g {p | ∃ i, γ k s i = g ∧ p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i)}ᶜ = 0)) → ∀ (H₀ : ℕ → ℝ) (θ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E₀ : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), prepData H₀ θ E₀ → graphOracle E₀ → qualOracle E₀) (fun E₀ => ∀ M : ℕ, 2 ≤ M → ∀ L : ℝ, 0 < L → ∃ (H : ℕ → ℝ) (B : ℝ) (G : (k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), graphData E₀ L H B G E ∧ ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun k => (∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) {p | ∃ i : Fin (n k 1), γ k 1 i = g ∧ p.1 ∈ A k 1 i ∧ p.2 ∈ I (T k 1) (j k 1 i) ∧ ¬ fit k M G E B ε p i}).toReal / (∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ).toReal) Filter.atTop (nhds (0 : ℝ)))) (fun k M G E B ε p i => ∃ P : Fin 2 → Polynomial ℝ, (∀ e, (P e).natDegree ≤ M ∧ ∀ a : ℕ, |(P e).coeff a| ≤ N k ^ ε) ∧ (∀ e, |G k (γ k 1 i) (phys k B p) e - (P e).eval p.2| ≤ ((2 : ℝ) ^ T k 1)⁻¹ ^ M) ∧ ENNReal.ofReal (((2 : ℝ) ^ T k 1)⁻¹ * N k ^ (-ε)) ≤ MeasureTheory.volume {t : ℝ | (p.1,t) ∈ E k (γ k 1 i) ∧ t ∈ I (T k 1) (j k 1 i) ∧ ∀ e, |G k (γ k 1 i) (phys k B (p.1,t)) e - (P e).eval t| ≤ ((2 : ℝ) ^ T k 1)⁻¹ ^ M})) (fun E₀ => ∀ L : ℝ, 0 < L → ∃ (H : ℕ → ℝ) (B : ℝ) (G : (k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), graphData E₀ L H B G E)) (fun E₀ L H B G E => subpower H ∧ L + 10 ≤ B ∧ (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ ∧ ∀ g : Fin (W k), MeasurableSet (E k g) ∧ E k g ⊆ E₀ k g ∧ (∀ p ∈ E k g, (∀ e : Fin 2, |G k g (phys k B p) e| ≤ H k) ∧ |p.1.2 3 + 2 * p.2 * p.1.2 4 - G k g (phys k B p) 0 - G k g (phys k B p) 1 * p.1.2 1| ≤ H k * N k ^ (-L)) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → r ≤ L → ∀ q : Fin 3 → ℤ, ({v : Fin 2 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ rowbin k r (G k g (phys k B p)) = v} ≠ 0}.ncard : ℝ) ≤ H k) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (c : ℤ), (ρ k g).restrict (E k g) {p | phys k B p = q ∧ p.1.2 1 ∈ vel k r c} ≤ ENNReal.ofReal (H k) * (ρ k g).restrict (E k g) {p | phys k B p = q} * π k g (vel k r c))))) (fun H θ E => subpower H ∧ ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧ (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ ∧ ∀ g : Fin (W k), θ k g ≤ ν k g ∧ θ k g Set.univ ≤ 1 ∧ MeasurableSet (E k g) ∧ (∀ p ∈ E k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H k) ∧ (∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ H k) ∧ ENNReal.ofReal ((H k)⁻¹) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ≤ (ρ k g).restrict (E k g) ∧ (ρ k g).restrict (E k g) ≤ ENNReal.ofReal (H k) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) → Set.Finite {q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q} ≠ 0} ∧ ({q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q} ≠ 0}.ncard : ℝ) ≤ H k * N k ^ ((2 + d) * r) ∧ (∀ r₀ : ℝ, R⁻¹ ≤ r₀ → r₀ ≤ r → (∃ m : ℕ, r₀ = (m : ℝ) / (M k : ℝ)) → ∀ q₀ : Fin 3 → ℤ, ({q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ phys k r₀ p = q₀} ≠ 0}.ncard : ℝ) ≤ H k * N k ^ ((2 + d) * (r - r₀))) ∧ (∀ q : Fin 5 → ℤ, (ρ k g).restrict (E k g) {p | coeff k r p.1 = q} ≠ 0 → ENNReal.ofReal (N k ^ (-(1 + d) * r) / H k) * π k g (vel k r (q 1)) ≤ θ k g {l | coeff k r l = q} ∧ θ k g {l | coeff k r l = q} ≤ ENNReal.ofReal (H k * N k ^ (-(1 + d) * r)) * π k g (vel k r (q 1))) ∧ (∀ (q : Fin 3 → ℤ) (c : ℤ), ({b : Fin 5 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ coeff k r p.1 1 = c ∧ coeff k r p.1 = b} ≠ 0}.ncard : ℝ) ≤ H k)) ∧ (∀ (r s b t : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∃ m₁ m₂ m₃ : ℕ, r = (m₁ : ℝ) / (M k : ℝ) ∧ s = (m₂ : ℝ) / (M k : ℝ) ∧ b = (m₃ : ℝ) / (M k : ℝ)) → ∀ (q a c : ℤ), θ k g {l | (l,t) ∈ E k g ∧ (⌊y l t / (N k ^ (-r))⌋ : ℤ) = q ∧ (⌊x l t / (N k ^ (-s))⌋ : ℤ) = a ∧ l.2 1 ∈ vel k b c} ≤ ENNReal.ofReal (H k * N k ^ (-r - d * s)) * π k g (vel k b c))))) (fun H => (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ N k ^ ε)) (fun k r v e => (⌊v e / (N k ^ (-r))⌋ : ℤ))) (fun k r c => {v : ℝ | (⌊v / (N k ^ (-r))⌋ : ℤ) = c})) (fun k r l e => (⌊l.2 e / (N k ^ (-r))⌋ : ℤ))) (fun k r p e => (⌊(![p.2, y p.1 p.2, x p.1 p.2] : Fin 3 → ℝ) e / (N k ^ (-r))⌋ : ℤ))) (fun B r p e => (⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋ : ℤ))) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4)) (fun l t => l.2 0 + t * l.2 1) := by
  suffices hdiscovery : PolynomialDiscoveryStatement by
    intro hMK N K hN hNt hK d κ S hd hd1 hκ hκ1 hS W ω ν ρ π T n γ j A u v F
    let D : ScalarData :=
      { N := N, K := K, d := d, κ := κ, S := S, W := W, ω := ω, ν := ν, ρ := ρ, π := π,
        T := T, n := n, γ := γ, j := j, A := A, u := u, v := v, F := F }
    change D.base → D.caps → D.packets →
      ∀ (H₀ : ℕ → ℝ) (θ : (k : ℕ) → Fin (D.W k) → MeasureTheory.Measure ScalarLine)
        (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence),
        D.prepData H₀ θ E₀ → D.graphOracle E₀ → D.qualOracle E₀
    intro hbase hcaps hpackets H₀ θ E₀ hprep hgraph
    exact ScalarData.qualOracle_of_polynomialDiscovery hN hbase hgraph
      (hdiscovery hMK D ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hS⟩
        hbase hcaps hpackets H₀ θ E₀ hprep)
  exact polynomialDiscovery_of_children
