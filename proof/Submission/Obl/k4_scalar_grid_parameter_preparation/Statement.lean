import Mathlib

/-!
# The frozen statement of o228, unfolded

The frozen type of `Submission.k4_scalar_grid_parameter_preparation` binds its trajectory
coordinates, cell codes and the certificate `prepData` by `fun`. After `beta_reduce` its three
hypotheses and its conclusion are, definitionally, `FrozenBase`, `FrozenCaps`, `FrozenPackets` and
`PrepConclusion` below. Nothing is proved here.
-/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open MeasureTheory Filter

/-- The trajectory position `y_l(t) = l₀ + t l₁`. -/
def trajY (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : ℝ := l.2 0 + t * l.2 1

/-- The hidden coordinate `X_l(t) = l₂ + t l₃ + t² l₄`. -/
def trajX (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

/-- The floor-grid physical `(t, y, X)` cube of side `N^{-r}`. -/
def physTag (N r : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) : Fin 3 → ℤ :=
  fun e => ⌊(![p.2, trajY p.1 p.2, trajX p.1 p.2] : Fin 3 → ℝ) e / N ^ (-r)⌋

/-- The floor-grid coefficient bin of side `N^{-r}`. -/
def coeffTag (N r : ℝ) (l : ℕ × (Fin 5 → ℝ)) : Fin 5 → ℤ :=
  fun e => ⌊l.2 e / N ^ (-r)⌋

/-- The velocity bin of side `N^{-r}`. -/
def velBin (N r : ℝ) (c : ℤ) : Set ℝ := {v | ⌊v / N ^ (-r)⌋ = c}

/-- The `(t, y)` floor cell of side `B^{-r}`. -/
def baseTag (B r : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) : Fin 2 → ℤ :=
  fun e => ⌊(![p.2, trajY p.1 p.2] : Fin 2 → ℝ) e / B ^ (-r)⌋

/-- The dyadic time block `I(T, j)`. -/
def timeBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

/-- The frozen base hypothesis. -/
def FrozenBase (K : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) : Prop :=
  ∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧
    (∀ g, IsProbabilityMeasure (ν k g) ∧ IsProbabilityMeasure (π k g) ∧
      (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧
      ρ k g ≤ ENNReal.ofReal (K k) • ((ν k g).prod volume) ∧
      ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧
    ENNReal.ofReal ((K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ

/-- The frozen angular, pure and joint caps. -/
def FrozenCaps (N K : ℕ → ℝ) (d S : ℝ) (W : ℕ → ℕ)
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) : Prop :=
  ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
    R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
    (∀ c : ℤ, π k g (velBin (N k) b c) ≤ ENNReal.ofReal (K k * N k ^ (-S * b))) ∧
    (∀ (q : Fin 2 → ℤ) (a : ℤ), ρ k g {p | baseTag (N k) r p = q ∧
      (⌊trajX p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a} ≤
        ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧
    (∀ (q : Fin 2 → ℤ) (a c : ℤ), ρ k g {p | baseTag (N k) r p = q ∧
      (⌊trajX p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a ∧ (⌊p.1.2 1 / (N k ^ (-b))⌋ : ℤ) = c} ≤
        ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) * π k g (velBin (N k) b c))

/-- The frozen dyadic quadratic packets at every depth. -/
def FrozenPackets (N K : ℕ → ℝ) (d κ : ℝ) (W : ℕ → ℕ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k))
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ)))
    (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ)
    (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
    N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧
    (∀ i, MeasurableSet (A k s i)) ∧
    (∀ i i', i ≠ i' → γ k s i = γ k s i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧
    (∀ i, ENNReal.ofReal (N k ^ (-d * s) / (K k * (2 : ℝ) ^ T k s)) ≤ ν k (γ k s i) (A k s i) ∧
      ν k (γ k s i) (A k s i) ≤ ENNReal.ofReal (K k * N k ^ (-d * s) / (2 : ℝ) ^ T k s) ∧
      ENNReal.ofReal ((K k * (2 : ℝ) ^ T k s)⁻¹) * ν k (γ k s i) (A k s i) ≤
        ρ k (γ k s i) (A k s i ×ˢ timeBlock (T k s) (j k s i)) ∧
      |u k s i| + |v k s i| ≤ K k ∧ (F k s i).totalDegree ≤ 2 ∧
      (∀ t ∈ timeBlock (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2,
        |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s] (F k s i)| ≤ K k) ∧
      (∀ l ∈ A k s i, ∀ t ∈ timeBlock (T k s) (j k s i),
        |trajY l t - u k s i - t * v k s i| ≤ K k / (2 : ℝ) ^ T k s ∧
        |trajX l t - MvPolynomial.eval ![t, trajY l t] (F k s i)| ≤ K k * N k ^ (-s))) ∧
    (∀ g : Fin (W k), ρ k g {p | ∃ i, γ k s i = g ∧ p.1 ∈ A k s i ∧
      p.2 ∈ timeBlock (T k s) (j k s i)}ᶜ = 0)

/-- `H` is a subpower of `N`. -/
def Subpower (N H : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε

/-- `r` is a point of the grid `ℕ / M`. -/
def OnGrid (M : ℕ) (r : ℝ) : Prop := ∃ m : ℕ, r = (m : ℝ) / (M : ℝ)

/-- The clauses of `prepData` at one exponent `r` of the grid, in one world. -/
def GridClauses (N : ℕ → ℝ) (d : ℝ) (W : ℕ → ℕ)
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) (H : ℕ → ℝ)
    (θ : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (M : ℕ → ℕ) (R : ℝ) (k : ℕ) (g : Fin (W k)) (r : ℝ) : Prop :=
  Set.Finite {q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | physTag (N k) r p = q} ≠ 0} ∧
  ({q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | physTag (N k) r p = q} ≠ 0}.ncard : ℝ) ≤
    H k * N k ^ ((2 + d) * r) ∧
  (∀ r₀ : ℝ, R⁻¹ ≤ r₀ → r₀ ≤ r → OnGrid (M k) r₀ → ∀ q₀ : Fin 3 → ℤ,
    ({q : Fin 3 → ℤ | (ρ k g).restrict (E k g)
      {p | physTag (N k) r p = q ∧ physTag (N k) r₀ p = q₀} ≠ 0}.ncard : ℝ) ≤
      H k * N k ^ ((2 + d) * (r - r₀))) ∧
  (∀ q : Fin 5 → ℤ, (ρ k g).restrict (E k g) {p | coeffTag (N k) r p.1 = q} ≠ 0 →
    ENNReal.ofReal (N k ^ (-(1 + d) * r) / H k) * π k g (velBin (N k) r (q 1)) ≤
      θ k g {l | coeffTag (N k) r l = q} ∧
    θ k g {l | coeffTag (N k) r l = q} ≤
      ENNReal.ofReal (H k * N k ^ (-(1 + d) * r)) * π k g (velBin (N k) r (q 1))) ∧
  (∀ (q : Fin 3 → ℤ) (c : ℤ), ({b : Fin 5 → ℤ | (ρ k g).restrict (E k g)
    {p | physTag (N k) r p = q ∧ (⌊p.1.2 1 / (N k ^ (-r))⌋ : ℤ) = c ∧
      coeffTag (N k) r p.1 = b} ≠ 0}.ncard : ℝ) ≤ H k)

/-- The clauses of `prepData` that hold eventually, for one compact range `R`, at one `k`. -/
def PrepAt (N : ℕ → ℝ) (d : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) (H : ℕ → ℝ)
    (θ : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (M : ℕ → ℕ) (R : ℝ) (k : ℕ) : Prop :=
  ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ ∧
  ∀ g : Fin (W k), θ k g ≤ ν k g ∧ θ k g Set.univ ≤ 1 ∧ MeasurableSet (E k g) ∧
    (∀ p ∈ E k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H k) ∧
    (∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ H k) ∧
    ENNReal.ofReal ((H k)⁻¹) • (((θ k g).prod volume).restrict (E k g)) ≤ (ρ k g).restrict (E k g) ∧
    (ρ k g).restrict (E k g) ≤ ENNReal.ofReal (H k) • (((θ k g).prod volume).restrict (E k g)) ∧
    (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → OnGrid (M k) r → GridClauses N d W ρ π H θ E M R k g r) ∧
    (∀ (r s b t : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
      (∃ m₁ m₂ m₃ : ℕ, r = (m₁ : ℝ) / (M k : ℝ) ∧ s = (m₂ : ℝ) / (M k : ℝ) ∧
        b = (m₃ : ℝ) / (M k : ℝ)) →
      ∀ (q a c : ℤ), θ k g {l | (l, t) ∈ E k g ∧ (⌊trajY l t / (N k ^ (-r))⌋ : ℤ) = q ∧
        (⌊trajX l t / (N k ^ (-s))⌋ : ℤ) = a ∧ l.2 1 ∈ velBin (N k) b c} ≤
        ENNReal.ofReal (H k * N k ^ (-r - d * s)) * π k g (velBin (N k) b c))

/-- The conclusion of o228: some `(H₀, θ, E₀)` satisfies `prepData`. -/
def PrepConclusion (N : ℕ → ℝ) (d : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) : Prop :=
  ∃ (H : ℕ → ℝ) (θ : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)),
    Subpower N H ∧ ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, PrepAt N d W ω ν ρ π H θ E M R k

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
