import Submission.Obl.k4_scalar_noisy_block_packets.DirectAngular

/-!
Interfaces for the scalar crop. The first two coefficients are the affine intercept and
velocity; the remaining three quadratic coefficients do not change under cropping.
-/
namespace Submission.Obl.k4_scalar_noisy_block_packets

noncomputable section

/-- The endpoint information needed by the subsequent measure and packet arguments. -/
def EndpointData (d s m C₀ : ℝ) (angular : Bool) (η : ℝ) (F : ℝ → ℝ → ℝ)
    (L u₀ d' S' U' : ℝ) : Prop :=
  0 < L ∧ L ≤ s ∧ 0 ≤ u₀ ∧ u₀ ≤ m + η ∧
  0 ≤ d' ∧ d' < 1 ∧ 0 < S' ∧ 0 < U' ∧
  u₀ + U' ≤ 4 * (m + s + 1) ∧
  s - L ≤ η ∧ F L u₀ ≤ d * s - C₀ + η ∧
  (angular = true → u₀ = 0) ∧
  (∀ r : ℝ, 0 ≤ r → r ≤ L → F L u₀ - F r u₀ ≤ d' * (L - r)) ∧
  (∀ u : ℝ, 0 ≤ u → u ≤ U' → F L u₀ + S' * u ≤ F L (u₀ + u))

/-- Scalar crop cells at the exact power scale, with disjoint integer labels. -/
def scalarCell (N u₀ : ℝ) (z : Fin 2 → ℤ) : Set Line :=
  {l | (⌊l.2 0 / N ^ (-u₀)⌋ : ℤ) = z 0 ∧
    (⌊l.2 1 / N ^ (-u₀)⌋ : ℤ) = z 1}

def scalarCropLine (N u₀ : ℝ) (z : Fin 2 → ℤ) (l : Line) : Line :=
  (l.1, ![l.2 0 / N ^ (-u₀) - (z 0 : ℝ),
    l.2 1 / N ^ (-u₀) - (z 1 : ℝ), l.2 2, l.2 3, l.2 4])

def scalarCropPoint (N u₀ : ℝ) (z : Fin 2 → ℤ) (p : Inc) : Inc :=
  (scalarCropLine N u₀ z p.1, p.2)

/-- Finite identities used by the proved affine packet lifting lemma. -/
def LiftFacts (N : ℕ → ℝ) (u₀ : ℝ) (W : ℕ → ℕ)
    (ν₀ : ℕ → MeasureTheory.Measure Line) (E₀ : ℕ → Set Inc)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc)
    (p : (k : ℕ) → Fin (W k) → ℝ)
    (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) : Prop :=
  (∀ k γ, MeasurableSet (scalarCell (N k) u₀ (z k γ))) ∧
  (∀ k γ, Measurable (scalarCropLine (N k) u₀ (z k γ))) ∧
  (∀ k, Pairwise (fun γ γ' => Disjoint
    (scalarCell (N k) u₀ (z k γ)) (scalarCell (N k) u₀ (z k γ')))) ∧
  (∀ k γ Z, MeasurableSet Z →
    ENNReal.ofReal (p k γ) * selected (ν k γ) (E k γ) Z =
      selected (ν₀ k) (E₀ k)
        {a | a.1 ∈ scalarCell (N k) u₀ (z k γ) ∧
          (scalarCropLine (N k) u₀ (z k γ) a.1, a.2) ∈ Z}) ∧
  (∀ k γ l, l ∈ scalarCell (N k) u₀ (z k γ) → ∀ t,
    x (scalarCropLine (N k) u₀ (z k γ) l) t = x l t) ∧
  (∀ k γ l, l ∈ scalarCell (N k) u₀ (z k γ) → ∀ t,
    y (scalarCropLine (N k) u₀ (z k γ) l) t =
      (y l t - N k ^ (-u₀) * (z k γ 0 : ℝ) -
        t * (N k ^ (-u₀) * (z k γ 1 : ℝ))) / N k ^ (-u₀)) ∧
  (∀ k γ l, l ∈ scalarCell (N k) u₀ (z k γ) →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, |y (scalarCropLine (N k) u₀ (z k γ) l) t| ≤ 2)

/-- Exact conditional-law identities, retained prior weights and their common exponent.
The same subpower bound controls crop centers and the normalized worlds. -/
def ScalarCrops (N K : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure Line)
    (E₀ : ℕ → Set Inc) (u₀ α : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc)
    (p : (k : ℕ) → Fin (W k) → ℝ)
    (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) (ρ : ℕ → ℝ) : Prop :=
  (∀ k, MeasureTheory.IsProbabilityMeasure (ν₀ k) ∧ MeasurableSet (E₀ k) ∧
    E₀ k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) ∧
  (∀ k, Function.Injective (z k)) ∧
  (∀ k γ, 0 < p k γ ∧
    p k γ = ((ν₀ k) (scalarCell (N k) u₀ (z k γ))).toReal ∧
    ν k γ = (ENNReal.ofReal (p k γ))⁻¹ •
      MeasureTheory.Measure.map (scalarCropLine (N k) u₀ (z k γ))
        ((ν₀ k).restrict (scalarCell (N k) u₀ (z k γ))) ∧
    E k γ = scalarCropPoint (N k) u₀ (z k γ) ''
      (E₀ k ∩ (scalarCell (N k) u₀ (z k γ) ×ˢ Set.univ)) ∧
    |N k ^ (-u₀) * (z k γ 0 : ℝ)| +
      |N k ^ (-u₀) * (z k γ 1 : ℝ)| ≤ K k) ∧
  (∀ k, 0 < ρ k ∧ ρ k ≤ 1 ∧ (∑ γ, p k γ) = ρ k ∧
    ∀ γ, ω k γ = p k γ / ρ k) ∧
  (∀ τ : ℝ, 0 < τ → ∀ᶠ k in Filter.atTop, (ρ k)⁻¹ ≤ N k ^ τ) ∧
  (∀ τ : ℝ, 0 < τ → ∀ᶠ k in Filter.atTop,
    ∀ γ, N k ^ (-α - τ) ≤ p k γ ∧ p k γ ≤ N k ^ (-α + τ)) ∧
  LiftFacts N u₀ W ν₀ E₀ ν E p z

/-- Polynomial format and positive weighted incidence mass, without density profiles. -/
def WorldFormat (N K : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc) : Prop :=
  ∃ M D : ℕ, 1 ≤ M ∧ 1 ≤ D ∧
  (∀ k, (W k : ℝ) ≤ N k ^ (M : ℝ) ∧ (∀ γ, 0 ≤ ω k γ) ∧
    (∑ γ, ω k γ) = 1 ∧
    (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧
      (∃ n : ℕ, (n : ℝ) ≤ N k ^ (M : ℝ) ∧
        ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ)),
          (∀ j, 0 ≤ h j ∧ h j ≤ N k ^ (M : ℝ) ∧
            (i j : ℝ) ≤ N k ^ (M : ℝ) ∧
            Format 5 (N k ^ (M : ℝ)) D (B j) ∧
            ∀ b ∈ B j, ∀ e, |b e| ≤ N k ^ (M : ℝ)) ∧
          ν k γ = ∑ j, ENNReal.ofReal (h j) •
            MeasureTheory.Measure.map (fun b => (i j, b))
              (MeasureTheory.volume.restrict (B j))) ∧
      (∀ᵐ l ∂ν k γ, ∀ e, |l.2 e| ≤ K k) ∧ MeasurableSet (E k γ) ∧
      E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
      (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ (M : ℝ)) ∧
      (∀ i : ℕ, Format 6 (N k ^ (M : ℝ)) D
        {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ E k γ})) ∧
    ENNReal.ofReal ((K k)⁻¹) ≤
      ∑ γ, ENNReal.ofReal (ω k γ) * selected (ν k γ) (E k γ) Set.univ)

/-- Precisely the hypotheses supplied to the assumed scalar exact packet assertion. -/
def AngularWorlds (N K : ℕ → ℝ) (L d S U : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc) (f : ℝ → ℝ) : Prop :=
  WorldFormat N K W ω ν E ∧
  ∃ (g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → Joint → ENNReal),
    (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧
      MeasureTheory.Measure.map (obs (N k) r) (selected (ν k γ) (E k γ)) =
        (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) ∧
    (∀ k γ u, 0 < u → u ≤ U → Measurable (G k γ u) ∧
      MeasureTheory.Measure.map (aug (N k) L u) (selected (ν k γ) (E k γ)) =
        ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod
          MeasureTheory.Measure.count).withDensity (G k γ u)) ∧
    (∀ r r' : ℝ, 0 ≤ r → r ≤ r' → r' ≤ L →
      0 ≤ f r' - f r ∧ f r' - f r ≤ r' - r) ∧
    (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in Filter.atTop,
        (∑ γ, ENNReal.ofReal (ω k γ) * selected (ν k γ) (E k γ)
          {p | g k γ r (obs (N k) r p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨
            ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r (obs (N k) r p)}) ≤
          ENNReal.ofReal (N k ^ (-c))) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) ∧
    (∀ u τ : ℝ, 0 < u → u ≤ U → 0 < τ → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in Filter.atTop,
        (∑ γ, ENNReal.ofReal (ω k γ) * selected (ν k γ) (E k γ)
          {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) <
            G k γ u (aug (N k) L u p)}) ≤ ENNReal.ofReal (N k ^ (-c)))

/-- The finite-dimensional compact-maximizer problem, independent of any law. -/
def ProfileSelection : Prop :=
  ∀ (d s m S U C₀ : ℝ) (angular : Bool) (F : ℝ → ℝ → ℝ),
    0 ≤ d → d < 1 → 0 < s → s < m → 0 < S → 0 < U → U < m →
    ProfileShape d s m S U C₀ angular F →
    ∀ η : ℝ, 0 < η → ∃ L u₀ d' S' U' : ℝ,
      EndpointData d s m C₀ angular η F L u₀ d' S' U'

/-- Select conditional scalar worlds at one prior-mass exponent and preserve format. -/
def CropSelection : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) →
    Filter.Tendsto N Filter.atTop Filter.atTop → Subpower N K →
    ∀ (m u₀ : ℝ) (M : ℕ) (H J : ℕ → ℕ)
      (b₀ : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
      (w : (k : ℕ) → Fin (H k) → ℝ)
      (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool),
      0 < m → 0 ≤ u₀ →
      (∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) →
      ∃ (ψ : ℕ → ℕ) (K' : ℕ → ℝ) (α : ℝ) (W : ℕ → ℕ)
        (ω : (k : ℕ) → Fin (W k) → ℝ)
        (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line)
        (E : (k : ℕ) → Fin (W k) → Set Inc)
        (p : (k : ℕ) → Fin (W k) → ℝ)
        (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) (ρ : ℕ → ℝ),
        StrictMono ψ ∧ Subpower (N ∘ ψ) K' ∧
        ScalarCrops (N ∘ ψ) K'
          (fun k => MarkedPrior ((N (ψ k)) ^ (-m)) (H (ψ k)) (b₀ (ψ k)) (w (ψ k)))
          (fun k => MarkedEvent (H (ψ k)) (J (ψ k)) (mark (ψ k)))
          u₀ α W ω ν E p z ρ ∧
        WorldFormat (N ∘ ψ) K' W ω ν E

/-- Transport a source joint profile through any selected family of the stated crops. -/
def CropTypicality : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) →
    Filter.Tendsto N Filter.atTop Filter.atTop → Subpower N K →
    ∀ (ν₀ : ℕ → MeasureTheory.Measure Line) (E₀ : ℕ → Set Inc)
      (d s m S U C₀ η L u₀ d' S' U' α : ℝ) (angular : Bool)
      (F : ℝ → ℝ → ℝ),
      0 ≤ d → d < 1 → 0 < s → s < m → 0 < η →
      ProfileShape d s m S U C₀ angular F →
      EndpointData d s m C₀ angular η F L u₀ d' S' U' →
      Homogeneous N s (4 * (m + s + 1)) (fun k => selected (ν₀ k) (E₀ k)) F →
      ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
        (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line)
        (E : (k : ℕ) → Fin (W k) → Set Inc)
        (p : (k : ℕ) → Fin (W k) → ℝ)
        (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) (ρ : ℕ → ℝ),
        ScalarCrops N K ν₀ E₀ u₀ α W ω ν E p z ρ →
        WorldFormat N K W ω ν E →
        AngularWorlds N K L d' S' U' W ω ν E (fun r => F r u₀ + u₀ - α)

end
end Submission.Obl.k4_scalar_noisy_block_packets
