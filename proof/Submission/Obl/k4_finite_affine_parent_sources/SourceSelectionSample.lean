-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceComponents
import Submission.Obl.k4_finite_affine_parent_sources.SourceQGroups
import Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.ConditionalRawHiddenCaps

/-!
# The per-sample selection: interface for the outer schedule

`SelectionSample` is the per-sample content of `SourceSelectionSpec`. At one sample `k`, for a
valid path `p` and a residual `H` (inside the terminal path) that already lies in the original
density masks at a depth grid `Qd`, the lower density mask at depth `L`, the angular masks at a
depth menu `Qa`, avoids every axis-deficient label of nominal depth at most `1/2` and keeps mass
`1/(4κ²)`, either the original mixed candidate holds on `H`, or the selection package
`SelectionPackage` holds with the given floor `τ`: a parent `a` in the band `[1/8, 1/4]`, a
prepared set `Gm ⊆ H(world a)` with room above `m τ packet(a)`, and a palette `π`, such that
every source model over a subset of `Gm` has its velocity caps and `EH2` at range `n`.

The fixed numbers enter through `stagePower n ρ = ρ/(10⁶(n+1))`, the budget exponent
`selectionBudget n ρ u L = u L θ / (100 (groupsC + 2))`, and the window `T` of the uniform
raw-hidden upgrade (`RawUpgrade`, from `SignalUpgrade.uniform_conditional_raw_hidden_caps_from_signal`).
The outer schedule (x0891) chooses them and pays the masks from the frozen typicality estimates.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial

noncomputable section

/-- The oscillation-group exponent used by the selection (groups cover all but `K^(-1)`). -/
def groupsC : ℕ := (exists_groupsProp 1).choose

theorem groupsC_spec : 1 ≤ groupsC ∧ GroupsProp 1 groupsC := (exists_groupsProp 1).choose_spec

/-- The power of the source models' constant: `θ = ρ / (10⁶ (n + 1))`. -/
def stagePower (n : ℕ) (ρ : ℝ) : ℝ := ρ / (1000000 * ((n : ℝ) + 1))

/-- The budget exponent of the selection: every loss of the selection is a power of `N^b₀`. -/
def selectionBudget (n : ℕ) (ρ u L : ℝ) : ℝ :=
  u * L * stagePower n ρ / (100 * ((groupsC : ℝ) + 2))

/-- A fixed constant that the sample's budget `N^b₀` must exceed. -/
def selectionConst (m n : ℕ) (T κ₁ ρ u L : ℝ) : ℝ :=
  10 ^ 40 * ((m : ℝ) + 2) ^ 4 * (((n : ℝ) + 2) * (T + 2) * ((groupsC : ℝ) + 2)) ^ 8 /
    (κ₁ * ρ * u * min L 1) ^ 8

/-- The uniform signal-to-raw upgrade at range `R` with window `T` and threshold `N₀`
(the conclusion of `SignalUpgrade.uniform_conditional_raw_hidden_caps_from_signal`). -/
def RawUpgrade (R T N₀ : ℝ) : Prop :=
  ∀ N K d : ℝ, N₀ ≤ N → 1 ≤ K → K ≤ N → 0 ≤ d → d ≤ 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
      (x : Ω → Fin 4 → ℝ), Measurable x →
      ∀ P : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 →
      (∀ᵐ p ∂μ, (∀ i : Fin 3, |x p i.castSucc| ≤ K) ∧
        |eval (x p) P| ≤ K ∧ |eval (x p) (pderiv (3 : Fin 4) P)| ≤ K ∧
        |eval (x p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K) →
      ∀ (C : Set Ω) (β : ENNReal), β ≠ ⊤ →
      (∀ u t : ℝ, T⁻¹ ≤ u → u ≤ T → 0 ≤ t → t ≤ T →
        ∀ (q : Fin 3 → ℤ) (j : ℤ),
          μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-u))
              (fun i : Fin 3 => x p i.castSucc) = q ∧
            ⌊eval (x p) P / N ^ (-t)⌋ = j ∧ p ∈ C} ≤
            ENNReal.ofReal (K * N ^ (-3 * u - d * t)) * β) →
      ∀ r s : ℝ, 0 ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
        ∀ (q : Fin 3 → ℤ) (j : ℤ),
          μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
              (fun i : Fin 3 => x p i.castSucc) = q ∧
            ⌊x p 3 / N ^ (-s)⌋ = j ∧ p ∈ C} ≤
            ENNReal.ofReal (400 * K ^ 2 * N ^ (-3 * r - d * s)) * β

/-- The upgrade window exists (x0735's theorem, adapted by x0807 in `SignalUpgrade`). -/
theorem exists_rawUpgrade (R : ℝ) (hR : 1 ≤ R) :
    ∃ T N₀ : ℝ, R < T ∧ 1 < T ∧ 2 ≤ N₀ ∧ RawUpgrade R T N₀ := by
  obtain ⟨T, N₀, hRT, hT, hN₀, h⟩ :=
    SignalUpgrade.uniform_conditional_raw_hidden_caps_from_signal R hR
  exact ⟨T, N₀, hRT, hT, hN₀, fun N K d hN hK hKN hd hd1 Ω _ μ _ x hx P hP hgood C β hβ hcap =>
    h N K d hN hK hKN hd hd1 Ω μ x hx P hP hgood C β hβ hcap⟩

/-- The pointwise original masks of the selection on an incidence `z` of a world with
hidden scale `Bw`, density `gw` and angular density `Gw`. -/
def SelectionMask (Nk L S τd τa : ℝ) (f : ℝ → ℝ) (Bw : ℝ)
    (gw : ℝ → Observation → ENNReal) (Gw : ℝ → Observation × (Fin 2 → ℤ) → ENNReal)
    (Qd Qa : Finset ℝ) (z : Incidence) : Prop :=
  (∀ r ∈ Qd, gw r (obs Bw (δ Nk r) z) ≤ ENNReal.ofReal (Nk ^ (-f r + τd))) ∧
  ENNReal.ofReal (Nk ^ (-f L - τd)) ≤ gw L (obs Bw (δ Nk L) z) ∧
  ∀ r ∈ Qa, Gw r (obs Bw (δ Nk L) z, fun j : Fin 2 => ⌊v z.1 j / δ Nk r⌋) ≤
    ENNReal.ofReal (Nk ^ (-f L - S * r + τa))

/-- The selection package of `SourceSelectionSpec` with a given floor `τ`. -/
def SelectionPackage {W : ℕ} (p : PathData W) (ν : Fin W → Measure Trajectory)
    (B : Fin W → ℝ) (Nk L : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (n : ℕ) (ℓ ρ u d₁ S : ℝ)
    (H : Fin W → Set Incidence) (τ : ℝ) : Prop :=
  ∃ (a : Fin p.C) (Gm : Set Incidence) (π : Measure ℝ),
    MeasurableSet Gm ∧ Gm ⊆ H (p.world a) ∧
    (m : ℝ) * τ * (((ν (p.world a)).prod volume) (p.packet a)).toReal <
      (((ν (p.world a)).prod volume) (Gm ∩ p.counted a)).toReal ∧
    1 / 8 ≤ s (p.lev a) ∧ s (p.lev a) ≤ 1 / 4 ∧
    (∀ b : Fin p.C, p.world b = p.world a → p.lev a ≤ p.lev b → s (p.lev b) ≤ 1 / 2 →
      (Gm ∩ p.counted b).Nonempty →
      ¬p.axisDeficient (sourceAxisMask n ℓ ρ u Nk L) b) ∧
    s (p.lev a) + u + δ₀ ≤ 1 / 2 ∧
    IsProbabilityMeasure π ∧
    ∀ D : SourceData p, D.parent = a → D.π = π → D.S ⊆ Gm → MeasurableSet D.S →
      D.S.Nonempty → D.D₀ = MajorFrame.frame (p.frame a) →
      D.K = (Nk ^ (u * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1))) →
      D.depth = sourceDepth m s (p.lev a) u →
      D.S ⊆ p.assigned a ×ˢ Ioo ((p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
        (((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a)) →
      (∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
        z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) →
      ¬p.axisDeficient (sourceAxisMask n ℓ ρ u Nk L) a →
      (∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
        ¬p.axisDeficient (sourceAxisMask n ℓ ρ u Nk L) (D.old x i)) →
      ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet D.parent) ≤
        ((ν D.w₀).prod volume) (D.S ∩ p.counted D.parent) →
      (∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
        ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old x i)) ≤
          ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old x i))) →
      D.VelCaps n u Nk L ν B ∧ EH2 d₁ S (D.stage Nk L u ν B) n

/-- **The per-sample selection.** -/
def SelectionSample : Prop :=
  ∀ (d₁ κ₁ ℓ S η ρ : ℝ) (n : ℕ) (u gain : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ)
    (N K : ℕ → ℝ) (L d : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence)
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ)
    (f : ℝ → ℝ) (g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → Observation × (Fin 2 → ℤ) → ENNReal)
    (Mp Dp Mprep : ℕ) (ε σ : ℝ) (k : ℕ) (p : PathData (W k))
    (H : Fin (W k) → Set Incidence) (T N₀ τ τd τa hd ma : ℝ) (Qd Qa : Finset ℝ),
    -- the standing hypotheses of `SourceSelectionSpec`
    0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 → 0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ →
    ρ ≤ 1 / 4 → 2 ≤ n → 0 < u → 0 < gain → FineGrid m s gain ρ → 0 < δ₀ →
    δ₀ ≤ ρ * gain → prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) → 0 < ε → 0 < σ →
    p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ →
    -- the fixed numbers
    (n : ℝ) < T → RawUpgrade n T N₀ →
    u * T * (((n : ℝ) + 2) ^ 2 * ((groupsC : ℝ) + 2)) * 10 ^ 15 ≤ κ₁ * ρ →
    u * ((n : ℝ) + 2) ≤ η → u * ((n : ℝ) + 2) ≤ ℓ / 8 →
    gain * (10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2)) ≤ u →
    -- the depth grid of the density masks and the depth menu of the angular masks
    L ∈ Qd → (∀ r ∈ Qd, 0 ≤ r ∧ r ≤ L) → 0 < hd →
    (∀ t, 0 ≤ t → t ≤ L → ∃ r ∈ Qd, t ≤ r ∧ r ≤ t + hd) →
    (∀ r ∈ Qa, 0 < r ∧ r ≤ η * L) → 0 < ma →
    (∀ t, u * L / n ≤ t → t ≤ u * L * n → ∃ r ∈ Qa, t - ma ≤ r ∧ r ≤ t) →
    0 ≤ τd → 0 ≤ τa → τd ≤ selectionBudget n ρ u L → τa ≤ selectionBudget n ρ u L →
    hd ≤ selectionBudget n ρ u L → ma ≤ selectionBudget n ρ u L →
    -- the sample
    N₀ ≤ N k ^ (u * L) →
    p.κ ^ 20 * K k ^ 4 * selectionConst m n T κ₁ ρ u L ≤ N k ^ selectionBudget n ρ u L →
    2 * p.κ ≤ N k ^ (Mprep : ℝ) →
    0 < τ → τ * (10 ^ 6 * ((m : ℝ) + 1) ^ 2 * p.κ ^ 12) ≤ 1 →
    -- the residual: terminal, masked, axis-full, and heavy
    (∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted w) →
    (∀ w, ∀ z ∈ H w, SelectionMask (N k) L S τd τa f (B k w) (g k w) (G k w) Qd Qa z) →
    (∀ b : Fin p.C, s (p.lev b) ≤ 1 / 2 → (H (p.world b) ∩ p.counted b).Nonempty →
      ¬p.axisDeficient (sourceAxisMask n ℓ ρ u (N k) L) b ∧
      ((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
          N k ^ (u * L * min (stagePower n ρ / 1000) (ℓ / 1000)) ≤
        Submission.Obl.k4_compatible_pair_frame_preparation.Construction.r₁ (p.frame b)) →
    ENNReal.ofReal (1 / (4 * p.κ ^ 2)) ≤
      ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w) →
    MixedCandidate (N k) L (W k) (ν k) (B k) Mprep d₁ ρ gain ε
        p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H ∨
      SelectionPackage p (ν k) (B k) (N k) L m s δ₀ n ℓ ρ u d₁ S H τ

end

end Submission.Obl.k4_finite_affine_parent_sources
