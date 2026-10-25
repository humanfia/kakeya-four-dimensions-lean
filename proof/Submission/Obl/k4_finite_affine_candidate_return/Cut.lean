-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/Cut.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
-- Shared same-obligation interface from o232 session x0859, commit c1a6d175.
import Submission.Obl.k4_finite_affine_candidate_return.Path
import Submission.Obl.k4_finite_affine_candidate_return.Stages

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory

noncomputable section

/-- The explicit original-to-parent affine line map. The hidden coordinate
is scaled by the parent's derivative unit. -/
def AffineCoefficients (t₀ q₀ scale : ℝ)
    (c₀ u₀ : EuclideanSpace ℝ (Fin 2)) (D₀ : Matrix (Fin 2) (Fin 2) ℝ)
    (correction : Fin 4 → ℝ) (l : Trajectory) : Fin 6 → ℝ :=
  let a₀ := l.2 0 + t₀ * l.2 3 - c₀ 0 - t₀ * u₀ 0
  let a₁ := l.2 1 + t₀ * l.2 4 - c₀ 1 - t₀ * u₀ 1
  let z₀ := D₀⁻¹ 0 0 * a₀ + D₀⁻¹ 0 1 * a₁
  let z₁ := D₀⁻¹ 1 0 * a₀ + D₀⁻¹ 1 1 * a₁
  let v₀ := q₀ * (D₀⁻¹ 0 0 * (l.2 3 - u₀ 0) + D₀⁻¹ 0 1 * (l.2 4 - u₀ 1))
  let v₁ := q₀ * (D₀⁻¹ 1 0 * (l.2 3 - u₀ 0) + D₀⁻¹ 1 1 * (l.2 4 - u₀ 1))
  ![z₀, z₁,
    scale * (l.2 2 + t₀ * l.2 5) - correction 0 - correction 2 * z₀ - correction 3 * z₁,
    v₀, v₁,
    scale * (q₀ * l.2 5) - correction 1 - correction 2 * v₀ - correction 3 * v₁]

/-- Concrete source information required for native-to-original return.
No conclusion about original candidates is included in this certificate.
`J` measures actual input slack; `st.K` may also contain the fixed stage
rounding error. The prior is conditioned on the FULL old parent assignment. -/
def NativeSource (n M : ℕ) (d₁ ℓ ρ gain ε unit Nk L : ℝ)
    {W : ℕ} (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (p : PathData W) (H : Fin W → Set Incidence) (st : EStage Trajectory) : Prop :=
  2 ≤ n ∧ 1 ≤ M ∧ 2 ≤ Nk ∧ 0 < L ∧ 0 ≤ d₁ ∧ 0 < ℓ ∧
  0 < ρ ∧ ρ ≤ 1 / 4 ∧ 0 < ε ∧ 0 < unit ∧
  unit * n ≤ 1 / 8 ∧ 0 < gain ∧ gain ≤ ρ * unit / (1000000 * ((n : ℝ) + 1)) ∧
  100 ≤ Nk ^ (ε / 1000000) ∧
  st.N = Nk ^ (unit * L) ∧ 2 ≤ st.N ∧ 1 ≤ st.K ∧
  st.K ≤ st.N ^ (ρ / (1000000 * ((n : ℝ) + 1))) ∧
  ∃ (parent : Fin p.C) (J t₀ q₀ : ℝ)
    (c₀ u₀ : EuclideanSpace ℝ (Fin 2)) (D₀ : Matrix (Fin 2) (Fin 2) ℝ)
    (correction : Fin 4 → ℝ)
    (old : (s : ℝ) → Fin (st.nl s) → Fin p.C),
  1 ≤ J ∧ J ≤ Nk ^ (ε / 1000000) ∧ p.κ ≤ J ∧
  IsProbabilityMeasure (ν (p.world parent)) ∧
  MeasurableSet (p.assigned parent) ∧ 0 < ν (p.world parent) (p.assigned parent) ∧
  0 < B (p.world parent) ∧
  t₀ = (p.bin parent : ℝ) / (2 : ℝ) ^ p.T (p.lev parent) ∧
  q₀ = ((2 : ℝ) ^ p.T (p.lev parent))⁻¹ ∧ D₀.det ≠ 0 ∧
  st.b = AffineCoefficients t₀ q₀ (B (p.world parent) / δ Nk (p.r (p.lev parent))) c₀ u₀ D₀ correction ∧
  st.ν = (ν (p.world parent) (p.assigned parent))⁻¹ •
    (ν (p.world parent)).restrict (p.assigned parent) ∧
  st.ρ ≤ ENNReal.ofReal J •
    ((ENNReal.ofReal q₀ * ν (p.world parent) (p.assigned parent))⁻¹ •
      Measure.map (fun z : Incidence => (z.1, (z.2 - t₀) / q₀))
        (((ν (p.world parent)).prod volume).restrict
          (H (p.world parent) ∩ (p.assigned parent ×ˢ Set.Icc t₀ (t₀ + q₀))))) ∧
  (∀ l ∈ p.assigned parent, |st.b l 0| + |st.b l 1| + |st.b l 3| + |st.b l 4| ≤ J) ∧
  J + st.N + st.N ^ ℓ + |δ Nk (p.r (p.lev parent))| +
    |(δ Nk (p.r (p.lev parent)))⁻¹| + |B (p.world parent)| + |(B (p.world parent))⁻¹| +
    |t₀| + |q₀| + |q₀⁻¹| + ‖c₀‖ + ‖u₀‖ +
    (∑ e : Fin 4, |correction e|) +
    (∑ e : Fin 2, ∑ e' : Fin 2, (|D₀ e e'| + |D₀⁻¹ e e'|)) ≤ Nk ^ M ∧
  (∑ e ∈ st.P.support, |st.P.coeff e|) ≤ Nk ^ M ∧
  ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (st.nl s),
    p.world (old s i) = p.world parent ∧
    st.A s i = p.assigned (old s i) ∧
    p.assigned (old s i) ⊆ p.assigned parent ∧
    MeasurableSet (st.B s i) ∧ st.B s i ⊆ st.A s i ∧
    0 < ν (p.world parent) (p.assigned (old s i)) ∧
    (∀ t : ℝ,
      t ∈ Set.Icc ((p.bin (old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (old s i)))
        (((p.bin (old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (old s i))) ↔
      (t - t₀) / q₀ ∈ IS (st.T s) (st.j s i)) ∧
    |p.r (p.lev (old s i)) - p.r (p.lev parent) - unit * L * s| ≤
      ρ * unit * L / (1000000 * ((n : ℝ) + 1)) ∧
    p.r (p.lev (old s i)) ≤ L / 2 ∧
    st.N ^ (-ℓ * s) / st.K ≤
      |((q₀ / (((2 : ℝ) ^ p.T (p.lev (old s i)))⁻¹)) •
        (D₀⁻¹ * p.frame (old s i))).det| ∧
    ENNReal.ofReal ((((2 : ℝ) ^ p.T (p.lev (old s i)))⁻¹) / J) *
      ν (p.world parent) (p.assigned (old s i)) ≤
      ((ν (p.world parent)).prod volume)
        {z | z ∈ H (p.world parent) ∧ z.1 ∈ p.assigned (old s i) ∧
          z.2 ∈ Set.Icc ((p.bin (old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (old s i)))
            (((p.bin (old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (old s i)))} ∧
    ‖p.velocity (old s i)‖ +
      (∑ e : Fin 2, ∑ e' : Fin 2,
        (|p.frame (old s i) e e'| + |(p.frame (old s i))⁻¹ e e'|)) ≤ Nk ^ M ∧
    (∑ e ∈ (st.F s i).support, |(st.F s i).coeff e|) ≤ Nk ^ M

/-- A supply of nonempty finite model data independent of the original
problem. Used after an original candidate has already been found. -/
def SyntheticModels : Prop :=
  ∀ d₁ κ₁ ℓ S : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → ∀ n : ℕ, 2 ≤ n →
    ∃ st : EStage Trajectory, StageGood d₁ κ₁ ℓ S n st

/-- Finite probability and true-label preparation, with explicit original
source data. This assertion contains no native candidate and no return
implication. The tangent unit and grid precede the exact problem. -/
def SourcePreparation : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, 2 ≤ n →
    ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ unit : ℝ),
      FineGrid m s gain ρ ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ₀ ∧ δ₀ ≤ ρ * gain ∧
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
      (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
      ∀ Mp Dp : ℕ, ∃ M : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∀ p : PathData (W k), p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁
          m s δ₀ Mp Dp σ →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod volume) (TerminalInc (W k) p.C m p.lev p.world p.counted w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w) →
        MixedCandidate (N k) L (W k) (ν k) (B k) M d₁ ρ gain ε
          p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H ∨
        ∃ st : EStage Trajectory, StageGood d₁ κ₁ ℓ S n st ∧
          NativeSource n M d₁ ℓ ρ gain ε unit (N k) L (ν k) (B k) p H st

/-- Uniform transport of candidates from a concrete affine source. The
coefficient exponent is chosen before every original loss and every source.
No pure or joint caps, entropy assumption, or model existence is assumed. -/
def SourceReturn : Prop :=
  ∀ n M : ℕ, ∃ Mc : ℕ,
    ∀ (d₁ κ₁ ℓ ρ gain ε unit Nk L : ℝ) (W : ℕ)
      (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
      (E : Fin W → Set Incidence) (B : Fin W → ℝ) (f : ℝ → ℝ)
      (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ)
      (p : PathData W) (H : Fin W → Set Incidence) (st : EStage Trajectory),
      p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ →
      (∀ w, MeasurableSet (H w)) →
      NativeSource n M d₁ ℓ ρ gain ε unit Nk L ν B p H st →
      ∀ R : ℝ, 1 < R → R ≤ n → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ρ / (4 * R) →
        ECand d₁ ℓ 1 st R ε' →
        MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world p.bin
          p.velocity p.frame p.assigned H

end
end Submission.Obl.k4_finite_affine_candidate_return
