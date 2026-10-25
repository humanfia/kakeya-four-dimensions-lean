import Submission.Obl.k4_critical_switching_state_preparation.PreparedModel
import Submission.Lib.K4QuadSheetMatching.Matching

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set
open Submission.Obl.k4_critical_switching_state_preparation

/-- Common asymptotic parameters; the contact and horizontal contexts use the
same imported data, basic bounds, mesh caps, nesting and candidate event. -/
structure Parameters {α : Type} [MeasurableSpace α] (cfg : Data α) : Prop where
  scale : ∀ k, 2 ≤ cfg.N k
  scale_limit : Filter.Tendsto cfg.N Filter.atTop Filter.atTop
  subpower : (∀ k, 1 ≤ cfg.K k) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, cfg.K k ≤ cfg.N k ^ ε
  dimension_nonneg : 0 ≤ cfg.d
  dimension_lt_one : cfg.d < 1
  rate_pos : 0 < cfg.κ
  rate_le_one : cfg.κ ≤ 1
  transverse_pos : 0 < cfg.ℓ
  palette_pos : 0 < cfg.S
  palette_le_one : cfg.S ≤ 1
  depth_pos : 0 < cfg.U
  defect_pos : 0 < cfg.e₀

/-- The original atlas with the false horizontal flag, exactly as frozen. -/
def ContactAtlas {α : Type} [MeasurableSpace α] (cfg : Data α) : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → (fun (q : ℝ) (a g : ℝ → ℝ) => cfg.N k ^ (cfg.κ * s) / cfg.K k ≤ (2 : ℝ) ^ cfg.T k s ∧ (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) ∧ (∀ i, MeasurableSet (cfg.A k s i) ∧ MeasurableSet (cfg.B k s i) ∧ cfg.B k s i ⊆ cfg.A k s i) ∧ (∀ i i', i ≠ i' → cfg.j k s i = cfg.j k s i' → Disjoint (cfg.A k s i) (cfg.A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ cfg.d * q ^ 2 * g s / cfg.K k) ≤ cfg.ν k (cfg.A k s i) ∧ cfg.ν k (cfg.A k s i) ≤ ENNReal.ofReal (cfg.K k * a s ^ cfg.d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / cfg.K k) * cfg.ν k (cfg.A k s i) ≤ cfg.μ k (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)) ∧ (∀ e, |cfg.c k s i e| ≤ cfg.K k) ∧ (cfg.F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ cfg.A k s i, ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i), |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤ cfg.K k * q ∧ |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤ cfg.K k * q * g s ∧ |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤ cfg.K k * g s) ∧ (∀ l ∈ cfg.B k s i, cfg.fit k (cfg.K k) (a s) (cfg.F k s i) l (Data.I (cfg.T k s) (cfg.j k s i))) ∧ (∀ᵐ p ∂cfg.μ k, p.1 ∈ cfg.B k s i → p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) → (cfg.K k)⁻¹ ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (cfg.F k s i))|) ∧ ((false : Bool) = true → cfg.P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) ∧ |cfg.c k s i 3 + cfg.c k s i 0 + ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q * cfg.c k s i 1| + |cfg.c k s i 4 - ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ cfg.K k * q ∧ (∃ L : Fin 4 → ℝ, cfg.F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ cfg.K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ cfg.B k s i, ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i), |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ cfg.K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i)) ∧ (∀ (i : Fin (cfg.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (cfg.K k * q) * cfg.ν k (cfg.A k s i) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(cfg.T k s : ℤ))) (fun s => cfg.N k ^ (-s)) (fun s => cfg.N k ^ (-cfg.ℓ * s)))


/-- The original contact equation is an independent hypothesis in this child. -/
def ContactEquation {α : Type} [MeasurableSpace α] (cfg : Data α) : Prop :=
  ∀ k, ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)

/-- Simultaneous affine palettes retain the original residual law and its mass. -/
def AffinePalettes {α : Type} [MeasurableSpace α] (cfg : Data α) : Prop :=
  ∃ U₁ : ℝ, 0 < U₁ ∧ U₁ ≤ cfg.U ∧
    ∀ (m : ℕ) (σ : Fin m → ℝ), (∀ h, 0 < σ h ∧ σ h ≤ U₁) →
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ cfg.N k ^ ε) ∧
      ∀ᶠ k in Filter.atTop, ∃ (M : Fin m → ℕ)
        (L : (h : Fin m) → Fin (cfg.n k (σ h)) → Fin (M h) → Fin 4 → ℝ),
        (∀ h, (M h : ℝ) ≤ H k) ∧
        ENNReal.ofReal ((cfg.K k)⁻¹ / 2) ≤ cfg.ρ k {p | ∀ h,
          ∃ (i : Fin (cfg.n k (σ h))) (u : Fin (M h)),
          p.1 ∈ cfg.B k (σ h) i ∧ p.2 ∈ Data.I (cfg.T k (σ h)) (cfg.j k (σ h) i) ∧
          ∀ t ∈ Data.I (cfg.T k (σ h)) (cfg.j k (σ h) i),
            |(cfg.x k p.1 t) 3 - (L h i u 0 + L h i u 1 * t +
              L h i u 2 * (cfg.x k p.1 t) 1 + L h i u 3 * (cfg.x k p.1 t) 2)| ≤
              H k * cfg.N k ^ (-σ h)}

/-- The supplied full horizontal candidate principle, using the imported
horizontal atlas and unchanged full original candidate denominators. -/
def HorizontalPrinciple : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), Parameters cfg →
    cfg.ℓ = cfg.κ → cfg.Basic → cfg.Caps → cfg.Atlas → cfg.Nested → cfg.Candidates

/-- All hypotheses of the contact source, with its original measures and
assignment weights still present. -/
structure ContactProblem {α : Type} [MeasurableSpace α] (cfg : Data α) : Prop where
  parameters : Parameters cfg
  basic : cfg.Basic
  caps : cfg.Caps
  atlas : ContactAtlas cfg
  nested : cfg.Nested
  contact : ContactEquation cfg
  equal_rates : cfg.ℓ = cfg.κ
  palettes : AffinePalettes cfg

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
