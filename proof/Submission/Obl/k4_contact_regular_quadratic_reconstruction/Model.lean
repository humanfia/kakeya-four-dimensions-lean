import Submission.Obl.k4_critical_switching_state_preparation.PreparedModel
import Submission.Lib.K4ContactNormalization.ResidualNormalization

/-!
We use the data record and original observation formulas of the accepted o238
module. Its atlas is horizontal; `OriginalAtlas` below instead spells out the
frozen nonhorizontal atlas. No horizontal affine representation is imposed.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation.Data

noncomputable section

abbrev Model (α : Type) [MeasurableSpace α] :=
  Submission.Obl.k4_critical_switching_state_preparation.Data α

namespace Model

variable {α : Type} [MeasurableSpace α] (cfg : Model α)

def OriginalAtlas : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → (fun (q : ℝ) (a g : ℝ → ℝ) => cfg.N k ^ (cfg.κ * s) / cfg.K k ≤ (2 : ℝ) ^ cfg.T k s ∧ (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) ∧ (∀ i, MeasurableSet (cfg.A k s i) ∧ MeasurableSet (cfg.B k s i) ∧ cfg.B k s i ⊆ cfg.A k s i) ∧ (∀ i i', i ≠ i' → cfg.j k s i = cfg.j k s i' → Disjoint (cfg.A k s i) (cfg.A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ cfg.d * q ^ 2 * g s / cfg.K k) ≤ cfg.ν k (cfg.A k s i) ∧ cfg.ν k (cfg.A k s i) ≤ ENNReal.ofReal (cfg.K k * a s ^ cfg.d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / cfg.K k) * cfg.ν k (cfg.A k s i) ≤ cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) ∧ (∀ e, |cfg.c k s i e| ≤ cfg.K k) ∧ (cfg.F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ cfg.A k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i), |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤ cfg.K k * q ∧ |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤ cfg.K k * q * g s ∧ |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤ cfg.K k * g s) ∧ (∀ l ∈ cfg.B k s i, cfg.fit k (cfg.K k) (a s) (cfg.F k s i) l (I (cfg.T k s) (cfg.j k s i))) ∧ (∀ᵐ p ∂cfg.μ k, p.1 ∈ cfg.B k s i → p.2 ∈ I (cfg.T k s) (cfg.j k s i) → (cfg.K k)⁻¹ ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (cfg.F k s i))|) ∧ ((false : Bool) = true → cfg.P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) ∧ |cfg.c k s i 3 + cfg.c k s i 0 + ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q * cfg.c k s i 1| + |cfg.c k s i 4 - ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ cfg.K k * q ∧ (∃ L : Fin 4 → ℝ, cfg.F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ cfg.K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i), |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ cfg.K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i)) ∧ (∀ (i : Fin (cfg.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (cfg.K k * q) * cfg.ν k (cfg.A k s i) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(cfg.T k s : ℤ))) (fun s => cfg.N k ^ (-s)) (fun s => cfg.N k ^ (-cfg.ℓ * s)))


/-- Only the original assignment facts needed by the homogeneous return. -/
structure ReturnLevel (k : ℕ) (s : ℝ) : Prop where
  time_upper : (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s)
  prior_lower : ∀ i, ENNReal.ofReal
    ((cfg.N k ^ (-s)) ^ cfg.d * ((2 : ℝ) ^ cfg.T k s)⁻¹ ^ (2 : ℕ) *
      cfg.N k ^ (-cfg.ℓ * s) / cfg.K k) ≤ cfg.ν k (cfg.A k s i)
  degree : ∀ i, (cfg.F k s i).totalDegree ≤ 2
  fitted : ∀ i l, l ∈ cfg.B k s i → cfg.fit k (cfg.K k) (cfg.N k ^ (-s))
    (cfg.F k s i) l (I (cfg.T k s) (cfg.j k s i))
  floor : ∀ i, ∀ᵐ p ∂cfg.μ k,
    p.1 ∈ cfg.B k s i → p.2 ∈ I (cfg.T k s) (cfg.j k s i) →
      (cfg.K k)⁻¹ ≤ |eval (cfg.x k p.1 p.2) (pderiv (3 : Fin 4) (cfg.F k s i))|

structure Valid : Prop where
  scale : ∀ k, 2 ≤ cfg.N k
  scale_limit : Tendsto cfg.N atTop atTop
  subpower : (∀ k, 1 ≤ cfg.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε
  dimension_nonneg : 0 ≤ cfg.d
  dimension_lt_one : cfg.d < 1
  rate_pos : 0 < cfg.κ
  rate_le_one : cfg.κ ≤ 1
  transverse_pos : 0 < cfg.ℓ
  palette_pos : 0 < cfg.S
  palette_le_one : cfg.S ≤ 1
  depth_pos : 0 < cfg.U
  defect_pos : 0 < cfg.e₀
  equal_rate : cfg.ℓ = cfg.κ
  basic : cfg.Basic
  caps : cfg.Caps
  atlas : cfg.OriginalAtlas
  nested : cfg.Nested
  contact : ∀ k, ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)

variable {cfg}

/-- Dropping the unused geometry leaves the exact true test and its old floor. -/
theorem Valid.eventually_return_levels (h : cfg.Valid) (R : ℝ) (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → cfg.ReturnLevel k s := by
  filter_upwards [h.atlas R hR] with k hk
  intro s hs hsU
  have ha := hk s hs hsU
  refine ⟨ha.2.1, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [zpow_neg, zpow_natCast] using (ha.2.2.2.2.1 i).1
  · intro i
    exact (ha.2.2.2.2.1 i).2.2.2.2.1
  · intro i
    exact (ha.2.2.2.2.1 i).2.2.2.2.2.2.1
  · intro i
    exact (ha.2.2.2.2.1 i).2.2.2.2.2.2.2.1

variable (cfg)

/-- The original velocity alternative. -/
def VelocityCandidate (k : ℕ) (s v ε R : ℝ) (i : Fin (cfg.n k s)) : Prop :=
  ∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ cfg.N k ^ R) ∧
    ENNReal.ofReal (cfg.N k ^ (-ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
        |cfg.b k p.1 4 - z 0 - z 1 * cfg.b k p.1 3| ≤
          cfg.N k ^ ε * cfg.N k ^ (-cfg.ℓ * s - v)}

/-- A candidate after the second affine preparation, before homogeneous
calibration. The source law keeps its mass in original units. -/
def AffineCandidate (k : ℕ) (s v ε : ℝ) (i : Fin (cfg.n k s)) : Prop :=
  ∃ (σ : Measure (α × ℝ)) (L : Fin 4 → ℝ), σ ≤ cfg.ρ k ∧
    ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤ σ univ ∧
    ∀ᵐ p ∂σ, p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
      ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |eval (cfg.x k p.1 t) (affineBase L) - cfg.x k p.1 t 3| ≤
          cfg.N k ^ ε * cfg.N k ^ (-s - v)

def AffineCandidates : Prop :=
  ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ (s v : ℝ) (i : Fin (cfg.n k s)),
      R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ cfg.U ∧
        (cfg.AffineCandidate k s v ε i ∨ cfg.VelocityCandidate k s v ε R i)

/-- The coordinates used by the assumed shifted candidates. -/
def shiftedPoint (k : ℕ) (L : Fin 4 → ℝ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  ![t, (cfg.x k l t) 1, (cfg.x k l t) 2,
    (cfg.x k l t) 3 - (L 0 + L 1 * t + L 2 * (cfg.x k l t) 1 + L 3 * (cfg.x k l t) 2)]

def ShiftedCandidate (k : ℕ) (s v ε R : ℝ) (i : Fin (cfg.n k s)) : Prop :=
  ∃ (L : Fin 4 → ℝ) (G : MvPolynomial (Fin 4) ℝ), G.totalDegree ≤ 2 ∧
    (∀ e, |G.coeff e| ≤ cfg.N k ^ R) ∧
    ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤
    cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
      (∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |cfg.shiftedPoint k L p.1 t 3| ≤ 1 ∧
        |eval (cfg.shiftedPoint k L p.1 t) G| ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v) ∧
        |eval (cfg.shiftedPoint k L p.1 t) (pderiv (3 : Fin 4) G)| ≤ cfg.N k ^ ε ∧
        |eval (cfg.shiftedPoint k L p.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤
          cfg.N k ^ ε / cfg.N k ^ (-s - v)) ∧
      cfg.N k ^ (-ε) ≤ |eval (cfg.shiftedPoint k L p.1 p.2) (pderiv (3 : Fin 4) G)|}

def ShiftedCandidates : Prop :=
  ∀ V : ℝ, 0 < V → V ≤ cfg.U →
    ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ (s v : ℝ) (i : Fin (cfg.n k s)),
        R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ V ∧
          (cfg.ShiftedCandidate k s v ε R i ∨ cfg.VelocityCandidate k s v ε R i)

end Model

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
