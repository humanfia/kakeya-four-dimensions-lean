/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/Remainder.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.Transfer
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Conditioning

/-! A concrete interface between homogeneous remainder construction and finite
chart lifting. The priors are conditioned on the full parent assignments, and
the hidden coordinate remains unchanged. The terminal calibration uses the
original within-world prior, without a world weight or a mixture normalizer. -/

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open MeasureTheory Filter

/-- Parent geometric data at one resolution, without a true lower floor. -/
def Atlas.GeometricAt {p : Data} {k : ℕ} (a : Atlas p k) (M D : ℕ) (r : ℝ) : Prop :=
  (a.C : ℝ) ≤ p.N k ^ M ∧ a.Separated ∧
    ∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b))
      (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b) True

/-- A homogeneous normalized problem together with the original assignments and
actual coefficient maps needed to lift arbitrary terminal child charts. -/
structure Remainder (p q : Data) (r h w : ℝ) where
  φ : ℕ → ℕ
  increasing : StrictMono φ
  same_base : ∀ k, q.N k = p.N (φ k)
  valid : q.Valid
  length : q.L = p.L - r
  density_cap : q.d = p.d
  angular_rate : q.S = p.S
  angular_range : q.η = p.η
  M : ℕ
  D : ℕ
  parent : (k : ℕ) → Atlas p (φ k)
  worlds : (k : ℕ) → Fin (q.W k) ≃ Fin (parent k).C
  error : ℕ → ℝ
  error_pos : ∀ k, 0 < error k
  error_le_one : ∀ k, error k ≤ 1
  error_limit : Tendsto error atTop (nhds 0)
  parent_valid : ∀ k, (parent k).GeometricAt M D r
  slack_one : ∀ k, 1 ≤ (parent k).κ
  old_slack : ∀ k, p.K (φ k) ≤ (parent k).κ
  slack_bound : ∀ k, (parent k).κ ≤ p.N (φ k) ^ error k
  time_bound : ∀ k, (2 : ℝ) ^ (parent k).T ≤ p.N (φ k) ^ (h + error k)
  width_bound : ∀ k b, |Matrix.det ((parent k).Q b)| * (4 : ℝ) ^ (parent k).T ≤
    p.N (φ k) ^ (-w + error k)
  coefficient_map : (k : ℕ) → Fin (q.W k) → Trajectory ≃ᵐ Trajectory
  index_preserved : ∀ k b l, (coefficient_map k b l).1 = l.1
  planar_map : ∀ k b l t,
    y (coefficient_map k b l) t =
      Matrix.toEuclideanLin ((parent k).Q (worlds k b))⁻¹
        (y l (((parent k).j (worlds k b) : ℝ) / (2 : ℝ) ^ (parent k).T +
          t / (2 : ℝ) ^ (parent k).T) -
         (parent k).c (worlds k b) -
         (((parent k).j (worlds k b) : ℝ) / (2 : ℝ) ^ (parent k).T +
          t / (2 : ℝ) ^ (parent k).T) • (parent k).u (worlds k b))
  hidden_map : ∀ k b l t,
    x (coefficient_map k b l) t 3 =
      x l (((parent k).j (worlds k b) : ℝ) / (2 : ℝ) ^ (parent k).T +
        t / (2 : ℝ) ^ (parent k).T) 3
  prior_pos : ∀ k b, 0 < p.ν (φ k) ((parent k).γ (worlds k b))
    ((parent k).A (worlds k b))
  prior_inverse_bound : ∀ k b,
    (p.ν (φ k) ((parent k).γ (worlds k b)) ((parent k).A (worlds k b))).toReal⁻¹ ≤
      p.N (φ k) ^ M
  conditioned_prior : ∀ k b, q.ν k b =
    Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior
      (p.ν (φ k) ((parent k).γ (worlds k b))) ((parent k).A (worlds k b))
      (coefficient_map k b)
  selected_pullback : ∀ k b z, z ∈ q.E k b →
    ((coefficient_map k b).symm z.1,
      ((parent k).j (worlds k b) : ℝ) / (2 : ℝ) ^ (parent k).T +
        z.2 / (2 : ℝ) ^ (parent k).T) ∈ (parent k).F (worlds k b)
  derivative_unit : ∀ k b, q.B k b = p.B (φ k) ((parent k).γ (worlds k b)) /
    δ (p.N (φ k)) r
  Z : ℕ → ℝ
  normalizer_pos : ∀ k, 0 < Z k
  normalizer_lower : ∀ k, (parent k).κ⁻¹ ≤ Z k
  normalizer_upper : ∀ k, Z k ≤ 1
  normalizer_sum : ∀ k, Z k = ∑ b,
    p.ω (φ k) ((parent k).γ b) / (2 : ℝ) ^ (parent k).T *
      (p.ν (φ k) ((parent k).γ b) ((parent k).A b)).toReal
  world_weights : ∀ k b, q.ω k b =
    (p.ω (φ k) ((parent k).γ (worlds k b)) / (2 : ℝ) ^ (parent k).T *
      (p.ν (φ k) ((parent k).γ (worlds k b)) ((parent k).A (worlds k b))).toReal) / Z k
  terminal_calibration : ∀ k b,
    p.N (φ k) ^ (-p.f p.L) * |Matrix.det ((parent k).Q (worlds k b))| ≤
      (parent k).κ *
        (p.ν (φ k) ((parent k).γ (worlds k b)) ((parent k).A (worlds k b))).toReal *
        q.N k ^ (-q.f q.L)

/-- Construction of an actual homogeneous remainder; all later child atlases
use the same chosen problem and its retained full parent assignments. -/
def RemainderConstruction : Prop :=
  ∀ (p : Data), p.Valid → ∀ r h w : ℝ, 0 ≤ r → r < p.L → Known p r h w →
    ∃ q : Data, Nonempty (Remainder p q r h w)

/-- The geometric and polynomial-format composition step, isolated from
homogenization and from any choice of an optimal horizon. -/
def FiniteLifting : Prop :=
  ∀ (p q : Data) (r h w : ℝ), p.Valid → 0 ≤ r → r < p.L →
    Remainder p q r h w → ∃ φ : ℕ → ℕ,
      Tendsto φ atTop atTop ∧ SampleTransfer p q φ h w

theorem composition_of_remainder_and_finite_lifting
    (hc : RemainderConstruction) (hl : FiniteLifting) : Composition := by
  apply composition_of_sampleTransfer
  intro p hp r h w hr hrL hk
  obtain ⟨q, ⟨rem⟩⟩ := hc p hp r h w hr hrL hk
  obtain ⟨φ, hφ, ht⟩ := hl p q r h w hp hr hrL rem
  exact ⟨q, φ, rem.valid, rem.length, rem.density_cap, rem.angular_rate,
    rem.angular_range, hφ, ht⟩

end Submission.Obl.k4_native_finite_terminal_atlas_lift
