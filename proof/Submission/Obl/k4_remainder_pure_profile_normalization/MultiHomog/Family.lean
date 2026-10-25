import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Prior
import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Format
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

/-!
# Multi-world tempered families and their one-world encoding

`Tempered` collects the per-sample conditions of a multi-world family which the
homogenization of paper Lemma 2.5 uses. A `Sample` bundles the data of one sample with
the format exponent `M` and an exponent `M₀` bounding the slack `K`.

Each world `γ` is moved into one world by the affine change `encLine` of
`MultiHomog.Lines` with

* planar scales `a = 4K/Λ` (first coordinate) and `b γ = max (ω γ) thr / (4K)` (second),
  where `Λ = N ^ (M + 2M₀ + 4)`, so that `ω γ / (a b γ) = Λ` for every retained world;
* offsets `o γ = 9 K² γ / Λ`, which separate the worlds at every time;
* hidden scale `θ γ = B γ δ(N, 2M+2)`, which makes the encoded hidden coordinate at most one.

Worlds of weight below `thr = (2 K N^M)⁻¹` are not retained: their incidences are left
out of the encoded event, at a cost of at most half of the selected mass.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set Filter
open scoped ENNReal

/-- The per-sample tempered conditions of a multi-world family used by homogenization. -/
structure Tempered (N K : ℝ) (M D W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) : Prop where
  card : (W : ℝ) ≤ N ^ M
  weight_nonneg : ∀ γ, 0 ≤ ω γ
  weight_sum : ∑ γ, ω γ = 1
  prob : ∀ γ, IsProbabilityMeasure (ν γ)
  scale_pos : ∀ γ, 0 < B γ
  scale_le : ∀ γ, B γ ≤ N ^ M
  scale_inv_le : ∀ γ, (B γ)⁻¹ ≤ N ^ M
  prior : ∀ γ, ∃ m : ℕ, (m : ℝ) ≤ N ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N ^ M ∧ (i j : ℝ) ≤ N ^ M ∧
      fmt 6 (N ^ M) D (A j) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N ^ M)) ∧
      ν γ = ∑ j, ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x)) (volume.restrict (A j))
  event_meas : ∀ γ, MeasurableSet (E γ)
  event_time : ∀ γ, E γ ⊆ univ ×ˢ Icc (0 : ℝ) 1
  event_bdd : ∀ γ, ∀ p ∈ E γ, (p.1.1 : ℝ) ≤ N ^ M ∧ ∀ e, |p.1.2 e| ≤ N ^ M
  event_fmt : ∀ γ i, fmt 7 (N ^ M) D
    {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ E γ}
  native : ∀ γ, ∀ᵐ l ∂ν γ, ∀ t ∈ Icc (0 : ℝ) 1, ‖y l t‖ + ‖v l‖ ≤ K
  mass : ENNReal.ofReal K⁻¹ ≤ ∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ)

/-- The data of one sample, with its format exponent `M` and slack exponent `M₀`. -/
structure Sample where
  N : ℝ
  K : ℝ
  M : ℕ
  M₀ : ℕ
  W : ℕ
  ω : Fin W → ℝ
  ν : Fin W → Measure Trajectory
  E : Fin W → Set Incidence
  B : Fin W → ℝ

namespace Sample

variable (S : Sample)

/-- The exponent of the density factor. -/
def mL : ℕ := S.M + 2 * S.M₀ + 4

/-- The common density factor `Λ = N ^ mL`. -/
noncomputable def Lam : ℝ := S.N ^ S.mL

/-- The weight threshold for retained worlds. -/
noncomputable def thr : ℝ := (2 * S.K * S.N ^ S.M)⁻¹

/-- The scale of the first planar coordinate. -/
noncomputable def a : ℝ := 4 * S.K / S.Lam

/-- The scale of the second planar coordinate of a world. -/
noncomputable def b (γ : Fin S.W) : ℝ := max (S.ω γ) S.thr / (4 * S.K)

/-- The offset of a world. -/
noncomputable def o (γ : Fin S.W) : ℝ := 9 * S.K ^ 2 * ((γ : ℕ) : ℝ) / S.Lam

/-- The depth shift of the hidden coordinate. -/
def s0 : ℝ := ((2 * S.M + 2 : ℕ) : ℝ)

/-- The hidden scale of a world. -/
noncomputable def θ (γ : Fin S.W) : ℝ := S.B γ * δ S.N S.s0

/-- The encoding of the trajectories of a world. -/
noncomputable def enc (γ : Fin S.W) : Trajectory → Trajectory :=
  encLine S.W γ S.a (S.b γ) (S.θ γ) (S.o γ)

/-- The encoding of the incidences of a world. -/
noncomputable def encInc (γ : Fin S.W) (p : Incidence) : Incidence := (S.enc γ p.1, p.2)

/-- Retained worlds. -/
def Retained (γ : Fin S.W) : Prop := S.thr ≤ S.ω γ

/-- The encoded prior. -/
noncomputable def prior : Measure Trajectory :=
  ∑ γ, ENNReal.ofReal (S.ω γ) • (S.ν γ).map (S.enc γ)

/-- The encoded event: the encoded incidences of retained worlds. -/
def event : Set Incidence :=
  {p | ∃ γ : Fin S.W, S.Retained γ ∧ p.1.1 % S.W = (γ : ℕ) ∧
    ((p.1.1 / S.W, decCoeff S.a (S.b γ) (S.θ γ) (S.o γ) p.1.2), p.2) ∈ S.E γ}

end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
