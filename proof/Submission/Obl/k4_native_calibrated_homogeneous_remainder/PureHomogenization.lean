import Submission.Obl.k4_native_calibrated_homogeneous_remainder.PurePhase
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.GeometrySelection
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ValidParts

/-! A common weighted pure profile, with the exact native observation scales. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable def setProfile (p : Data) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (p.W k) → ℝ → Observation → ENNReal)
    (G : (k : ℕ) → Fin (p.W k) → ℝ → JointObservation → ENNReal) : Data :=
  { p with f := f, g := g, G := G }

def RemainderGeometry.setProfile {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (q.W k) → ℝ → Observation → ENNReal)
    (G : (k : ℕ) → Fin (q.W k) → ℝ → JointObservation → ENNReal) :
    RemainderGeometry p (setProfile q f g G) r h w := { a with }

def RawRemainder.setProfile {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (q.W k) → ℝ → Observation → ENNReal)
    (G : (k : ℕ) → Fin (q.W k) → ℝ → JointObservation → ENNReal) :
    RawRemainder p (setProfile q f g G) r h w := { a with }

noncomputable def canonicalProfile (p : Data) (hp : RawValid p) (f : ℝ → ℝ) : Data :=
  setProfile p f (fun k b s => pureDensity hp k b (δ (p.N k) s))
    (fun k b u => jointDensity hp k b (δ (p.N k) p.L) (δ (p.N k) u))

/-- Exact density laws and a common weighted pure profile; the two native cap
conditions will be inherited from the original family after calibration. -/
def WeightedPureHomogeneous (p : Data) : Prop :=
  RawValid p ∧
  (∀ k b s, Measurable (p.g k b s) ∧
    (selected p k b).map (obs (p.B k b) (δ (p.N k) s)) =
      (volume.prod Measure.count).withDensity (p.g k b s)) ∧
  (∀ k b u, Measurable (p.G k b u) ∧
    (selected p k b).map (fun z => (obs (p.B k b) (δ (p.N k) p.L) z,
      fun j : Fin 2 => ⌊v z.1 j / δ (p.N k) u⌋)) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (p.G k b u)) ∧
  (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ p.L →
    0 ≤ p.f s - p.f r ∧ p.f s - p.f r ≤ s - r) ∧
  (∀ s : ℝ, 0 ≤ s → s ≤ p.L → HasTypicalDensity p.N (familyLaw p)
    (fun k z => ENNReal.ofReal (p.ω k z.1) *
      p.g k z.1 s (obs (p.B k z.1) (δ (p.N k) s) z.2)) (p.f s))

def PureHomogeneous (p : Data) : Prop :=
  RawValid p ∧
  (∀ k b s, Measurable (p.g k b s) ∧
    (selected p k b).map (obs (p.B k b) (δ (p.N k) s)) =
      (volume.prod Measure.count).withDensity (p.g k b s)) ∧
  (∀ k b u, Measurable (p.G k b u) ∧
    (selected p k b).map (fun z => (obs (p.B k b) (δ (p.N k) p.L) z,
      fun j : Fin 2 => ⌊v z.1 j / δ (p.N k) u⌋)) =
      ((volume.prod Measure.count).prod Measure.count).withDensity (p.G k b u)) ∧
  (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ p.L →
    0 ≤ p.f s - p.f r ∧ p.f s - p.f r ≤ s - r) ∧
  (∀ s : ℝ, 0 ≤ s → s ≤ p.L → HasTypicalDensity p.N (familyLaw p)
    (fun k z => p.g k z.1 s (obs (p.B k z.1) (δ (p.N k) s) z.2)) (p.f s))

theorem pure_homogeneous_valid_of_caps {p : Data} (hp : PureHomogeneous p)
    (hd : ∀ s : ℝ, 0 ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ p.d * (p.L - s))
    (hS : ∀ u τ : ℝ, 0 < u → u ≤ p.η * p.L → 0 < τ →
      IsPowerSmall p.N (fun k => familyLaw p k {z |
        ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) <
          p.G k z.1 u (obs (p.B k z.1) (δ (p.N k) p.L) z.2,
            fun j : Fin 2 => ⌊v z.2.1 j / δ (p.N k) u⌋)})) : Valid p :=
  valid_of_raw_profile hp.1
    ⟨(fun k b s _ _ => hp.2.1 k b s), (fun k b u _ _ => hp.2.2.1 k b u),
      hp.2.2.2.1, hp.2.2.2.2, hd, hS⟩

theorem PureHomogeneous.reindex {p : Data} (hp : PureHomogeneous p)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) : PureHomogeneous (p.reindex ψ) := by
  refine ⟨hp.1.reindex hψ.tendsto_atTop, (fun k b s => hp.2.1 (ψ k) b s),
    (fun k b u => hp.2.2.1 (ψ k) b u), hp.2.2.2.1, ?_⟩
  intro s hs hsL τ hτ
  obtain ⟨c, hc, hev⟩ := hp.2.2.2.2 s hs hsL τ hτ
  exact ⟨c, hc, hψ.tendsto_atTop.eventually hev⟩

theorem WeightedPureHomogeneous.reindex {p : Data} (hp : WeightedPureHomogeneous p)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) : WeightedPureHomogeneous (p.reindex ψ) := by
  refine ⟨hp.1.reindex hψ.tendsto_atTop, (fun k b s => hp.2.1 (ψ k) b s),
    (fun k b u => hp.2.2.1 (ψ k) b u), hp.2.2.2.1, ?_⟩
  intro s hs hsL τ hτ
  obtain ⟨c, hc, hev⟩ := hp.2.2.2.2 s hs hsL τ hτ
  exact ⟨c, hc, hψ.tendsto_atTop.eventually hev⟩

theorem canonicalProfile_weighted_homogeneous {p : Data} (hp : RawValid p)
    {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) {F : ℝ → ℝ → ℝ}
    (hreg : Submission.Obl.k4_joint_homogenization.ProfileRegular (ρ₀ + p.L) 1 F)
    (htyp : WeightedJointTypical p p.L 1 ρ₀ F) :
    WeightedPureHomogeneous (canonicalProfile p hp (fun s => F (ρ₀ + s) 0)) := by
  refine ⟨hp, (fun k b s => pureDensity_spec hp k b _),
    (fun k b u => jointDensity_spec hp k b _ _), ?_, ?_⟩
  · intro r s hr hrs hs
    change s ≤ p.L at hs
    change 0 ≤ F (ρ₀ + s) 0 - F (ρ₀ + r) 0 ∧
      F (ρ₀ + s) 0 - F (ρ₀ + r) 0 ≤ s - r
    have h := hreg.1 (ρ₀ + r) (ρ₀ + s) 0 (by linarith) (by linarith)
      (by linarith) le_rfl zero_le_one
    simpa only [add_sub_add_left_eq_sub] using h
  · intro s hs hsL
    exact hp.pure_phase_typical hρ₀ hs (htyp.intrinsic_pure hp zero_le_one s hs hsL)

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
