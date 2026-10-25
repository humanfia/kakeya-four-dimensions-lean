-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/PhysicalPotentialPacket.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o265, x1011 ca57481c, FieldPacket.lean.
-- The parent P replaces the refuted arbitrary-old-test derivative.
import Submission.Obl.k4_physical_parent_potential_candidates.StagedInterface

set_option autoImplicit false

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

namespace PhysicalPotentialData

/-- Base coordinates use the old clock and a translation, without a velocity shear. -/
def packetBase : ℕ → ℕ → P2 → P2 → Ev → P3 := (fun T j c u p =>
    let h := (((2 : ℝ) ^ T)⁻¹ : ℝ)
    let t0 := ((j : ℝ) * h : ℝ)
  WithLp.toLp 2 ![(p.2 - t0) / h,
    ((xp p.1 p.2) 1 - (c 0 + t0 * u 0)) / h,
    ((xp p.1 p.2) 2 - (c 1 + t0 * u 1)) / h])

/-- The original parent quadratic, in physical units. -/
def packetSignal : Po → Ev → ℝ :=
  (fun P p => MvPolynomial.eval (xp p.1 p.2) P)

def physicalCode : (Ev → P3) → (Ev → ℝ) → ℝ → Ev → ((Fin 3 → ℤ) × ℤ) :=
  (fun z X ε p => (fun i => ⌊z p i / ε⌋, ⌊X p / ε⌋))


end PhysicalPotentialData

/-- A physical-parent potential source at one original old packet. The path test
and physical parent are separate. Only the state height is divided by a. -/
def PhysicalPotentialPacket : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ →
    MeasureTheory.Measure Ln → ℝ → ℝ → ℕ → ℕ → P2 → P2 → Po →
    Set Ln → Set Ev → Set Ev → Prop :=
  (fun q precision loss Nk L d₁ gain κ ν B r T j c u P A F H =>
    let a := δ Nk r
    let h := (((2 : ℝ) ^ T)⁻¹ : ℝ)
    let ζ := δ Nk (precision * gain * L)
    let z := PhysicalPotentialData.packetBase T j c u
    let X := PhysicalPotentialData.packetSignal P
    let Xn := (fun p => X p / a)
    let ref := ENNReal.ofReal h * ν A
    ∃ (K ε : ℝ) (S : Set Ev) (Pot : MvPolynomial (Fin 3) ℝ),
      0 < ε ∧ ε ≤ ζ ∧ ε ≤ (a / h) * ζ ∧
      0 < a ∧ a ≤ K * h ∧ h ≤ ζ ∧
      2 ≤ K ∧ κ ≤ K ∧ K ≤ Nk ^ (loss * gain * L) ∧
      MeasurableSet S ∧ S ⊆ H ∩ F ∧
      0 < ref ∧ ref / ENNReal.ofReal K ≤ ((ν.prod MeasureTheory.volume).restrict S) Set.univ ∧
      Pot.totalDegree ≤ q ∧ (∀ e, |Pot.coeff e| ≤ K * h) ∧
      (∀ p ∈ S, ‖z p‖ ≤ K ∧ ‖v p.1‖ ≤ K ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ K ∧
          |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧
          |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K * B ^ 2) ∧
        B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)| ∧
        (∀ t ∈ Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
          |(MvPolynomial.eval (xp p.1 t) P -
              MvPolynomial.eval (fun i => z (p.1, t) i) Pot) -
            (MvPolynomial.eval (xp p.1 ((j : ℝ) * h)) P -
              MvPolynomial.eval (fun i => z (p.1, (j : ℝ) * h) i) Pot)| ≤ a * ζ)) ∧
      (∀ k : (Fin 3 → ℤ) × ℤ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
        ((ν.prod MeasureTheory.volume).restrict S)
          {p | PhysicalPotentialData.physicalCode z Xn ε p = k ∧ |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
        (1 / 1000000000000 : ENNReal) *
          ((ν.prod MeasureTheory.volume).restrict S) {p | PhysicalPotentialData.physicalCode z Xn ε p = k}) ∧
      (∀ U : Set P3, MeasurableSet U →
        ((ν.prod MeasureTheory.volume).restrict S) {p | z p ∈ U} ≤
          ENNReal.ofReal K * ref * MeasureTheory.volume U) ∧
      (∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U →
          ∀ f : P3 → ℝ, Measurable f →
            ((ν.prod MeasureTheory.volume).restrict S)
              {p | z p ∈ U ∧ |Xn p - f (z p)| ≤ w} ≤
              ENNReal.ofReal (K * w ^ d₁) * ref * MeasureTheory.volume U) ∧
      (∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 → K ^ (100 : ℕ) * h * p ≤ a * w →
          Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
            (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k} ∧
          (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
              (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k}).ncard : ℝ) ≤
            K / (p ^ (3 : ℕ) * w ^ d₁)))

end
end Submission.Obl.k4_physical_parent_potential_candidates
