-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/DominatedQuadraticReturn.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.AffineHiddenReturn
import Submission.Obl.k4_finite_affine_candidate_return.DominatedMassReturn
import Submission.Obl.k4_finite_affine_candidate_return.ModelEH1
import Submission.Obl.k4_finite_affine_candidate_return.ModelEvents

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory MvPolynomial

noncomputable section

/-- A quadratic in the explicit affinely corrected source returns with
its actual old block, unchanged full prior, and exactly the domination
loss from the source certificate. -/
theorem dominated_affine_quadratic_return
    (ν : Measure Trajectory) (A₀ A' B' : Set Trajectory)
    (hA : MeasurableSet A') (hB' : MeasurableSet B')
    (hAA₀ : A' ⊆ A₀) (hBA : B' ⊆ A') (hν0 : ν A₀ ≠ 0) (hνT : ν A₀ ≠ ⊤)
    (Φ : PFrame) (hq : 0 < Φ.F.q) (a : Fin 4 → ℝ) (δ B c c₀ H C : ℝ)
    (hδ : 0 < δ) (hB : 0 ≤ B) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hH : 0 < H) (hsc : Φ.sc = B / δ)
    (T : ℕ) (j : Fin (2 ^ T)) (I : Set ℝ)
    (hI : ∀ t : ℝ, t ∈ I ↔ (t - Φ.F.t₀) / Φ.F.q ∈ IS T j)
    (Q : MvPolynomial (Fin 4) ℝ) (S Hres : Set Incidence) (hSH : S ⊆ Hres)
    (ρ : Measure Incidence) (J : ENNReal) (hJ0 : J ≠ 0) (hJT : J ≠ ⊤)
    (hρ : ρ ≤ J • muE ν A₀ Φ.F.t₀ Φ.F.q S)
    (hvalue : δ * (H * c) ≤ C * c₀) (hfirst : H ≤ C)
    (hsecond : H * c₀ ≤ C * δ * c) (cNative cOld : ENNReal)
    (hcoef : cOld ≤ ENNReal.ofReal Φ.F.q * (J⁻¹ * cNative))
    (hfloor : cNative * nuE ν A₀ A' ≤ ρ
      {p | p.1 ∈ B' ∧ p.2 ∈ IS T j ∧ fitS (hiddenShear Φ.eb a) H c Q p.1 (IS T j) ∧
        H⁻¹ ≤ |eval (exS (hiddenShear Φ.eb a) p.1 p.2) (pderiv (3 : Fin 4) Q)|}) :
    cOld * ν A' ≤ (ν.prod volume)
      {p | p ∈ Hres ∧ p.1 ∈ A' ∧ p.2 ∈ I ∧
        Fits C c₀ B (Φ.affineLift a δ Q) p.1 I ∧
        B / C ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) (Φ.affineLift a δ Q))|} := by
  let X : Set Incidence :=
    {p | p.1 ∈ B' ∧ p.2 ∈ IS T j ∧ fitS (hiddenShear Φ.eb a) H c Q p.1 (IS T j) ∧
      H⁻¹ ≤ |eval (exS (hiddenShear Φ.eb a) p.1 p.2) (pderiv (3 : Fin 4) Q)|}
  have hXm : MeasurableSet X := measurableSet_quadraticEvent
    (measurable_hiddenShear Φ.eb Φ.measurable_eb a) B' hB' T j H c H⁻¹ Q
  apply (mul_le_mul' hcoef (le_refl (ν A'))).trans
  apply dominated_muE_floor_return_mono ν A₀ A' hA hAA₀ hν0 hνT
    Φ.F.t₀ Φ.F.q hq S X _ hXm _ ρ J cNative hJ0 hJT hρ hfloor
  rintro p ⟨hp, hpS⟩
  change p.1 ∈ B' ∧ (p.2 - Φ.F.t₀) / Φ.F.q ∈ IS T j ∧
      fitS (hiddenShear Φ.eb a) H c Q p.1 (IS T j) ∧
      H⁻¹ ≤ |eval (exS (hiddenShear Φ.eb a) p.1 ((p.2 - Φ.F.t₀) / Φ.F.q))
        (pderiv (3 : Fin 4) Q)| at hp
  refine ⟨hSH hpS, hBA hp.1, (hI p.2).mpr hp.2.1, ?_, ?_⟩
  · exact Φ.fitS_affine_return hq.ne' a δ B c c₀ H C hδ hB hc hc₀ hsc Q p.1 I
      (IS T j) (fun t ht => (hI t).mp ht) hp.2.2.1 hvalue hfirst hsecond
  · exact Φ.affine_lower_return hq.ne' a δ B H C hδ.ne' hB hH hfirst hsc Q p.1 p.2 hp.2.2.2

end

end Submission.Obl.k4_finite_affine_candidate_return
