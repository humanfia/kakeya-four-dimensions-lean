/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNormalInterface.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNormalInterface.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalData
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarClosedCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarClippedRow

/-! Adapt original active-row bounds and half-open spatial caps to the stored first-jet data. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

namespace ScalarNormalHyp

/-- Clipping changes no active row, scalar, or residual value. The
only enlargement is the fixed factor four for closed spatial squares. -/
theorem of_half_open_active_row {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (ν : Measure Λ) [IsProbabilityMeasure ν]
    (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ)
    {K ζ d : ℝ} (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : 0 ≤ d)
    (hE : MeasurableSet E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ E, D.Bounded K p.1) (hF : Measurable F)
    (hrow : ∀ p ∈ E, |F p.2| ≤ K)
    (hrowcmp : ∀ p ∈ E, ∀ q ∈ E, |F p.2 - F q.2| ≤ K * (|p.2 - q.2| + ζ))
    (hrescmp : ∀ p ∈ E, ∀ q ∈ E,
      |D.residual F p.1 p.2 - D.residual F q.1 q.2| ≤
        K * (|p.2 - q.2| + |D.x p.1 p.2 - D.x q.1 q.2| +
          |D.y p.1 p.2 - D.y q.1 q.2| + ζ))
    (hAD : ∀ t, IntervalAD ζ d K (S t)) (hsupport : ∀ p ∈ E, D.scalar F p.1 p.2 ∈ S p.2)
    (hcap : ∀ t a b r : ℝ, ζ ≤ r → r ≤ 1 →
      ν {l | (l, t) ∈ E ∧ D.x l t ∈ Ico a (a + r) ∧ D.y l t ∈ Ico b (b + r)} ≤
        ENNReal.ofReal (K * r ^ (1 + d))) :
    ScalarNormalHyp D ν E (scalarClippedRow K F) S (4 * K) ζ d := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKK : K ≤ 4 * K := by linarith
  have hclip p (hp : p ∈ E) : scalarClippedRow K F p.2 = F p.2 :=
    scalarClippedRow_eq hKpos (hrow p hp)
  refine ⟨hE, hunit, ?_, measurable_scalarClippedRow hF,
    fun t => (scalarClippedRow_bound hKpos.le F t).trans hKK, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hx0, hx1, hx2, hy0, hy1⟩ := hcoeff p hp
    exact ⟨hx0.trans hKK, hx1.trans hKK, hx2.trans hKK, hy0.trans hKK, hy1.trans hKK⟩
  · intro p hp q hq
    rw [hclip p hp, hclip q hq]
    exact (hrowcmp p hp q hq).trans
      (mul_le_mul_of_nonneg_right hKK (by positivity))
  · intro p hp q hq
    have heq p (hp : p ∈ E) :
        D.residual (scalarClippedRow K F) p.1 p.2 = D.residual F p.1 p.2 := by
      dsimp only [ScalarMotion.residual]
      rw [hclip p hp]
    rw [heq p hp, heq q hq]
    exact (hrescmp p hp q hq).trans
      (mul_le_mul_of_nonneg_right hKK (by positivity))
  · intro t
    exact CellProofs.Assouad.mono_constant hζ (hAD t) hKK
  · intro p hp
    have heq : D.scalar (scalarClippedRow K F) p.1 p.2 = D.scalar F p.1 p.2 := by
      dsimp only [ScalarMotion.scalar]
      rw [hclip p hp]
    rw [heq]
    exact hsupport p hp
  · intro t a b r hr
    exact original_closed_square_cap_of_half_open ν {l | (l, t) ∈ E}
      (fun l => D.x l t) (fun l => D.y l t) hK hζ hd (hcap t) a b r hr

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
