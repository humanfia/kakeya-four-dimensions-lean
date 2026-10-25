-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 334b24fb.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CalibratedRawBinCaps.lean.
-- Only the namespace and own-module import prefix are changed here.
import Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.RawBinTranslation
import Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.RawHiddenSignalCaps

/-! Restore the original raw-cell mass after calibrating the translated
base value and derivative. All original palette factors remain explicit. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade

noncomputable section

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open RawBinTranslation
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

/-- On a law supported in one original raw cell, calibrated base slices
supply the whole raw-cell mass bound. The hidden endpoint itself is never
bounded and the law is never normalized by the raw cell's mass. -/
theorem calibrated_raw_bin_mass_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (x : Ω → Fin 4 → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {N A r s d K : ℝ} (hN : 2 ≤ N) (hA : 0 ≤ A)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hK : 1 ≤ K) (hKN : K ≤ N ^ A)
    (q : Fin 3 → ℤ) (j : ℤ)
    (hvalue : ∀ e, |(restrictBase (shiftedTest ((j : ℝ) * N ^ (-s)) P)).coeff e| ≤ N ^ A)
    (hfirst : ∀ e, |(restrictBase (pderiv (3 : Fin 4)
      (shiftedTest ((j : ℝ) * N ^ (-s)) P))).coeff e| ≤ N ^ A)
    (hsecond : |curvature (shiftedTest ((j : ℝ) * N ^ (-s)) P) (3 : Fin 4)| ≤ N ^ A)
    (hgood : ∀ᵐ p ∂μ,
      (∀ i : Fin 3, |x p i.castSucc| ≤ K) ∧
      Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
        (fun i : Fin 3 => x p i.castSucc) = q ∧
      ⌊x p 3 / N ^ (-s)⌋ = j ∧
      |eval (x p) (pderiv (3 : Fin 4) P)| ≤ K ∧
      |eval (x p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K)
    (β : ENNReal) (hβ : β ≠ ⊤)
    (hcap : ∀ (q' : Fin 3 → ℤ) (j' : ℤ),
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh
          (N ^ (-(r + s + 10 * (A + 6) + 10)))
          (fun i : Fin 3 => x p i.castSucc) = q' ∧
        ⌊eval (x p) P / N ^ (-s)⌋ = j'} ≤
        ENNReal.ofReal (K * N ^ (-3 * (r + s + 10 * (A + 6) + 10) - d * s)) * β) :
    μ univ ≤ ENNReal.ofReal (400 * K ^ 2 * N ^ (-3 * r - d * s)) * β := by
  let w := (j : ℝ) * N ^ (-s)
  let Q := shiftedTest w P
  let y : Ω → Fin 4 → ℝ := fun p => shiftedPoint w (x p)
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have ha : 0 < N ^ (-s) := by positivity
  have ha1 : N ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hA6 : 0 ≤ A + 6 := by linarith
  have hQ : Q.totalDegree ≤ 2 := (shiftedTest_degree w P).trans hP
  have hcoeff : ∀ e, |Q.coeff e| ≤ N ^ (A + 6) :=
    coefficient_power_bound_of_base_slices Q hQ hN hA hvalue hfirst hsecond
  have hAB : N ^ A ≤ N ^ (A + 6) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hybase (p : Ω) : (fun i : Fin 3 => y p i.castSucc) =
      (fun i : Fin 3 => x p i.castSucc) := by
    funext i
    exact shiftedPoint_base w (x p) i
  have hygood : ∀ᵐ p ∂μ,
      (∀ i, |y p i| ≤ N ^ (A + 6)) ∧
      |eval (y p) (pderiv (3 : Fin 4) Q)| ≤ K ∧
      |eval (y p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ K := by
    filter_upwards [hgood] with p hp
    refine ⟨?_, ?_, ?_⟩
    · exact shiftedPoint_box_bound ha ha1 (Real.one_le_rpow hN1 hA6) j (x p)
        hp.2.2.1 (fun i => (hp.1 i).trans (hKN.trans hAB))
    · simpa only [y, Q, eval_shiftedTest_pderiv] using hp.2.2.2.1
    · simpa only [y, Q, eval_shiftedTest_pderiv_twice] using hp.2.2.2.2
  have hcap' (q' : Fin 3 → ℤ) (j' : ℤ) :
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh
          (N ^ (-(r + s + 10 * (A + 6) + 10)))
          (fun i : Fin 3 => y p i.castSucc) = q' ∧
        ⌊eval (y p) Q / N ^ (-s)⌋ = j' ∧ True} ≤
        ENNReal.ofReal (K * N ^ (-3 * (r + s + 10 * (A + 6) + 10) - d * s)) * β := by
    simpa only [hybase, y, Q, eval_shiftedTest, and_true] using hcap q' j'
  have hbound := raw_hidden_power_cell_cap_of_native_signal μ y Q hQ (fun _ => True)
    hN hA6 hr hs hK hcoeff hygood β hβ hcap' q 0
  have heq : μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
        (fun i : Fin 3 => y p i.castSucc) = q ∧ ⌊y p 3 / N ^ (-s)⌋ = 0 ∧ True} = μ univ := by
    apply measure_congr
    filter_upwards [hgood] with p hp
    have hbin0 : ⌊y p 3 / N ^ (-s)⌋ = 0 :=
      (shiftedPoint_raw_bin ha j (x p) hp.2.2.1).2.2
    have hevent : Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
        (fun i : Fin 3 => y p i.castSucc) = q ∧ ⌊y p 3 / N ^ (-s)⌋ = 0 ∧ True := by
      rw [hybase]
      exact ⟨hp.2.1, hbin0, trivial⟩
    exact propext (iff_true_intro hevent)
  rwa [heq] at hbound

end

end Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade
