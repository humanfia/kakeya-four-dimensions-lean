/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/UnitStripCodes.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripGeometry
import Submission.Lib.K4ListedExceptions.FrameCodes
import Submission.Obl.k4_oss_collision_cauchy_schwarz.Cells

/-!
Strip labels using a unit normal and an offset. Three parameter bins avoid
any bound on a scalar slope. One actual unit-normal representative can be
chosen per used code, so replacing a candidate by that representative costs
only a fixed multiple of the grid width and the actual velocity bound.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open Submission.Lib.K4ListedExceptions
open Submission.Lib.K4VelocityStrips
open Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

noncomputable section

def stripParameters (n : Plane) (β : ℝ) : Fin 3 → ℝ := ![n 0, n 1, β]

def stripParameterCode (h : ℝ) (n : Plane) (β : ℝ) : Fin 3 → ℤ :=
  fun i => ⌊stripParameters n β i / h⌋

theorem stripParameterCode_close {h : ℝ} (hh : 0 < h) {n m : Plane} {β γ : ℝ}
    (hc : stripParameterCode h n β = stripParameterCode h m γ) :
    ‖n - m‖ + |β - γ| ≤ 3 * h := by
  have hparam (i : Fin 3) : |stripParameters n β i - stripParameters m γ i| ≤ h :=
    k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell hh (congrFun hc i)
  have h₀ : |n 0 - m 0| ≤ h := hparam 0
  have h₁ : |n 1 - m 1| ≤ h := hparam 1
  have hβ : |β - γ| ≤ h := hparam 2
  have hn : ‖n - m‖ ≤ 2 * h := by
    calc
      _ ≤ |(n - m) 0| + |(n - m) 1| :=
        k4_scalar_coefficient_clustering.plane_norm_le_abs_add (n - m)
      _ ≤ h + h := by simpa only [PiLp.sub_apply] using add_le_add h₀ h₁
      _ = 2 * h := by ring
  linarith

/-- Replacing a strip by an actual representative with the same parameter
code gives slack depending only on the actual velocity bound. -/
theorem strip_fit_of_same_code {h ε V β γ : ℝ} {n m v : Plane}
    (hh : 0 < h) (hV : 0 ≤ V) (hv : ‖v‖ ≤ V) (hε : ε ≤ h)
    (hc : stripParameterCode h n β = stripParameterCode h m γ)
    (hfit : |inner ℝ v n - β| ≤ ε) :
    |inner ℝ v m - γ| ≤ (4 + 3 * V) * h := by
  have hclose := stripParameterCode_close hh hc
  have hmem : v ∈ affineStrip n β ε := hfit
  have hfit' := affineStrip_mem_of_close_parameters hV hv hclose hmem
  change |inner ℝ v m - γ| ≤ ε + (1 + V) * (3 * h) at hfit'
  exact hfit'.trans (by nlinarith)

theorem stripParameterCode_mem_of_close {h : ℝ} (hh : 0 < h) (C : ℕ)
    {n m : Plane} {β γ : ℝ} (hc : ‖n - m‖ + |β - γ| ≤ (C : ℝ) * h) :
    stripParameterCode h n β ∈ integerCodeBox C (stripParameterCode h m γ) := by
  apply floor_code_mem_integerCodeBox C (stripParameters n β) (stripParameters m γ)
    (fun _ => h) (fun _ => hh)
  intro i
  have hnorm : ‖n - m‖ ≤ (C : ℝ) * h := by linarith [abs_nonneg (β - γ)]
  have hβ : |β - γ| ≤ (C : ℝ) * h := by linarith [norm_nonneg (n - m)]
  have hcoord (j : Fin 2) : |n j - m j| ≤ (C : ℝ) * h := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (n - m) j).trans hnorm
  fin_cases i
  · exact hcoord 0
  · exact hcoord 1
  · exact hβ

def signedStripParameterCodes (C : ℕ) (h : ℝ) (m : Plane) (γ : ℝ) : Finset (Fin 3 → ℤ) :=
  integerCodeBox C (stripParameterCode h m γ) ∪
    integerCodeBox C (stripParameterCode h (-m) (-γ))

theorem card_signedStripParameterCodes_le (C : ℕ) (h : ℝ) (m : Plane) (γ : ℝ) :
    (signedStripParameterCodes C h m γ).card ≤ 2 * (2 * C + 1) ^ 3 := by
  exact (Finset.card_union_le _ _).trans (by rw [card_integerCodeBox, card_integerCodeBox]; omega)

theorem stripParameterCode_mem_signed {h : ℝ} (hh : 0 < h) (C : ℕ)
    {n m : Plane} {β γ : ℝ}
    (hc : ‖n - m‖ + |β - γ| ≤ (C : ℝ) * h ∨
      ‖n + m‖ + |β + γ| ≤ (C : ℝ) * h) :
    stripParameterCode h n β ∈ signedStripParameterCodes C h m γ := by
  rcases hc with hc | hc
  · exact Finset.mem_union.mpr (Or.inl (stripParameterCode_mem_of_close hh C hc))
  · apply Finset.mem_union.mpr
    apply Or.inr
    apply stripParameterCode_mem_of_close hh C
    simpa only [sub_neg_eq_add] using hc

abbrev UnitStripCode := (Fin 3 → ℤ) × ℤ

/-- After the parameter code is fixed, its chosen actual representative
determines a short list of midpoint-position bins from the current base. -/
def unitStripCodeList (Cr Cp : ℕ) (h : ℝ) (m : Plane) (γ r : ℝ)
    (normal : (Fin 3 → ℤ) → Plane) (bias : (Fin 3 → ℤ) → ℝ)
    (t : ℝ) (Y : Plane) : Finset UnitStripCode :=
  (signedStripParameterCodes Cr h m γ).biUnion fun row =>
    (midpointBinList r (normal row) (bias row) t Y Cp).image (fun z => (row, z))

theorem card_unitStripCodeList_le (Cr Cp : ℕ) (h : ℝ) (m : Plane) (γ r : ℝ)
    (normal : (Fin 3 → ℤ) → Plane) (bias : (Fin 3 → ℤ) → ℝ)
    (t : ℝ) (Y : Plane) :
    (unitStripCodeList Cr Cp h m γ r normal bias t Y).card ≤
      2 * (2 * Cr + 1) ^ 3 * (2 * Cp + 1) := by
  calc
    _ ≤ ∑ row ∈ signedStripParameterCodes Cr h m γ,
        ((midpointBinList r (normal row) (bias row) t Y Cp).image (fun z => (row, z))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _row ∈ signedStripParameterCodes Cr h m γ, (2 * Cp + 1) := by
      apply Finset.sum_le_sum
      intro row _
      exact Finset.card_image_le.trans_eq (midpointBinList_card _ _ _ _ _ _)
    _ = (signedStripParameterCodes Cr h m γ).card * (2 * Cp + 1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_signedStripParameterCodes_le Cr h m γ)

theorem original_unit_strip_code_mem_list (l : Line)
    {t₀ q h r t : ℝ} {Cr Cp : ℕ} {c u n m : Plane} {Q : Frame} {β γ : ℝ}
    (normal : (Fin 3 → ℤ) → Plane) (bias : (Fin 3 → ℤ) → ℝ)
    (hq : 0 < q) (hh : 0 < h) (hr : 0 < r) (ht : t ∈ Set.Icc t₀ (t₀ + q))
    (hparams : ‖n - m‖ + |β - γ| ≤ (Cr : ℝ) * h ∨
      ‖n + m‖ + |β + γ| ≤ (Cr : ℝ) * h)
    (hvel : |inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (gv l - u))
      (normal (stripParameterCode h n β)) - bias (stripParameterCode h n β)| ≤ (Cp : ℝ) * r) :
    (stripParameterCode h n β,
      ⌊inner ℝ (Matrix.toEuclideanLin Q⁻¹
        (gy l (t₀ + q / 2) - c - (t₀ + q / 2) • u))
        (normal (stripParameterCode h n β)) / r⌋) ∈
      unitStripCodeList Cr Cp h m γ r normal bias ((t - t₀) / q)
        (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨stripParameterCode h n β, stripParameterCode_mem_signed hh Cr hparams, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨_, original_midpoint_bin_mem_list l hq hr ht hvel, rfl⟩

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
