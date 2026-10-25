import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeSheetGrid
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.AllParentSheets
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.DerivativeListPreparation

-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/ActualNativeSheets.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_stable_native_signal_oscillation
open Native.SheetComparison
open scoped ENNReal

noncomputable section

def nativeSheetSlope : ℕ := all_parents_native_sheets.choose

def nativeSheetIntercept : ℕ := all_parents_native_sheets.choose_spec.choose

/-- A universal fixed sheet exponent: the native deletion exponent is four. -/
def nativeSheetPower : ℕ := nativeSheetSlope * 4 + nativeSheetIntercept

theorem nativeSheetPower_one : 1 ≤ nativeSheetPower := by
  have h := all_parents_native_sheets.choose_spec.choose_spec.1
  change 1 ≤ nativeSheetIntercept at h
  dsimp [nativeSheetPower]
  omega

def nativeSheetExponent : ℕ := 27 * nativeSheetPower + 25

def nativeSheetLoss (M : ℝ) : ℝ := M ^ nativeSheetExponent

/-- Replace the numerical constants of the native kernel by one fixed
power of the enlarged parent loss. -/
theorem native_sheet_power_bounds {M : ℝ} (hM : 2 ≤ M) (n : ℕ) :
    (2 * M * (442368 * M ^ 6)) ^ n ≤ M ^ (27 * n + 25) ∧
      32 * (2 * M) ^ 9 ≤ M ^ (27 * n + 25) := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hconst : (884736 : ℝ) ≤ M ^ 20 := by
    exact (by norm_num : (884736 : ℝ) ≤ 2 ^ 20).trans
      (pow_le_pow_left₀ (by norm_num) hM 20)
  have hbase : 2 * M * (442368 * M ^ 6) ≤ M ^ 27 := by
    calc
      _ = 884736 * M ^ 7 := by ring
      _ ≤ M ^ 20 * M ^ 7 := mul_le_mul_of_nonneg_right hconst (pow_nonneg hM0 _)
      _ = _ := by ring
  constructor
  · calc
      _ ≤ (M ^ 27) ^ n := pow_le_pow_left₀ (by positivity) hbase _
      _ = M ^ (27 * n) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hM1 (by omega)
  · have hconst' : (16384 : ℝ) ≤ M ^ 14 := by
      exact (by norm_num : (16384 : ℝ) ≤ 2 ^ 14).trans
        (pow_le_pow_left₀ (by norm_num) hM 14)
    calc
      _ = 16384 * M ^ 9 := by ring
      _ ≤ M ^ 14 * M ^ 9 := mul_le_mul_of_nonneg_right hconst' (pow_nonneg hM0 _)
      _ = M ^ 23 := by ring
      _ ≤ _ := pow_le_pow_right₀ hM1 (by omega)

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def nativeSheetPoint (M : ℕ → ℝ) (k : ℕ) (s : ℝ) (Q : Fin (p.n k s)) (ω : α × ℝ) : NativePoint :=
  parentZoomPoint (p.withLoss M).toParams p.toModel k s Q ω

def nativeSheetBase (M : ℕ → ℝ) (k : ℕ) (s : ℝ) (Q : Fin (p.n k s)) (ω : α × ℝ) :
    EuclideanSpace ℝ (Fin 3) := toEuc (rootBaseCoordinates (p.nativeSheetPoint M k s Q ω))

def nativeSheetBranch (M : ℕ → ℝ) (k : ℕ) (s : ℝ) (Q : Fin (p.n k s)) (ω : α × ℝ) : Bool :=
  branch ((p.toModel.parentSupportZoom (p.withLoss M).toParams k s Q).push (p.F k s Q))
    (rootBaseCoordinates (p.nativeSheetPoint M k s Q ω)) (p.nativeSheetPoint M k s Q ω 3)

/-- Actual stable native sheets at one depth, for the literal original
incidence law and native signal. All parents share one original bad set. -/
structure NativeSheetAtlas (M : ℕ → ℝ) (k : ℕ) (s : ℝ) where
  relation : Fin (p.n k s) → MvPolynomial (Fin 4) ℂ
  sheet : Fin (p.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ
  relation_nonzero : ∀ Q, relation Q ≠ 0
  relation_degree : ∀ Q, (relation Q).totalDegree ≤ 4
  bad : Set (α × ℝ)
  bad_measurable : MeasurableSet bad
  bad_mass : p.μ k bad ≤ ENNReal.ofReal ((4 * M k)⁻¹)
  stable : ∀ Q, ∀ᵐ ω ∂p.μ k, ω.1 ∈ p.B k s Q →
    ω.2 ∈ block (p.T k s) (p.j k s Q) → ω ∉ bad →
    SheetOn (relation Q) (sheet Q (p.nativeSheetBranch M k s Q ω))
      (p.nativeSheetBase M k s Q ω) (4 * (nativeSheetLoss (M k))⁻¹) (nativeSheetLoss (M k)) ∧
    |eval (p.x k ω.1 ω.2) (p.P k) -
      (sheet Q (p.nativeSheetBranch M k s Q ω) (emb (p.nativeSheetBase M k s Q ω))).re| ≤
        nativeSheetLoss (M k) * p.N k ^ (-s)

/-- The actual native-sheet atlas follows from the original prepared
parent inputs. No continuous-density or new graph hypothesis is assumed. -/
theorem Valid.eventually_nativeSheetAtlas (hp : p.Valid)
    {M : ℕ → ℝ} (hKM : ∀ k, p.K k ≤ M k) (hM : ∀ k, 2 ≤ M k)
    (hMs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, ∀ R : ℝ, p.AtDepth k s R → Nonempty (p.NativeSheetAtlas M k s) := by
  let p' := p.withLoss M
  have hp' : p'.Valid := hp.withLoss hKM hMs
  have hAll := all_parents_native_sheets.choose_spec.choose_spec.2
  filter_upwards [hp.eventually_nativeSheetGrid hKM hM hMs hs nativeSheetPower] with k hk
  intro R hat
  obtain ⟨grid⟩ := hk R hat
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hK : 0 < p.K k := zero_lt_one.trans_le (hp.subpower.1 k)
  have hM1 : 1 ≤ M k := by linarith [hM k]
  have ha : 0 < p.N k ^ (-s) := by positivity
  have ha1 : p.N k ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.scale k])
    (by linarith)
  have hat' : p'.AtDepth k s R := p.atDepth_withLoss hat hN hK (hKM k)
  obtain ⟨Rel, g, E, hRel, hEm, hE, hae⟩ := hAll 4 p'.toParams hp'.toParams_valid p.toModel
    hp'.toModel_common R k s hs.le hat'.toAtlasAt
    grid.δ grid.σ grid.δ grid.σ grid.physical_pos grid.normalized_pos grid.physical_pos grid.normalized_pos
    grid.resolve_scalar grid.resolve_scalar grid.coarse_resolution grid.native_resolution grid.bin_resolution
    grid.pure_cap grid.native_cap
  have hfill := parent_filling_two_pass_bounds hM1 ha ha1
  have hB : 1 ≤ parentBinCap (M k) := parentBinCap_ge _ hM1
  have hF : 1 ≤ parentFilling (M k) (p.N k ^ (-s)) := (by linarith : 1 ≤ 2 * M k).trans hfill.1
  have hpow := native_sheet_power_bounds (hM k) nativeSheetPower
  have hV : 0 < (2 * M k * (442368 * M k ^ 6)) ^ nativeSheetPower := by positivity
  refine ⟨{
    relation := Rel
    sheet := g
    relation_nonzero := fun Q => (hRel Q).1
    relation_degree := fun Q => (hRel Q).2
    bad := E
    bad_measurable := hEm
    bad_mass := hE.trans (ENNReal.ofReal_le_ofReal (two_pass_original_exception_four (hM k) hF hB))
    stable := ?_ }⟩
  intro Q
  filter_upwards [hae Q] with ω hω hl ht hnot
  obtain ⟨hstable, hfit⟩ := hω ⟨hl, ht⟩ hnot
  refine ⟨(hstable.mono_radius ?_).mono hpow.1, ?_⟩
  · exact mul_le_mul_of_nonneg_left (inv_anti₀ hV hpow.1) (by norm_num)
  · exact hfit.trans (mul_le_mul_of_nonneg_right hpow.2 ha.le)

theorem Valid.eventually_nativeSheetAtlas_of_depth (hp : p.Valid)
    {M : ℕ → ℝ} (hKM : ∀ k, p.K k ≤ M k) (hM : ∀ k, 2 ≤ M k)
    (hMs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε)
    {s : ℝ} (hs : 0 < s) (hsU : s ≤ p.U) :
    ∀ᶠ k in atTop, Nonempty (p.NativeSheetAtlas M k s) := by
  have hsp : 0 < s⁻¹ := inv_pos.mpr hs
  let R := 2 + s + s⁻¹
  have hR : 1 < R := by dsimp [R]; linarith
  have hRs : R⁻¹ ≤ s := by
    have hh := inv_anti₀ hsp (show s⁻¹ ≤ R by dsimp [R]; linarith)
    simpa only [inv_inv] using hh
  filter_upwards [Valid.eventually_nativeSheetAtlas p hp hKM hM hMs hs, hp.prepared R hR] with k hk hprep
  exact hk R (hprep s hRs hsU)

/-- The native exceptional set costs at most a quarter of an original
source of mass 1/M. Restriction retains at least 1/(2M) in the same units. -/
theorem NativeSheetAtlas.retained_mass {M : ℕ → ℝ} {k : ℕ} {s : ℝ}
    (a : p.NativeSheetAtlas M k s) (hp : p.Valid) (hM : 0 < M k)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.ρ k)
    (hmass : ENNReal.ofReal ((M k)⁻¹) ≤ σ univ) :
    ENNReal.ofReal ((2 * M k)⁻¹) ≤ (σ.restrict a.badᶜ) univ := by
  apply Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.restrict_mass_after_deletion
    σ MeasurableSet.univ a.bad_measurable.compl (subset_univ _) (by simp)
    (by positivity : 0 ≤ (2 * M k)⁻¹) (by positivity : 0 ≤ (4 * M k)⁻¹) hmass
  · simpa using ((hσ.trans (hp.basic k).2.2.2.2.1) a.bad).trans a.bad_mass
  · rw [mul_inv, mul_inv]
    norm_num
    nlinarith [inv_nonneg.mpr hM.le]

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
