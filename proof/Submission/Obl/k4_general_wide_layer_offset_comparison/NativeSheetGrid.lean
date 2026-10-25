import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeLossNumerics
import Submission.Obl.k4_general_wide_layer_offset_comparison.ParentLoss
import Submission.Obl.k4_general_wide_layer_offset_comparison.Confine.Support
import Submission.Obl.k4_profile_density_bounds.Asymptotics

-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeSheetGrid.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh

noncomputable section

/-- A SINGLE original physical mesh resolves both native stable-sheet
passes, with the actual original law and native polynomial. -/
structure NativeSheetGrid {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) (k : ℕ) (s : ℝ) (n : ℕ) where
  δ : ℝ
  σ : ℝ
  physical_pos : 0 < δ
  normalized_pos : 0 < σ
  resolve : ∀ i e, (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * δ) ≤ σ
  resolve_scalar : δ * (2 * p.K k + 2) ≤
    σ * (16 * p.K k * a.q k s * PreparedModel.narrow p k s)
  coarse_resolution : (2 * p.K k * parentFilling (p.K k) (PreparedModel.width p k s)) ^ n * σ ≤ 1
  native_resolution : (2 * p.K k * parentFilling (p.K k) (PreparedModel.width p k s)) ^ n * σ ≤
    PreparedModel.width p k s
  bin_resolution : (2 * p.K k * (442368 * p.K k ^ 6)) ^ n * σ ≤ 1
  pure_cap : ∀ c : Fin 3 → ℤ,
    a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ
      (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = c} ≤
      ENNReal.ofReal ((4 * p.K k + 2) * p.K k * δ ^ 3)
  native_cap : ∀ (c : Fin 3 → ℤ) (j : ℤ),
    a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ
      (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = c ∧
      ⌊eval (a.x k z.1 z.2) (a.P k) / PreparedModel.width p k s⌋ = j} ≤
      ENNReal.ofReal (p.K k * (PreparedModel.width p k s) ^ p.d * δ ^ 3)

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- Actual primitive caps and the true atlas construct the common native
grid at one fixed physical exponent. Increasing the subpower loss changes
no original measure, assignment or native polynomial. -/
theorem Valid.eventually_nativeSheetGrid (hp : p.Valid)
    {M : ℕ → ℝ} (hKM : ∀ k, p.K k ≤ M k) (hM : ∀ k, 2 ≤ M k)
    (hMs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε)
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∀ᶠ k in atTop, ∀ R : ℝ, p.AtDepth k s R →
      Nonempty (NativeSheetGrid (p.withLoss M).toParams p.toModel k s n) := by
  let p' := p.withLoss M
  have hp' : p'.Valid := hp.withLoss hKM hMs
  have hpar := hp'.toParams_valid
  have hcommon : p.toModel.Common p'.toParams := hp'.toModel_common
  have hcaps : p.toModel.Caps p'.toParams := hp'.toModel_caps
  have hM1 : ∀ k, 1 ≤ M k := fun k => by linarith [hM k]
  let J : ℕ := 2 * n + 1
  let C : ℝ := ((J : ℝ) + p.κ + p.ℓ) * s + 1
  have hCp : 0 < C := by
    dsimp [C]
    nlinarith [hp.rate_pos, hp.transverse_pos, (Nat.cast_nonneg J : (0 : ℝ) ≤ (J : ℝ))]
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hCp
  let R₀ : ℝ := 2 + C + s + C⁻¹
  have hR₀ : 1 < R₀ := by dsimp [R₀]; linarith
  have hChi : C ≤ R₀ := by dsimp [R₀]; linarith
  have hsR : s ≤ R₀ := by dsimp [R₀]; linarith
  have hClo : R₀⁻¹ ≤ C := by
    have hh := inv_anti₀ (inv_pos.mpr hCp) (show C⁻¹ ≤ R₀ by dsimp [R₀]; linarith)
    simpa only [inv_inv] using hh
  have h1lo : R₀⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR₀.le
  have h1hi : 1 ≤ R₀ := hR₀.le
  have hpure := p.toModel.eventually_pure_base_caps p'.toParams hpar hcommon hcaps hR₀
  have h4 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [hp.scale k] : ∀ k, 1 ≤ p.N k) hp.scale_limit hM1 hMs
    (20 * J + 1) (by norm_num : (-1 : ℝ) < 0) (by positivity : 0 ≤ (3000000 : ℝ) ^ J)
  filter_upwards [hpure, hcaps R₀ hR₀, h4] with k hpurek hcapsk h4k
  intro R hat
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hNp1 : 1 ≤ p.N k := by linarith [hp.scale k]
  have hMp : 0 < M k := by linarith [hM k]
  have hKp : 0 < p.K k := zero_lt_one.trans_le (hp.subpower.1 k)
  have hat' : p'.AtDepth k s R := p.atDepth_withLoss hat hN hKp (hKM k)
  let δ := p.N k ^ (-C)
  let q := ((2 : ℝ) ^ p.T k s)⁻¹
  let g := p.N k ^ (-p.ℓ * s)
  let σ := δ / (q * g)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNp1 (by nlinarith [hp.transverse_pos])
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have ha : 0 < p.N k ^ (-s) := by positivity
  have ha1 : p.N k ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNp1 (by linarith)
  have hfill := parent_filling_two_pass_bounds (hM1 k) ha ha1
  have hres : σ ≤ (parentFilling (M k) (p.N k ^ (-s)) ^ J)⁻¹ := by
    simpa only [σ, δ, C, q, g, p', Parent.withLoss] using
      (resolution_numeric hN (hM1 k) (by positivity : 0 < (2 : ℝ) ^ p.T k s) hat'.2.1 h4k)
  have hB : 1 ≤ 442368 * M k ^ 6 := by
    have hh : 1 ≤ M k ^ 6 := one_le_pow₀ (hM1 k)
    nlinarith
  have hmesh := two_pass_mesh_of_filling (hM1 k) hfill.1 hB hfill.2.1 hfill.2.2 ha1 hσ.le n hres
  refine ⟨{
    δ := δ
    σ := σ
    physical_pos := hδ
    normalized_pos := hσ
    resolve := ?_
    resolve_scalar := ?_
    coarse_resolution := hmesh.1.trans ha1
    native_resolution := hmesh.1
    bin_resolution := hmesh.2
    pure_cap := fun c => hpurek C hClo hChi c
    native_cap := ?_ }⟩
  · intro i e
    change (∑ j, |(p'.toModel.parentSupportZoom p'.toParams k s i).baseMatrix e j| * δ) ≤ σ
    rw [toModel_parentSupportZoom p' k s i]
    exact supportZoom_mesh_resolution (hM1 k) hq hg hg1 hδ.le _ _ _
      ((hat'.2.2.2.2.1 i).2.2.2.1 3) ((hat'.2.2.2.2.1 i).2.2.2.1 4) e
  · change δ * (2 * M k + 2) ≤
      σ * (16 * M k * (2 : ℝ) ^ (-(p.T k s : ℤ)) * g)
    rw [zpow_neg, zpow_natCast]
    change δ * (2 * M k + 2) ≤ σ * (16 * M k * q * g)
    have heq : σ * (16 * M k * q * g) = 16 * M k * δ := by
      dsimp only [σ]
      field_simp
    rw [heq]
    nlinarith [hM1 k, hδ.le]
  · intro c j
    have hc := (hcapsk C s 1 hClo hChi hs.le hsR h1lo h1hi).2.1 true c j
    have hpowers : p.N k ^ (-3 * C - p.d * s) = (p.N k ^ (-s)) ^ p.d * δ ^ 3 := by
      dsimp [δ]
      rw [← Real.rpow_mul hN.le, ← Real.rpow_mul_natCast hN.le, ← Real.rpow_add hN]
      congr 1
      ring
    change p.toModel.mu k {z | p.toModel.cell (p.N k) C k z = c ∧
      ⌊eval (p.toModel.x k z.1 z.2) (p.toModel.P k) / p.N k ^ (-s)⌋ = j} ≤
      ENNReal.ofReal (M k * p.N k ^ (-3 * C - p.d * s)) at hc
    simpa only [PreparedModel.cell_eq_baseMesh, hpowers, δ, mul_assoc,
      p', Parent.withLoss, toParams, toModel, PreparedModel.width] using hc

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
