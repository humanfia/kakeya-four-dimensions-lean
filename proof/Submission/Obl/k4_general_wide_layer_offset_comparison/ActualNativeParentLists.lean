-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/ActualNativeParentLists.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.ActualNativeParentListsAt
import Submission.Obl.k4_critical_intercept_concentration.CriticalScales

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter MvPolynomial
open Native.SheetComparison
open Submission.Obl.k4_contact_affine_residual_candidate_transfer
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The true/coarse native comparison, with all common frames, meshes,
original caps, source deletions and list counts derived from the original
prepared model. The returned loss is subpower at every positive exponent. -/
theorem actual_native_parent_lists (hp : p.Valid)
    (hmatching : Submission.Lib.K4QuadSheetMatching.TwoColorStatement)
    {s m : ℝ} (hs : 0 < s) (hsU : s ≤ p.U) (hgap : (p.κ + p.ℓ) * s < m)
    (H : ℕ → ℝ) (hH : ∀ k, 2 ≤ H k) (hKH : ∀ k, p.K k ≤ H k)
    (hHs : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, H k ≤ p.N k ^ η)
    (L : ℕ → ProjectedLayer α) (hL : ∀ k, (L k).Valid p k s m (H k))
    (source : ℕ → Measure (α × ℝ)) (hsource : ∀ k, source k ≤ p.ρ k)
    (hmass : ∀ k, ENNReal.ofReal ((H k)⁻¹) ≤ source k univ)
    (hcovered : ∀ k, (L k).Covers (source k)) :
    ∃ J : ℕ → ℝ, (∀ k, 2 ≤ J k ∧ p.K k ≤ J k) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, J k ≤ p.N k ^ η) ∧
      ∀ᶠ k in atTop, Nonempty (p.NativeParentLists k s m (J k) (L k) (source k)) := by
  obtain ⟨ε, hε, C, hC1, Match⟩ := sheet_comparison hmatching 4 (by norm_num)
    p.d hp.dimension_nonneg hp.dimension_lt_one
  have hC : 0 ≤ C := zero_le_one.trans hC1
  let D := max 2 (max projectedSheetConstant C)
  have hD2 : 2 ≤ D := le_max_left _ _
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hDC : C ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hDP : projectedSheetConstant ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  let M : ℕ → ℝ := fun k => D * (1 + H k + p.K k)
  have hlarge (k : ℕ) : 2 ≤ M k ∧ H k ≤ M k ∧ p.K k ≤ M k ∧
      projectedSheetConstant ≤ M k ∧ C ≤ M k := by
    have hK := hp.subpower.1 k
    have hHk := hH k
    have hsum : 1 ≤ 1 + H k + p.K k := by linarith
    have hsum0 : 0 ≤ 1 + H k + p.K k := by linarith
    have hsumM : 1 + H k + p.K k ≤ M k := le_mul_of_one_le_left hsum0 hD1
    have hDM : D ≤ M k := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum hD0
    exact ⟨hD2.trans hDM, (by linarith : H k ≤ 1 + H k + p.K k).trans hsumM,
      (by linarith : p.K k ≤ 1 + H k + p.K k).trans hsumM,
      hDP.trans hDM, hDC.trans hDM⟩
  have hM2 : ∀ k, 2 ≤ M k := fun k => (hlarge k).1
  have hM1 : ∀ k, 1 ≤ M k := fun k => by linarith [hM2 k]
  have hKM : ∀ k, p.K k ≤ M k := fun k => (hlarge k).2.2.1
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.scale k]
  have hN0 : ∀ k, 0 ≤ p.N k := fun k => zero_le_one.trans (hN1 k)
  have hHsmall : Small p.N H := ⟨Eventually.of_forall (fun k => by linarith [hH k]), hHs⟩
  have hKsmall : Small p.N p.K :=
    ⟨Eventually.of_forall (fun k => zero_le_one.trans (hp.subpower.1 k)), hp.subpower.2⟩
  have hMsmall : Small p.N M := (Small.const hp.scale_limit hD0).mul hN0
    (((Small.const hp.scale_limit zero_le_one).add hp.scale_limit hHsmall).add hp.scale_limit hKsmall)
  have hMs := hMsmall.2
  have hpM : (p.withLoss M).Valid := hp.withLoss hKM hMs
  let J : ℕ → ℝ := fun k => nativeFinalListLoss (M k) (H k) p.d ε C
  have hJsmall : Small p.N J := nativeFinalListLoss_small hN1 hp.scale_limit
    hMsmall hHsmall hp.dimension_nonneg hε hC
  refine ⟨J, ?_, hJsmall.2, ?_⟩
  · intro k
    have hh := (nativeFinalListLoss_bounds (H := H k) (d := p.d) (hM1 k) hC
      (hlarge k).2.2.2.2 hε).1
    exact ⟨by dsimp [J]; linarith [hM2 k], by dsimp [J]; linarith [hKM k, hM2 k]⟩
  have hm : 0 < m := by nlinarith [hp.rate_pos, hp.transverse_pos]
  let P := m + s + 1
  have hP : 0 < P := by dsimp [P]; linarith
  let R := 2 + s + m + P + s⁻¹ + m⁻¹ + P⁻¹
  have hsi : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hmi : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
  have hPi : 0 ≤ P⁻¹ := inv_nonneg.mpr hP.le
  have hR : 1 < R := by dsimp [R]; linarith
  have hsR : s ≤ R := by dsimp [R]; linarith
  have hmR : m ≤ R := by dsimp [R]; linarith
  have hPR : P ≤ R := by dsimp [R]; linarith
  have hRs : R⁻¹ ≤ s := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hs)
      (show s⁻¹ ≤ R by dsimp [R]; linarith)
  have hRm : R⁻¹ ≤ m := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hm)
      (show m⁻¹ ≤ R by dsimp [R]; linarith)
  have hRP : R⁻¹ ≤ P := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hP)
      (show P⁻¹ ≤ R by dsimp [R]; linarith)
  have hχevent := eventually_native_common_mesh hN1 hp.scale_limit hM1 hMs nativeSheetExponent hgap
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.scale_limit hM1 hMs 1 (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) ≤ 3)
  filter_upwards [Valid.eventually_nativeSheetAtlas_of_depth p hp hKM hM2 hMs hs hsU,
    hpM.prepared R hR, hpM.caps R hR, hχevent, hsmall] with k hatlas hprep hcaps hχk hsmallk
  obtain ⟨atlas⟩ := hatlas
  have hat : (p.withLoss M).AtDepth k s R := hprep s hRs hsU
  have hNp : 0 < p.N k := by linarith [hp.scale k]
  have hMp : 0 < M k := by linarith [hM2 k]
  have hlength := Submission.Obl.k4_critical_intercept_concentration.time_length_comparison
    hNp hMp hat.1 hat.2.1
  have hQlow : p.N k ^ (-p.κ * s) / M k ≤ p.toModel.q k s := by
    apply (div_le_iff₀ hMp).mpr
    simpa only [Parent.toModel_q, Parent.withLoss, zpow_neg, zpow_natCast, mul_comm] using hlength.2
  have hχsmall : p.N k ^ (-m) ≤
      (p.toModel.q k s * p.N k ^ (-p.ℓ * s)) / (10000 * nativeSheetLoss (M k)) :=
    hχk (p.toModel.q k s) hQlow
  have hcap : ∀ t : ℝ, 0 ≤ t → t ≤ s → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      p.μ k {ω | p.toModel.cell (p.N k) (m + s + 1) k ω = z ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / p.N k ^ (-t)⌋ = j ∧
        ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = v₀} ≤
      ENNReal.ofReal (M k * p.N k ^ (-3 * (m + s + 1) - p.d * t)) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = v₀} := by
    intro t ht hts z j v₀
    exact (hcaps P t m hRP hPR ht (hts.trans hsR) hRm hmR).2.2 true z j v₀
  have hmassM : ENNReal.ofReal ((M k)⁻¹) ≤ source k univ :=
    (ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith [hH k] : 0 < H k)
      (hlarge k).2.1)).trans (hmass k)
  apply atlas.parent_lists_at p hp hpM hat hs.le (hM2 k) (by linarith [hH k])
    (hlarge k).2.1 (hlarge k).2.2.2.1 hC (hlarge k).2.2.2.2 hε Match
    (L k) (hL k) hχsmall
  · simpa only [pow_one, Real.rpow_zero] using hsmallk.le
  · exact hcap
  · exact hsource k
  · exact hmassM
  · exact hcovered k

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
