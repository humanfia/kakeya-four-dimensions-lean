-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.Packing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.Basic

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

open Set Metric
open scoped BigOperators

/-- A radius-`δ` ball contains at most 25 points of a `δ`-separated plane set. -/
theorem card_le_twentyfive_of_separated {δ : ℝ} (hδ : 0 < δ)
    (S : Finset Plane) (c : Plane) (hball : ∀ x ∈ S, dist x c ≤ δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) : S.card ≤ 25 := by
  classical
  let u : Plane → Plane := fun x => δ⁻¹ • (x - c)
  have hu (x y : Plane) : ‖u x - u y‖ = δ⁻¹ * dist x y := by
    dsimp [u]
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hδ.le), dist_eq_norm]
  have huinj : Function.Injective u := by
    intro x y hxy
    have hz : δ⁻¹ * dist x y = 0 := by rw [← hu, hxy, sub_self, norm_zero]
    exact dist_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (inv_ne_zero hδ.ne'))
  have hB := Besicovitch.card_le_of_separated (S.image u) (by
    rintro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hn : ‖u x‖ = δ⁻¹ * dist x c := by
      dsimp [u]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hδ.le), dist_eq_norm]
    rw [hn]
    calc δ⁻¹ * dist x c ≤ δ⁻¹ * δ :=
        mul_le_mul_of_nonneg_left (hball x hx) (inv_nonneg.mpr hδ.le)
      _ = 1 := inv_mul_cancel₀ hδ.ne'
      _ ≤ 2 := by norm_num) (by
    rintro z hz w hw hzw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    rw [hu]
    calc 1 = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
      _ ≤ δ⁻¹ * dist x y := mul_le_mul_of_nonneg_left
        (hsep x hx y hy (fun h => hzw (congrArg u h))) (inv_nonneg.mpr hδ.le))
  rw [Finset.card_image_of_injective _ huinj] at hB
  simpa [Plane, finrank_euclideanSpace_fin] using hB

/-- A finite cover bounds the cardinality of a separated plane set. -/
theorem separated_card_le_twentyfive_mul_cover {δ : ℝ} (hδ : 0 < δ)
    (S : Finset Plane)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    {m : ℕ} {c : Fin m → Plane} (hcov : Covers δ (↑S : Set Plane) c) :
    S.card ≤ 25 * m := by
  classical
  let T (i : Fin m) : Finset Plane := S.filter (fun x => dist x (c i) ≤ δ)
  have hS : S ⊆ Finset.univ.biUnion T := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hx, hi⟩⟩
  have hT (i : Fin m) : (T i).card ≤ 25 := by
    apply card_le_twentyfive_of_separated hδ (T i) (c i)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  calc S.card ≤ (Finset.univ.biUnion T).card := Finset.card_le_card hS
    _ ≤ ∑ i, (T i).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin m, 25 := Finset.sum_le_sum (fun i hi => hT i)
    _ = 25 * m := by simp [Nat.mul_comm]

theorem coverLower_of_separated {δ : ℝ} (hδ : 0 < δ) (S : Finset Plane)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    CoverLower δ (↑S : Set Plane) ((S.card : ℝ) / 25) := by
  intro m c hc
  have hcard := separated_card_le_twentyfive_mul_cover hδ S hsep hc
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 25)).mpr
  have h : (S.card : ℝ) ≤ 25 * (m : ℝ) := by exact_mod_cast hcard
  nlinarith

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
