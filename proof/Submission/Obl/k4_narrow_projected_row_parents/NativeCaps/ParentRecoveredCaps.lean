/- Adapted from this LOT tree o222, session x0774, commit 9dbb47a74d2ab640ef4d8807465d86d7e9066adc,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentRecoveredCaps.lean. -/
import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.ParentRecoveryMesh
import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.OriginalNativeCaps

/-! Recovered parent base caps on every fixed row mesh, with original palettes. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set MvPolynomial Filter Matrix
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_stable_native_signal_oscillation (nativeBase)

noncomputable section

def recoveredParentBaseConstant (K M : ℝ) : ℝ :=
  27 * (2 * (2 * (2 * (2 * K) ^ 14 + 1) + 2)) * K ^ 2 * M

/-- Once the stable groups are fixed, every finer row mesh inherits pure
and velocity-joint base caps on the SAME retained original law. -/
theorem eventually_parent_recovered_caps {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    (hcaps : a.Caps p) (hatlases : a.Atlases p) {r B C : ℝ}
    (hr : 0 < r) (hrU : r ≤ p.U) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (E : (k : ℕ) → Fin (a.n k r) → Fin 2 → Set (α × ℝ))
    (ν : (k : ℕ) → Fin (a.n k r) → Measure (α × ℝ))
    (A : (k : ℕ) → Fin (a.n k r) → Matrix (Fin 3) (Fin 3) ℝ)
    (b₀ : (k : ℕ) → Fin (a.n k r) → Fin 3 → ℝ)
    (lam : (k : ℕ) → Fin (a.n k r) → ℝ) (M : ℕ → ℝ)
    (hA : ∀ᶠ k in atTop, ∀ i e, (∑ j, |A k i e j|) ≤ p.N k ^ C)
    (hchart : ∀ᶠ k in atTop, ∀ i, (A k i).det ≠ 0 ∧
      |(A k i).det|⁻¹ = |lam k i| * a.q k r ^ 3 * PreparedModel.narrow p k r ∧
        |lam k i| ≤ M k)
    (hsource : ∀ᶠ k in atTop, ∀ i, ν k i ≤ a.mu k ∧
      (∀ᵐ z ∂ν k i, ∃ e, z ∈ E k i e) ∧
      ∀ e z, z ∈ E k i e → ∀ w, w ∈ E k i e →
        |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
          2 * (2 * p.K k) ^ 14 * PreparedModel.width p k r + p.N k ^ B *
            ‖nativeBase ((a.parentSupportZoom p k r i).nativePoint (a.nativePoint k z)) -
              nativeBase ((a.parentSupportZoom p k r i).nativePoint (a.nativePoint k w))‖) :
    ∀ t v : ℝ, 0 < t → 0 < v → ∀ᶠ k in atTop, ∀ i : Fin (a.n k r),
      let ζ := (ENNReal.ofReal (a.q k r * (a.nu k (a.A k r i)).toReal))⁻¹ • ν k i
      let z := fun u : α × ℝ => affineBase (A k i) (b₀ k i) (basePoint (a.b k u.1) u.2)
      (∀ q : Fin 3 → ℤ, ζ {u | baseMesh (p.N k ^ (-t)) (z u) = q} ≤
        ENNReal.ofReal (recoveredParentBaseConstant (p.K k) (M k) * (p.N k ^ (-t)) ^ 3)) ∧
      (∀ (q : Fin 3 → ℤ) (j : ℤ),
        ζ {u | baseMesh (p.N k ^ (-t)) (z u) = q ∧ ⌊a.b k u.1 3 / p.N k ^ (-v)⌋ = j} ≤
          ENNReal.ofReal (recoveredParentBaseConstant (p.K k) (M k) * (p.N k ^ (-t)) ^ 3) *
            a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = j}) ∧
      ∀ j : ℤ, a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = j} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-p.S * v)) := by
  intro t v ht hv
  obtain ⟨D, hD, hmesh⟩ := eventually_parent_recovery_mesh p hp a hr hB hC ht A hA
  let R : ℝ := 2 + r + r⁻¹
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by dsimp [R]; linarith
  have hRr : R⁻¹ ≤ r := by
    have h : r⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ hri h
  filter_upwards [hmesh, eventually_original_native_bin_caps p hp a hcaps hD hr.le hv,
    hatlases R hR, hchart, hsource] with k hkm hkc hka hkchart hksource
  intro i
  dsimp only
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hatlas : a.AtlasAt p R k r := hka r hRr hrU
  have hmsh := hkm R hatlas i
  letI : IsProbabilityMeasure (a.pi k) := (hcommon k).2.2.1
  have hrecover (condition : α × ℝ → Prop) (weight : ENNReal) (hw : weight ≠ ⊤)
      (horig : ∀ (q : Fin 3 → ℤ) (j : ℤ),
        a.mu k {u | baseMesh (p.N k ^ (-D)) (basePoint (a.b k u.1) u.2) = q ∧
          ⌊eval (a.x k u.1 u.2) (a.P k) / PreparedModel.width p k r⌋ = j ∧ condition u} ≤
          ENNReal.ofReal (p.K k * PreparedModel.width p k r ^ p.d * (p.N k ^ (-D)) ^ 3) *
            weight) (q : Fin 3 → ℤ) :
      ((ENNReal.ofReal (a.q k r * (a.nu k (a.A k r i)).toReal))⁻¹ • ν k i)
          {u | baseMesh (p.N k ^ (-t))
            (affineBase (A k i) (b₀ k i) (basePoint (a.b k u.1) u.2)) = q ∧ condition u} ≤
        ENNReal.ofReal (recoveredParentBaseConstant (p.K k) (M k) * (p.N k ^ (-t)) ^ 3) *
          weight := by
    have h := parent_stable_affine_base_cap p hp a hcommon hatlas i (ν k i)
      (hksource i).1 (E k i) (hksource i).2.1 (Real.rpow_nonneg hN.le B)
      (Real.rpow_pos_of_pos hN (-D)) (Real.rpow_pos_of_pos hN (-t)) hmsh.1 hmsh.2.1
      (hksource i).2.2 condition weight hw horig (A k i) (b₀ k i)
      (hkchart i).1 hmsh.2.2 (hkchart i).2.1 q
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    dsimp [recoveredParentBaseConstant]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hkchart i).2.2 (by positivity)) (by positivity)
  refine ⟨?_, ?_, hkc.2.2⟩
  · intro q
    simpa only [and_true, mul_one] using hrecover (fun _ => True) 1 (by simp)
      (fun q j => by simpa only [and_true, mul_one] using hkc.1 q j) q
  · intro q j
    exact hrecover (fun u => ⌊a.b k u.1 3 / p.N k ^ (-v)⌋ = j)
      (a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = j}) (measure_ne_top _ _)
      (fun q l => hkc.2.1 q l j) q

end

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
