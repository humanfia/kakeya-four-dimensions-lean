/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/NormalizedCaps.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.AffineResidualCaps

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open Set MeasureTheory Filter MvPolynomial Matrix
open Submission.Lib.K4ContactNormalization (affineBase)
open Submission.Lib.K4AffineMeshCaps (baseMesh)
open Submission.Obl.k4_critical_switching_state_preparation

/-- Dividing by a positive original reference preserves any original palette
factor verbatim. -/
theorem cap_divide_original_reference {Ω : Type*} [MeasurableSpace Ω]
    (τ : Measure Ω) (E : Set Ω) {W C C' : ℝ} (hW : 0 < W)
    (hbudget : C ≤ C' * W) (Γ : ENNReal)
    (hcap : τ E ≤ ENNReal.ofReal C * Γ) :
    (ENNReal.ofReal W⁻¹ • τ) E ≤ ENNReal.ofReal C' * Γ := by
  rw [Measure.smul_apply, smul_eq_mul]
  calc
    ENNReal.ofReal W⁻¹ * τ E ≤ ENNReal.ofReal W⁻¹ * (ENNReal.ofReal C * Γ) :=
      mul_le_mul' le_rfl hcap
    _ ≤ ENNReal.ofReal W⁻¹ * (ENNReal.ofReal (C' * W) * Γ) :=
      mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl)
    _ = ENNReal.ofReal C' * Γ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hW).le,
        show W⁻¹ * (C' * W) = C' by field_simp]

/-- Residual scalar caps after division by the original parent reference.
The determinant and the coarse scalar thickness are cancelled together;
the loss `J` is the original-reference comparison, not the inverse mass of
the successful incidence subset. -/
theorem normalized_affine_residual_mesh_caps {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {B A R s₀ : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hR : 1 < R) (hs₀ : 0 ≤ s₀) :
    ∀ᶠ k in atTop, ∀ (τ : Measure (α × ℝ)), τ ≤ D.μ k →
      ENNReal.ofReal (D.N k ^ (-B)) ≤ τ univ → ∀ L : Fin 4 → ℝ,
      (∀ᵐ x ∂τ, |eval (D.x k x.1 x.2) (affineBase L) - (D.x k x.1 x.2) 3| ≤ 1 / 4) →
      ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ), M.det ≠ 0 →
      (∀ i, ∑ j, |M i j| ≤ D.N k ^ A) →
      ∀ W J : ℝ, 0 < W → 0 ≤ J →
      |M.det|⁻¹ * D.N k ^ (-D.d * s₀) ≤ J * W →
      ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
      let Z := fun x : α × ℝ => D.x k x.1 x.2 ∘ Fin.castSucc
      let code := fun x => baseMesh (D.N k ^ (-r))
        (Submission.Lib.K4AffineMeshCaps.affineBase M b (Z x))
      let scalar := fun x => ((D.x k x.1 x.2) 3 - eval (D.x k x.1 x.2) (affineBase L)) /
        D.N k ^ (-(s₀ + s))
      let C := 27 * (6 * D.K k + 5) * D.K k * J * D.N k ^ (-3 * r - D.d * s)
      (∀ (q : Fin 3 → ℤ) (j : ℤ),
        (ENNReal.ofReal W⁻¹ • τ) {x | code x = q ∧ ⌊scalar x⌋ = j} ≤ ENNReal.ofReal C) ∧
      (∀ (q : Fin 3 → ℤ) (j v₀ : ℤ),
        (ENNReal.ofReal W⁻¹ • τ)
          {x | code x = q ∧ ⌊scalar x⌋ = j ∧ ⌊D.b k x.1 3 / D.N k ^ (-v)⌋ = v₀} ≤
          ENNReal.ofReal C * D.π k {w : ℝ | ⌊w / D.N k ^ (-v)⌋ = v₀}) := by
  let R' : ℝ := R + s₀ + 2
  have hR' : 1 < R' := by dsimp [R']; linarith
  have hRR' : R ≤ R' := by dsimp [R']; linarith
  have hRinv : R'⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < R) hRR'
  filter_upwards [affine_residual_mesh_caps D p h1 h2 hB hA hR'] with k hk
  intro τ hτ hmass L hfit M b hM hsize W J hW hJ href r s v hrl hru hs hsu hvl hvu
  dsimp only
  have hN : 0 < D.N k := lt_of_lt_of_le (by norm_num) (p.scale k)
  have hK : 0 ≤ D.K k := (by norm_num : (0 : ℝ) ≤ 1).trans (p.subpower.1 k)
  have hcap := hk τ hτ hmass L hfit M b hM hsize r (s₀ + s) v
    (hRinv.trans hrl) (hru.trans hRR') (add_nonneg hs₀ hs)
    (by dsimp [R']; linarith) (hRinv.trans hvl) (hvu.trans hRR')
  have hexp : D.N k ^ (-3 * r - D.d * (s₀ + s)) =
      D.N k ^ (-D.d * s₀) * D.N k ^ (-3 * r - D.d * s) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hbudget : 27 * (6 * D.K k + 5) * D.K k * |M.det|⁻¹ *
      D.N k ^ (-3 * r - D.d * (s₀ + s)) ≤
      (27 * (6 * D.K k + 5) * D.K k * J * D.N k ^ (-3 * r - D.d * s)) * W := by
    rw [hexp]
    have hh := mul_le_mul_of_nonneg_left href
      (by positivity : 0 ≤ (27 : ℝ) * (6 * D.K k + 5) * D.K k *
        D.N k ^ (-3 * r - D.d * s))
    nlinarith only [hh]
  constructor
  · intro q j
    have hh := cap_divide_original_reference τ _ hW hbudget 1
      (by simpa only [mul_one] using hcap.1 q j)
    simpa only [mul_one] using hh
  · intro q j v₀
    exact cap_divide_original_reference τ _ hW hbudget _ (hcap.2 q j v₀)

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
