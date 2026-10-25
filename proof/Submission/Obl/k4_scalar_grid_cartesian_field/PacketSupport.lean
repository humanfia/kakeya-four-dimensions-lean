import Submission.Obl.k4_scalar_grid_cartesian_field.ActiveCodes
import Submission.Obl.k4_scalar_grid_cartesian_field.CoarseGraphCodes
import Submission.Obl.k4_scalar_grid_cartesian_field.GridCodeTransfer
import Submission.Obl.k4_scalar_grid_cartesian_field.RegisteredGrid

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial

/-- Hereditary physical counts localize to the original coarse graph cells of a packet. -/
theorem physical_support_of_coarse_graph {Ω : Type*} [MeasurableSpace Ω]
    (ρ μ : Measure Ω) (hμ : μ ≤ ρ) (S : Set Ω) (hsupport : μ Sᶜ = 0)
    (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    {δ h b L R : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hL : 1 ≤ L)
    (hscale : δ ≤ L * h) (hR : 0 ≤ R) (origin : Fin 2 → ℝ)
    (hbase : ∀ p ∈ S, ∀ e, |z p e - origin e| ≤ L * h)
    (hfit : ∀ p ∈ S, |x p - eval (z p) F| ≤ L * δ)
    (hgrad : ∀ p ∈ S, ∀ e, |eval (z p) (pderiv e F)| ≤ L)
    (hfinite : (activeCodes ρ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋ : ℤ))).Finite)
    (hcount : ∀ q₀ : Fin 3 → ℤ,
      ({q : Fin 3 → ℤ | ρ {p |
        (fun e : Fin 3 => (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋ : ℤ)) = q ∧
        (fun e : Fin 3 => (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / δ⌋ : ℤ)) = q₀} ≠ 0}.ncard : ℝ) ≤ R) :
    (activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋ : ℤ))).Finite ∧
    ((activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋ : ℤ))).ncard : ℝ) ≤
        1000 * L ^ 3 * (h / δ) ^ 2 * R := by
  classical
  let fine : Ω → Fin 3 → ℤ := fun p e => ⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋
  let coarse : Ω → Fin 3 → ℤ := fun p e => ⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / δ⌋
  obtain ⟨C, hC, hcover⟩ := coarse_graph_code_cover_scaled S z x F hF hδ hh hL
    hscale origin hbase hfit hgrad
  have hCae : ∀ᵐ p ∂μ, coarse p ∈ C := by
    filter_upwards [ae_iff.mpr hsupport] with p hp
    exact hcover p (by simpa using hp)
  have hjointfinite (q₀ : Fin 3 → ℤ) : {q | ρ {p | fine p = q ∧ coarse p = q₀} ≠ 0}.Finite := by
    apply hfinite.subset
    intro q hq
    change ρ {p | fine p = q} ≠ 0
    intro hz
    exact hq (measure_mono_null (fun _ hp => hp.1) hz)
  obtain ⟨hf, hn⟩ := hereditary_active_code_count ρ μ hμ fine coarse C hCae
    hjointfinite (fun q₀ _ => hcount q₀)
  exact ⟨hf, hn.trans (mul_le_mul_of_nonneg_right hC hR)⟩

/-- A grid width within one preparation loss of the requested hidden width suffices. -/
theorem joint_support_of_physical_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ) (origin : Fin 2 → ℝ)
    {b h ξ w δ A H d : ℝ} (hb : 0 < b) (hh : 0 < h) (hξ : 0 < ξ)
    (hδ : 0 < δ) (hA : 0 ≤ A) (hH : 1 ≤ H) (hd : 0 ≤ d) (hdone : d ≤ 1)
    (hbase : h * ξ ≤ b) (hhidden : b ≤ w) (hround : w ≤ H * b)
    (hfinite : (activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋ : ℤ))).Finite)
    (hcount : ((activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / b⌋ : ℤ))).ncard : ℝ) ≤
        A * (h / b) ^ 2 * (δ / b) ^ d) :
    (activeCodes μ (fun p => ((fun e : Fin 2 => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)),
      (⌊x p / w⌋ : ℤ)))).Finite ∧
    ((activeCodes μ (fun p => ((fun e : Fin 2 => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)),
      (⌊x p / w⌋ : ℤ)))).ncard : ℝ) ≤
        32 * A * H * ξ⁻¹ ^ 2 * (δ / w) ^ d := by
  have hw : 0 < w := hb.trans_le hhidden
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hratio : δ / b ≤ H * (δ / w) := by
    apply (div_le_iff₀ hb).mpr
    have hid : H * (δ / w) * b = δ * (H * b) / w := by ring
    rw [hid]
    exact (le_div_iff₀ hw).mpr (by nlinarith)
  have hrpow : (δ / b) ^ d ≤ H * (δ / w) ^ d := by
    calc
      _ ≤ (H * (δ / w)) ^ d := Real.rpow_le_rpow (div_nonneg hδ.le hb.le) hratio hd
      _ = H ^ d * (δ / w) ^ d := Real.mul_rpow hHp.le (div_nonneg hδ.le hw.le)
      _ ≤ H ^ (1 : ℝ) * (δ / w) ^ d := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hH hdone) (by positivity)
      _ = _ := by rw [Real.rpow_one]
  obtain ⟨hf, hn⟩ := physical_to_normalized_joint_count μ z x origin hb hh hξ hbase hhidden hfinite
  refine ⟨hf, hn.trans ?_⟩
  calc
    _ ≤ 32 * (b / (h * ξ)) ^ 2 * (A * (h / b) ^ 2 * (δ / b) ^ d) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = 32 * A * ξ⁻¹ ^ 2 * (δ / b) ^ d := by field_simp
    _ ≤ 32 * A * ξ⁻¹ ^ 2 * (H * (δ / w) ^ d) := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_scalar_grid_cartesian_field
