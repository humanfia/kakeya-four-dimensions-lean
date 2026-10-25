/- Adapted from this LOT tree o222, session x0774, commit 9dbb47a74d2ab640ef4d8807465d86d7e9066adc,
   Submission/Obl/k4_projected_parent_contact_reduction/StableBaseLaw.lean. -/
import Submission.Lib.K4AffineMeshCaps.Transport
import Submission.Lib.K4SignalMeshSupport.Caps

/-! Recover and transport the original base caps before contact normalization. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set Matrix
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4SignalMeshSupport (base_cap_of_stable_signal_groups)

noncomputable section

/-- Stable native-signal groups give pure base caps for any retained sublaw.
The original palette factor survives the affine chart and mass normalization. -/
theorem normalized_stable_affine_base_cap {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ ν : Measure Ω) (hν : ν ≤ μ) (Z : Ω → Fin 3 → ℝ)
    (signal : Ω → ℝ) (condition : Ω → Prop) (E : ι → Set Ω)
    {a M C delta sigma m : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hd : 0 < delta) (hs : 0 < sigma) (hm : 0 < m)
    (hcover : ∀ᵐ p ∂ν, ∃ i, p ∈ E i)
    (hosc : ∀ i p, p ∈ E i → ∀ p', p' ∈ E i →
      baseMesh delta (Z p) = baseMesh delta (Z p') → |signal p - signal p'| ≤ M * a)
    (weight : ENNReal) (hw : weight ≠ ⊤)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh delta (Z p) = q ∧ ⌊signal p / a⌋ = j ∧ condition p} ≤
        ENNReal.ofReal (C * delta ^ 3) * weight)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hA : A.det ≠ 0)
    (hresolve : ∀ i, (∑ j, |A i j| * delta) ≤ sigma)
    (q : Fin 3 → ℤ) :
    ((ENNReal.ofReal m)⁻¹ • ν)
        {p | baseMesh sigma (affineBase A b (Z p)) = q ∧ condition p} ≤
      ENNReal.ofReal (27 * ((Fintype.card ι : ℝ) * (2 * M + 2)) *
        C * |A.det|⁻¹ / m * sigma ^ 3) * weight := by
  let T : ℝ := (Fintype.card ι : ℝ) * (2 * M + 2)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hbase (r : Fin 3 → ℤ) :
      ν {p | baseMesh delta (Z p) = r ∧ condition p} ≤
        ENNReal.ofReal ((T * C * weight.toReal) * delta ^ 3) := by
    have hsub : {p | baseMesh delta (Z p) = r ∧ condition p} ≤ᵐ[ν]
        {p | baseMesh delta (Z p) = r ∧ (∃ i, p ∈ E i) ∧ condition p} := by
      filter_upwards [hcover] with p hp he
      exact ⟨he.1, hp, he.2⟩
    have hstable := base_cap_of_stable_signal_groups μ (fun p => baseMesh delta (Z p))
      signal condition E ha hM hosc
      (fun _ => ENNReal.ofReal (C * delta ^ 3) * weight) hcap r
    calc
      _ ≤ ν {p | baseMesh delta (Z p) = r ∧ (∃ i, p ∈ E i) ∧ condition p} :=
        measure_mono_ae hsub
      _ ≤ μ {p | baseMesh delta (Z p) = r ∧ (∃ i, p ∈ E i) ∧ condition p} := hν _
      _ ≤ ENNReal.ofReal T * (ENNReal.ofReal (C * delta ^ 3) * weight) := hstable
      _ = ENNReal.ofReal ((T * C * weight.toReal) * delta ^ 3) := by
        symm
        calc
          _ = ENNReal.ofReal ((T * (C * delta ^ 3)) * weight.toReal) := by
            congr 1
            ring
          _ = ENNReal.ofReal (T * (C * delta ^ 3)) * weight := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ T * (C * delta ^ 3)),
              ENNReal.ofReal_toReal hw]
          _ = _ := by rw [ENNReal.ofReal_mul hT, mul_assoc]
  have htarget := affine_mesh_cell_cap ν Z condition A b hA hd hs
    (by positivity : 0 ≤ T * C * weight.toReal) hresolve hbase q
  calc
    _ = (ENNReal.ofReal m)⁻¹ *
        ν {p | baseMesh sigma (affineBase A b (Z p)) = q ∧ condition p} := by
      rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ (ENNReal.ofReal m)⁻¹ *
        ENNReal.ofReal (27 * (T * C * weight.toReal) * |A.det|⁻¹ * sigma ^ 3) :=
      mul_le_mul' le_rfl htarget
    _ = ENNReal.ofReal (27 * T * C * |A.det|⁻¹ / m * sigma ^ 3) * weight := by
      rw [← ENNReal.ofReal_inv_of_pos hm,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)]
      have heq : m⁻¹ * (27 * (T * C * weight.toReal) * |A.det|⁻¹ * sigma ^ 3) =
          (27 * T * C * |A.det|⁻¹ / m * sigma ^ 3) * weight.toReal := by
        simp only [div_eq_mul_inv]
        ring
      rw [heq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hw]

end

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
