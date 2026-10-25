-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.ScaleProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RadiusTransfer
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Quantization

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

/-- Transport a projection gain through an affine change of scalar output,
including the loss needed to restore the minimum admissible radius. The two
numerical hypotheses expose exactly the reserve needed in the parameters. -/
theorem ProjectionGain.of_affine_rescaling {δ d η θ ε k u M : ℝ} {Q Q' : Set Triple}
    (h : ProjectionGain d θ (ε / 2) Q)
    (hδ : 0 < δ) (hd : 0 < d) (hk : 0 < k) (hM : 1 ≤ M)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hscale : δ ≤ M * k * d)
    (hlength : M * δ ^ (-η) ≤ d ^ (-θ))
    (hreserve : 3 * M ≤ (d ^ (-θ)) ^ (ε / 2))
    (hmap : ∀ p ∈ Q, ∃ q ∈ Q', dotValue q = k * dotValue p + u) :
    ProjectionGain δ η ε Q' := by
  obtain ⟨ρ, a, L, hdρ, hL, hcover⟩ := h
  have hρ : 0 < ρ := hd.trans_le hdρ
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hLpos : 0 < L := (mul_pos (Real.rpow_pos_of_pos hd _) hρ).trans_le hL
  have hratio : d ^ (-θ) ≤ L / ρ := (le_div_iff₀ hρ).mpr hL
  have hRpos : 0 < L / ρ := div_pos hLpos hρ
  let ρ₁ := max δ (k * ρ)
  have hρ₁ : 0 < ρ₁ := hδ.trans_le (le_max_left _ _)
  have hρle : k * ρ ≤ ρ₁ := le_max_right _ _
  have hρupper : ρ₁ ≤ M * (k * ρ) := by
    apply max_le
    · calc δ ≤ M * k * d := hscale
        _ ≤ M * k * ρ := mul_le_mul_of_nonneg_left hdρ (by positivity)
        _ = _ := by ring
    · nlinarith [mul_pos hk hρ]
  have hKpos : 0 < ρ₁ / (k * ρ) := div_pos hρ₁ (mul_pos hk hρ)
  have hKle : ρ₁ / (k * ρ) ≤ M := (div_le_iff₀ (mul_pos hk hρ)).mpr hρupper
  have hlarge : 3 * M ≤ (L / ρ) ^ (ε / 2) :=
    hreserve.trans (Real.rpow_le_rpow (by positivity) hratio (by positivity))
  have hprod : 3 * (ρ₁ / (k * ρ)) * (L / ρ) ^ (1 - ε) ≤
      (L / ρ) ^ (1 - ε / 2) := by
    calc 3 * (ρ₁ / (k * ρ)) * (L / ρ) ^ (1 - ε) ≤
          (3 * M) * (L / ρ) ^ (1 - ε) := by gcongr
      _ ≤ (L / ρ) ^ (ε / 2) * (L / ρ) ^ (1 - ε) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hRpos.le _)
      _ = (L / ρ) ^ (1 - ε / 2) := by rw [← Real.rpow_add hRpos]; congr 1; ring
  have hratio' : (k * L) / ρ₁ ≤ L / ρ := by
    apply (div_le_div_iff₀ hρ₁ hρ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hρle hLpos.le]
  have hpower : ((k * L) / ρ₁) ^ (1 - ε) ≤
      (L / ρ) ^ (1 - ε / 2) / (3 * (ρ₁ / (k * ρ))) := by
    calc ((k * L) / ρ₁) ^ (1 - ε) ≤ (L / ρ) ^ (1 - ε) :=
        Real.rpow_le_rpow (by positivity) hratio' (sub_nonneg.mpr hε1)
      _ ≤ (L / ρ) ^ (1 - ε / 2) / (3 * (ρ₁ / (k * ρ))) :=
        (le_div_iff₀ (by positivity)).mpr (by nlinarith [hprod])
  have himage : (fun t : ℝ => k * t + u) '' (Set.Icc a (a + L) ∩ DotSet Q) ⊆
      Set.Icc (k * a + u) ((k * a + u) + k * L) ∩ DotSet Q' := by
    rintro t ⟨s, ⟨hs, p, hp, rfl⟩, rfl⟩
    obtain ⟨q, hq, heq⟩ := hmap p hp
    have hs' : a ≤ dotValue p ∧ dotValue p ≤ a + L := hs
    refine ⟨⟨?_, ?_⟩, q, hq, heq.symm⟩
    · change k * a + u ≤ k * dotValue p + u
      nlinarith [hs'.1]
    · change k * dotValue p + u ≤ (k * a + u) + k * L
      nlinarith [hs'.2]
  have hcov := (hcover.affine_image hk).mono_set himage
  have hcoarse := hcov.coarsen (mul_pos hk hρ) hρle
  refine ⟨ρ₁, k * a + u, k * L, le_max_left _ _, ?_, hcoarse.weaken hpower⟩
  calc δ ^ (-η) * ρ₁ ≤ δ ^ (-η) * (M * (k * ρ)) := by gcongr
    _ = k * (M * δ ^ (-η) * ρ) := by ring
    _ ≤ k * (d ^ (-θ) * ρ) := by gcongr
    _ ≤ k * L := mul_le_mul_of_nonneg_left hL hk.le

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
