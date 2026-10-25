-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_small_slab_reduction.Glue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_balanced_small_slab_reduction.Interface
import Submission.WZ.Obl.wz_unit_segment_convex_slab_cover
import Submission.WZ.Obl.wz_balanced_affine_tube_packets
import Submission.WZ.Obl.wz_affine_packet_counting_transfer

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_balanced_small_slab_reduction

private theorem A_mono {d d' δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hd : d' ≤ d) (hA : A d δ n x v Y) :
    A d' δ n x v Y := by
  refine ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1,
    hA.2.2.2.2.2.1, ?_⟩
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n)) (sq_nonneg δ))).trans
    hA.2.2.2.2.2.2

private theorem L_mono {δ l l' : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hl : l ≤ l') (hL : L δ l n x v) : L δ l' n x v := by
  intro u a r hu hr
  exact (hL u a r hu hr).trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg n))) le_rfl)

private theorem loss_cutoff (C ζ : ℝ) (hC : 1 ≤ C) (hζ : 0 < ζ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ (1/100 : ℝ) ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      C / (δ ^ (ζ / 4)) ^ 2 ≤ δ ^ (-ζ) ∧
      C * δ ^ ζ ≤ (δ ^ (ζ / 4)) ^ 2 := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let d : ℝ := min (1/100) ((C⁻¹) ^ (2 / ζ))
  have hd : 0 < d := lt_min (by norm_num) (Real.rpow_pos_of_pos (inv_pos.mpr hC0) _)
  refine ⟨d, hd, min_le_left _ _, ?_⟩
  intro δ hδ hδd
  have hδpow : δ ^ (ζ / 2) ≤ C⁻¹ := by
    calc
      δ ^ (ζ / 2) ≤ ((C⁻¹) ^ (2 / ζ)) ^ (ζ / 2) :=
        Real.rpow_le_rpow hδ.le (hδd.trans (min_le_right _ _)) (by positivity)
      _ = (C⁻¹) ^ ((2 / ζ) * (ζ / 2)) :=
        (Real.rpow_mul (inv_nonneg.mpr hC0.le) _ _).symm
      _ = C⁻¹ := by
        have he : (2 / ζ) * (ζ / 2) = 1 := by field_simp
        rw [he, Real.rpow_one]
  have hhalf : (δ ^ (ζ / 4)) ^ 2 = δ ^ (ζ / 2) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    norm_num
    ring
  have hfull : δ ^ ζ = ((δ ^ (ζ / 4)) ^ 2) ^ 2 := by
    rw [hhalf, ← Real.rpow_mul_natCast hδ.le]
    congr 1
    norm_num
  have hs : 0 < (δ ^ (ζ / 4)) ^ 2 := sq_pos_of_pos (Real.rpow_pos_of_pos hδ _)
  have hbudget : C * (δ ^ (ζ / 4)) ^ 2 ≤ 1 := by
    rw [hhalf]
    calc
      C * δ ^ (ζ / 2) ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left hδpow hC0.le
      _ = 1 := mul_inv_cancel₀ hC0.ne'
  constructor
  · rw [Real.rpow_neg hδ.le, hfull]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hs)).2
    calc
      (C / (δ ^ (ζ / 4)) ^ 2) * ((δ ^ (ζ / 4)) ^ 2) ^ 2 =
          C * (δ ^ (ζ / 4)) ^ 2 := by field_simp
      _ ≤ 1 := hbudget
  · rw [hfull]
    nlinarith [mul_le_mul_of_nonneg_right hbudget hs.le]



theorem reduction_of_children (hextraction : Extraction) (hcounting : Counting)
    (hslab : SlabCover) : Packing → Reduction := by
  intro hpacking ζ hζ
  obtain ⟨C, hC, hcount⟩ := hcounting hslab hpacking
  obtain ⟨η, hη, d₁, hd₁, hd₁max, hextract⟩ := hextraction (ζ / 4) (by positivity)
  obtain ⟨d₂, hd₂, hd₂max, hloss⟩ := loss_cutoff C ζ hC hζ
  refine ⟨η, hη, min d₁ d₂, lt_min hd₁ hd₂, (min_le_left _ _).trans hd₁max, ?_⟩
  intro δ hδ hδmax m l hm hl n U hP
  have hδd₁ : δ ≤ d₁ := hδmax.trans (min_le_left _ _)
  have hδd₂ : δ ≤ d₂ := hδmax.trans (min_le_right _ _)
  have hδsmall : δ ≤ (1/100 : ℝ) := hδd₁.trans hd₁max
  have hδone : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hh : 0 < δ ^ (ζ / 4) := Real.rpow_pos_of_pos hδ _
  have hhone : δ ^ (ζ / 4) ≤ 1 := Real.rpow_le_one hδ.le hδone (by positivity)
  have hdensity : δ ^ ζ ≤ δ ^ (ζ / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδone (by linarith)
  have hslabloss : (δ ^ (ζ / 4))⁻¹ ≤ δ ^ (-ζ) := by
    rw [Real.rpow_neg hδ.le]
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hδ _) hdensity
  obtain ⟨hloss₂, hloss₃⟩ := hloss δ hδ hδd₂
  rcases hP with ⟨x, v, Y, hA, hK, hL, hU⟩
  obtain ⟨k, N, q, hk, hN, hq, ρ, t, hρlo, hρhi, ht, z, w, Z, hR, hout, hvol⟩ :=
    hextract δ hδ hδd₁ n x v Y hA
  have hρ : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans_le hρlo
  obtain ⟨M, hM, houtK, hG₂, hG₃, hG₄⟩ :=
    hcount δ ρ (δ ^ (ζ / 4)) t hδ hδsmall hρ hρhi hh hhone ht
      n k N q hA.1 hk hN hq x v z w hA.2.1 hA.2.2.1 hA.2.2.2.1
      (fun j => (hout j).1.2.1) (fun j => (hout j).1.2.2.1) hR m l hm hl hK hL
  refine ⟨k, N, hk, hN, ρ, t, M, ?_, hρhi, ht, hM,
    (fun j => MeasureTheory.volume (⋃ a, Z j a)), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_ge hδ hδone (by linarith)).trans hρlo
  · intro j
    exact ⟨z j, w j, Z j, A_mono hdensity (hout j).1, houtK j,
      L_mono hslabloss (hout j).2, rfl⟩
  · rw [hU]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hdensity ht.le)) le_rfl).trans hvol
  · exact hG₂.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hloss₂ (by linarith))
        (by positivity)) (by positivity))
  · have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hbound : C * δ ^ ζ ≤ C * (l * (k : ℝ) * t ^ (1/2 : ℝ)) := by
      calc
        C * δ ^ ζ ≤ (δ ^ (ζ / 4)) ^ 2 := hloss₃
        _ ≤ C * l * (k : ℝ) * t ^ (1/2 : ℝ) := hG₃
        _ = C * (l * (k : ℝ) * t ^ (1/2 : ℝ)) := by ring
    nlinarith
  · exact hG₄.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hloss₂ ht.le) (sq_nonneg ρ))

end WangZahlLot.Obl.wz_balanced_small_slab_reduction
