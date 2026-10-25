-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.AssignedRichness.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.AssignedCover

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor

open Finset LeanEval.Analysis.WangZahlKakeya

/-- Summing richness over the balanced box assignment counts each retained
coarse tube exactly once. -/
theorem AssignedCover.rich_total {N L : ℕ} {R ρ K m a b : ℝ}
    {y w : Fin N → Space} {U : Finset (Fin N)} {z : Fin L → Space}
    {e : Fin L → Space ≃ₗᵢ[ℝ] Space} {g : Fin N → Fin L}
    (h : AssignedCover R ρ K y w U m a b L z e g) :
    m * (a * b * (2 * R)) * L ≤ K * U.card * ρ ^ 2 := by
  classical
  have hsum : (∑ j : Fin L, ((U.filter fun k => g k = j).card : ℝ)) = U.card := by
    exact_mod_cast (U.card_eq_sum_card_fiberwise (t := univ) (f := g)
      (fun _ _ => mem_univ _)).symm
  have hh := Finset.sum_le_sum (s := (univ : Finset (Fin L))) (fun j _ => h.rich j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul, hsum, mul_assoc, mul_left_comm, mul_comm] using hh

/-- The large coefficient and the almost-round transverse shape give the
rich-cover relation (9.6), including the exact power loss. -/
theorem AssignedCover.rich_scale_count {N L : ℕ} {R δ ρ m a b ν t ζ : ℝ}
    {y w : Fin N → Space} {U : Finset (Fin N)} {z : Fin L → Space}
    {e : Fin L → Space ≃ₗᵢ[ℝ] Space} {g : Fin N → Fin L}
    (h : AssignedCover R ρ (δ ^ (-ν)) y w U m a b L z e g)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hR : 1 ≤ 2 * R)
    (hm : δ ^ (-ζ) ≤ m) (hshape : δ ^ t * b ≤ a) :
    δ ^ (t + ν - ζ) * (b / ρ) ^ 2 * L ≤ U.card := by
  have ha : 0 < a := hρ.trans_le h.width
  have hb : 0 < b := ha.trans_le h.ordered
  have harea : δ ^ t * b * b ≤ a * b * (2 * R) := by
    calc
      _ ≤ a * b := mul_le_mul_of_nonneg_right hshape hb.le
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg ha.le hb.le) hR
  have hlower : δ ^ (-ζ) * (δ ^ t * b * b) * L ≤ m * (a * b * (2 * R)) * L := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hm harea (by positivity) h.coefficient_pos.le) (Nat.cast_nonneg _)
  have hp := mul_le_mul_of_nonneg_left (hlower.trans h.rich_total)
    (by positivity : 0 ≤ δ ^ ν / ρ ^ 2)
  have hexp : δ ^ (t + ν - ζ) = δ ^ ν * (δ ^ (-ζ) * δ ^ t) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    ring
  have hcancel : δ ^ ν * δ ^ (-ν) = 1 := by rw [← Real.rpow_add hδ]; simp
  calc
    _ = (δ ^ ν / ρ ^ 2) * (δ ^ (-ζ) * (δ ^ t * b * b) * L) := by
      rw [hexp]
      field_simp
    _ ≤ (δ ^ ν / ρ ^ 2) * (δ ^ (-ν) * U.card * ρ ^ 2) := hp
    _ = U.card := by
      calc
        _ = (δ ^ ν * δ ^ (-ν)) * U.card := by field_simp
        _ = _ := by rw [hcancel, one_mul]

/-- The same richness estimate with the original coarse count, which is the
normalization used by the fine-fiber balance bound. -/
theorem AssignedCover.rich_scale_count_original {N L : ℕ} {R δ ρ m a b ν t ζ : ℝ}
    {y w : Fin N → Space} {U : Finset (Fin N)} {z : Fin L → Space}
    {e : Fin L → Space ≃ₗᵢ[ℝ] Space} {g : Fin N → Fin L}
    (h : AssignedCover R ρ (δ ^ (-ν)) y w U m a b L z e g)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hR : 1 ≤ 2 * R)
    (hm : δ ^ (-ζ) ≤ m) (hshape : δ ^ t * b ≤ a) :
    δ ^ ((t + ν) - ζ) * (b / ρ) ^ 2 * L ≤ N :=
  (h.rich_scale_count hδ hρ hR hm hshape).trans
    (Nat.cast_le.mpr (by simpa using U.card_le_univ))

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor
