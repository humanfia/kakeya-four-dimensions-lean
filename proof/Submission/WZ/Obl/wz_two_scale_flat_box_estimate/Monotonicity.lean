-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Monotonicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Elementary

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric

lemma error_le {δ η η' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') :
    δ ^ (-η) ≤ δ ^ (-η') :=
  Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)

lemma admissible_mono_error {δ η η' : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    (h : Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y) :
    Admissible δ η' (δ ^ (-η')) (δ ^ (-η')) n x v Y := by
  have h' := admissible_mono_density hδ hδ1 hη h
  have he := error_le hδ hδ1 hη
  refine ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, ?_, ?_⟩
  · exact WangZahlLot.Obl.wz_tower_balanced_refinement.convexCount_mono h'.2.2.2.2.1 he
  · intro u t r hu hr
    apply (h'.2.2.2.2.2 u t r hu hr).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg n)

lemma belowSlab_mono {δ ρ l l' : ℝ} {n N : ℕ} {x v : Fin n → Space}
    {S : Finset (Fin n)} {y w : Fin N → Space} {f : Fin n → Fin N}
    (h : BelowSlab δ ρ l n N x v S y w f) (hl : l ≤ l') :
    BelowSlab δ ρ l' n N x v S y w f := by
  intro k
  dsimp only
  intro u t r hu hr
  apply (h k u t r hu hr).trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _)

lemma cover_mono_error {δ η η' ρ : ℝ} {n N : ℕ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space} {S : Finset (Fin n)} {y w : Fin N → Space}
    {f : Fin n → Fin N} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    (h : Cover δ η n x v Y S Z ρ N y w f) : Cover δ η' n x v Y S Z ρ N y w f := by
  obtain ⟨hZ, hmass, hw, hT, hF, hB, hbal, hX, hdeg⟩ := h
  have he := error_le hδ hδ1 hη
  refine ⟨hZ, ?_, hw, hT, ?_, belowSlab_mono hB he, ?_, hX, ?_⟩
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη)) le_rfl).trans hmass
  · intro u t r hu hr
    apply (hF u t r hu hr).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)
  · intro k k'
    exact (hbal k k').trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))
  · intro i hi
    exact (hdeg i hi).trans he

lemma boxCover_mono_error {δ η η' ρ a b c : ℝ} {N L : ℕ} {y w : Fin N → Space}
    {z : Fin L → Space} {e : Fin L → Space ≃ₗᵢ[ℝ] Space} {g : Fin N → Fin L}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    (h : BoxCover δ η ρ a b c N L y w z e g) : BoxCover δ η' ρ a b c N L y w z e g := by
  obtain ⟨hT, hbal, hdeg, hKT, hrel⟩ := h
  have he := error_le hδ hδ1 hη
  refine ⟨hT, ?_, ?_, ?_, ?_⟩
  · intro j j'
    exact (hbal j j').trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))
  · intro k
    exact (hdeg k).trans he
  · intro W hW
    exact (hKT W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal he) le_rfl)
  · intro j W hW
    exact (hrel j W hW).trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) le_rfl)

lemma bound_mono {σ ω ε κ κ' δ a b n : ℝ} (hκ : κ ≤ κ') (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 ≤ n) :
    bound σ ω ε κ δ a b n ≤ bound σ ω ε κ' δ a b n := by
  unfold bound
  gcongr

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
