-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Factoring.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Pruning
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Enumeration

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

lemma cancel_scaled_measure {A H t c : ℝ} {μ : ENNReal}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hc : 0 < c) (hscale : c * A ≤ H * t)
    (ht : ENNReal.ofReal t ≤ ENNReal.ofReal c * μ) :
    ENNReal.ofReal A ≤ ENNReal.ofReal H * μ := by
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal A * ENNReal.ofReal c = ENNReal.ofReal (c * A) := by
      rw [← ENNReal.ofReal_mul hA, mul_comm]
    _ ≤ ENNReal.ofReal (H * t) := ENNReal.ofReal_le_ofReal hscale
    _ = ENNReal.ofReal H * ENNReal.ofReal t := ENNReal.ofReal_mul hH
    _ ≤ ENNReal.ofReal H * (ENNReal.ofReal c * μ) := mul_le_mul' le_rfl ht
    _ = (ENNReal.ofReal H * μ) * ENNReal.ofReal c := by ring

lemma Upper.rescale {ι : Type*} [DecidableEq ι] {T : ι → Set Space}
    {S : Finset ι} {w a c C : ℝ} (h : Upper T w S c)
    (hw : 0 < w) (ha : 0 ≤ a) (hc : 0 ≤ c) (hC : 0 ≤ C) (hscale : c * a ≤ C * w) :
    Upper T a S C := by
  intro U hU
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hw).ne' ENNReal.ofReal_ne_top).mp
  have hs : ENNReal.ofReal a * ENNReal.ofReal c ≤ ENNReal.ofReal C * ENNReal.ofReal w := by
    rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hC, mul_comm a c]
    exact ENNReal.ofReal_le_ofReal hscale
  calc
    ENNReal.ofReal ((count T S U : ℝ) * a) * ENNReal.ofReal w =
        ENNReal.ofReal a * ENNReal.ofReal ((count T S U : ℝ) * w) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ha]
      congr 1
      ring
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal c * volume U) := mul_le_mul' le_rfl (h U hU)
    _ = (ENNReal.ofReal a * ENNReal.ofReal c) * volume U := by ring
    _ ≤ (ENNReal.ofReal C * ENNReal.ofReal w) * volume U := mul_le_mul' hs le_rfl
    _ = (ENNReal.ofReal C * volume U) * ENNReal.ofReal w := by ring

/-- Saturation and bounded incidence imply both factoring estimates. -/
theorem factor_bounds {ι : Type*} [DecidableEq ι] {T : ι → Set Space}
    {S : Finset ι} {n : ℕ} (W : Fin n → Set Space) {w a b c B : ℝ}
    (hw : 0 < w) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hB : 0 ≤ B)
    (hu : Upper T w S c)
    (hW : ∀ j, Convex ℝ (W j) ∧ volume (W j) = ENNReal.ofReal (16 * a * b))
    (hdeg : ∀ i ∈ S, (ncard {j | T i ⊆ W j} : ℝ) ≤ 64 * B)
    (hsat : ∀ j, c * a * b ≤ 2 * B * (count T S (W j) : ℝ) * w) :
    (∀ j j', (count T S (W j) : ℝ) ≤ 32 * B * (count T S (W j') : ℝ)) ∧
    Upper W (a * b) Finset.univ (128 * B ^ 2) ∧
    (∀ j, Upper T (a * b) (S.filter fun i => T i ⊆ W j) (2 * B * count T S (W j))) := by
  classical
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hcount (j) : (count T S (W j) : ℝ) * w ≤ 16 * c * a * b := by
    have h := hu.real hc.le (hW j).1 (by rw [(hW j).2]; exact ENNReal.ofReal_ne_top)
    rw [(hW j).2, ENNReal.toReal_ofReal (by positivity)] at h
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro j j'
    apply (mul_le_mul_iff_left₀ hw).mp
    nlinarith [hcount j, hsat j']
  · intro U hU
    let J := Finset.univ.filter fun j => W j ⊆ U
    let R := S.filter fun i => T i ⊆ U
    have hsum : (∑ j ∈ J, (count T S (W j) : ℝ)) ≤ 64 * B * count T S U := by
      have he (j) (hj : j ∈ J) : (R.filter fun i => T i ⊆ W j).card = count T S (W j) := by
        unfold count
        congr 1
        ext i
        simp only [R, Finset.mem_filter]
        have hWU : W j ⊆ U := (Finset.mem_filter.mp hj).2
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · exact fun h => ⟨⟨h.1, h.2.trans hWU⟩, h.2⟩
      calc
        (∑ j ∈ J, (count T S (W j) : ℝ)) =
            ∑ j ∈ J, ((R.filter fun i => T i ⊆ W j).card : ℝ) :=
          Finset.sum_congr rfl fun j hj => by rw [he j hj]
        _ = ∑ i ∈ R, ((J.filter fun j => T i ⊆ W j).card : ℝ) := by
          exact_mod_cast (incidence_sum R J (fun i j => T i ⊆ W j)).symm
        _ ≤ ∑ _i ∈ R, 64 * B := by
          apply Finset.sum_le_sum
          intro i hi
          have hj : (J.filter fun j => T i ⊆ W j) ⊆ Finset.univ.filter (fun j => T i ⊆ W j) :=
            Finset.filter_subset_filter _ (Finset.subset_univ _)
          have hh := hdeg i (Finset.mem_filter.mp hi).1
          rw [ncard_fintype] at hh
          exact (Nat.cast_le.mpr (Finset.card_le_card hj)).trans hh
        _ = 64 * B * count T S U := by simp [R, count, mul_comm]
    have hscale : c * ((J.card : ℝ) * (a * b)) ≤ 128 * B ^ 2 * ((count T S U : ℝ) * w) := by
      calc
        c * ((J.card : ℝ) * (a * b)) = ∑ _j ∈ J, c * a * b := by simp; ring
        _ ≤ ∑ j ∈ J, 2 * B * (count T S (W j) : ℝ) * w :=
          Finset.sum_le_sum fun j _ => hsat j
        _ = 2 * B * (∑ j ∈ J, (count T S (W j) : ℝ)) * w := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ 2 * B * (64 * B * count T S U) * w := by
          gcongr
        _ = 128 * B ^ 2 * ((count T S U : ℝ) * w) := by ring
    exact cancel_scaled_measure (by positivity) (by positivity) hc hscale (hu U hU)
  · intro j
    apply (hu.subset hw.le (Finset.filter_subset _ _)).rescale hw hab hc.le (by positivity)
    nlinarith [hsat j]

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
