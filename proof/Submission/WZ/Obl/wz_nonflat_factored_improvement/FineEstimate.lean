-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.FineEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.AffineCounts

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

noncomputable abbrev fineRetainedFraction : ℝ :=
  WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst / fineFiberBound

theorem fineRetainedFraction_pos : 0 < fineRetainedFraction := by
  exact div_pos WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst_pos (by norm_num)

/-- Apply `E` to the separated affine image of a prism family. The remaining expression
keeps the exact rescaling factors, so that it can be combined with the coarse estimate. -/
theorem fine_estimate {σ u : ℝ} (hE : EstimateE σ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ a b δ lam m L : ℝ, 0 < δ → δ ≤ a → a ≤ b → b ≤ 1 →
      1 ≤ m → 1 ≤ L → 0 ≤ lam →
      (fineRadius δ b) ^ η ≤ fineContraction * lam / 16 →
      ∀ (e : AffineIsometryEquiv ℝ Space Space) (n : ℕ) (x v : Fin n → Space)
        (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ e '' standardPrism a b) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → ConvexCount δ m x v →
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * (a * b)) ≤
          ENNReal.ofReal (L * n) * volume U) →
      ENNReal.ofReal (A * (fineRadius δ b) ^ (u + ε) * (16 * m / fineContraction)⁻¹ *
        ((n : ℝ) * (fineRadius δ b) ^ 2) *
        ((16 * m / fineContraction) ^ (-(3 / 2 : ℝ)) *
          (L * n / (a * b * (fineContraction ^ 3 * b⁻¹ ^ 2))) * fineRadius δ b) ^ (-σ)) ≤
      ENNReal.ofReal (fineContraction ^ 3 * b⁻¹ ^ 2) * volume (⋃ i, Y i) := by
  obtain ⟨A, hA, η, hη, H⟩ := hE ε hε
  refine ⟨A * fineRetainedFraction, η, mul_pos hA fineRetainedFraction_pos, hη, ?_⟩
  intro a b δ lam m L hδ hδa hab hb1 hm hL hlam hden e n x v Y hn hv hT hover hYm hYT hind hconv hrel
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hκ : 0 < fineContraction := by norm_num
  let r := fineRadius δ b
  let J := fineContraction ^ 3 * b⁻¹ ^ 2
  let m' := 16 * m / fineContraction
  have hr : 0 < r := by dsimp [r, fineRadius]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hr100 : r ≤ 1 / 100 := by
    have h := mul_le_mul_of_nonneg_left (hδa.trans hab)
      (by positivity : 0 ≤ 4 * fineContraction * b⁻¹)
    have he : 4 * fineContraction * b⁻¹ * b = 4 * fineContraction := by field_simp
    rw [he] at h
    dsimp [r, fineRadius, fineContraction] at *
    linarith
  have hm' : 1 ≤ m' := by dsimp [m', fineContraction]; linarith
  obtain ⟨M, j, z, w, hM, hj, hw, hB, hsep, hcover, hmass⟩ :=
    fine_prism_net hb hb1 hab hδ (hδa.trans hab) e hn x v hv hT hover
  let f := fineAffine e b hb
  let Z : Fin M → Set Space := fun i => f '' Y (j i)
  have hMc : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMn : (M : ℝ) ≤ n := by
    have hh : M ≤ n := by simpa using Fintype.card_le_of_injective j hj
    exact_mod_cast hh
  have habJ : a * b * J ≤ 1 := by
    have he : a * b * J = fineContraction ^ 3 * (a / b) := by dsimp [J]; field_simp
    rw [he]
    have hab' : a / b ≤ 1 := (div_le_one hb).mpr hab
    calc
      _ ≤ fineContraction ^ 3 * 1 := mul_le_mul_of_nonneg_left hab' (by positivity)
      _ ≤ 1 := by norm_num
  let l := (L * n / (a * b * J)) / M
  have hl : 1 ≤ l := by
    apply (le_div_iff₀ hMc).mpr
    apply (le_div_iff₀ (by positivity : 0 < a * b * J)).mpr
    have h1 := mul_le_mul_of_nonneg_left habJ hMc.le
    have h2 := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg n)
    nlinarith only [h1, h2, hMn]
  have hZmeas : ∀ i, MeasurableSet (Z i) := fun i =>
    f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm (j i))
  have hZsub : ∀ i, Z i ⊆ tube r (z i) (w i) := fun i =>
    (Set.image_mono (hYT (j i))).trans (hcover i)
  have hZden : ∀ i, ENNReal.ofReal (r ^ η * r ^ 2) ≤ volume (Z i) := by
    intro i
    rw [show volume (Z i) = ENNReal.ofReal J * volume (Y (j i)) from fineAffine_volume e hb _]
    calc
      _ ≤ ENNReal.ofReal ((fineContraction * lam / 16) * r ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hden (sq_nonneg r)
      _ = ENNReal.ofReal J * ENNReal.ofReal (lam * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul hJ.le]
        congr 1
        dsimp [J, r, fineRadius]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (hind (j i))
  have hrawconv := affine_count_transport f hJ (sq_pos_of_pos hδ) hm0.le
    (fineAffine_volume e hb) x v z w j hj hcover hconv
  have hconv' : ConvexCount r m' z w := by
    have hh := convexCount_of_raw_count (by positivity : 0 ≤ m / (δ ^ 2 * J)) z w hrawconv
    have he : m / (δ ^ 2 * J) * r ^ 2 = m' := by
      dsimp [J, r, fineRadius, m']
      field_simp
      ring
    rwa [he] at hh
  have hrawrel := affine_count_transport f hJ (mul_pos ha hb) (by positivity : 0 ≤ L * n)
    (fineAffine_volume e hb) x v z w j hj hcover hrel
  have hslab' : SlabCount r l z w := slabCount_of_raw_count hM z w hrawrel
  have hbound := H r hr hr100 m' l hm' hl M z w Z hM hw hB hsep hZmeas hZsub
    (subfamily_density hr.le (fun i => i) hZden) hconv' hslab'
  have hU : volume (⋃ i, Z i) ≤ ENNReal.ofReal J * volume (⋃ i, Y i) := by
    rw [← fineAffine_volume e hb]
    apply measure_mono
    intro p hp
    obtain ⟨i, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
    exact ⟨q, Set.mem_iUnion.mpr ⟨j i, hq⟩, rfl⟩
  apply le_trans (b := volume (⋃ i, Z i)) _ hU
  apply le_trans (ENNReal.ofReal_le_ofReal _) hbound
  have hlprod : m' ^ (-(3 / 2 : ℝ)) * l * ((M : ℝ) * r) =
      m' ^ (-(3 / 2 : ℝ)) * (L * n / (a * b * J)) * r := by
    dsimp [l]
    field_simp
  dsimp only
  rw [hlprod]
  have hsize : fineRetainedFraction * (n : ℝ) ≤ M := by
    rw [fineRetainedFraction, div_mul_eq_mul_div]
    exact (div_le_iff₀ (by norm_num : 0 < fineFiberBound)).mpr hmass
  change (A * fineRetainedFraction) * r ^ (u + ε) * m'⁻¹ * ((n : ℝ) * r ^ 2) *
    (m' ^ (-(3 / 2 : ℝ)) * (L * n / (a * b * J)) * r) ^ (-σ) ≤ _
  have hpos : 0 ≤ A * r ^ (u + ε) * m'⁻¹ * r ^ 2 *
      (m' ^ (-(3 / 2 : ℝ)) * (L * n / (a * b * J)) * r) ^ (-σ) := by
    have hm'0 : 0 < m' := zero_lt_one.trans_le hm'
    positivity
  nlinarith only [mul_le_mul_of_nonneg_left hsize hpos]

end WangZahlLot.Obl.wz_nonflat_factored_improvement
