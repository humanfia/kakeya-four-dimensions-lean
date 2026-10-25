-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.CoverComposition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.PacketComposition
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatCoarseEstimate
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Packets

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (packetSize packetIndex packetSize_eq packetIndex_injective packetIndex_contained packetIndex_count
    balanced_cover_minimum bounded_incidence_count gridCell gridUnion gridUnion_product gridCell_volume
    gridUnion_measurable gridCell_volume_ne_top)

def CoarseEstimateAt (σ u ε A η δ a b D l : ℝ) : Prop :=
  ∀ (q : ℕ) (e : Fin q → AffineIsometryEquiv ℝ Space Space) (Z : Fin q → Set Space),
    0 < q → (q : ℝ) ≤ δ ^ (-100 : ℝ) →
    (∀ j, (e j '' StandardPrism a b ∩ ball (0 : Space) 1).Nonempty) →
    (∀ j, MeasurableSet (Z j)) → (∀ j, Z j ⊆ e j '' dilatedPrism 3 a b) →
    (∀ j, ENNReal.ofReal (δ ^ η * (a * b)) ≤ volume (Z j)) →
    BodyConvexCount (fun j => e j '' StandardPrism a b) (a * b) D →
    BodySlabCount (fun j => coarsePrism (e j) a b) (256 * D ^ 2 * l) →
    ENNReal.ofReal (A * δ ^ ε * b ^ u * D ^ (-2 : ℝ) * l ^ (-σ) *
      (q : ℝ) ^ (1 - σ) * (a * b) ^ (1 - σ / 2)) ≤ volume (⋃ j, Z j)

theorem body_raw_count {n : ℕ} {U : Fin n → Set Space} {w m : ℝ}
    (hw : 0 < w) (hc : BodyConvexCount U w m) (Q : Set Space) (hQ : Convex ℝ Q) :
    ENNReal.ofReal (Set.ncard {i | U i ⊆ Q} : ℝ) ≤ ENNReal.ofReal (m / w) * volume Q := by
  calc
    _ = ENNReal.ofReal w⁻¹ * ENNReal.ofReal ((Set.ncard {i | U i ⊆ Q} : ℝ) * w) := by
      rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
    _ ≤ ENNReal.ofReal w⁻¹ * (ENNReal.ofReal m * volume Q) := mul_le_mul' le_rfl (hc Q hQ)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

set_option maxHeartbeats 1200000 in
/-- Assemble the fine cube densities and the coarse body estimate over a balanced cover. -/
theorem finite_flat_cover_product {σ u εf εc Af Ac ηf ηc δ ν s a b c l : ℝ}
    (hσ : 0 ≤ σ) (hAf : 0 < Af) (hAc : 0 < Ac) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδa : δ ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2) (haSmall : a ≤ 1 / 100)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hs : 0 < s) (hνs : ν ≤ s)
    (hηf : 2 * s ≤ ηf) (hηc : 8 * s ≤ ηc) (hc : 1 ≤ c) (hl : 1 ≤ l)
    (Hfine : ∀ e, FineEstimateAt σ u εf Af ηf δ a b (δ ^ (-3 * s)) e)
    (Hcoarse : CoarseEstimateAt σ u εc Ac ηc δ a b (δ ^ (-ν)) l)
    {K : ℕ} (hK : 0 < K) (hretBudget : 224 * K * δ ^ s ≤ 1)
    (hcut : 432 * (δ ^ s) ^ K * a * b ≤ δ ^ ν * δ ^ 2 / 2)
    (Kc : ℕ) (hKc : (1 / 2 : ℝ) ^ Kc ≤ δ)
    (hlog : (10 : ℝ) ^ (15 : ℕ) * ((Kc : ℝ) + 1) * δ ^ s ≤ 1)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hnmax : (n : ℝ) ≤ δ ^ (-10 : ℝ))
    (hAdm : Admissible δ ν c l n x v Y) (hY : IndividuallyDense ν δ Y)
    (hCover : PrismCover ν δ a b c n x v) :
    ∃ (q N : ℕ), 0 < q ∧ 0 < N ∧ (n : ℝ) ≤ q * δ ^ (-ν) * N ∧
      (N : ℝ) * δ ^ 2 ≤ 16 * c * a * b ∧
      ENNReal.ofReal (flatCellDensity σ u εf Af δ a b s N *
        (Ac * δ ^ εc * b ^ u * (δ ^ (-ν)) ^ (-2 : ℝ) * l ^ (-σ) *
          (q : ℝ) ^ (1 - σ) * (a * b) ^ (1 - σ / 2))) ≤ volume (⋃ i, Y i) := by
  classical
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hc' : 0 < c := zero_lt_one.trans_le hc
  have hl' : 0 < l := zero_lt_one.trans_le hl
  have hD : 0 < δ ^ (-ν) := Real.rpow_pos_of_pos hδ _
  obtain ⟨hn, hfamily, hsep, hmass, hconv, hslab⟩ := hAdm
  have hv := fun i => (hfamily i).1
  have hball := fun i => (hfamily i).2.1
  have hYm := fun i => (hfamily i).2.2.1
  have hYT := fun i => (hfamily i).2.2.2
  obtain ⟨q, hq, W, hW, hcover, hdegree, hbalance, hsat, hKT, hrel⟩ := hCover
  choose e he using hW
  simp only [he] at hcover hdegree hbalance hsat hKT hrel
  let R := fun i j => Tube δ (x i) (v i) ⊆ e j '' StandardPrism a b
  have hpos : ∀ j, 0 < Set.ncard {i | R i j} := by
    intro j
    have hh := hsat j
    have hp : 0 < δ ^ ν * c * a * b := by positivity
    have hh' : (0 : ℝ) < Set.ncard {i | R i j} := by
      change δ ^ ν * c * a * b ≤ (Set.ncard {i | R i j} : ℝ) * δ ^ 2 at hh
      nlinarith [sq_nonneg δ]
    exact_mod_cast hh'
  obtain ⟨N, hN, hNmin, hNmax, hsize⟩ := balanced_cover_minimum hq R hD.le hcover hpos hbalance
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqn : (q : ℝ) ≤ δ ^ (-ν) * n := by
    have hh := bounded_incidence_count R (fun _ => True) (fun _ => True) hD.le
      (N := 1) (fun j _ => by exact_mod_cast hpos j) hdegree (by intros; trivial)
    simpa using hh
  have hqmax : (q : ℝ) ≤ δ ^ (-100 : ℝ) := by
    have hDupper : δ ^ (-ν) ≤ δ ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc
      _ ≤ δ ^ (-ν) * n := hqn
      _ ≤ δ ^ (-1 : ℝ) * δ ^ (-10 : ℝ) := mul_le_mul hDupper hnmax (Nat.cast_nonneg n)
        (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-11 : ℝ) := by rw [← Real.rpow_add hδ]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  let g := fun j => packetIndex δ x v (e j '' StandardPrism a b)
  have hg := fun j => packetIndex_injective δ x v (e j '' StandardPrism a b)
  have hNjpos (j : Fin q) : 0 < packetSize δ x v (e j '' StandardPrism a b) := by
    rw [packetSize_eq]
    exact hpos j
  have hNvol : (N : ℝ) * δ ^ 2 ≤ 16 * c * a * b := by
    let j : Fin q := ⟨0, hq⟩
    have hh := WangZahlLot.Obl.wz_nonflat_factored_improvement.prism_occupancy_upper
      ha.le hb.le hc'.le (W := e j '' StandardPrism a b) ⟨e j, rfl⟩ hconv
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hNmin j)) (sq_nonneg δ)).trans hh
  have hmeet (j : Fin q) : (e j '' StandardPrism a b ∩ ball (0 : Space) 1).Nonempty :=
    WangZahlLot.Obl.wz_nonflat_factored_improvement.packet_meets_ball hδ x v hball _ (hNjpos j)
  have hpacket (j : Fin q) : ∃ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, (e j '' StandardPrism a b ∩ gridCell a z).Nonempty) ∧
      ENNReal.ofReal (δ ^ ηc * (a * b)) ≤ volume (gridUnion a S) ∧
      ∀ z ∈ S, flatCellDensity σ u εf Af δ a b s N * a ^ 3 ≤
        volume.real ((⋃ i, Y (g j i)) ∩ gridCell a z) := by
    have hNj : (packetSize δ x v (e j '' StandardPrism a b) : ℝ) ≤ n := by
      exact_mod_cast (show packetSize δ x v (e j '' StandardPrism a b) ≤ n by
        simpa using Fintype.card_le_of_injective (g j) (hg j))
    have hNpacket : (N : ℝ) ≤ packetSize δ x v (e j '' StandardPrism a b) := by
      rw [packetSize_eq]
      exact_mod_cast hNmin j
    have hraw : ∀ Q : Set Space, Convex ℝ Q →
        ENNReal.ofReal (Set.ncard {i | Tube δ (x (g j i)) (v (g j i)) ⊆ Q} : ℝ) ≤
          ENNReal.ofReal (δ ^ (-ν) * (packetSize δ x v (e j '' StandardPrism a b)) / (a * b)) * volume Q := by
      have hcP : BodyConvexCount (fun i => Tube δ (x (g j i)) (v (g j i)))
          (a * b) (δ ^ (-ν) * (packetSize δ x v (e j '' StandardPrism a b))) := by
        intro Q hQ
        dsimp [g]
        rw [packetIndex_count, packetSize_eq]
        simpa only [mul_assoc] using hrel j Q hQ
      exact body_raw_count (mul_pos ha hb) hcP
    obtain ⟨S, _, hmeet, hcoarse, hlocal⟩ := regularized_flat_packet hσ hAf hδ hδ1 hδa hab hb2 haSmall
      hs hνs hηf hηc hN' (e j) (Hfine (e j)) hK hretBudget hcut Kc hKc hlog
      (hNjpos j) hNpacket (hNj.trans (hnmax.trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num))))
      (x ∘ g j) (v ∘ g j) (Y ∘ g j) (fun i => hv (g j i)) (fun i => hball (g j i))
      (packetIndex_contained δ x v _) (fun i k hik => hsep _ _ ((hg j).ne hik))
      (fun i => hYm (g j i)) (fun i => hYT (g j i)) (fun i => hY (g j i)) hraw
    exact ⟨S, hmeet, hcoarse, hlocal⟩
  choose S hSmeet hSd hSlocal using hpacket
  let Z := fun j => gridUnion a (S j)
  have hCconv : BodyConvexCount (fun j => e j '' StandardPrism a b) (a * b) (δ ^ (-ν)) := by
    intro Q hQ
    simpa only [mul_assoc] using hKT Q hQ
  have hCslab : BodySlabCount (fun j => coarsePrism (e j) a b) (256 * (δ ^ (-ν)) ^ 2 * l) :=
    coarse_body_slabs hl'.le hN' hD.le x v _ R hball hslab
      (fun j => Nat.cast_le.mpr (hNmin j)) hdegree hsize (by
        intro i j hij
        exact image_mono (hij.trans (image_mono (standardPrism_subset_dilated ha.le hb.le (by norm_num)))))
  have hCoarse := Hcoarse q e Z hq hqmax hmeet (fun j => gridUnion_measurable a (S j))
    (fun j => gridUnion_flat_subset ha hab hb2 (e j) (S j) (hSmeet j)) hSd hCconv hCslab
  let Sall := Finset.univ.biUnion S
  have hUeq : (⋃ j, Z j) = gridUnion a Sall := by
    ext p
    simp [Z, gridUnion, Sall]
    aesop
  have hglobal : ENNReal.ofReal (flatCellDensity σ u εf Af δ a b s N) * volume (gridUnion a Sall) ≤
      volume (⋃ i, Y i) := by
    apply gridUnion_product ha Sall _ (MeasurableSet.iUnion hYm)
    intro z hz
    obtain ⟨j, _, hzj⟩ := Finset.mem_biUnion.mp hz
    rw [gridCell_volume ha.le, ← ENNReal.ofReal_mul
      (flatCellDensity_pos hAf hδ ha hb hN').le]
    apply (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top (gridCell_volume_ne_top ha z) (measure_mono inter_subset_right))).mpr
    exact (hSlocal j z hzj).trans (measureReal_mono
      (inter_subset_inter_left _ (iUnion_subset (fun i => subset_iUnion Y (g j i))))
      (ne_top_of_le_ne_top (gridCell_volume_ne_top ha z) (measure_mono inter_subset_right)))
  refine ⟨q, N, hq, hN, hsize, hNvol, ?_⟩
  rw [ENNReal.ofReal_mul (flatCellDensity_pos hAf hδ ha hb hN').le]
  rw [hUeq] at hCoarse
  exact (mul_le_mul' le_rfl hCoarse).trans hglobal

end WangZahlLot.Obl.wz_flat_factored_improvement
