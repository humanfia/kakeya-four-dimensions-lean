-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.CertifyCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PreparePacket
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PrismRefinement
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabCounting

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

open Classical in
lemma certify_regular_core {n K : ℕ} {C : PhysicalPacket n} {δ d S h t q θ w : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E} (hC : C.Valid δ d x v Y)
    (A : PreparedPacket (K := K) C δ S x v) (I : Finset (Fin n))
    (hIA : I ⊆ A.cell.indices) (Z : Fin n → Set E)
    (hZA : ∀ i ∈ I, Z i ⊆ A.cell.shading i)
    (R : PrismRefinement I A.cell.a A.cell.b θ q K A.cell.center A.cell.axes Z)
    (hret : q * (I.card : ℝ) ≤ ((I.filter fun i => (R.core i).Nonempty).card : ℝ))
    (hI : I.Nonempty) (hh : 0 < h) (ht : 0 < t) (hq : 0 < q) (hw : 0 < w)
    (htq : t * q ≤ 1) (hhq : h ≤ q) (hhθ : h ≤ θ) (hslack : h * 6144 ≤ t * q)
    (S₀ : SlabSpec) (htS : t ≤ S₀.width)
    (hmax : ∀ T : SlabSpec,
      T.weight I (fun i => A.cell.affine ⁻¹' closedTube δ (x i) (v i))
          (fun i => (volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i))).toReal) / T.width ≤
        2 * (∑ i ∈ I, (volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i))).toReal) / S₀.width)
    (hweights : ∀ i ∈ I,
      w ≤ (volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i))).toReal ∧
      (volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i))).toReal ≤ 384 * w)
    (ha : δ ^ (100 : ℕ) ≤ A.cell.a) (hb : δ * h ≤ A.cell.b)
    (hD : δ ^ (100 : ℕ) ≤ A.cell.jacobian ∧ A.cell.jacobian ≤ δ ^ (-100 : ℝ)) :
    let J := I.filter fun i => (R.core i).Nonempty
    let G : AffineCell n K := { A.cell with indices := J, shading := R.core }
    G.Valid δ h x v Y ∧ G.support ⊆ A.cell.affine '' (⋃ i ∈ I, Z i) := by
  classical
  let J := I.filter fun i => (R.core i).Nonempty
  let G : AffineCell n K := { A.cell with indices := J, shading := R.core }
  change G.Valid δ h x v Y ∧ G.support ⊆ A.cell.affine '' (⋃ i ∈ I, Z i)
  have hJI : J ⊆ I := Finset.filter_subset _ _
  have hJA : J ⊆ A.cell.indices := hJI.trans hIA
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    have hIc : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
    have hJc := lt_of_lt_of_le (mul_pos hq hIc) hret
    exact_mod_cast hJc
  have hGbody : ∀ i, G.body i = A.cell.body i := fun _ => rfl
  have hbodyNe (i : Fin n) : (A.cell.body i).Nonempty :=
    ⟨A.cell.center i, center_mem_prism (by dsimp [AffineCell.a]; positivity)
      (by dsimp [AffineCell.b]; positivity) _ _⟩
  have hprebody : ∀ i ∈ J, A.cell.affine ⁻¹' closedTube δ (x i) (v i) ⊆ A.cell.body i := by
    intro i hi p hp
    obtain ⟨q, hq, heq⟩ := A.whole_body i (hJA hi) hp
    exact A.cell.affine.injective heq ▸ hq
  constructor
  · refine ⟨hJ, ha, A.ordered, A.short_small, hb, hD.1, hD.2, A.volume_identity,
      fun i hi => A.body_small i (hJA hi),
      fun i hi => (tube_subset_closedTube _ _ _).trans (A.whole_body i (hJA hi)),
      fun i hi => R.core_measurable i (hJI hi), ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi p hp
      have hpZ := R.core_subset i (hJI hi) hp
      have hpA := hZA i (hJI hi) hpZ
      rw [A.shading_eq i] at hpA
      have hiC := A.indices_subset (hJA hi)
      exact ⟨hprebody i hi (hC.2.2.2.2.2.2.2.1 i hiC hpA),
        hC.2.2.2.2.2.2.1 i hiC hpA⟩
    · intro i hi
      exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal hhq) _).trans
        (R.core_density i (hJI hi) (Finset.mem_filter.mp hi).2)
    · intro i hi p hp r hra hr1
      exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal hhq) _).trans
        (R.core_regular i (hJI hi) p hp r hra hr1)
    · intro p hp
      obtain ⟨i, hi, hpi⟩ := hp
      obtain ⟨k, hk, l, hl, hpk, hpl, hangle⟩ := R.transverse p ⟨i, hJI hi, hpi⟩
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, p, hpk⟩, l, Finset.mem_filter.mpr ⟨hl, p, hpl⟩,
        hpk, hpl, hhθ.trans hangle⟩
    · intro ν s r hν hr
      have hcount := slab_counting_of_good I J
        (fun i => A.cell.affine ⁻¹' closedTube δ (x i) (v i)) A.cell.body S₀ hmax hJI
        ht hq hw (by norm_num : (1 : ℝ) ≤ 384) htq htS hweights hret hprebody
        (fun i _ => hbodyNe i) (fun i hi => A.body_small i (hJA hi)) ν s r hν hr
      have he : {i : Fin n | i ∈ G.indices ∧ G.body i ⊆ ball (0 : E) 1 ∩ slab (innerSL ℝ ν) s r} =
          ↑(J.filter fun i => A.cell.body i ⊆ ball (0 : E) 1 ∩ slab (innerSL ℝ ν) s r) := by
        ext i
        simp only [mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, G, hGbody]
      change ENNReal.ofReal (Set.ncard {i : Fin n | i ∈ G.indices ∧ G.body i ⊆
        ball (0 : E) 1 ∩ slab (innerSL ℝ ν) s r} : ℝ) ≤ _
      rw [he, ncard_coe_finset]
      apply hcount.trans
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [inv_eq_one_div, div_le_div_iff₀ (mul_pos ht hq) hh]
      nlinarith
  · rintro p ⟨z, hz, rfl⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    exact ⟨z, mem_iUnion₂.mpr ⟨i, hJI hi, R.core_subset i (hJI hi) hzi⟩, rfl⟩

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
