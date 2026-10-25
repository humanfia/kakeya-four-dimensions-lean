-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarClosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarHalf

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open scoped Pointwise

noncomputable def scalarClosureBound (c K : ℝ) : ℝ :=
  K + 288 * (9 * (6 * K) ^ 3) *
    (9 * (6 * (K + 144 * K ^ 2 / c + 144 * K ^ 2 / c)) ^ 3 +
      9 * (6 * (K + K + K)) ^ 3)

/-- A bounded algebraic enlargement admits an internal separated net.
Its covering estimates record both the additive and product enlargements. -/
theorem scalar_closure_net (A R S : Finset ℝ) {δ c K : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hc1 : c ≤ 1) (hK : 1 ≤ K)
    (hA : A.Nonempty) (hR : R.Nonempty)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hRb : ∀ r ∈ R, c ≤ r ∧ r ≤ 1)
    (hSb : ∀ s ∈ S, c ≤ s ∧ s ≤ 1)
    (hbase : SmallScalarProjection δ A K 1)
    (hgoodR : ∀ t ∈ R, SmallScalarProjection δ A K t)
    (hgoodS : ∀ t ∈ S, SmallScalarProjection δ A K t) :
    ∃ U : Finset ℝ, U.Nonempty ∧
      (∀ u ∈ U, c ^ 2 ≤ u ∧ u ≤ 1) ∧
      (∀ u ∈ U, ∀ v ∈ U, u ≠ v → δ ≤ dist u v) ∧
      (∀ u ∈ U, SmallScalarProjection δ A (scalarClosureBound c K) u) ∧
      RealCoverBound (2 * δ) (R + S) (U.card : ℝ) ∧
      RealCoverBound (2 * δ) (R * R + R * R) (U.card : ℝ) := by
  classical
  let H := R ∪ (R + S).image (fun t => t / 2) ∪
    (R * R + R * R).image (fun t => t / 2)
  have hRH : R ⊆ H := fun _ ht => Finset.mem_union_left _ (Finset.mem_union_left _ ht)
  have hH : H.Nonempty := hR.mono hRH
  have hKb : 0 ≤ K := by linarith
  have hKclosure : K ≤ scalarClosureBound c K := by
    unfold scalarClosureBound
    exact le_add_of_nonneg_right (by positivity)
  have hgood (t : ℝ) (ht : t ∈ H) : SmallScalarProjection δ A (scalarClosureBound c K) t := by
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact (hgoodR t ht).weaken hKclosure
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
        have hh := SmallScalarProjection.half hδ hKb (by positivity) hA hsep hbase
          (SmallScalarProjection.add hδ hKb hKb hKb hA hsep hbase (hgoodR u hu) (hgoodS v hv))
        apply hh.weaken
        unfold scalarClosureBound
        have : 0 ≤ 288 * (9 * (6 * K) ^ 3) *
            (9 * (6 * (K + 144 * K ^ 2 / c + 144 * K ^ 2 / c)) ^ 3) := by positivity
        nlinarith
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      have hh := SmallScalarProjection.half hδ hKb (by positivity) hA hsep hbase
        (product_sum_scalar_small A R hδ hc hKb hA hsep hRb hbase hgoodR x hx)
      apply hh.weaken
      unfold scalarClosureBound
      have : 0 ≤ 288 * (9 * (6 * K) ^ 3) * (9 * (6 * (K + K + K)) ^ 3) := by positivity
      nlinarith
  have hbound (t : ℝ) (ht : t ∈ H) : c ^ 2 ≤ t ∧ t ≤ 1 := by
    have hcc : c ^ 2 ≤ c := by nlinarith
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact ⟨hcc.trans (hRb t ht).1, (hRb t ht).2⟩
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
        constructor <;> linarith [(hRb u hu).1, (hRb u hu).2, (hSb v hv).1, (hSb v hv).2]
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      have hmul : ∀ z ∈ R * R, c ^ 2 ≤ z ∧ z ≤ 1 := by
        intro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hz
        constructor
        · simpa only [pow_two] using mul_le_mul (hRb a ha).1 (hRb b hb).1 hc.le
            (hc.le.trans (hRb a ha).1)
        · nlinarith [(hRb a ha).1, (hRb a ha).2, (hRb b hb).1, (hRb b hb).2,
            mul_nonneg (hc.le.trans (hRb a ha).1) (by linarith [(hRb b hb).2] : 0 ≤ 1 - b)]
      constructor <;> linarith [(hmul u hu).1, (hmul u hu).2, (hmul v hv).1, (hmul v hv).2]
  obtain ⟨m, cc, hccH, hccsep, hcover⟩ := exists_separated_cover H.finite_toSet.totallyBounded hδ
  let U := Finset.univ.image cc
  have hUH : U ⊆ H := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    exact hccH i
  have hinj : Function.Injective cc := by
    intro i j hij
    by_contra hh
    have := hccsep i j hh
    rw [hij, dist_self] at this
    linarith
  have hUm : U.card = m := by
    rw [Finset.card_image_iff.mpr (fun i _ j _ hij => hinj hij)]
    simp
  have hUsep : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → δ ≤ dist u v := by
    intro u hu v hv hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact (hccsep i j (fun hij => hne (hij ▸ rfl))).le
  have hUne : U.Nonempty := by
    obtain ⟨t, ht⟩ := hH
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ht)
    exact ⟨cc i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hcov (V : Finset ℝ) (hV : V.image (fun t => t / 2) ⊆ H) :
      RealCoverBound (2 * δ) V (U.card : ℝ) := by
    refine ⟨m, fun i => 2 * cc i, ?_, by rw [hUm]⟩
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (hV (Finset.mem_image.mpr ⟨x, hx, rfl⟩)))
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change dist x (2 * cc i) ≤ 2 * δ
    change dist (x / 2) (cc i) ≤ δ at hi
    rw [Real.dist_eq] at *
    have hid : x - 2 * cc i = 2 * (x / 2 - cc i) := by ring
    rw [hid, abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  exact ⟨U, hUne, fun t ht => hbound t (hUH ht), hUsep,
    fun t ht => hgood t (hUH ht),
    hcov (R + S) (fun _ ht => Finset.mem_union_left _ (Finset.mem_union_right _ ht)),
    hcov (R * R + R * R) (fun _ ht => Finset.mem_union_right _ ht)⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
