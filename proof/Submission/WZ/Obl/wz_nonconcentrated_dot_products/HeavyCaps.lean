-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.HeavyCaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Packing

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- A finite internal net, represented directly as a finset. -/
theorem finite_internal_net (S : Finset Plane) {r : ℝ} (hr : 0 < r) :
    ∃ D : Finset Plane, D ⊆ S ∧
      (∀ x ∈ D, ∀ y ∈ D, x ≠ y → r < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ D, dist x y ≤ r := by
  classical
  obtain ⟨m, c, hcS, hcsep, hcov⟩ := exists_separated_cover S.finite_toSet.totallyBounded hr
  let D : Finset Plane := Finset.univ.image c
  refine ⟨D, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hcS i
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hcsep i j (fun hij => hxy (congrArg c hij))
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact ⟨c i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩

/-- A separated family of heavy metric caps has bounded cardinality even
when the source map has repeated values. -/
theorem separated_heavy_caps_card {I : Type*} [Fintype I] (f : I → Plane)
    (D : Finset Plane) {r w : ℝ} (hr : 0 < r) (hw : 0 < w)
    (hsep : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → r ≤ dist x y)
    (hheavy : ∀ y ∈ D, w * (Fintype.card I : ℝ) ≤
      ((Finset.univ.filter (fun i => dist (f i) y ≤ r)).card : ℝ))
    [Nonempty I] : (D.card : ℝ) ≤ 25 / w := by
  classical
  have hIpos : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpoint (i : I) : (D.filter (fun y => dist (f i) y ≤ r)).card ≤ 25 := by
    apply card_le_twentyfive_of_separated hr _ (f i)
    · intro y hy
      simpa only [dist_comm] using (Finset.mem_filter.mp hy).2
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have hswap : (∑ y ∈ D, ((Finset.univ.filter (fun i => dist (f i) y ≤ r)).card : ℝ)) =
      ∑ i : I, ((D.filter (fun y => dist (f i) y ≤ r)).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
  have htotal : (D.card : ℝ) * (w * (Fintype.card I : ℝ)) ≤ 25 * (Fintype.card I : ℝ) := by
    calc (D.card : ℝ) * (w * (Fintype.card I : ℝ)) =
        ∑ _y ∈ D, w * (Fintype.card I : ℝ) := by simp
      _ ≤ ∑ y ∈ D, ((Finset.univ.filter (fun i => dist (f i) y ≤ r)).card : ℝ) :=
        Finset.sum_le_sum (fun y hy => hheavy y hy)
      _ = _ := hswap
      _ ≤ ∑ _i : I, (25 : ℝ) := Finset.sum_le_sum (fun i hi => by exact_mod_cast hpoint i)
      _ = _ := by simp [mul_comm]
  apply (le_div_iff₀ hw).mpr
  apply (mul_le_mul_iff_left₀ hIpos).mp
  nlinarith only [htotal]

/-- All heavy cap centers are covered by a small family of heavy caps. -/
theorem exists_heavy_cap_cover {I : Type*} [Fintype I] [Nonempty I] (f : I → Plane)
    {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    ∃ D : Finset Plane, (∀ y ∈ D, ∃ i, f i = y) ∧
      (D.card : ℝ) ≤ 25 / w ∧
      (∀ y ∈ D, w * (Fintype.card I : ℝ) ≤
        ((Finset.univ.filter (fun i => dist (f i) y ≤ r)).card : ℝ)) ∧
      ∀ i, w * (Fintype.card I : ℝ) ≤
        ((Finset.univ.filter (fun j => dist (f j) (f i) ≤ r)).card : ℝ) →
        ∃ y ∈ D, dist (f i) y ≤ r := by
  classical
  let S := (Finset.univ.image f).filter (fun y => w * (Fintype.card I : ℝ) ≤
    ((Finset.univ.filter (fun i => dist (f i) y ≤ r)).card : ℝ))
  obtain ⟨D, hDS, hsep, hcover⟩ := finite_internal_net S hr
  have hheavy : ∀ y ∈ D, w * (Fintype.card I : ℝ) ≤
      ((Finset.univ.filter (fun i => dist (f i) y ≤ r)).card : ℝ) :=
    fun y hy => (Finset.mem_filter.mp (hDS hy)).2
  refine ⟨D, ?_, separated_heavy_caps_card f D hr hw
    (fun x hx y hy hxy => (hsep x hx y hy hxy).le) hheavy, hheavy, ?_⟩
  · intro y hy
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (hDS hy)).1
    exact ⟨i, heq⟩
  · intro i hi
    exact hcover (f i) (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩)

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
