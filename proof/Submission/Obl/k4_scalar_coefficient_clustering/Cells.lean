import Submission.Obl.k4_scalar_coefficient_clustering.Input

namespace Submission.Obl.k4_scalar_coefficient_clustering

noncomputable section

abbrev Cell := ℕ × (Fin 2 → ℤ)

def cellTime (D : ℕ) (q : Cell) : ℝ := ((q.1 : ℝ) + 1 / 2) / (D : ℝ)

def ScalarCellCompatible (D : ℕ) (p R : ℝ) (f : ℤ × ℤ) (q : Cell) : Prop :=
  |cellTime D q - p * (f.1 : ℝ)| ≤ 2 * p ∧
  |(q.2 0 : ℝ) + cellTime D q * (q.2 1 : ℝ) - ((D : ℝ) / R) * (p * (f.2 : ℝ))| ≤ 30

/-- A scalar cell has O(R) time bins, O(D) transverse bins and O(1) remaining bins. -/
theorem compatible_cells_card {D : ℕ} (hD : 1 ≤ D) {p R : ℝ} (hp : 0 < p)
    (hR : 1 ≤ R) (hmesh : (D : ℝ) * p ≤ 2 * R) (f : ℤ × ℤ) (S : Finset Cell)
    (hS : ∀ q ∈ S, ScalarCellCompatible D p R f q)
    (hy : ∀ q ∈ S, |(q.2 1 : ℝ)| ≤ 3 * (D : ℝ)) :
    (S.card : ℝ) ≤ 100000 * R * (D : ℝ) := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let T := S.image (fun q => (q.1 : ℤ))
  have htcard : (T.card : ℝ) ≤ 18 * R := by
    have hh := card_int_grid_of_diameter T (by positivity : 0 ≤ 8 * R) (by
      intro i hi j hj
      rcases Finset.mem_image.mp hi with ⟨q, hq, rfl⟩
      rcases Finset.mem_image.mp hj with ⟨r, hr, rfl⟩
      have hq' := (hS q hq).1
      have hr' := (hS r hr).1
      have hd := (abs_sub (cellTime D q - p * (f.1 : ℝ))
        (cellTime D r - p * (f.1 : ℝ))).trans (add_le_add hq' hr')
      have heq : (cellTime D q - p * (f.1 : ℝ)) - (cellTime D r - p * (f.1 : ℝ)) =
          ((q.1 : ℝ) - (r.1 : ℝ)) / (D : ℝ) := by dsimp [cellTime]; ring
      rw [heq, abs_div, abs_of_pos hDpos] at hd
      have hh := (div_le_iff₀ hDpos).mp hd
      push_cast
      nlinarith)
    linarith
  let Y := S.image (fun q => q.2 1)
  have hycard : (Y.card : ℝ) ≤ 14 * (D : ℝ) := by
    have hh := card_int_grid_of_diameter Y (by positivity : 0 ≤ 6 * (D : ℝ)) (by
      intro i hi j hj
      rcases Finset.mem_image.mp hi with ⟨q, hq, rfl⟩
      rcases Finset.mem_image.mp hj with ⟨r, hr, rfl⟩
      exact (abs_sub _ _).trans (by linarith [hy q hq, hy r hr]))
    have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  let key : Cell → ℤ × ℤ := fun q => (q.1, q.2 1)
  have hkeycard : ((S.image key).card : ℝ) ≤ 252 * R * (D : ℝ) := by
    have hsub : S.image key ⊆ T ×ˢ Y := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨q, hq, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩,
        Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
    have hh : ((S.image key).card : ℝ) ≤ (T.card : ℝ) * (Y.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product T Y)
    have hm := mul_le_mul htcard hycard (Nat.cast_nonneg Y.card) (by positivity : 0 ≤ 18 * R)
    nlinarith
  have hfiber : ∀ k ∈ S.image key, ((S.filter (fun q => key q = k)).card : ℝ) ≤ 122 := by
    intro k hk
    let U := S.filter (fun q => key q = k)
    have hinj : Set.InjOn (fun q : Cell => q.2 0) (↑U : Set Cell) := by
      intro q hq r hr heq
      have hkey : key q = key r := (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm
      have hfst : q.1 = r.1 := Int.ofNat_inj.mp (congrArg Prod.fst hkey)
      have h1 : q.2 1 = r.2 1 := congrArg Prod.snd hkey
      exact Prod.ext hfst (by funext j; fin_cases j <;> assumption)
    have hh := card_int_grid_of_diameter (U.image (fun q => q.2 0)) (by norm_num : (0 : ℝ) ≤ 60) (by
      intro i hi j hj
      rcases Finset.mem_image.mp hi with ⟨q, hq, rfl⟩
      rcases Finset.mem_image.mp hj with ⟨r, hr, rfl⟩
      have hkey : key q = key r := (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm
      have hfst : q.1 = r.1 := Int.ofNat_inj.mp (congrArg Prod.fst hkey)
      have h1 : q.2 1 = r.2 1 := congrArg Prod.snd hkey
      have hq' := (hS q (Finset.mem_filter.mp hq).1).2
      have hr' := (hS r (Finset.mem_filter.mp hr).1).2
      have hd := (abs_sub _ _).trans (add_le_add hq' hr')
      have heq : ((q.2 0 : ℝ) + cellTime D q * (q.2 1 : ℝ) - ((D : ℝ) / R) * (p * (f.2 : ℝ))) -
          ((r.2 0 : ℝ) + cellTime D r * (r.2 1 : ℝ) - ((D : ℝ) / R) * (p * (f.2 : ℝ))) =
          (q.2 0 : ℝ) - (r.2 0 : ℝ) := by simp only [cellTime, hfst, h1]; ring
      rw [heq] at hd
      exact hd.trans (by norm_num))
    rw [Finset.card_image_of_injOn hinj] at hh
    norm_num at hh
    exact_mod_cast hh
  have hh := card_le_image_mul_fiber S key 122 hfiber
  nlinarith [mul_nonneg (by linarith : 0 ≤ R) (Nat.cast_nonneg D)]

theorem cells_card_of_scalar_support {D : ℕ} (hD : 1 ≤ D) {p R : ℝ} (hp : 0 < p)
    (hR : 1 ≤ R) (hmesh : (D : ℝ) * p ≤ 2 * R) (F : Finset (ℤ × ℤ)) (S : Finset Cell)
    (hS : ∀ q ∈ S, ∃ f ∈ F, ScalarCellCompatible D p R f q)
    (hy : ∀ q ∈ S, |(q.2 1 : ℝ)| ≤ 3 * (D : ℝ)) :
    (S.card : ℝ) ≤ 100000 * R * (D : ℝ) * (F.card : ℝ) := by
  classical
  let U := fun f => S.filter (ScalarCellCompatible D p R f)
  have hsub : S ⊆ F.biUnion U := by
    intro q hq
    rcases hS q hq with ⟨f, hf, hc⟩
    exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_filter.mpr ⟨hq, hc⟩⟩
  have hcard : (S.card : ℝ) ≤ ∑ f ∈ F, ((U f).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  calc
    _ ≤ ∑ f ∈ F, ((U f).card : ℝ) := hcard
    _ ≤ ∑ _f ∈ F, (100000 * R * (D : ℝ)) := by
      apply Finset.sum_le_sum
      intro f hf
      exact compatible_cells_card hD hp hR hmesh f (U f)
        (fun q hq => (Finset.mem_filter.mp hq).2)
        (fun q hq => hy q (Finset.mem_filter.mp hq).1)
    _ = _ := by simp; ring

end
end Submission.Obl.k4_scalar_coefficient_clustering
