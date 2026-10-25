import Submission.Obl.k4_matching_trimmed_grid.Basic
import Submission.Obl.k4_scalar_coefficient_clustering.Grid

noncomputable section

namespace Submission.Obl.k4_matching_trimmed_grid

open Set
open _root_.Finset hiding Icc
open scoped BigOperators

def crossing (β : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  ((p.2 : ℝ) * β p.1 - (p.1 : ℝ) * β p.2) / ((p.2 : ℝ) - p.1)

def crossings (J : ℕ) (β : ℕ → ℝ) : Finset ℝ := by
  classical
  exact (((Finset.Icc 1 J).product (Finset.Icc 1 J)).filter
    (fun p => p.1 ≠ p.2)).image (crossing β)

lemma crossing_mem {J m j : ℕ} {β : ℕ → ℝ} (hm : 1 ≤ m) (hmJ : m ≤ J)
    (hj : 1 ≤ j) (hjJ : j ≤ J) (hjm : j ≠ m) {x : ℝ}
    (he : line β j x = line β m x) : x ∈ crossings J β := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hdiff : (j : ℝ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjm)
  have heq : x = crossing β (m, j) := by
    apply (eq_div_iff hdiff).2
    have hc := (div_eq_div_iff hj0 hm0).1 he
    nlinarith
  rw [heq]
  apply Finset.mem_image.mpr
  refine ⟨(m, j), ?_, rfl⟩
  simp [hm, hmJ, hj, hjJ, Ne.symm hjm]

def nearGrid (n : ℕ) (c : ℝ) : Finset ℕ := by
  classical
  exact (range n).filter (fun k => (k : ℝ) - 1 ≤ (n : ℝ) * c ∧
    (n : ℝ) * c ≤ (k : ℝ) + 1)

lemma nearGrid_card (n : ℕ) (c : ℝ) : (nearGrid n c).card ≤ 6 := by
  classical
  have hc := k4_scalar_coefficient_clustering.card_int_grid_of_diameter
    ((nearGrid n c).image (fun k : ℕ => (k : ℤ))) (L := 2) (by norm_num) (by
      intro i hi j hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      simp only [Int.cast_natCast]
      exact abs_le.mpr ⟨by linarith [ha'.1, hb'.2], by linarith [hb'.1, ha'.2]⟩)
  rw [Finset.card_image_of_injective _ (fun a b he => Int.ofNat_inj.mp he)] at hc
  norm_num at hc
  exact_mod_cast hc

def goodCells (n : ℕ) (F : Finset ℝ) : Finset ℕ := by
  classical
  exact range n \ insert 0 (F.biUnion (nearGrid n))

lemma goodCells_subset (n : ℕ) (F : Finset ℝ) : goodCells n F ⊆ range n :=
  Finset.sdiff_subset

lemma goodCells_pos {n : ℕ} {F : Finset ℝ} {k : ℕ} (hk : k ∈ goodCells n F) :
    1 ≤ k := by
  classical
  have hk' := (Finset.mem_sdiff.mp hk).2
  have : k ≠ 0 := by intro he; subst k; exact hk' (Finset.mem_insert_self _ _)
  omega

lemma badCells_card (n : ℕ) (F : Finset ℝ) :
    ((range n) \ goodCells n F).card ≤ 1 + 6 * F.card := by
  classical
  have hsub : (range n) \ goodCells n F ⊆ insert 0 (F.biUnion (nearGrid n)) := by
    intro k hk
    have hk' := Finset.mem_sdiff.mp hk
    by_contra hn
    exact hk'.2 (Finset.mem_sdiff.mpr ⟨hk'.1, hn⟩)
  calc
    ((range n) \ goodCells n F).card ≤ (insert 0 (F.biUnion (nearGrid n))).card :=
      Finset.card_le_card hsub
    _ ≤ (F.biUnion (nearGrid n)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (∑ c ∈ F, (nearGrid n c).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ _c ∈ F, 6) + 1 := Nat.add_le_add_right
      (Finset.sum_le_sum (fun c _ => nearGrid_card n c)) 1
    _ = 1 + 6 * F.card := by simp; omega

lemma goodCells_active {J n : ℕ} {β : ℕ → ℝ} (hJ : 1 ≤ J) (hn : 1 ≤ n)
    {k : ℕ} (hk : k ∈ goodCells n (crossings J β)) :
    ∃ m, ∀ x ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n), Active J β m x := by
  classical
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk' := Finset.mem_sdiff.mp hk
  apply active_of_no_crossings hJ (by apply div_le_div_of_nonneg_right <;> linarith)
  intro m hm hmJ j hj hjJ hjm x hx he
  have hc := crossing_mem hm hmJ hj hjJ hjm he
  have hnear : k ∈ nearGrid n x := by
    apply Finset.mem_filter.mpr
    refine ⟨hk'.1, ?_⟩
    constructor
    · have := (div_le_iff₀ hnp).1 hx.1
      nlinarith
    · have := (le_div_iff₀ hnp).1 hx.2
      nlinarith
  exact hk'.2 (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, hc, hnear⟩))

def gridWeight (J : ℕ) (β : ℕ → ℝ) (n k : ℕ) : ℝ :=
  1 / (n : ℝ) + radius J β ((k + 1 : ℕ) / (n : ℝ)) - radius J β (k / (n : ℝ))

lemma gridWeight_le {J n : ℕ} {β : ℕ → ℝ} (hJ : 1 ≤ J) (hn : 1 ≤ n) (k : ℕ) :
    gridWeight J β n k ≤ 2 / (n : ℝ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hle : (k : ℝ) / n ≤ ((k + 1 : ℕ) : ℝ) / n := by
    apply div_le_div_of_nonneg_right _ hnp.le
    norm_cast
    omega
  have h := radius_sub_le (β := β) hJ hle
  simp only [Nat.cast_add, Nat.cast_one] at h
  unfold gridWeight
  push_cast
  simp only [add_div] at *
  have htwo : (2 : ℝ) / n = 1 / n + 1 / n := by ring
  linarith

lemma sum_gridWeight {J n : ℕ} {β : ℕ → ℝ} (hn : 1 ≤ n)
    (hzero : radius J β 0 = 0) :
    ∑ k ∈ range n, gridWeight J β n k = 1 + radius J β 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [gridWeight, add_sub_assoc, Finset.sum_add_distrib]
  rw [Finset.sum_range_sub (fun k : ℕ => radius J β ((k : ℝ) / n)) n]
  simp [hn0, hzero]

lemma gridWeight_active {J n k m : ℕ} {β : ℕ → ℝ} (hn : 1 ≤ n)
    (hactive : ∀ x ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n),
      Active J β m x) : gridWeight J β n k = (1 + 1 / (m : ℝ)) / n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha := hactive ((k : ℝ) / n) ⟨by gcongr; linarith, by gcongr; linarith⟩
  have hb := hactive (((k : ℝ) + 1) / n) ⟨by gcongr; linarith, le_rfl⟩
  unfold gridWeight
  push_cast
  rw [ha.radius_eq, hb.radius_eq]
  unfold line
  ring

lemma coarse_coverage {J n : ℕ} {β : ℕ → ℝ} (hJ : 1 ≤ J) (hn : 1 ≤ n)
    (hzero : radius J β 0 = 0) (m : ℕ → ℕ)
    (hm : ∀ k ∈ goodCells n (crossings J β),
      ∀ x ∈ Icc (((k : ℝ) - 1) / n) (((k : ℝ) + 1) / n), Active J β (m k) x) :
    1 + radius J β 1 - 2 * (1 + 6 * (crossings J β).card : ℕ) / (n : ℝ) ≤
      ∑ k ∈ goodCells n (crossings J β), (1 + 1 / (m k : ℝ)) / n := by
  classical
  let S := goodCells n (crossings J β)
  have hS : S ⊆ range n := goodCells_subset _ _
  have hsum := Finset.sum_sdiff (f := gridWeight J β n) hS
  rw [sum_gridWeight hn hzero] at hsum
  have hbad : (∑ k ∈ range n \ S, gridWeight J β n k) ≤
      2 * (1 + 6 * (crossings J β).card : ℕ) / (n : ℝ) := by
    calc
      (∑ k ∈ range n \ S, gridWeight J β n k) ≤ ∑ _k ∈ range n \ S, 2 / (n : ℝ) :=
        Finset.sum_le_sum (fun k _ => gridWeight_le hJ hn k)
      _ = ((range n \ S).card : ℝ) * (2 / (n : ℝ)) := by simp
      _ ≤ (1 + 6 * (crossings J β).card : ℕ) * (2 / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast badCells_card n (crossings J β)
      _ = _ := by ring
  have heq : (∑ k ∈ S, gridWeight J β n k) =
      ∑ k ∈ S, (1 + 1 / (m k : ℝ)) / n := by
    apply Finset.sum_congr rfl
    intro k hk
    exact gridWeight_active hn (hm k hk)
  rw [heq] at hsum
  linarith

end Submission.Obl.k4_matching_trimmed_grid
