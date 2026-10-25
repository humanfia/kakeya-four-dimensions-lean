/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 9471cb26ffd9014af31191dee110de3e83eca015,
Submission/Obl/k4_scalar_mesh_projection/GridSampling.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.DenseProductGrid

namespace Submission.Lib.K4ScalarActualSwitching

open Set

theorem gridMean_const {X : Type*} [Fintype X] (p : X → ℝ)
    (hp : ∑ x, p x = 1) (c : ℝ) : gridMean p (fun _ => c) = c := by
  simp only [gridMean, ← Finset.sum_mul, hp, one_mul]

theorem gridMean_exists_ge {X : Type*} [Fintype X] (p f : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (B : ℝ) (hB : B ≤ gridMean p f) :
    ∃ x, B ≤ f x := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (fun x _ => hp x)).mp
    (by simpa only [hp1] using (zero_lt_one : (0 : ℝ) < 1))
  have hlt : gridMean p f < gridMean p (fun _ => B) := by
    apply Finset.sum_lt_sum
    · intro y _
      exact mul_le_mul_of_nonneg_left (hn y).le (hp y)
    · exact ⟨x, Finset.mem_univ x, mul_lt_mul_of_pos_left (hn x) hx⟩
  rw [gridMean_const p hp1 B] at hlt
  exact (not_lt_of_ge hB) hlt

/-- The product-grid density theorem in the form of an actual Boolean
success event under the original coordinate probability weights. -/
theorem original_product_grid_success {X Y : Type*} [Fintype X] [Fintype Y]
    (r s : ℕ) (p : X → ℝ) (q : Y → ℝ) (R : X → Y → Prop) [DecidableRel R]
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (η : ℝ) (hη : 0 ≤ η)
    (hR : η ≤ gridMean p (fun x => gridMean q (fun y => if R x y then 1 else 0))) :
    η ^ (r * s) ≤ gridMean (gridProductWeights r p) (fun x =>
      gridMean (gridProductWeights s q) (fun y => if ∀ i j, R (x i) (y j) then 1 else 0)) := by
  classical
  have h := (pow_le_pow_left₀ hη hR (r * s)).trans
    (original_product_grid_density r s p q (fun x y => if R x y then 1 else 0)
      hp hp1 hq hq1 (by intro x y; split_ifs <;> norm_num))
  simpa only [productGridMean, Finset.prod_boole, Finset.mem_univ, forall_const,
    true_implies] using h

theorem gridMean_insertNth {X : Type*} [Fintype X] (n : ℕ)
    (p : X → ℝ) (F : (Fin (n + 1) → X) → ℝ) (i : Fin (n + 1)) :
    gridMean (gridProductWeights (n + 1) p) F =
      gridMean p (fun x => gridMean (gridProductWeights n p) (fun z => F (i.insertNth x z))) := by
  classical
  let e := Fin.insertNthEquiv (fun _ : Fin (n + 1) => X) i
  have he (z : X × (Fin n → X)) :
      gridProductWeights (n + 1) p (e z) = p z.1 * gridProductWeights n p z.2 := by
    change (∏ k : Fin (n + 1), p (Fin.insertNth (α := fun _ : Fin (n + 1) => X) i z.1 z.2 k)) = _
    rw [Fin.prod_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rfl
  have h := Fintype.sum_equiv e
    (fun z => p z.1 * gridProductWeights n p z.2 * F (e z))
    (fun z => gridProductWeights (n + 1) p z * F z) (by intro z; rw [he])
  rw [Fintype.sum_prod_type] at h
  have heapp (z : X × (Fin n → X)) :
      e z = Fin.insertNth (α := fun _ : Fin (n + 1) => X) i z.1 z.2 := rfl
  simpa only [heapp, gridMean, Finset.mul_sum, mul_assoc] using h.symm

/-- Two distinct coordinates retain the original thin-pencil bound under
the full product law, before any successful-grid restriction. -/
theorem gridMean_pair_pencil {X : Type*} [Fintype X] (n : ℕ)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (v : X → ℝ) (r B : ℝ)
    (hthin : ∀ w, gridMean p (fun x => if |v x - w| < r then 1 else 0) ≤ B)
    (i j : Fin n) (hij : i ≠ j) :
    gridMean (gridProductWeights n p)
      (fun x => if |v (x i) - v (x j)| < r then 1 else 0) ≤ B := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij.symm
    rw [gridMean_insertNth n p _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rw [gridMean_comm]
    exact (gridMean_mono (gridProductWeights_nonneg n hp)
      (fun x => hthin (v (x k)))).trans_eq
        (gridMean_const _ (gridProductWeights_sum n p hp1) B)

theorem gridMean_add {X : Type*} [Fintype X] (p f g : X → ℝ) :
    gridMean p (fun x => f x + g x) = gridMean p f + gridMean p g := by
  simp only [gridMean, mul_add, Finset.sum_add_distrib]

theorem gridMean_sum {X I : Type*} [Fintype X] [Fintype I]
    (p : X → ℝ) (f : I → X → ℝ) :
    gridMean p (fun x => ∑ i, f i x) = ∑ i, gridMean p (f i) := by
  simp only [gridMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem not_grid_collision_iff {X : Type*} (n : ℕ) (v : X → ℝ) (r : ℝ) (x : Fin n → X) :
    (¬∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < r) ↔
      Pairwise (fun i j => r ≤ |v (x i) - v (x j)|) := by
  simp only [not_exists, not_and, not_lt, Pairwise]

/-- A union bound for collisions among all sampled coordinates. The
bound uses the unchanged original pencil probabilities. -/
theorem gridMean_any_collision {X : Type*} [Fintype X] (n : ℕ)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (v : X → ℝ) (r B : ℝ) (hB : 0 ≤ B)
    (hthin : ∀ w, gridMean p (fun x => if |v x - w| < r then 1 else 0) ≤ B) :
    gridMean (gridProductWeights n p)
      (fun x => if ∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < r then 1 else 0) ≤
        (n : ℝ) ^ 2 * B := by
  classical
  let I := fun (i j : Fin n) (x : Fin n → X) =>
    if i ≠ j ∧ |v (x i) - v (x j)| < r then (1 : ℝ) else 0
  have hI : ∀ i j x, 0 ≤ I i j x := by
    intro i j x
    dsimp only [I]
    split_ifs <;> norm_num
  have hpoint (x : Fin n → X) :
      (if ∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < r then (1 : ℝ) else 0) ≤
        ∑ i, ∑ j, I i j x := by
    split_ifs with h
    · obtain ⟨i, j, hij, hclose⟩ := h
      have hinner := Finset.single_le_sum (fun k _ => hI i k x) (Finset.mem_univ j)
      have houter : (∑ j, I i j x) ≤ ∑ k, ∑ l, I k l x :=
        Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hI k l x)
          (Finset.mem_univ i)
      simpa [I, hij, hclose] using hinner.trans houter
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hI i j x
  have hpair (i j : Fin n) : gridMean (gridProductWeights n p) (I i j) ≤ B := by
    by_cases hij : i = j
    · subst j
      simpa only [I, ne_eq, not_true_eq_false, false_and, ↓reduceIte, gridMean, mul_zero,
        Finset.sum_const_zero] using hB
    · simpa [I, hij] using gridMean_pair_pencil n p hp hp1 v r B hthin i j hij
  calc
    _ ≤ gridMean (gridProductWeights n p) (fun x => ∑ i, ∑ j, I i j x) :=
      gridMean_mono (gridProductWeights_nonneg n hp) hpoint
    _ = ∑ i, ∑ j, gridMean (gridProductWeights n p) (I i j) := by
      simp_rw [gridMean_sum]
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, B :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = _ := by simp; ring

theorem gridMean_append {X : Type*} [Fintype X] (n : ℕ)
    (p : X → ℝ) (F : (Fin (n + 1) → X) → ℝ) :
    gridMean (gridProductWeights (n + 1) p) F =
      gridMean (gridProductWeights n p) (fun a => gridMean p (fun x => F (Fin.snoc a x))) := by
  rw [gridMean_insertNth n p F (Fin.last n), gridMean_comm]
  simp only [Fin.insertNth_last']

noncomputable def gridFlag (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

theorem gridFlag_eq_ite (P : Prop) [Decidable P] : gridFlag P = if P then 1 else 0 := by
  classical
  by_cases h : P <;> simp [gridFlag, h]

theorem gridFlag_nonneg (P : Prop) : 0 ≤ gridFlag P := by
  classical
  unfold gridFlag
  split_ifs <;> norm_num

theorem gridFlag_mono {P Q : Prop} (h : P → Q) : gridFlag P ≤ gridFlag Q := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp_all [gridFlag]

theorem gridFlag_restriction_budget (P A B : Prop) :
    gridFlag P ≤ gridFlag (P ∧ ¬A ∧ ¬B) + gridFlag A + gridFlag B := by
  classical
  by_cases hP : P <;> by_cases hA : A <;> by_cases hB : B <;> norm_num [gridFlag, hP, hA, hB]

/-- Collision removal is charged to the original product law. Its
successful complete-grid event is never made into a posterior law. -/
theorem original_separated_product_grid_budget {X Y : Type*} [Fintype X] [Fintype Y]
    (r s : ℕ) (p : X → ℝ) (q : Y → ℝ) (R : X → Y → Prop)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (v : X → ℝ) (w : Y → ℝ) (gap Bx By η : ℝ)
    (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) (hη : 0 ≤ η)
    (hthinX : ∀ z, gridMean p (fun x => if |v x - z| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ z, gridMean q (fun y => if |w y - z| < gap then 1 else 0) ≤ By)
    (hdensity : η ≤ gridMean p (fun x => gridMean q (fun y => gridFlag (R x y)))) :
    η ^ (r * s) ≤
      gridMean (gridProductWeights r p) (fun x => gridMean (gridProductWeights s q) (fun y =>
        gridFlag ((∀ i j, R (x i) (y j)) ∧
          (¬∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap) ∧
          (¬∃ i j, i ≠ j ∧ |w (y i) - w (y j)| < gap)))) +
        (r : ℝ) ^ 2 * Bx + (s : ℝ) ^ 2 * By := by
  classical
  let px := gridProductWeights r p
  let qy := gridProductWeights s q
  let badX := fun x : Fin r → X => ∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap
  let badY := fun y : Fin s → Y => ∃ i j, i ≠ j ∧ |w (y i) - w (y j)| < gap
  have hgrid : η ^ (r * s) ≤ gridMean px (fun x => gridMean qy
      (fun y => gridFlag (∀ i j, R (x i) (y j)))) := by
    simpa only [gridFlag_eq_ite, px, qy] using
      original_product_grid_success r s p q R hp hp1 hq hq1 η hη hdensity
  have hbudget := gridMean_mono (gridProductWeights_nonneg r hp)
    (fun x => gridMean_mono (gridProductWeights_nonneg s hq)
      (fun y => gridFlag_restriction_budget (∀ i j, R (x i) (y j)) (badX x) (badY y)))
  have hbudget' : gridMean px (fun x => gridMean qy (fun y => gridFlag (∀ i j, R (x i) (y j)))) ≤
      gridMean px (fun x => gridMean qy (fun y =>
        gridFlag ((∀ i j, R (x i) (y j)) ∧ ¬badX x ∧ ¬badY y))) +
        gridMean px (fun x => gridFlag (badX x)) + gridMean qy (fun y => gridFlag (badY y)) := by
    simpa only [px, qy, gridMean_add,
      gridMean_const (gridProductWeights s q) (gridProductWeights_sum s q hq1),
      gridMean_const (gridProductWeights r p) (gridProductWeights_sum r p hp1)] using hbudget
  have hX : gridMean px (fun x => gridFlag (badX x)) ≤ (r : ℝ) ^ 2 * Bx := by
    simpa only [gridFlag_eq_ite, px, badX] using gridMean_any_collision r p hp hp1 v gap Bx hBx hthinX
  have hY : gridMean qy (fun y => gridFlag (badY y)) ≤ (s : ℝ) ^ 2 * By := by
    simpa only [gridFlag_eq_ite, qy, badY] using gridMean_any_collision s q hq hq1 w gap By hBy hthinY
  exact (hgrid.trans hbudget').trans (add_le_add (add_le_add le_rfl hX) hY)

theorem gridMean_append_pair {X Y : Type*} [Fintype X] [Fintype Y]
    (r s : ℕ) (p : X → ℝ) (q : Y → ℝ)
    (F : (Fin (r + 1) → X) → (Fin (s + 1) → Y) → ℝ) :
    gridMean (gridProductWeights (r + 1) p) (fun x =>
      gridMean (gridProductWeights (s + 1) q) (F x)) =
      gridMean (gridProductWeights r p) (fun a => gridMean (gridProductWeights s q) (fun b =>
        gridMean p (fun x => gridMean q (fun y => F (Fin.snoc a x) (Fin.snoc b y))))) := by
  rw [gridMean_append r p]
  simp_rw [gridMean_append s q]
  apply congrArg (gridMean (gridProductWeights r p))
  funext a
  exact gridMean_comm p (gridProductWeights s q) _

theorem exists_fixed_grid_anchors {X Y : Type*} [Fintype X] [Fintype Y]
    (r s : ℕ) (p : X → ℝ) (q : Y → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (F : (Fin (r + 1) → X) → (Fin (s + 1) → Y) → ℝ)
    (B : ℝ) (hB : B ≤ gridMean (gridProductWeights (r + 1) p)
      (fun x => gridMean (gridProductWeights (s + 1) q) (F x))) :
    ∃ (a : Fin r → X) (b : Fin s → Y),
      B ≤ gridMean p (fun x => gridMean q (fun y => F (Fin.snoc a x) (Fin.snoc b y))) := by
  rw [gridMean_append_pair r s p q F] at hB
  obtain ⟨a, ha⟩ := gridMean_exists_ge (gridProductWeights r p) _
    (gridProductWeights_nonneg r hp) (gridProductWeights_sum r p hp1) B hB
  obtain ⟨b, hb⟩ := gridMean_exists_ge (gridProductWeights s q) _
    (gridProductWeights_nonneg s hq) (gridProductWeights_sum s q hq1) B ha
  exact ⟨a, b, hb⟩

/-- Freeze separated pure anchors while retaining a positive original
target-pair density. The target event contains every grid vertex needed
for successive tensor interpolation. -/
theorem exists_separated_original_grid_anchors {X Y : Type*} [Fintype X] [Fintype Y]
    (r s : ℕ) (p : X → ℝ) (q : Y → ℝ) (R : X → Y → Prop)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hq : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (v : X → ℝ) (w : Y → ℝ) (gap Bx By η : ℝ)
    (hBx : 0 ≤ Bx) (hBy : 0 ≤ By) (hη : 0 < η)
    (hthinX : ∀ z, gridMean p (fun x => if |v x - z| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ z, gridMean q (fun y => if |w y - z| < gap then 1 else 0) ≤ By)
    (hdensity : η ≤ gridMean p (fun x => gridMean q (fun y => gridFlag (R x y))))
    (hloss : ((r + 1 : ℕ) : ℝ) ^ 2 * Bx + ((s + 1 : ℕ) : ℝ) ^ 2 * By ≤
      η ^ ((r + 1) * (s + 1)) / 2) :
    ∃ (a : Fin r → X) (b : Fin s → Y),
      Pairwise (fun i j => gap ≤ |v (a i) - v (a j)|) ∧
      Pairwise (fun i j => gap ≤ |w (b i) - w (b j)|) ∧
      η ^ ((r + 1) * (s + 1)) / 2 ≤ gridMean p (fun x => gridMean q (fun y =>
        gridFlag (∀ i j, R (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x i) (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y j)))) := by
  classical
  let F := fun (x : Fin (r + 1) → X) (y : Fin (s + 1) → Y) =>
    gridFlag ((∀ i j, R (x i) (y j)) ∧
      (¬∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap) ∧
      (¬∃ i j, i ≠ j ∧ |w (y i) - w (y j)| < gap))
  let B := η ^ ((r + 1) * (s + 1)) / 2
  have hB : 0 < B := by dsimp only [B]; positivity
  have hbudget := original_separated_product_grid_budget (r + 1) (s + 1)
    p q R hp hp1 hq hq1 v w gap Bx By η hBx hBy hη.le hthinX hthinY hdensity
  have hmass : B ≤ gridMean (gridProductWeights (r + 1) p)
      (fun x => gridMean (gridProductWeights (s + 1) q) (F x)) := by
    dsimp only [B]
    change η ^ ((r + 1) * (s + 1)) ≤ _ + _ + _ at hbudget
    linarith
  obtain ⟨a, b, hab⟩ := exists_fixed_grid_anchors r s p q hp hp1 hq hq1 F B hmass
  obtain ⟨x₀, hx₀⟩ := gridMean_exists_ge p _ hp hp1 B hab
  obtain ⟨y₀, hy₀⟩ := gridMean_exists_ge q _ hq hq1 B hx₀
  have hgood : (∀ i j, R (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀ i) (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀ j)) ∧
      (¬∃ i j, i ≠ j ∧ |v (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀ i) - v (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀ j)| < gap) ∧
      (¬∃ i j, i ≠ j ∧ |w (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀ i) - w (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀ j)| < gap) := by
    by_contra hn
    have hz : F (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀) (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀) = 0 := by simp only [F, gridFlag, hn, ↓reduceIte]
    rw [hz] at hy₀
    linarith
  have hsepX := (not_grid_collision_iff (r + 1) v gap (Fin.snoc (α := fun _ : Fin (r + 1) => X) a x₀)).mp hgood.2.1
  have hsepY := (not_grid_collision_iff (s + 1) w gap (Fin.snoc (α := fun _ : Fin (s + 1) => Y) b y₀)).mp hgood.2.2
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro i j hij
    simpa only [Fin.snoc_castSucc] using hsepX (fun h => hij (Fin.castSucc_injective r h))
  · intro i j hij
    simpa only [Fin.snoc_castSucc] using hsepY (fun h => hij (Fin.castSucc_injective s h))
  · exact hab.trans (gridMean_mono hp (fun x => gridMean_mono hq (fun y =>
      gridFlag_mono (fun h => h.1))))

end Submission.Lib.K4ScalarActualSwitching
