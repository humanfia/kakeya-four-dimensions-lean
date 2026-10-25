-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainFine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainRefine

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

open Classical in
/-- **Coarse fan data**: from a coarse cube family `M` inside `r`-tubes and a measurable
refinement `Z` with a cone bound, saturation, density, trimming and density again give cube
families `M3 ⊆ M2 ⊆ M1 ⊆ M` with the hypotheses of the fan lemma and an explicit count. -/
theorem coarse_fan_data {k : ℕ} {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) {r : ℝ}
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) (M : Fin k → Finset (Fin 3 → ℤ))
    (hMT : ∀ j, cubeSet s (M j) ⊆ tube r (z j) (w j)) (hr : r ≤ (N : ℝ) * s)
    (h3 : 3 * ((N : ℝ) * s) ≤ 1) {Z : Fin k → Set Space} (hZm : ∀ j, MeasurableSet (Z j))
    (hZM : ∀ j, Z j ⊆ cubeSet s (M j)) {c θ μ2 B1 β : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ)
    (hμ2 : 0 ≤ μ2)
    (hcone : ∀ (x u : Space), ‖u‖ = 1 → ((Finset.univ.filter fun j =>
      x ∈ Z j ∧ min ‖w j - u‖ ‖w j + u‖ ≤ β).card : ℝ) ≤ B1) :
    ∃ M1 M2 M3 : Fin k → Finset (Fin 3 → ℤ),
      (∀ j, M3 j ⊆ M2 j) ∧ (∀ j, M2 j ⊆ M1 j) ∧ (∀ j, M1 j ⊆ M j) ∧
      (∀ (m : Fin 3 → ℤ) (u : Space), ‖u‖ = 1 → ((Finset.univ.filter fun j =>
        m ∈ M2 j ∧ min ‖w j - u‖ ‖w j + u‖ ≤ β).card : ℝ) ≤ B1 / c) ∧
      (∀ j m, m ∈ M3 j → μ2 ≤ (cubeLabels M2 m : ℝ)) ∧
      (∀ j B, ((M1 j).filter fun m => blockOf N m = B).Nonempty →
        θ ≤ (((M1 j).filter fun m => blockOf N m = B).card : ℝ)) ∧
      (∀ j B, ((M3 j).filter fun m => blockOf N m = B).Nonempty →
        θ ≤ (((M3 j).filter fun m => blockOf N m = B).card : ℝ)) ∧
      (∑ j, (volume (Z j)).toReal) - c * (∑ j, ((M j).card : ℝ)) * s ^ 3 -
          2 * θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) * s ^ 3 -
          μ2 * ((Finset.univ.biUnion M).card : ℝ) * s ^ 3 ≤
        (∑ j, ((M3 j).card : ℝ)) * s ^ 3 := by
  set SM := satCubes s M Z c with hSM
  set M1 := denseCubes SM N θ with hM1
  set M2 := trimCubes M1 μ2 with hM2
  set M3 := denseCubes M2 N θ with hM3
  have hSMM : ∀ j, SM j ⊆ M j := satCubes_subset s M Z c
  have hM1S : ∀ j, M1 j ⊆ SM j := denseCubes_subset SM N θ
  have hM21 : ∀ j, M2 j ⊆ M1 j := trimCubes_subset M1 μ2
  have hM32 : ∀ j, M3 j ⊆ M2 j := denseCubes_subset M2 N θ
  have hM1M : ∀ j, M1 j ⊆ M j := fun j => (hM1S j).trans (hSMM j)
  -- blocks per tube
  have hblocks : ∀ (P : Fin k → Finset (Fin 3 → ℤ)), (∀ j, P j ⊆ M j) →
      ∀ j, (((P j).image (blockOf N)).card : ℝ) ≤ 3456 / ((N : ℝ) * s) :=
    fun P hP j => card_blocks_le hs hN (hw j) ((cubeSet_mono (hP j)).trans (hMT j)) hr h3
  refine ⟨M1, M2, M3, hM32, hM21, hM1M, ?_, ?_, ?_, ?_, ?_⟩
  · -- cone bound
    intro m u hu
    set L := Finset.univ.filter fun j => min ‖w j - u‖ ‖w j + u‖ ≤ β
    have hL : ∀ x, ((L.filter fun j => x ∈ Z j).card : ℝ) ≤ B1 := by
      intro x
      have e : (L.filter fun j => x ∈ Z j) = Finset.univ.filter fun j =>
          x ∈ Z j ∧ min ‖w j - u‖ ‖w j + u‖ ≤ β := by
        ext j; simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      rw [e]; exact hcone x u hu
    have h1 := card_satCubes_le hs M hZm hc L hL m
    refine le_trans ?_ h1
    have hsub : (Finset.univ.filter fun j => m ∈ M2 j ∧ min ‖w j - u‖ ‖w j + u‖ ≤ β) ⊆
        L.filter fun j => m ∈ satCubes s M Z c j := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, L] at hj ⊢
      exact ⟨hj.2, hM1S j (hM21 j hj.1)⟩
    exact_mod_cast Finset.card_le_card hsub
  · intro j m hm
    exact le_cubeLabels_trimCubes M1 μ2 (hM32 j hm)
  · intro j B hne; exact denseCubes_block SM N θ j B hne
  · intro j B hne; exact denseCubes_block M2 N θ j B hne
  · -- the count
    have hsat : ∑ j, (volume (Z j)).toReal - c * (∑ j, ((M j).card : ℝ)) * s ^ 3 ≤
        (∑ j, ((SM j).card : ℝ)) * s ^ 3 := by
      have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
        volume_le_satCubes hs M hZM hc.le j
      rw [Finset.sum_add_distrib] at h
      have e1 : ∑ j, ((SM j).card : ℝ) * s ^ 3 = (∑ j, ((SM j).card : ℝ)) * s ^ 3 := by
        rw [Finset.sum_mul]
      have e2 : ∑ j, c * ((M j).card : ℝ) * s ^ 3 = c * (∑ j, ((M j).card : ℝ)) * s ^ 3 := by
        rw [Finset.mul_sum, Finset.sum_mul]
      rw [e1, e2] at h
      linarith
    have hden : ∀ (P : Fin k → Finset (Fin 3 → ℤ)), (∀ j, P j ⊆ M j) →
        (∑ j, ((P j).card : ℝ)) - θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) ≤
          ∑ j, ((denseCubes P N θ j).card : ℝ) := by
      intro P hP
      have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => card_denseCubes_ge P N hθ j
      rw [Finset.sum_sub_distrib] at h
      have h2 : ∑ j, θ * (((P j).image (blockOf N)).card : ℝ) ≤
          θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) := by
        calc ∑ j, θ * (((P j).image (blockOf N)).card : ℝ) ≤
              ∑ _j : Fin k, θ * (3456 / ((N : ℝ) * s)) :=
              Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hblocks P hP j) hθ
          _ = θ * (k : ℝ) * (3456 / ((N : ℝ) * s)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      linarith
    have h1 := hden SM hSMM
    have h2 := card_trimCubes_ge M1 hμ2
    have hsubU : Finset.univ.biUnion M1 ⊆ Finset.univ.biUnion M := by
      intro m hm
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hm
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hM1M j hj⟩
    have hU : ((Finset.univ.biUnion M1).card : ℝ) ≤ ((Finset.univ.biUnion M).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubU
    have h3' := hden M2 (fun j => (hM21 j).trans (hM1M j))
    have hs3 : 0 < s ^ 3 := by positivity
    have hμU : μ2 * ((Finset.univ.biUnion M1).card : ℝ) ≤
        μ2 * ((Finset.univ.biUnion M).card : ℝ) := mul_le_mul_of_nonneg_left hU hμ2
    nlinarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- Points of one block are closer than twice the block side. -/
theorem dist_lt_of_mem_block {ω : ℝ} (hω : 0 < ω) {B : Fin 3 → ℤ} {y y' : Space}
    (hy : y ∈ gridCube ω B) (hy' : y' ∈ gridCube ω B) : dist y y' ≤ 2 * ω :=
  (diam_le_of_mem_gridCube hω hy hy').le

open Classical in
/-- **Grain volume at a fine point**: the fan of the coarse family around the contracted point
`λ q`, transferred to the fine set by the balanced cover, gives a lower bound for the fine
volume in the block of `λ q` within the `u`-slab through it. -/
theorem fine_grain_volume {k : ℕ} {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) {r D β π μlo μmax θ θb lam : ℝ}
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {M M1 M2 M3 : Fin k → Finset (Fin 3 → ℤ)}
    (hMT : ∀ j, cubeSet s (M j) ⊆ tube r (z j) (w j))
    (hM32 : ∀ j, M3 j ⊆ M2 j) (hM21 : ∀ j, M2 j ⊆ M1 j) (hM1M : ∀ j, M1 j ⊆ M j)
    (hr : 0 < r) (hD : 0 < D) (h4rD : 4 * r ≤ D) (hβ : 16 * r / D < β)
    (hmax : ∀ m, (cubeLabels M m : ℝ) ≤ μmax) (hμ : 0 < μmax)
    (hcone : ∀ (m : Fin 3 → ℤ) (u : Space), ‖u‖ = 1 → ((Finset.univ.filter fun j =>
      m ∈ M2 j ∧ min ‖w j - u‖ ‖w j + u‖ ≤ β).card : ℝ) ≤ μlo / 2)
    (hlo : ∀ j m, m ∈ M3 j → μlo ≤ (cubeLabels M2 m : ℝ))
    (hP1 : ∀ j B, ((M1 j).filter fun m => blockOf N m = B).Nonempty →
      θ ≤ (((M1 j).filter fun m => blockOf N m = B).card : ℝ))
    (hP3 : ∀ j B, ((M3 j).filter fun m => blockOf N m = B).Nonempty →
      θ ≤ (((M3 j).filter fun m => blockOf N m = B).card : ℝ))
    (hθ : 0 ≤ θ) (hθb : 0 ≤ θb) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    {E1 : Set Space} (hE1 : MeasurableSet E1)
    (hbal : ∀ j, ∀ m ∈ M j, ENNReal.ofReal θb * volume (gridCube s m) ≤
      volume (lam • E1 ∩ gridCube s m))
    {q : Space} {j0 : Fin k} (hq : lam • q ∈ cubeSet s (M3 j0)) {u : Space} (hu : ‖u‖ = 1)
    (hplane : ∀ j, (cubeSet s (M1 j) ∩
      gridCube ((N : ℝ) * s) (blockOf N (cubeIndex s (lam • q)))).Nonempty →
      |inner ℝ (w j) u| ≤ π) :
    ENNReal.ofReal (θb * ((θ * s ^ 3) ^ 2 * μlo / (256 * (4 * (D + r) + r) * r ^ 2 * μmax))) ≤
      volume (E1 ∩ lam⁻¹ • (gridCube ((N : ℝ) * s) (blockOf N (cubeIndex s (lam • q))) ∩
        {y | |inner ℝ u (y - lam • q)| ≤ 2 * ((2 * ((N : ℝ) * s) + 2 * r) * π + 2 * r) + 2 * s})) := by
  set ω := (N : ℝ) * s with hω
  have hω0 : 0 < ω := mul_pos (by exact_mod_cast hN) hs
  set B := blockOf N (cubeIndex s (lam • q)) with hB
  set W := gridCube ω B with hW
  set x0 := lam • q with hx0
  set h := 2 * ((2 * ω + 2 * r) * π + 2 * r) with hh
  have hx0W : x0 ∈ W := gridCube_subset_block hs hN _ (mem_gridCube_cubeIndex hs x0)
  -- the fan lemma on the cube sets
  have hWb : Bornology.IsBounded W :=
    (isBounded_closedBall (x := x0) (r := 2 * ω)).subset fun y hy =>
      mem_closedBall.2 (dist_lt_of_mem_block hω0 hy hx0W)
  have hblockne : ∀ (P : Finset (Fin 3 → ℤ)), (cubeSet s P ∩ W).Nonempty →
      (P.filter fun m => blockOf N m = B).Nonempty := by
    intro P ⟨y, hy⟩
    rw [hW, cubeSet_inter_block hs hN] at hy
    obtain ⟨m, hm, -⟩ := mem_iUnion₂.1 hy
    exact ⟨m, hm⟩
  have hvolblock : ∀ (P : Finset (Fin 3 → ℤ)), volume (cubeSet s P ∩ W) =
      ((P.filter fun m => blockOf N m = B).card : ℝ≥0∞) * ENNReal.ofReal s ^ 3 := by
    intro P
    rw [hW, cubeSet_inter_block hs hN, volume_cubeSet hs]
  have hθvol : ∀ (P : Finset (Fin 3 → ℤ)), θ ≤ ((P.filter fun m => blockOf N m = B).card : ℝ) →
      ENNReal.ofReal (θ * s ^ 3) ≤ volume (cubeSet s P ∩ W) := by
    intro P hP
    rw [hvolblock, ← ENNReal.ofReal_pow hs.le, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hP (by positivity))
  have hfan := fan_volume_lower (k := k) (z := z) (w := w)
    (Y1 := fun j => cubeSet s (M1 j)) (Y2 := fun j => cubeSet s (M2 j))
    (Y3 := fun j => cubeSet s (M3 j)) (r := r) (D := D) (β := β) (π := π) (dW := 2 * ω)
    (μmax := μmax) (μlo := μlo) (θP := θ * s ^ 3) (u := u) (W := W) (j0 := j0) (x0 := x0)
    hr hD h4rD hβ hw hu (fun j => measurableSet_cubeSet s _)
    (fun j => (cubeSet_mono (hM1M j)).trans (hMT j)) (fun j => cubeSet_mono (hM21 j))
    (fun j => cubeSet_mono (hM32 j)) hWb (measurableSet_gridCube ω B)
    (fun y hy y' hy' => dist_lt_of_mem_block hω0 hy hy')
    (fun y => by
      rw [fineMult_cubeSet hs]
      refine le_trans ?_ (hmax (cubeIndex s y))
      exact_mod_cast Finset.card_le_card (fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hM1M j hj))
    (fun y _ hy3 => by
      rw [fineMult_cubeSet hs]
      exact hlo j0 _ ((mem_cubeSet hs).1 hy3))
    (fun y _ _ => by
      have e : {j | y ∈ cubeSet s (M2 j) ∧ min ‖w j - w j0‖ ‖w j + w j0‖ ≤ β} =
          ↑(Finset.univ.filter fun j => cubeIndex s y ∈ M2 j ∧
            min ‖w j - w j0‖ ‖w j + w j0‖ ≤ β) := by
        ext j; simp [mem_cubeSet hs]
      rw [e, Set.ncard_coe_finset]
      exact hcone (cubeIndex s y) (w j0) (hw j0))
    (fun j hne => hθvol (M1 j) (hP1 j B (hblockne (M1 j) hne)))
    (hθvol (M3 j0) (hP3 j0 B (hblockne (M3 j0) ⟨x0, hq, hx0W⟩)))
    (fun j hne => hplane j hne)
    ⟨hq, hx0W⟩ hμ (by positivity)
  -- transfer to the fine set by the balanced cover
  set A := (⋃ j, cubeSet s (M1 j)) ∩ (W ∩ {y | |inner ℝ u (y - x0)| ≤ h}) with hA
  set S := W ∩ {y | |inner ℝ u (y - x0)| ≤ h + 2 * s} with hS
  set T := (Finset.univ.biUnion M1).filter fun m => (gridCube s m ∩
    (W ∩ {y | |inner ℝ u (y - x0)| ≤ h})).Nonempty with hT
  have hTS : ∀ m ∈ T, gridCube s m ⊆ S := by
    intro m hm y hy
    obtain ⟨y', hy'm, hy'W, hy'h⟩ := (Finset.mem_filter.1 hm).2
    have hmB : blockOf N m = B := by
      have h1 := (mem_gridCube_iff hω0).1 hy'W
      rw [cubeIndex_mul hs hN, cubeIndex_eq_of_mem hs hy'm] at h1
      exact h1
    refine ⟨?_, ?_⟩
    · rw [hW, ← hmB]; exact gridCube_subset_block hs hN m hy
    · show |inner ℝ u (y - x0)| ≤ h + 2 * s
      have hd := diam_le_of_mem_gridCube hs hy hy'm
      have e : y - x0 = (y - y') + (y' - x0) := by abel
      rw [e, inner_add_right]
      have h1 : |inner ℝ u (y - y')| ≤ 2 * s := by
        calc |inner ℝ u (y - y')| ≤ ‖u‖ * ‖y - y'‖ := abs_real_inner_le_norm _ _
          _ ≤ 2 * s := by rw [hu, one_mul, ← dist_eq_norm]; exact hd.le
      calc |inner ℝ u (y - y') + inner ℝ u (y' - x0)| ≤ |inner ℝ u (y - y')| +
            |inner ℝ u (y' - x0)| := abs_add_le _ _
        _ ≤ 2 * s + h := add_le_add h1 hy'h
        _ = h + 2 * s := by ring
  have hAT : A ⊆ ⋃ m ∈ T, gridCube s m := by
    rintro y ⟨hy1, hyW, hyh⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hy1
    have hm := (mem_cubeSet hs).1 hj
    refine mem_iUnion₂.2 ⟨cubeIndex s y, Finset.mem_filter.2 ⟨Finset.mem_biUnion.2
      ⟨j, Finset.mem_univ _, hm⟩, y, mem_gridCube_cubeIndex hs y, hyW, hyh⟩,
      mem_gridCube_cubeIndex hs y⟩
  have hvolA : volume A ≤ (T.card : ℝ≥0∞) * ENNReal.ofReal (s ^ 3) := by
    calc volume A ≤ volume (⋃ m ∈ T, gridCube s m) := measure_mono hAT
      _ ≤ ∑ m ∈ T, volume (gridCube s m) := measure_biUnion_finset_le _ _
      _ = (T.card : ℝ≥0∞) * ENNReal.ofReal (s ^ 3) := by
          simp only [volume_gridCube hs, Finset.sum_const, nsmul_eq_mul,
            ENNReal.ofReal_pow hs.le]
  have hlamE : MeasurableSet (lam • E1) := hE1.const_smul₀ lam
  have hbalT : (T.card : ℝ≥0∞) * (ENNReal.ofReal θb * ENNReal.ofReal (s ^ 3)) ≤
      volume (lam • E1 ∩ S) := by
    calc (T.card : ℝ≥0∞) * (ENNReal.ofReal θb * ENNReal.ofReal (s ^ 3))
        = ∑ _m ∈ T, ENNReal.ofReal θb * volume (gridCube s _m) := by
          simp only [volume_gridCube hs, Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_pow hs.le]
      _ ≤ ∑ m ∈ T, volume (lam • E1 ∩ gridCube s m) := by
          apply Finset.sum_le_sum
          intro m hm
          obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (Finset.mem_filter.1 hm).1
          exact hbal j m (hM1M j hj)
      _ = volume (⋃ m ∈ T, lam • E1 ∩ gridCube s m) := by
          rw [measure_biUnion_finset]
          · intro m _ m' _ hmm
            exact (gridCube_disjoint hs hmm).mono inter_subset_right inter_subset_right
          · intro m _; exact hlamE.inter (measurableSet_gridCube s m)
      _ ≤ volume (lam • E1 ∩ S) := by
          apply measure_mono
          intro y hy
          obtain ⟨m, hm, hyE, hyQ⟩ := mem_iUnion₂.1 hy
          exact ⟨hyE, hTS m hm hyQ⟩
  have hfine : ENNReal.ofReal (θb * ((θ * s ^ 3) ^ 2 * μlo /
      (256 * (4 * (D + r) + r) * r ^ 2 * μmax))) ≤ volume (lam • E1 ∩ S) := by
    refine le_trans ?_ hbalT
    rw [ENNReal.ofReal_mul hθb]
    calc ENNReal.ofReal θb * ENNReal.ofReal ((θ * s ^ 3) ^ 2 * μlo /
          (256 * (4 * (D + r) + r) * r ^ 2 * μmax))
        ≤ ENNReal.ofReal θb * volume A := by gcongr
      _ ≤ ENNReal.ofReal θb * ((T.card : ℝ≥0∞) * ENNReal.ofReal (s ^ 3)) := by gcongr
      _ = (T.card : ℝ≥0∞) * (ENNReal.ofReal θb * ENNReal.ofReal (s ^ 3)) := by ring
  -- undo the contraction
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hset : E1 ∩ lam⁻¹ • S = lam⁻¹ • (lam • E1 ∩ S) := by
    ext y
    simp only [mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hlam0), inv_inv,
      Set.smul_mem_smul_set_iff₀ hlam0]
  change _ ≤ volume (E1 ∩ lam⁻¹ • S)
  rw [hset, Measure.addHaar_smul]
  have hge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal |lam⁻¹ ^ Module.finrank ℝ Space| := by
    rw [ENNReal.one_le_ofReal]
    rw [abs_of_nonneg (by positivity)]
    exact one_le_pow₀ (one_le_inv₀ hlam |>.2 hlam1)
  calc _ ≤ volume (lam • E1 ∩ S) := hfine
    _ = 1 * volume (lam • E1 ∩ S) := (one_mul _).symm
    _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
