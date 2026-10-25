-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.StrongPlaneMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.ParityCubes
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.WeakPlaneMap

/-!
# Strong plane map at the coarse scale (sticky Lemma 4.4)

`strong_plane_map`: from a fine plane map of precision `ρc / 2`, fine directions within `ρc / 2`
of their coarse tubes, coarse shadings that are unions of grid cubes each meeting the contracted
shading of a tube of its fibre, and the multiplicity bounds of the two-scale structure (fine lower
bound `A`, fibre bound `B`, coarse bound `Cc`), the coarse family gets a measurable plane map of
precision `ρc`, constant on grid cubes, on refined coarse shadings keeping a fraction
`A / (B Cc)` of the coarse incidence at every point.
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

theorem measurable_cubeIndex {s : ℝ} : Measurable (cubeIndex s) := by
  refine measurable_pi_iff.2 fun j => ?_
  have h : Measurable fun p : Space => p j / s := by fun_prop
  exact (Int.measurable_floor (R := ℝ)).comp h

/-- The inner product with a unit vector changes by at most the distance of the directions,
up to sign. -/
theorem abs_inner_le_of_dir {u w V : Space} (hV : ‖V‖ = 1) :
    |inner ℝ w V| ≤ |inner ℝ u V| + min ‖w - u‖ ‖w + u‖ := by
  rcases le_total ‖w - u‖ ‖w + u‖ with h | h
  · rw [min_eq_left h]
    have : inner ℝ w V = inner ℝ u V + inner ℝ (w - u) V := by rw [inner_sub_left]; ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    have := abs_real_inner_le_norm (w - u) V
    rwa [hV, mul_one] at this
  · rw [min_eq_right h]
    have : inner ℝ w V = -inner ℝ u V + inner ℝ (w + u) V := by rw [inner_add_left]; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    refine add_le_add le_rfl ?_
    have := abs_real_inner_le_norm (w + u) V
    rwa [hV, mul_one] at this


theorem mem_iUnion_gridCube_iff {s : ℝ} (hs : 0 < s) (S : Finset (Fin 3 → ℤ)) (q : Space) :
    q ∈ (⋃ m ∈ S, gridCube s m) ↔ cubeIndex s q ∈ S := by
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, hq⟩; rwa [cubeIndex_eq_of_mem hs hq]
  · intro h; exact ⟨_, h, mem_gridCube_cubeIndex hs q⟩

/-- **Strong plane map at the coarse scale** (sticky Lemma 4.4).  The coarse shadings are unions
of grid cubes; each cube gets the value of the fine plane map at a representative fine point, and
the cubes whose representative lies on a tube of the fibre are kept. -/
theorem strong_plane_map {n k : ℕ} {v : Fin n → Space} {Y' : Fin n → Set Space}
    {w : Fin k → Space} {Yt : Fin k → Set Space} {a : Fin n → Fin k} {s ρc lam A B Cc : ℝ}
    (hs : 0 < s) {M : Fin k → Finset (Fin 3 → ℤ)}
    (hYt : ∀ j, Yt j = ⋃ m ∈ M j, gridCube s m)
    (hcontr : ∀ i, lam • Y' i ⊆ Yt (a i))
    (hmeet : ∀ j, ∀ m ∈ M j, ∃ i, a i = j ∧ ∃ p ∈ Y' i, lam • p ∈ gridCube s m)
    (hdir : ∀ i, (Y' i).Nonempty → min ‖w (a i) - v i‖ ‖w (a i) + v i‖ ≤ ρc / 2)
    (hfine : ∀ p ∈ ⋃ i, Y' i, A ≤ incidence Y' p)
    (hfibre : ∀ j p, ({i | a i = j ∧ p ∈ Y' i}.ncard : ℝ) ≤ B)
    (hcoarse : ∀ q, incidence Yt q ≤ Cc)
    (V : Space → Space) (hVm : Measurable V) (hVu : ∀ p ∈ ⋃ i, Y' i, ‖V p‖ = 1)
    (hVp : ∀ i p, p ∈ Y' i → |inner ℝ (v i) (V p)| ≤ ρc / 2)
    (hA : 0 ≤ A) (hB : 0 < B) (hC : 0 < Cc) :
    ∃ (Yt'' : Fin k → Set Space) (Vt : Space → Space),
      (∀ j, Yt'' j ⊆ Yt j) ∧ (∀ j, MeasurableSet (Yt'' j)) ∧
      (∀ q, A / (B * Cc) * incidence Yt q ≤ incidence Yt'' q) ∧ Measurable Vt ∧
      (∀ q ∈ ⋃ j, Yt'' j, ‖Vt q‖ = 1) ∧
      (∀ j q, q ∈ Yt'' j → |inner ℝ (w j) (Vt q)| ≤ ρc) ∧
      (∀ q q', cubeIndex s q = cubeIndex s q' → Vt q = Vt q') := by
  classical
  -- representatives of the cubes
  let rep : (Fin 3 → ℤ) → Space := fun m =>
    if h : ∃ p, (∃ i, p ∈ Y' i) ∧ lam • p ∈ gridCube s m then h.choose else 0
  have hrep : ∀ m, (∃ p, (∃ i, p ∈ Y' i) ∧ lam • p ∈ gridCube s m) →
      (∃ i, rep m ∈ Y' i) ∧ lam • rep m ∈ gridCube s m := by
    intro m h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  let good : Fin k → (Fin 3 → ℤ) → Prop := fun j m => ∃ i, a i = j ∧ rep m ∈ Y' i
  let Yt'' : Fin k → Set Space := fun j => ⋃ m ∈ (M j).filter (good j), gridCube s m
  let Vt : Space → Space := fun q => V (rep (cubeIndex s q))
  -- membership in kept cubes
  have hmem'' : ∀ j q, q ∈ Yt'' j ↔ cubeIndex s q ∈ M j ∧ good j (cubeIndex s q) := by
    intro j q
    rw [show Yt'' j = ⋃ m ∈ (M j).filter (good j), gridCube s m from rfl,
      mem_iUnion_gridCube_iff hs, Finset.mem_filter]
  have hmemt : ∀ j q, q ∈ Yt j ↔ cubeIndex s q ∈ M j := by
    intro j q
    rw [hYt j, mem_iUnion_gridCube_iff hs]
  -- a good tube's cube is a cube of its coarse shading
  have hgoodM : ∀ m j, (∃ p, (∃ i, p ∈ Y' i) ∧ lam • p ∈ gridCube s m) → good j m → m ∈ M j := by
    intro m j hex hg
    obtain ⟨i, hij, hi⟩ := hg
    have h1 := hcontr i (Set.smul_mem_smul_set hi)
    rw [hij, hmemt] at h1
    rwa [cubeIndex_eq_of_mem hs (hrep m hex).2] at h1
  refine ⟨Yt'', Vt, ?_, ?_, ?_, ?_, ?_, ?_, fun q q' h => by simp only [Vt, h]⟩
  · intro j q hq
    rw [hmem''] at hq
    rw [hmemt]; exact hq.1
  · intro j
    exact Finset.measurableSet_biUnion _ fun m _ => measurableSet_gridCube s m
  · intro q
    set m := cubeIndex s q with hm
    by_cases hM : ∃ j, m ∈ M j
    · obtain ⟨j₀, hj₀⟩ := hM
      obtain ⟨i₀, _, p₀, hp₀, hlp₀⟩ := hmeet j₀ m hj₀
      have hex : ∃ p, (∃ i, p ∈ Y' i) ∧ lam • p ∈ gridCube s m := ⟨p₀, ⟨i₀, hp₀⟩, hlp₀⟩
      obtain ⟨⟨i₁, hi₁⟩, _⟩ := hrep m hex
      -- the good coarse tubes
      set G := Finset.univ.filter fun j => good j m with hG
      have hinc'' : incidence Yt'' q = (G.card : ℝ) := by
        rw [incidence_eq_ncard, ← Set.ncard_coe_finset]
        congr 2
        ext j
        rw [mem_ofPred_eq, Finset.mem_coe, hG, Finset.mem_filter, hmem'']
        exact ⟨fun h => ⟨Finset.mem_univ _, h.2⟩, fun h => ⟨hgoodM m j hex h.2, h.2⟩⟩
      have hAG : A ≤ B * G.card := by
        have h1 := hfine (rep m) (mem_iUnion.2 ⟨i₁, hi₁⟩)
        rw [incidence_eq_card_through] at h1
        have hsplit : (through Y' (rep m)).card =
            ∑ j ∈ G, ((through Y' (rep m)).filter fun i => a i = j).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := a) (t := G)]
          intro i hi
          rw [Finset.mem_coe, mem_through] at hi
          rw [Finset.mem_coe, hG, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, i, rfl, hi⟩
        have hfib : ∀ j, (((through Y' (rep m)).filter fun i => a i = j).card : ℝ) ≤ B := by
          intro j
          refine le_trans (le_of_eq ?_) (hfibre j (rep m))
          rw [← Set.ncard_coe_finset]
          congr 2
          ext i
          rw [Finset.coe_filter, mem_ofPred_eq, mem_ofPred_eq, mem_through, and_comm]
        rw [hsplit, Nat.cast_sum] at h1
        calc A ≤ ∑ j ∈ G, (((through Y' (rep m)).filter fun i => a i = j).card : ℝ) := h1
          _ ≤ ∑ _j ∈ G, B := Finset.sum_le_sum fun j _ => hfib j
          _ = B * G.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hcq := hcoarse q
      have hinc0 := incidence_nonneg Yt q
      rw [hinc'']
      calc A / (B * Cc) * incidence Yt q ≤ A / (B * Cc) * Cc := by
            exact mul_le_mul_of_nonneg_left hcq (div_nonneg hA (by positivity))
        _ = A / B := by field_simp
        _ ≤ G.card := by rw [div_le_iff₀ hB]; linarith
    · push Not at hM
      have h0 : incidence Yt q = 0 := by
        rw [incidence_eq_ncard]
        have : {j | q ∈ Yt j} = ∅ := by
          ext j; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, hmemt]; exact hM j
        rw [this, Set.ncard_empty, Nat.cast_zero]
      rw [h0, mul_zero]
      exact incidence_nonneg _ _
  · exact hVm.comp ((measurable_of_countable rep).comp measurable_cubeIndex)
  · intro q hq
    obtain ⟨j, hj⟩ := mem_iUnion.1 hq
    obtain ⟨_, i, _, hi⟩ := (hmem'' j q).1 hj
    exact hVu _ (mem_iUnion.2 ⟨i, hi⟩)
  · intro j q hq
    obtain ⟨_, i, hij, hi⟩ := (hmem'' j q).1 hq
    have hd := hdir i ⟨_, hi⟩
    rw [hij] at hd
    have hu := hVu _ (mem_iUnion.2 ⟨i, hi⟩)
    calc |inner ℝ (w j) (Vt q)| ≤ |inner ℝ (v i) (Vt q)| + min ‖w j - v i‖ ‖w j + v i‖ :=
          abs_inner_le_of_dir hu
      _ ≤ ρc / 2 + ρc / 2 := add_le_add (hVp i _ hi) hd
      _ = ρc := by ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
