-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.TwoScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Window
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSTheorem

/-!
# Shadings meeting a grid cube, from the two-scale decomposition

In the two-scale decomposition the contracted fine shadings lie in the coarse shadings, which are
unions of grid cubes of side `s`; a contracted grid cube meets at most `8` grid cubes, each in at
most `A` coarse shadings (coarse multiplicity), and each coarse tube carries at most `B`
nonempty fine shadings (balanced fibres). Hence at most `8 A B` fine shadings meet a grid cube.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal Pointwise

/-- The lower corner of a grid cube. -/
noncomputable def cubeCorner (s : ℝ) (e : Fin 3 → ℤ) : Space :=
  pt (s * e 0) (s * e 1) (s * e 2)

lemma cubeCorner_mem {s : ℝ} (hs : 0 < s) (e : Fin 3 → ℤ) :
    cubeCorner s e ∈ Coarse.gridCube s e := by
  intro c
  fin_cases c <;> simp [cubeCorner, pt] <;> linarith

/-- The cube index of a contracted point of a grid cube. -/
lemma cubeIndex_smul_mem {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1)
    {m : Fin 3 → ℤ} {p : Space} (hp : p ∈ Coarse.gridCube s m) (j : Fin 3) :
    Coarse.cubeIndex s (c • p) j = ⌊c * m j⌋ ∨ Coarse.cubeIndex s (c • p) j = ⌊c * m j⌋ + 1 := by
  obtain ⟨h1, h2⟩ := hp j
  have hq : (c • p) j = c * p j := by simp
  have hlo : c * m j ≤ (c • p) j / s := by
    rw [hq, le_div_iff₀ hs]; nlinarith
  have hhi : (c • p) j / s < c * m j + 1 := by
    rw [hq, div_lt_iff₀ hs]; nlinarith
  simp only [Coarse.cubeIndex]
  have a1 : ⌊c * m j⌋ ≤ ⌊(c • p) j / s⌋ := Int.floor_mono hlo
  have a2 : ⌊(c • p) j / s⌋ ≤ ⌊c * m j⌋ + 1 := by
    have : (c • p) j / s < (⌊c * m j⌋ : ℝ) + 2 := by
      have := Int.lt_floor_add_one (c * m j)
      linarith
    have h3 : ⌊(c • p) j / s⌋ < ⌊c * m j⌋ + 2 := by
      rw [Int.floor_lt]; push_cast; exact this
    omega
  omega

/-- The possible cube indices of the contracted points of a grid cube. -/
lemma exists_index_finset {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1) (m : Fin 3 → ℤ) :
    ∃ T : Finset (Fin 3 → ℤ), T.card ≤ 8 ∧
      ∀ p ∈ Coarse.gridCube s m, Coarse.cubeIndex s (c • p) ∈ T := by
  classical
  refine ⟨(Finset.univ : Finset (Fin 3 → Fin 2)).image
    (fun t => fun j => ⌊c * m j⌋ + (t j : ℤ)), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp
  · intro p hp
    refine Finset.mem_image.mpr ⟨fun j => if Coarse.cubeIndex s (c • p) j = ⌊c * m j⌋ then 0 else 1,
      Finset.mem_univ _, ?_⟩
    funext j
    rcases cubeIndex_smul_mem hs hc hc1 hp j with h | h
    · simp [h]
    · have hne : Coarse.cubeIndex s (c • p) j ≠ ⌊c * m j⌋ := by omega
      simp [hne, h]

/-- The coarse tubes whose shading contains a given point, as a finset. -/
lemma exists_tubes_finset {k : ℕ} (Yt : Fin k → Set Space) (q : Space) :
    ∃ J : Finset (Fin k), (J.card : ℕ) = Coarse.fineMult Yt q ∧ ∀ j, q ∈ Yt j → j ∈ J := by
  classical
  refine ⟨Finset.univ.filter fun j => q ∈ Yt j, ?_, fun j hj => by simp [hj]⟩
  unfold Coarse.fineMult
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j; simp

/-- The nonempty fine shadings of a coarse tube, as a finset. -/
lemma exists_fibre_finset {n k : ℕ} (Y' : Fin n → Set Space) (a : Fin n → Fin k) (j : Fin k) :
    ∃ F : Finset (Fin n), (F.card : ℕ) = {i | a i = j ∧ (Y' i).Nonempty}.ncard ∧
      ∀ i, a i = j → (Y' i).Nonempty → i ∈ F := by
  classical
  refine ⟨Finset.univ.filter fun i => a i = j ∧ (Y' i).Nonempty, ?_,
    fun i h1 h2 => by simp [h1, h2]⟩
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i; simp

/-- At most `8 A B` fine shadings meet a grid cube. -/
theorem card_meeting_cube_le {n k : ℕ} {Y' : Fin n → Set Space} {Yt : Fin k → Set Space}
    {a : Fin n → Fin k} {s c A B : ℝ} {M : Fin k → Finset (Fin 3 → ℤ)}
    (hs : 0 < s) (hc : 0 < c) (hc1 : c ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcov : ∀ i, c • Y' i ⊆ Yt (a i))
    (hgrid : ∀ j, Yt j = ⋃ m ∈ M j, Coarse.gridCube s m)
    (hcm : ∀ q, (Coarse.fineMult Yt q : ℝ) ≤ A)
    (hbal : ∀ j, (({i | a i = j ∧ (Y' i).Nonempty}.ncard : ℕ) : ℝ) ≤ B)
    (m : Fin 3 → ℤ) :
    (({i | (Y' i ∩ Coarse.gridCube s m).Nonempty}.ncard : ℕ) : ℝ) ≤ 8 * A * B := by
  classical
  obtain ⟨T, hTc, hT⟩ := exists_index_finset hs hc hc1 m
  choose J hJc hJ using fun e => exists_tubes_finset Yt (cubeCorner s e)
  choose F hFc hF using fun j => exists_fibre_finset Y' a j
  have hsub : {i | (Y' i ∩ Coarse.gridCube s m).Nonempty} ⊆
      ((T.biUnion fun e => (J e).biUnion F : Finset (Fin n)) : Set (Fin n)) := by
    intro i hi
    obtain ⟨p, hpY, hpQ⟩ := hi
    have hq : c • p ∈ Yt (a i) := hcov i ⟨p, hpY, rfl⟩
    have he := hT p hpQ
    have hcube : Coarse.gridCube s (Coarse.cubeIndex s (c • p)) ⊆ Yt (a i) := by
      rw [hgrid] at hq ⊢
      obtain ⟨m', hm', hqm'⟩ := mem_iUnion₂.mp hq
      rw [Coarse.cubeIndex_eq_of_mem hs hqm']
      exact subset_iUnion₂ (s := fun m'' _ => Coarse.gridCube s m'') m' hm'
    have haJ := hJ _ (a i) (hcube (cubeCorner_mem hs _))
    simp only [Finset.coe_biUnion, mem_iUnion, Finset.mem_coe]
    exact ⟨_, he, a i, haJ, hF (a i) i rfl ⟨p, hpY⟩⟩
  calc (({i | (Y' i ∩ Coarse.gridCube s m).Nonempty}.ncard : ℕ) : ℝ)
      ≤ ((T.biUnion fun e => (J e).biUnion F).card : ℝ) := by
        rw [← Set.ncard_coe_finset]
        exact_mod_cast Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ ∑ e ∈ T, (((J e).biUnion F).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ e ∈ T, ∑ j ∈ J e, ((F j).card : ℝ) := by
        apply Finset.sum_le_sum
        intro e _
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ T, A * B := by
        apply Finset.sum_le_sum
        intro e _
        calc ∑ j ∈ J e, ((F j).card : ℝ) ≤ ∑ _j ∈ J e, B := by
              apply Finset.sum_le_sum
              intro j _
              rw [hFc j]; exact hbal j
          _ = (J e).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ A * B := by
              apply mul_le_mul_of_nonneg_right _ hB
              rw [hJc e]; exact hcm _
    _ = T.card * (A * B) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 8 * (A * B) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA hB)
        exact_mod_cast hTc
    _ = 8 * A * B := by ring

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
