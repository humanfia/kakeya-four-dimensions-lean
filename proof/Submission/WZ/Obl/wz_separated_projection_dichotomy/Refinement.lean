-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

section Refinement

variable {X I : Type*} [Fintype I] [DecidableEq I]
variable {Y : I → Type*} [∀ i, DecidableEq (Y i)]

/-- Simultaneous removal of small fibers. The budget for each family of fibers is
its threshold times the number of labels appearing in the original finite set.
This is the finite hypergraph refinement used in Section 8.1.1. -/
theorem exists_dense_fiber_refinement (H : Finset X) (f : ∀ i, X → Y i)
    (t : I → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∃ S ⊆ H,
      (H.card : ℝ) - ∑ i, t i * ((H.image (f i)).card : ℝ) ≤ (S.card : ℝ) ∧
      ∀ i x, x ∈ S → t i ≤ ((S.filter (fun y => f i y = f i x)).card : ℝ) := by
  classical
  let cost (S : Finset X) : ℝ := ∑ i, t i * ((S.image (f i)).card : ℝ)
  let score (S : Finset X) : ℝ := (S.card : ℝ) - cost S
  obtain ⟨S, hSH, hmax⟩ := H.powerset.exists_max_image score ⟨∅, by simp⟩
  have hSH' : S ⊆ H := Finset.mem_powerset.mp hSH
  have hcost : 0 ≤ cost S := Finset.sum_nonneg fun i _ => mul_nonneg (ht i) (Nat.cast_nonneg _)
  refine ⟨S, hSH', ?_, ?_⟩
  · have hm := hmax H (by simp)
    change score H ≤ score S at hm
    dsimp [score, cost] at hm hcost ⊢
    linarith
  · intro i x hx
    by_contra hsmall
    have hsmall' : ((S.filter (fun y => f i y = f i x)).card : ℝ) < t i :=
      lt_of_not_ge hsmall
    let R := S.filter (fun y => f i y ≠ f i x)
    have hRS : R ⊆ S := Finset.filter_subset _ _
    have hRH : R ⊆ H := hRS.trans hSH'
    have hmaxR : score R ≤ score S := hmax R (Finset.mem_powerset.mpr hRH)
    have himage : R.image (f i) = (S.image (f i)).erase (f i x) := by
      ext a
      simp only [R, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨y, ⟨hy, hne⟩, rfl⟩
        exact ⟨hne, y, hy, rfl⟩
      · rintro ⟨ha, y, hy, rfl⟩
        exact ⟨y, ⟨hy, ha⟩, rfl⟩
    have hximage : f i x ∈ S.image (f i) := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hcardi : ((R.image (f i)).card : ℝ) + 1 = ((S.image (f i)).card : ℝ) := by
      rw [himage]
      exact_mod_cast Finset.card_erase_add_one hximage
    have hcostloss : cost R + t i ≤ cost S := by
      have hother :
          ∑ j ∈ Finset.univ.erase i, t j * ((R.image (f j)).card : ℝ) ≤
            ∑ j ∈ Finset.univ.erase i, t j * ((S.image (f j)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (ht j)
        exact_mod_cast Finset.card_le_card (Finset.image_subset_image hRS)
      dsimp [cost]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      nlinarith
    have hcards : (R.card : ℝ) +
        ((S.filter (fun y => f i y = f i x)).card : ℝ) = (S.card : ℝ) := by
      have hc : R.card + (S.filter (fun y => f i y = f i x)).card = S.card := by
        simpa only [R, not_not] using
          Finset.card_filter_add_card_filter_not (s := S) (fun y => f i y ≠ f i x)
      exact_mod_cast hc
    dsimp [score] at hmaxR
    linarith

end Refinement

section RelativeRefinement

variable {X I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
variable {Y : I → Type*} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]

/-- A normalized version of simultaneous fiber pruning. There is one budget of
`ε * |H| / |I|` for each family of projections. -/
theorem exists_relative_fiber_refinement (H : Finset X) (f : ∀ i, X → Y i)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ S ⊆ H, (1 - ε) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
      ∀ i x, x ∈ S → ε * (H.card : ℝ) ≤
        (Fintype.card I : ℝ) * (Fintype.card (Y i) : ℝ) *
          ((S.filter (fun y => f i y = f i x)).card : ℝ) := by
  classical
  by_cases hH : H = ∅
  · subst hH
    exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hH
  have hY (i : I) : 0 < Fintype.card (Y i) :=
    Fintype.card_pos_iff.mpr ⟨f i x₀⟩
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  let t (i : I) : ℝ := ε * H.card / ((Fintype.card I : ℝ) * Fintype.card (Y i))
  have ht : ∀ i, 0 ≤ t i := fun i => by dsimp [t]; positivity
  have hden (i : I) : (0 : ℝ) < (Fintype.card I : ℝ) * Fintype.card (Y i) := by
    exact mul_pos hI (by exact_mod_cast hY i)
  obtain ⟨S, hSH, hcard, hfiber⟩ := exists_dense_fiber_refinement H f t ht
  have hbudget : ∑ i, t i * ((H.image (f i)).card : ℝ) ≤ ε * (H.card : ℝ) := by
    calc
      ∑ i, t i * ((H.image (f i)).card : ℝ)
          ≤ ∑ i, t i * (Fintype.card (Y i) : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_univ _) (ht i)
      _ = ∑ _ : I, ε * (H.card : ℝ) / (Fintype.card I : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hYi : (Fintype.card (Y i) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hY i)
        dsimp [t]
        field_simp
      _ = ε * (H.card : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  refine ⟨S, hSH, by nlinarith, ?_⟩
  intro i x hx
  have hf := hfiber i x hx
  dsimp [t] at hf
  have h := (div_le_iff₀ (hden i)).mp hf
  nlinarith

end RelativeRefinement

end WangZahlLot.Obl.wz_separated_projection_dichotomy
