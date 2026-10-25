-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Coefficient.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory Metric
open scoped ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Tube (δ : ℝ) (x v : Space) : Set Space := thickening δ (segment ℝ x (x + v))

noncomputable section

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι]

/-- Count the members of a finite family contained in a test set. -/
def count (T : ι → Set Space) (S : Finset ι) (U : Set Space) : ℕ :=
  (S.filter fun i => T i ⊆ U).card

lemma count_mono (T : ι → Set Space) {S R : Finset ι} (h : S ⊆ R) (U : Set Space) :
    count T S U ≤ count T R U :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma count_le_card (T : ι → Set Space) (S : Finset ι) (U : Set Space) :
    count T S U ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)

lemma count_eq_card (T : ι → Set Space) (S : Finset ι) (U : Set Space)
    (h : ∀ i ∈ S, T i ⊆ U) : count T S U = S.card := by
  classical
  unfold count
  rw [Finset.filter_eq_self.mpr h]

/-- The exact convex-count upper estimate, in the normalization of the obligation. -/
def Upper (T : ι → Set Space) (w : ℝ) (S : Finset ι) (c : ℝ) : Prop :=
  ∀ U : Set Space, Convex ℝ U →
    ENNReal.ofReal ((count T S U : ℝ) * w) ≤ ENNReal.ofReal c * volume U

lemma Upper.subset {T : ι → Set Space} {w c : ℝ} {S R : Finset ι}
    (h : Upper T w R c) (hw : 0 ≤ w) (hSR : S ⊆ R) : Upper T w S c := by
  intro U hU
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (count_mono T hSR U)) hw)).trans (h U hU)

lemma Upper.mono {T : ι → Set Space} {w c d : ℝ} {S : Finset ι}
    (h : Upper T w S c) (hcd : c ≤ d) : Upper T w S d := by
  intro U hU
  exact (h U hU).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcd) le_rfl)

/-- A density defined even for zero and infinite measure test sets. -/
def density (T : ι → Set Space) (w : ℝ) (S : Finset ι) (U : Set Space) : ℝ :=
  (count T S U : ℝ) * w / (volume U).toReal

/-- Flooring at one preserves the bound supplied by the theorem's m ≥ 1 hypothesis. -/
def coefficient (T : ι → Set Space) (w : ℝ) (S : Finset ι) : ℝ :=
  sSup (insert 1 {r : ℝ | ∃ U : Set Space, Convex ℝ U ∧ r = density T w S U})

lemma density_le {T : ι → Set Space} {w c : ℝ} {S : Finset ι}
    (hc : 0 ≤ c) (h : Upper T w S c) {U : Set Space} (hU : Convex ℝ U) :
    density T w S U ≤ c := by
  by_cases hzero : volume U = 0
  · simp [density, hzero, hc]
  by_cases htop : volume U = ⊤
  · simp [density, htop, hc]
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos hzero htop
  rw [density, div_le_iff₀ hvol]
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) (h U hU)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hreal
  by_cases hn : 0 ≤ (count T S U : ℝ) * w
  · simpa only [ENNReal.toReal_ofReal hn] using hreal
  · exact (le_of_not_ge hn).trans (mul_nonneg hc hvol.le)

lemma coefficient_bdd {T : ι → Set Space} {w c : ℝ} {S : Finset ι}
    (hc : 1 ≤ c) (h : Upper T w S c) :
    BddAbove (insert 1 {r : ℝ | ∃ U : Set Space, Convex ℝ U ∧ r = density T w S U}) := by
  refine ⟨c, ?_⟩
  rintro r (rfl | ⟨U, hU, rfl⟩)
  · exact hc
  · exact density_le (by linarith) h hU

lemma coefficient_le {T : ι → Set Space} {w c : ℝ} {S : Finset ι}
    (hc : 1 ≤ c) (h : Upper T w S c) : coefficient T w S ≤ c := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, hU, rfl⟩)
  · exact hc
  · exact density_le (by linarith) h hU

lemma one_le_coefficient {T : ι → Set Space} {w c : ℝ} {S : Finset ι}
    (hc : 1 ≤ c) (h : Upper T w S c) : 1 ≤ coefficient T w S :=
  le_csSup (coefficient_bdd hc h) (mem_insert _ _)

lemma density_le_coefficient {T : ι → Set Space} {w c : ℝ} {S : Finset ι}
    (hc : 1 ≤ c) (h : Upper T w S c) {U : Set Space} (hU : Convex ℝ U) :
    density T w S U ≤ coefficient T w S :=
  le_csSup (coefficient_bdd hc h) (mem_insert_of_mem _ ⟨U, hU, rfl⟩)

lemma coefficient_upper {T : ι → Set Space} {w c : ℝ} {S : Finset ι}
    (hw : 0 ≤ w) (hc : 1 ≤ c) (h : Upper T w S c) :
    Upper T w S (coefficient T w S) := by
  have hc1 := one_le_coefficient hc h
  have hc0 : 0 ≤ coefficient T w S := by linarith
  intro U hU
  by_cases hzero : volume U = 0
  · simpa [hzero] using h U hU
  by_cases htop : volume U = ⊤
  · simp [htop, ENNReal.ofReal_ne_zero_iff.mpr (by linarith : 0 < coefficient T w S)]
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos hzero htop
  have hd := density_le_coefficient hc h hU
  rw [density, div_le_iff₀ hvol] at hd
  calc
    ENNReal.ofReal ((count T S U : ℝ) * w) ≤
        ENNReal.ofReal (coefficient T w S * (volume U).toReal) := ENNReal.ofReal_le_ofReal hd
    _ = ENNReal.ofReal (coefficient T w S) * volume U := by
      rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal htop]

lemma coefficient_mono {T : ι → Set Space} {w c : ℝ} {S R : Finset ι}
    (hw : 0 ≤ w) (hc : 1 ≤ c) (h : Upper T w R c) (hSR : S ⊆ R) :
    coefficient T w S ≤ coefficient T w R :=
  coefficient_le (one_le_coefficient hc h) ((coefficient_upper hw hc h).subset hw hSR)

/-- If the coefficient is above its floor, some convex test set nearly attains it. -/
lemma exists_dense_test {T : ι → Set Space} {w c : ℝ} {S : Finset ι}
    (hw : 0 ≤ w) (hc : 1 ≤ c) (h : Upper T w S c)
    (hlarge : 2 < coefficient T w S) :
    ∃ U : Set Space, Convex ℝ U ∧ volume U ≠ ⊤ ∧
      coefficient T w S / 2 * (volume U).toReal < (count T S U : ℝ) * w := by
  have hn : ¬ Upper T w S (coefficient T w S / 2) := by
    intro hu
    have := coefficient_le (by linarith : 1 ≤ coefficient T w S / 2) hu
    linarith
  simp only [Upper, not_forall] at hn
  obtain ⟨U, hUconv, hU⟩ := hn
  have hlt := lt_of_not_ge hU
  have hpos : 0 < ENNReal.ofReal (coefficient T w S / 2) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  have htop : volume U ≠ ⊤ := by
    intro ht
    simp [ht, hpos.ne'] at hlt
  refine ⟨U, hUconv, htop, ?_⟩
  have hr := (ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) ENNReal.ofReal_ne_top).mpr hlt
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ coefficient T w S / 2),
    ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hw), ENNReal.toReal_ofReal hw] using hr

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
