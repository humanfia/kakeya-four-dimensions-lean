-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ParentAdjacency.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LabeledFlat

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file ParentAdjacency.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

/-- Parentwise KT estimates add over the bounded set of labels that can occur
in a geometric neighborhood.  The parent labels need not be unique there. -/
theorem kt_in_region_of_bounded_parent_labels {I : Type*} {p : ℕ}
    (P : Fin p → Set Space) (label : Fin p → I) (B : Set Space) (S : Finset I)
    {D M : ℝ} {V : ENNReal} (hM : 0 ≤ M)
    (hdegree : (S.card : ℝ) ≤ D)
    (hlabel : ∀ j, P j ⊆ B → label j ∈ S)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal (ncard {j | label j = l ∧ P j ⊆ U} : ℝ) * V ≤
        ENNReal.ofReal M * volume U) :
    ∀ U, Convex ℝ U →
      ENNReal.ofReal (ncard {j | P j ⊆ B ∧ P j ⊆ U} : ℝ) * V ≤
        ENNReal.ofReal (D * M) * volume U := by
  classical
  intro U hU
  let N : ℕ := ncard {j | P j ⊆ B ∧ P j ⊆ U}
  let F : I → ℕ := fun l => ncard {j' | label j' = l ∧ P j' ⊆ U}
  have hcount : N ≤ ∑ l ∈ S, F l := by
    have hsub : {j' | P j' ⊆ B ∧ P j' ⊆ U} ⊆
        ⋃ l ∈ S, {j' | label j' = l ∧ P j' ⊆ U} := by
      intro j' hj'
      exact mem_iUnion.mpr ⟨label j', mem_iUnion.mpr
        ⟨hlabel j' hj'.1, rfl, hj'.2⟩⟩
    exact (Set.ncard_le_ncard hsub).trans
      (S.set_ncard_biUnion_le fun l => {j' | label j' = l ∧ P j' ⊆ U})
  have hcount' : (N : ENNReal) ≤ ∑ l ∈ S, (F l : ENNReal) := by
    exact_mod_cast hcount
  change ENNReal.ofReal (N : ℝ) * V ≤ _
  calc
    _ = (N : ENNReal) * V := by rw [ENNReal.ofReal_natCast]
    _ ≤ (∑ l ∈ S, (F l : ENNReal)) * V := mul_le_mul' hcount' le_rfl
    _ = ∑ l ∈ S, (F l : ENNReal) * V := Finset.sum_mul _ _ _
    _ ≤ ∑ _l ∈ S, ENNReal.ofReal M * volume U := by
      apply Finset.sum_le_sum
      intro l hl
      simpa only [F, ENNReal.ofReal_natCast] using hparent l U hU
    _ = (S.card : ENNReal) * (ENNReal.ofReal M * volume U) := by simp
    _ = ENNReal.ofReal ((S.card : ℝ) * M) * volume U := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hdegree hM)) le_rfl

theorem local_kt_of_bounded_parent_labels {I : Type*} {p : ℕ}
    (P : Fin p → Set Space) (label : Fin p → I) (neighbors : Fin p → Finset I)
    {b D M : ℝ} {V : ENNReal} (hM : 0 ≤ M)
    (hdegree : ∀ j, ((neighbors j).card : ℝ) ≤ D)
    (hlabel : ∀ j j', P j' ⊆ Metric.thickening b (P j) → label j' ∈ neighbors j)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal (ncard {j | label j = l ∧ P j ⊆ U} : ℝ) * V ≤
        ENNReal.ofReal M * volume U) :
    ∀ j U, Convex ℝ U →
      ENNReal.ofReal (ncard {j' | P j' ⊆ Metric.thickening b (P j) ∧ P j' ⊆ U} : ℝ) * V ≤
        ENNReal.ofReal (D * M) * volume U := by
  intro j
  exact kt_in_region_of_bounded_parent_labels P label (Metric.thickening b (P j)) (neighbors j)
    hM (hdegree j) (hlabel j) hparent

/-- The flat exit allowing a bounded number of neighboring parent families. -/
theorem flat_prisms_of_bounded_parent_cover {I : Type*} {n p : ℕ}
    (A : Fin n → Set Space) (P : Fin p → Set Space)
    (c e₁ e₂ e₃ : Fin p → Space) (label : Fin p → I) (neighbors : Fin p → Finset I)
    {δ ζ₂ ζ₃ a b K L D E M : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b)
    (hflat : a ≤ δ ^ (ζ₂ / 200) * b) (hb1 : b ≤ 1)
    (hn : 0 < n) (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (herrorL : L ≤ δ ^ (-ζ₃)) (herrorM : E * M ≤ δ ^ (-ζ₃))
    (herrorF : K * L * D ≤ δ ^ (-ζ₃))
    (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (hP : ∀ j, P j = Prism a b (c j) (e₁ j) (e₂ j) (e₃ j))
    (hF : Frostman K A)
    (hcover : ∀ i, ∃ j, A i ⊆ P j)
    (hbalance : ∀ j j', (contained A (P j) : ℝ) ≤ L * contained A (P j'))
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hbelow : ∀ j U, Convex ℝ U →
      ENNReal.ofReal (ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * volume (P j) ≤
        ENNReal.ofReal (L * contained A (P j)) * volume U)
    (hneighbors : ∀ j, ((neighbors j).card : ℝ) ≤ E)
    (hlabel : ∀ j j', P j' ⊆ Metric.thickening b (P j) → label j' ∈ neighbors j)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal (ncard {j | label j = l ∧ P j ⊆ U} : ℝ) *
        ENNReal.ofReal (8 * a * b) ≤ ENNReal.ofReal M * volume U) :
    FlatPrisms ζ₂ ζ₃ δ A := by
  have ha : 0 ≤ a := hδ.le.trans hδa
  have hb : 0 ≤ b := ha.trans hab
  have hFP : Frostman (δ ^ (-ζ₃)) P :=
    (frostman_of_balanced_cover A P hn hK hL hD hF hcover hbalance hdegree).mono herrorF
  have hbal (j j') : (contained A (P j) : ℝ) ≤
      δ ^ (-ζ₃) * contained A (P j') :=
    (hbalance j j').trans (mul_le_mul_of_nonneg_right herrorL (Nat.cast_nonneg _))
  have hlocal (j) (U : Set Space) (hU : Convex ℝ U) :
      ENNReal.ofReal (ncard {j' | P j' ⊆ Metric.thickening b (P j) ∧ P j' ⊆ U} : ℝ) *
        volume (P j) ≤ ENNReal.ofReal (δ ^ (-ζ₃)) * volume U := by
    have hvol : volume (P j) = ENNReal.ofReal (8 * a * b) := by
      rw [hP j]
      exact prism_volume ha hb _ _ _ _ (he j)
    rw [hvol]
    exact (local_kt_of_bounded_parent_labels P label neighbors hM hneighbors hlabel hparent j U hU).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal herrorM) le_rfl)
  have hbelow' (j) (U : Set Space) (hU : Convex ℝ U) :
      ENNReal.ofReal (ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * volume (P j) ≤
        ENNReal.ofReal (δ ^ (-ζ₃) * contained A (P j)) * volume U :=
    (hbelow j U hU).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right herrorL (Nat.cast_nonneg _))) le_rfl)
  refine ⟨a, b, hδa, hflat, hb1, p, c, e₁, e₂, e₃, he, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← hP] using hcover
  · simpa only [← hP, contained] using hbal
  · simpa only [← hP] using hFP
  · simpa only [← hP, contained] using hbelow'
  · simpa only [← hP] using hlocal

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
