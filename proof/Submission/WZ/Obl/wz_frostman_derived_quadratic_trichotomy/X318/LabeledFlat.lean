-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LabeledFlat.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CoverCounts
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.PrismAdjacency

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file LabeledFlat.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

/-- Assemble the flat conclusion from parentwise KT control when geometric
adjacency cannot cross parent labels.  The global Frostman estimate is inherited
from the input through the balanced cover. -/
theorem flat_prisms_of_labeled_cover {I : Type*} {n p : ℕ}
    (A : Fin n → Set Space) (P : Fin p → Set Space)
    (c e₁ e₂ e₃ : Fin p → Space) (label : Fin p → I)
    {δ ζ₂ ζ₃ a b K L D M : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b)
    (hflat : a ≤ δ ^ (ζ₂ / 200) * b) (hb1 : b ≤ 1)
    (hn : 0 < n) (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (herrorL : L ≤ δ ^ (-ζ₃)) (herrorM : M ≤ δ ^ (-ζ₃))
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
    (hlabel : ∀ j j', P j' ⊆ Metric.thickening b (P j) → label j = label j')
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
    have hcount : ncard {j' | P j' ⊆ Metric.thickening b (P j) ∧ P j' ⊆ U} ≤
        ncard {j' | label j' = label j ∧ P j' ⊆ U} :=
      Set.ncard_le_ncard (fun j' h => ⟨(hlabel j j' h.1).symm, h.2⟩)
    have hvol : volume (P j) = ENNReal.ofReal (8 * a * b) := by
      rw [hP j]
      exact prism_volume ha hb _ _ _ _ (he j)
    rw [hvol]
    calc
      _ ≤ ENNReal.ofReal (ncard {j' | label j' = label j ∧ P j' ⊆ U} : ℝ) *
          ENNReal.ofReal (8 * a * b) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hcount)) le_rfl
      _ ≤ ENNReal.ofReal M * volume U := hparent (label j) U hU
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal herrorM) le_rfl
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
