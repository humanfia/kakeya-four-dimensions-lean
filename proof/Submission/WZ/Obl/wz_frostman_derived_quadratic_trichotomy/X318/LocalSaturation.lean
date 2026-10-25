-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalSaturation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ParentContributors
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Saturation

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file LocalSaturation.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization
  (Upper count ncard_fintype incidence_sum cancel_scaled_measure)

attribute [local instance] Classical.propDecidable

/-- Count only the incidences belonging to a specified parent label. -/
lemma labeled_cover_incidence_le {n p q : ℕ}
    (A : Fin n → Set Space) (P : Fin p → Set Space) (R : Fin q → Set Space)
    (label : Fin p → Fin q) {D : ℝ}
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D) (l : Fin q) (U : Set Space) :
    (∑ j ∈ Finset.univ.filter (fun j => label j = l ∧ P j ⊆ U),
      (ncard {i | A i ⊆ R (label j) ∧ A i ⊆ P j} : ℝ)) ≤
        D * (ncard {i | A i ⊆ R l ∧ A i ⊆ U} : ℝ) := by
  classical
  let I := Finset.univ.filter fun i => A i ⊆ R l ∧ A i ⊆ U
  let J := Finset.univ.filter fun j => label j = l ∧ P j ⊆ U
  have hcount (j) (hj : j ∈ J) :
      (I.filter fun i => A i ⊆ P j).card = ncard {i | A i ⊆ R (label j) ∧ A i ⊆ P j} := by
    obtain ⟨hlabel, hPU⟩ := (Finset.mem_filter.mp hj).2
    rw [ncard_fintype, hlabel]
    congr 1
    ext i
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hPU⟩, h.2⟩⟩
  calc
    _ = ∑ j ∈ J, ((I.filter fun i => A i ⊆ P j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcount j hj]
    _ = ∑ i ∈ I, ((J.filter fun j => A i ⊆ P j).card : ℝ) := by
      exact_mod_cast (incidence_sum I J (fun i j => A i ⊆ P j)).symm
    _ ≤ ∑ _i ∈ I, D := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := hdegree i
      rw [ncard_fintype] at hh
      exact (Nat.cast_le.mpr (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_univ J)))).trans hh
    _ = _ := by
      rw [ncard_fintype]
      simp [I, mul_comm]
      left
      congr 1
      ext i
      simp

/-- Saturation in each assigned parent and upper bounds for all true prism
incidences give the three estimates needed for the local flat exit. -/
theorem locally_saturated_cover_bounds {n p q : ℕ}
    (A : Fin n → Set Space) (P : Fin p → Set Space) (R : Fin q → Set Space)
    (label : Fin p → Fin q) {w V c E L D : ℝ}
    (hw : 0 < w) (hV : 0 ≤ V) (hc : 0 < c) (hE : 0 < E) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hlocal : ∀ j U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * w) ≤
        ENNReal.ofReal (c * E) * volume U)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ R l ∧ A i ⊆ U} : ℝ) * w) ≤
        ENNReal.ofReal c * volume U)
    (hP : ∀ j, Convex ℝ (P j) ∧ volume (P j) = ENNReal.ofReal V)
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hsat : ∀ j, c * V ≤ L * (ncard {i | A i ⊆ R (label j) ∧ A i ⊆ P j} : ℝ) * w) :
    (∀ j j', (contained A (P j) : ℝ) ≤ (E * L) * contained A (P j')) ∧
    (∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {j | label j = l ∧ P j ⊆ U} : ℝ) * V) ≤
        ENNReal.ofReal (L * D) * volume U) ∧
    (∀ j U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * V) ≤
        ENNReal.ofReal ((E * L) * contained A (P j)) * volume U) := by
  classical
  have hbound (j) : (contained A (P j) : ℝ) * w ≤ (c * E) * V := by
    have hh := hlocal j (P j) (hP j).1
    simp only [and_self] at hh
    rw [(hP j).2, ← ENNReal.ofReal_mul (by positivity)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hsatfull (j) : c * V ≤ L * (contained A (P j) : ℝ) * w := by
    apply (hsat j).trans
    apply mul_le_mul_of_nonneg_right _ hw.le
    apply mul_le_mul_of_nonneg_left _ hL
    exact Nat.cast_le.mpr (Set.ncard_le_ncard fun i hi => hi.2)
  have hsatE (j) : (c * E) * V ≤ ((E * L) * contained A (P j)) * w := by
    have hh := mul_le_mul_of_nonneg_left (hsatfull j) hE.le
    nlinarith only [hh]
  refine ⟨?_, ?_, ?_⟩
  · intro j j'
    apply (mul_le_mul_iff_left₀ hw).mp
    exact (hbound j).trans (hsatE j')
  · intro l U hU
    let J := Finset.univ.filter fun j => label j = l ∧ P j ⊆ U
    have hJcard : ncard {j | label j = l ∧ P j ⊆ U} = J.card := by
      rw [ncard_fintype]
      congr 1
      ext j
      simp [J]
    have hscale : c * ((ncard {j | label j = l ∧ P j ⊆ U} : ℝ) * V) ≤
        (L * D) * ((ncard {i | A i ⊆ R l ∧ A i ⊆ U} : ℝ) * w) := by
      calc
        _ = ∑ _j ∈ J, c * V := by rw [hJcard]; simp only [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ j ∈ J, L * (ncard {i | A i ⊆ R (label j) ∧ A i ⊆ P j} : ℝ) * w :=
          Finset.sum_le_sum fun j _ => hsat j
        _ = L * (∑ j ∈ J, (ncard {i | A i ⊆ R (label j) ∧ A i ⊆ P j} : ℝ)) * w := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ ≤ L * (D * (ncard {i | A i ⊆ R l ∧ A i ⊆ U} : ℝ)) * w :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (labeled_cover_incidence_le A P R label hdegree l U) hL) hw.le
        _ = _ := by ring
    exact cancel_scaled_measure (by positivity) (by positivity) hc hscale (hparent l U hU)
  · intro j U hU
    have hu : Upper A w (Finset.univ.filter fun i => A i ⊆ P j) (c * E) := by
      intro W hW
      have hh := hlocal j W hW
      rw [ncard_fintype] at hh
      convert hh using 1
      congr 3
      simp only [count, Finset.filter_filter]
      congr 1
      ext i
      simp
    have hh := (hu.rescale hw hV (by positivity)
      (by positivity : 0 ≤ (E * L) * contained A (P j)) (hsatE j)) U hU
    convert hh using 1
    congr 3
    rw [ncard_fintype]
    simp only [count, Finset.filter_filter]
    congr 1
    ext i
    simp

/-- Exact branch C from locally saturated, normalized prisms, with both the
true-incidence loss and the neighboring-parent loss made explicit. -/
theorem flat_prisms_of_local_saturation {n p q : ℕ}
    (A : Fin n → Set Space) (P : Fin p → Set Space) (R : Fin q → Set Space)
    (label : Fin p → Fin q) (neighbors : Fin p → Finset (Fin q))
    (c e₁ e₂ e₃ : Fin p → Space) {δ ζ₂ ζ₃ a b w κ E L D M K : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b)
    (hflat : a ≤ δ ^ (ζ₂ / 200) * b) (hb1 : b ≤ 1)
    (hn : 0 < n) (hw : 0 < w) (hκ : 0 < κ) (hE : 0 < E)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (hP : ∀ j, P j = Prism a b (c j) (e₁ j) (e₂ j) (e₃ j))
    (hF : Frostman K A) (hcover : ∀ i, ∃ j, A i ⊆ P j)
    (hlocal : ∀ j U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * w) ≤
        ENNReal.ofReal (κ * E) * volume U)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ R l ∧ A i ⊆ U} : ℝ) * w) ≤
        ENNReal.ofReal κ * volume U)
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hsat : ∀ j, κ * (8 * a * b) ≤ L * (ncard {i | A i ⊆ R (label j) ∧ A i ⊆ P j} : ℝ) * w)
    (hneighbors : ∀ j, ((neighbors j).card : ℝ) ≤ M)
    (hlabel : ∀ j j', P j' ⊆ Metric.thickening b (P j) → label j' ∈ neighbors j)
    (herrorL : E * L ≤ δ ^ (-ζ₃)) (herrorM : M * (L * D) ≤ δ ^ (-ζ₃))
    (herrorF : K * (E * L) * D ≤ δ ^ (-ζ₃)) : FlatPrisms ζ₂ ζ₃ δ A := by
  have ha : 0 ≤ a := hδ.le.trans hδa
  have hb : 0 ≤ b := ha.trans hab
  have hPV (j) : Convex ℝ (P j) ∧ volume (P j) = ENNReal.ofReal (8 * a * b) := by
    rw [hP j]
    exact ⟨prism_convex _ _ _ _ _ _, prism_volume ha hb _ _ _ _ (he j)⟩
  obtain ⟨hbalance, hKT, hbelow⟩ := locally_saturated_cover_bounds A P R label
    hw (by positivity : 0 ≤ 8 * a * b) hκ hE hL hD hlocal hparent hPV hdegree hsat
  apply flat_prisms_of_bounded_parent_cover A P c e₁ e₂ e₃ label neighbors
    hδ hδa hab hflat hb1 hn hK (by positivity) hD (by positivity)
    herrorL herrorM herrorF he hP hF hcover hbalance hdegree
  · intro j U hU
    rw [(hPV j).2, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact hbelow j U hU
  · exact hneighbors
  · exact hlabel
  · intro l U hU
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact hKT l U hU

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
