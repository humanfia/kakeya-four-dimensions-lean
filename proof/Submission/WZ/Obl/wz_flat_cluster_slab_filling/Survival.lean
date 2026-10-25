-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.Survival.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Basic

/-!
Counting lemmas for the proof of `WangZahlLot.wz_flat_cluster_slab_filling`: survival of
points whose retained multiplicity is comparable to the original one, and selection of the
indices carrying a substantial share of a mass.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

/-- The points of the `i`-th retained shading whose retained multiplicity in the fibre of `i`
is at least `s` times the original multiplicity there. -/
def survivors {n N : ℕ} (S G : Finset (Fin n)) (f : Fin n → Fin N) (Z Z2 : Fin n → Set Space)
    (s : ℝ) (i : Fin n) : Set Space :=
  {p | s * ((S.filter fun j => f j = f i ∧ p ∈ Z j).card : ℝ) ≤
    ((G.filter fun j => f j = f i ∧ p ∈ Z2 j).card : ℝ)}

/-- The number of indices `j ∈ S` with `f j = k` whose set `Z j` contains `p` is a measurable
function of `p`. -/
lemma measurable_card_filter_mem {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (k : Fin N)
    (Z : Fin n → Set Space) (hZ : ∀ j, MeasurableSet (Z j)) :
    Measurable fun p : Space => ((S.filter fun j => f j = k ∧ p ∈ Z j).card : ℝ) := by
  have heq : (fun p : Space => ((S.filter fun j => f j = k ∧ p ∈ Z j).card : ℝ)) =
      fun p => ∑ j ∈ S, if f j = k then (Z j).indicator (fun _ => (1 : ℝ)) p else 0 := by
    funext p
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    by_cases hP : f j = k <;> by_cases hp : p ∈ Z j <;> simp [hP, hp]
  rw [heq]
  apply Finset.measurable_sum
  intro j _
  split_ifs
  · exact measurable_const.indicator (hZ j)
  · exact measurable_const

lemma survivors_measurable {n N : ℕ} (S G : Finset (Fin n)) (f : Fin n → Fin N)
    (Z Z2 : Fin n → Set Space) (hZ : ∀ j, MeasurableSet (Z j))
    (hZ2 : ∀ j, MeasurableSet (Z2 j)) (s : ℝ) (i : Fin n) :
    MeasurableSet (survivors S G f Z Z2 s i) := by
  exact measurableSet_le
    ((measurable_card_filter_mem S f (f i) Z hZ).const_mul s)
    (measurable_card_filter_mem G f (f i) Z2 hZ2)

/-- Pointwise counting form of the survival estimate. -/
lemma card_bad_le {n N : ℕ} (S G : Finset (Fin n)) (f : Fin n → Fin N) (A B : Fin n → Prop)
    {s : ℝ} (hs : 0 ≤ s) :
    ((G.filter fun i => B i ∧ ¬ (s * ((S.filter fun j => f j = f i ∧ A j).card : ℝ) ≤
        ((G.filter fun j => f j = f i ∧ B j).card : ℝ))).card : ℝ) ≤
      s * ((S.filter fun j => A j).card : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  rw [Finset.card_eq_sum_card_fiberwise (s := S.filter fun j => A j) (f := f) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hm : ((S.filter fun j => A j).filter fun j => f j = k) =
      S.filter fun j => f j = k ∧ A j := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro j _
    exact And.comm
  rw [hm]
  by_cases h : s * ((S.filter fun j => f j = k ∧ A j).card : ℝ) ≤
      ((G.filter fun j => f j = k ∧ B j).card : ℝ)
  · have hempty : ((G.filter fun i => B i ∧ ¬ (s * ((S.filter fun j => f j = f i ∧ A j).card : ℝ) ≤
        ((G.filter fun j => f j = f i ∧ B j).card : ℝ))).filter fun i => f i = k) = ∅ := by
      apply Finset.filter_false_of_mem
      intro i hi hik
      rw [Finset.mem_filter] at hi
      apply hi.2.2
      rw [hik]
      exact h
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  · push Not at h
    refine le_trans ?_ h.le
    exact_mod_cast Finset.card_le_card (by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, hi.2, hi.1.2.1⟩)

/-- Deleting the non-surviving points costs at most `s` times the original mass. -/
theorem survival_loss {n N : ℕ} (S G : Finset (Fin n)) (f : Fin n → Fin N)
    (Z Z2 : Fin n → Set Space) (hZ : ∀ j, MeasurableSet (Z j))
    (hZ2 : ∀ j, MeasurableSet (Z2 j)) {s : ℝ} (hs : 0 ≤ s) :
    ∑ i ∈ G, volume (Z2 i \ survivors S G f Z Z2 s i) ≤
      ENNReal.ofReal s * ∑ j ∈ S, volume (Z j) := by
  have hsurv : ∀ i, MeasurableSet (survivors S G f Z Z2 s i) :=
    fun i => survivors_measurable S G f Z Z2 hZ hZ2 s i
  have hpt : ∀ p : Space,
      ∑ i ∈ G, (Z2 i \ survivors S G f Z Z2 s i).indicator (fun _ => (1 : ℝ≥0∞)) p ≤
        ENNReal.ofReal s * ∑ j ∈ S, (Z j).indicator (fun _ => (1 : ℝ≥0∞)) p := by
    intro p
    have h1 : ∑ i ∈ G, (Z2 i \ survivors S G f Z Z2 s i).indicator (fun _ => (1 : ℝ≥0∞)) p =
        ((G.filter fun i => p ∈ Z2 i ∧ ¬ (s * ((S.filter fun j => f j = f i ∧ p ∈ Z j).card : ℝ) ≤
          ((G.filter fun j => f j = f i ∧ p ∈ Z2 j).card : ℝ))).card : ℝ≥0∞) := by
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      simp only [Set.indicator, Set.mem_sdiff, survivors, Set.mem_ofPred_eq]
    have h2 : ∑ j ∈ S, (Z j).indicator (fun _ => (1 : ℝ≥0∞)) p =
        ((S.filter fun j => p ∈ Z j).card : ℝ≥0∞) := by
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro j _
      simp only [Set.indicator]
    rw [h1, h2]
    have key := card_bad_le S G f (fun j => p ∈ Z j) (fun j => p ∈ Z2 j) hs
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hs]
    exact ENNReal.ofReal_le_ofReal key
  calc ∑ i ∈ G, volume (Z2 i \ survivors S G f Z Z2 s i)
        = ∫⁻ p, ∑ i ∈ G, (Z2 i \ survivors S G f Z Z2 s i).indicator
            (fun _ => (1 : ℝ≥0∞)) p := by
        rw [lintegral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i _
          rw [lintegral_indicator_const ((hZ2 i).diff (hsurv i)), one_mul]
        · intro i _
          exact measurable_const.indicator ((hZ2 i).diff (hsurv i))
    _ ≤ ∫⁻ p, ENNReal.ofReal s * ∑ j ∈ S, (Z j).indicator (fun _ => (1 : ℝ≥0∞)) p :=
        lintegral_mono hpt
    _ = ENNReal.ofReal s * ∑ j ∈ S, volume (Z j) := by
        rw [lintegral_const_mul, lintegral_finsetSum]
        · congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [lintegral_indicator_const (hZ j), one_mul]
        · intro j _
          exact measurable_const.indicator (hZ j)
        · exact Finset.measurable_sum _ (fun j _ => measurable_const.indicator (hZ j))

/-- If the total mass is at least `A` and each mass is at most `B`, then many indices carry
mass at least `t`. -/
lemma many_heavy {n : ℕ} (G : Finset (Fin n)) (m : Fin n → ℝ≥0∞) {A B t : ℝ} (hB : 0 < B)
    (ht : 0 ≤ t) (hmB : ∀ i ∈ G, m i ≤ ENNReal.ofReal B)
    (hA : ENNReal.ofReal A ≤ ∑ i ∈ G, m i) :
    A - G.card * t ≤ B * ((G.filter fun i => ENNReal.ofReal t ≤ m i).card : ℝ) := by
  set H := G.filter fun i => ENNReal.ofReal t ≤ m i with hH
  have hsplit := Finset.sum_filter_add_sum_filter_not G (fun i => ENNReal.ofReal t ≤ m i) m
  have h1 : ∑ i ∈ H, m i ≤ H.card * ENNReal.ofReal B := by
    have := Finset.sum_le_card_nsmul H m (ENNReal.ofReal B)
      (fun i hi => hmB i (Finset.mem_filter.1 hi).1)
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ i ∈ G.filter (fun i => ¬ ENNReal.ofReal t ≤ m i), m i ≤
      G.card * ENNReal.ofReal t := by
    calc ∑ i ∈ G.filter (fun i => ¬ ENNReal.ofReal t ≤ m i), m i
          ≤ (G.filter (fun i => ¬ ENNReal.ofReal t ≤ m i)).card * ENNReal.ofReal t := by
          have := Finset.sum_le_card_nsmul (G.filter (fun i => ¬ ENNReal.ofReal t ≤ m i)) m
            (ENNReal.ofReal t)
            (fun i hi => le_of_lt (not_le.1 (Finset.mem_filter.1 hi).2))
          simpa [nsmul_eq_mul] using this
      _ ≤ G.card * ENNReal.ofReal t := by
          gcongr
          exact Finset.filter_subset _ _
  have hpos : 0 ≤ B * (H.card : ℝ) + G.card * t := by positivity
  have h3 : ENNReal.ofReal A ≤ ENNReal.ofReal (B * (H.card : ℝ) + G.card * t) := by
    calc ENNReal.ofReal A ≤ ∑ i ∈ G, m i := hA
      _ = ∑ i ∈ H, m i + ∑ i ∈ G.filter (fun i => ¬ ENNReal.ofReal t ≤ m i), m i := hsplit.symm
      _ ≤ H.card * ENNReal.ofReal B + G.card * ENNReal.ofReal t := add_le_add h1 h2
      _ = ENNReal.ofReal (B * (H.card : ℝ) + G.card * t) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hB.le,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
          mul_comm (ENNReal.ofReal B)]
  have := (ENNReal.ofReal_le_ofReal_iff hpos).1 h3
  linarith

/-- Broadness at a surviving point produces a crossing retained tube through it. -/
lemma crossing_exists {n N : ℕ} {δ η ρ β θ s : ℝ} (S G : Finset (Fin n)) (f : Fin n → Fin N)
    (v : Fin n → Space) (Z Z2 : Fin n → Set Space)
    (hGS : G ⊆ S) (hZ2Z : ∀ j, Z2 j ⊆ Z j)
    (hbroad : ∀ (k : Fin N) (p u : Space) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      (({i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} : Set (Fin n)).ncard
        : ℝ) ≤ δ ^ (-η) * (r / ρ) ^ β * (({i | i ∈ S ∧ f i = k ∧ p ∈ Z i} : Set (Fin n)).ncard : ℝ))
    (hθ : δ ≤ θ) (hθρ : θ ≤ ρ) (hs : 0 < s) (hsmall : δ ^ (-η) * (θ / ρ) ^ β ≤ s / 2)
    (i : Fin n) (hi : i ∈ S) (hvi : ‖v i‖ = 1) (p : Space) (hpZ : p ∈ Z i)
    (hgood : p ∈ survivors S G f Z Z2 s i) :
    ∃ j ∈ G, f j = f i ∧ p ∈ Z2 j ∧ θ < angle (v j) (v i) := by
  by_contra hcon
  push Not at hcon
  have hb := hbroad (f i) p (v i) θ hvi hθ hθρ
  have e1 : ({j | j ∈ S ∧ f j = f i ∧ p ∈ Z j ∧ min ‖v j - v i‖ ‖v j + v i‖ ≤ θ} :
      Set (Fin n)) =
      ↑(S.filter fun j => f j = f i ∧ p ∈ Z j ∧ min ‖v j - v i‖ ‖v j + v i‖ ≤ θ) := by
    ext j; simp
  have e2 : ({j | j ∈ S ∧ f j = f i ∧ p ∈ Z j} : Set (Fin n)) =
      ↑(S.filter fun j => f j = f i ∧ p ∈ Z j) := by
    ext j; simp
  rw [e1, e2, Set.ncard_coe_finset, Set.ncard_coe_finset] at hb
  have hsub : (G.filter fun j => f j = f i ∧ p ∈ Z2 j) ⊆
      (S.filter fun j => f j = f i ∧ p ∈ Z j ∧ min ‖v j - v i‖ ‖v j + v i‖ ≤ θ) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hGS hj.1, hj.2.1, hZ2Z j hj.2.2, hcon j hj.1 hj.2.1 hj.2.2⟩
  have hgg : ((G.filter fun j => f j = f i ∧ p ∈ Z2 j).card : ℝ) ≤
      ((S.filter fun j => f j = f i ∧ p ∈ Z j ∧ min ‖v j - v i‖ ‖v j + v i‖ ≤ θ).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hm1 : (1 : ℝ) ≤ ((S.filter fun j => f j = f i ∧ p ∈ Z j).card : ℝ) := by
    have : 0 < (S.filter fun j => f j = f i ∧ p ∈ Z j).card :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, rfl, hpZ⟩⟩
    exact_mod_cast this
  have hgood' : s * ((S.filter fun j => f j = f i ∧ p ∈ Z j).card : ℝ) ≤
      ((G.filter fun j => f j = f i ∧ p ∈ Z2 j).card : ℝ) := hgood
  have h3 : δ ^ (-η) * (θ / ρ) ^ β * ((S.filter fun j => f j = f i ∧ p ∈ Z j).card : ℝ) ≤
      s / 2 * ((S.filter fun j => f j = f i ∧ p ∈ Z j).card : ℝ) :=
    mul_le_mul_of_nonneg_right hsmall (by linarith)
  nlinarith

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
