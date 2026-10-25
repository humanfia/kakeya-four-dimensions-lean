import Mathlib

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Set MeasureTheory Finset
open scoped ENNReal

/-- A product of time cells, with the final arrival in the first coordinate. -/
def tupleBox {Tc : Type*} {m : ℕ} (I : Tc → Set ℝ) (t : Fin (m + 1) → Tc) :
    Set (ℝ × (Fin m → ℝ)) :=
  I (t (Fin.last m)) ×ˢ Set.univ.pi (fun p : Fin m => I (t p.castSucc))

theorem measurableSet_tupleBox {Tc : Type*} {m : ℕ} (I : Tc → Set ℝ)
    (hI : ∀ t, MeasurableSet (I t)) (t : Fin (m + 1) → Tc) :
    MeasurableSet (tupleBox I t) :=
  (hI _).prod (MeasurableSet.univ_pi fun p => hI _)

theorem volume_tupleBox {Tc : Type*} {m : ℕ} (I : Tc → Set ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hI : ∀ t, volume (I t) = ENNReal.ofReal d) (t : Fin (m + 1) → Tc) :
    volume (tupleBox I t) = ENNReal.ofReal (d ^ (m + 1)) := by
  change ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) _ = _
  rw [tupleBox, Measure.prod_prod, hI, volume_pi, Measure.pi_pi]
  simp only [hI, prod_const, card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hd, ← ENNReal.ofReal_mul hd]
  congr 1
  ring

theorem tupleBox_disjoint {Tc : Type*} {m : ℕ} (I : Tc → Set ℝ)
    (hI : Pairwise (fun s t => Disjoint (I s) (I t))) {t u : Fin (m + 1) → Tc} (htu : t ≠ u) :
    Disjoint (tupleBox I t) (tupleBox I u) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hcoord {i j : Tc} {z : ℝ} (hi : z ∈ I i) (hj : z ∈ I j) : i = j := by
    by_contra hij
    exact Set.disjoint_left.mp (hI hij) hi hj
  apply htu
  funext p
  refine Fin.lastCases ?_ (fun q => ?_) p
  · exact hcoord hx.1 hy.1
  · exact hcoord (Set.mem_pi.mp hx.2 q (mem_univ q))
      (Set.mem_pi.mp hy.2 q (mem_univ q))

/-- Disjoint cells transfer a finite count to Lebesgue volume. -/
theorem tupleBox_count_volume_le {Tc : Type*} [DecidableEq Tc] {m : ℕ}
    (I : Tc → Set ℝ) (hIm : ∀ t, MeasurableSet (I t))
    (hId : Pairwise (fun s t => Disjoint (I s) (I t))) {d : ℝ} (hd : 0 < d)
    (hIv : ∀ t, volume (I t) = ENNReal.ofReal d)
    (Q : Finset (Fin (m + 1) → Tc)) (E : Set (ℝ × (Fin m → ℝ)))
    (hsub : ∀ t ∈ Q, tupleBox I t ⊆ E) :
    ENNReal.ofReal ((Q.card : ℝ) * d ^ (m + 1)) ≤ volume E := by
  classical
  calc
    ENNReal.ofReal ((Q.card : ℝ) * d ^ (m + 1)) =
        ∑ t ∈ Q, volume (tupleBox I t) := by
      simp only [volume_tupleBox I hd.le hIv, sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg Q.card)]
      simp
    _ = volume (⋃ t ∈ Q, tupleBox I t) :=
      (measure_biUnion_finset
        (fun t ht u hu htu => tupleBox_disjoint I hId htu)
        (fun t ht => measurableSet_tupleBox I hIm t)).symm
    _ ≤ volume E := by
      apply measure_mono
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨ht, hx⟩
      exact hsub t ht hx

/-- Real form of the count-to-volume estimate. -/
theorem tupleBox_count_le {Tc : Type*} [Fintype Tc] [DecidableEq Tc] {m : ℕ}
    (I : Tc → Set ℝ) (hIm : ∀ t, MeasurableSet (I t))
    (hId : Pairwise (fun s t => Disjoint (I s) (I t))) {d : ℝ} (hd : 0 < d)
    (hIv : ∀ t, volume (I t) = ENNReal.ofReal d)
    (Q : (Fin (m + 1) → Tc) → Prop) [DecidablePred Q]
    (E : Set (ℝ × (Fin m → ℝ))) (hE : volume E ≠ ∞)
    (hsub : ∀ t, Q t → tupleBox I t ⊆ E) :
    (∑ t, if Q t then (1 : ℝ) else 0) ≤ (volume E).toReal / d ^ (m + 1) := by
  have h := tupleBox_count_volume_le I hIm hId hd hIv (univ.filter Q) E
    (fun t ht => hsub t (mem_filter.mp ht).2)
  have hr := ENNReal.toReal_mono hE h
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  exact (le_div_iff₀ (pow_pos hd _)).mpr hr

end Submission.Obl.k4_matching_abstract_switching_mixture
