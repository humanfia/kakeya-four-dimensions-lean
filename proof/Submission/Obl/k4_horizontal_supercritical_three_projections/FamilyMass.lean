import Submission.Obl.k4_horizontal_supercritical_three_projections.Refinement

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- The old scalar floors pay for the entire coarse reference budget, using
unchanged disjoint assignments under the original current measure. -/
theorem coarse_weight_budget {α : Type} [MeasurableSpace α]
    {N τ K χ D d s : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (ζ : Measure (α × ℝ)) (π : Measure ℝ) (L : CoarseProjectionLayer α)
    (hA : ∀ i, MeasurableSet (L.A i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (L.A i) (L.A j))
    (hfloor : ∀ i, ENNReal.ofReal (L.weight π χ D (N ^ (-s)) d i * N ^ (-τ) / N ^ τ) ≤
      ζ (L.A i ×ˢ Icc (0 : ℝ) 1))
    (hmass : ζ univ ≤ ENNReal.ofReal K) :
    ∑ i, L.weight π χ D (N ^ (-s)) d i ≤ (N ^ τ) ^ 2 * K := by
  have hQ : 0 < N ^ τ := Real.rpow_pos_of_pos hN _
  have hw (i) : 0 ≤ L.weight π χ D (N ^ (-s)) d i := by
    unfold CoarseProjectionLayer.weight
    positivity
  have hf (i) : ENNReal.ofReal (L.weight π χ D (N ^ (-s)) d i) ≤
      ENNReal.ofReal ((N ^ τ) ^ 2) * ζ (L.A i ×ˢ Icc (0 : ℝ) 1) := by
    calc
      _ = ENNReal.ofReal ((N ^ τ) ^ 2) *
          ENNReal.ofReal (L.weight π χ D (N ^ (-s)) d i * N ^ (-τ) / N ^ τ) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), Real.rpow_neg hN.le τ]
        congr 1
        field_simp
      _ ≤ _ := mul_le_mul_right (hfloor i) _
  have hdisj' : Pairwise (fun i j =>
      Disjoint (L.A i ×ˢ Icc (0 : ℝ) 1) (L.A j ×ˢ Icc (0 : ℝ) 1)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro p hp hq
    exact disjoint_left.mp (hdisj i j hij) hp.1 hq.1
  have hsum := reference_budget_of_original_floors ζ
    (fun i => L.A i ×ˢ Icc (0 : ℝ) 1) (fun i => (hA i).prod measurableSet_Icc)
    hdisj' (fun i => ENNReal.ofReal (L.weight π χ D (N ^ (-s)) d i))
    (ENNReal.ofReal ((N ^ τ) ^ 2)) hf
  have hsum' : ENNReal.ofReal (∑ i, L.weight π χ D (N ^ (-s)) d i) ≤
      ENNReal.ofReal ((N ^ τ) ^ 2 * K) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)]
    exact hsum.trans ((mul_le_mul_right hmass _).trans_eq
      (ENNReal.ofReal_mul (sq_nonneg _)).symm)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) hK)).mp hsum'

/-- Incidence mass on any assignment is bounded by its full original prior
weight. The support removes the infinite ambient time interval. -/
theorem incidence_assignment_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (ζ : Measure (α × ℝ)) (A : Set α) (K : ENNReal)
    (hdom : ζ ≤ K • (ν.prod volume))
    (hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) :
    ζ {p | p.1 ∈ A} ≤ K * ν A := by
  have htime : ∀ᵐ p ∂ζ, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    convert hsupp using 1
    congr 1
    ext p
    simp
  have heq : ζ {p | p.1 ∈ A} = ζ (A ×ˢ Icc (0 : ℝ) 1) := by
    apply measure_congr
    filter_upwards [htime] with p hp
    apply propext
    exact ⟨fun h => ⟨h, hp⟩, fun h => h.1⟩
  rw [heq]
  apply (hdom _).trans_eq
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
    Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- The weighted scalar successes over disjoint charts give the original
mass of their union, with only the scalar loss and original domination cost. -/
theorem scalar_ensemble_mass {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) [IsFiniteMeasure ν] (ζ : Measure (α × ℝ))
    (G : ι → Set α) (hG : ∀ i, MeasurableSet (G i))
    (hdisj : Pairwise (fun i j => Disjoint (G i) (G j)))
    {K u : ℝ} (hK : 0 < K) (hu : 0 ≤ u)
    (hdom : ζ ≤ ENNReal.ofReal K • (ν.prod volume))
    (hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (C : Set (α × ℝ))
    (hmass : (∑ i, ENNReal.ofReal ((ν (G i)).toReal * u)) ≤ ζ C) :
    ENNReal.ofReal (u / K) * ζ {p | ∃ i, p.1 ∈ G i} ≤ ζ C := by
  have hbound := incidence_assignment_bound ν ζ (⋃ i, G i) (ENNReal.ofReal K) hdom hsupp
  have hsum : ν (⋃ i, G i) = ∑ i, ν (G i) := by
    rw [measure_iUnion hdisj hG, tsum_fintype]
  have heq : {p : α × ℝ | p.1 ∈ ⋃ i, G i} = {p | ∃ i, p.1 ∈ G i} := by
    ext p
    exact mem_iUnion
  rw [heq, hsum] at hbound
  calc
    _ ≤ ENNReal.ofReal (u / K) * (ENNReal.ofReal K * ∑ i, ν (G i)) :=
      mul_le_mul_right hbound _
    _ = ENNReal.ofReal u * ∑ i, ν (G i) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hu hK.le), div_mul_cancel₀ _ hK.ne']
    _ = ∑ i, ENNReal.ofReal ((ν (G i)).toReal * u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top ν _), mul_comm]
    _ ≤ _ := hmass

end Submission.Obl.k4_horizontal_supercritical_three_projections
