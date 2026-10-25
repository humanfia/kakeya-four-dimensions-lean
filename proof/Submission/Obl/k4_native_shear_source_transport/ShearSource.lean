-- Copied from LOT tree oai_074_kakeya_four_dimensions, obligation o075 (k4_joint_homogenization),
-- branch x0254, file Submission/Obl/k4_joint_homogenization/ShearSource.lean (session x0254's own proofs), renamed into this namespace.
import Submission.Obl.k4_native_shear_source_transport.ShearedDensity

/-!
# The native law in the time-position-velocity chart (statement of o095)

The selected native law, pushed by the chart `(x, t) ↦ (t, y(t), w(t), s)`, has the explicit
density `∑ⱼ cⱼ 1[x ∈ Aⱼ, (x, t) ∈ E_{iⱼ}]`; every measurable further selection has an
observation density. This is the frozen statement of o095
(`k4_native_shear_source_transport`), proved here from `NativeLaw`.
-/

namespace Submission.Obl.k4_native_shear_source_transport

open MeasureTheory Set
open scoped ENNReal

/-- The chart of o095 is the shear. -/
theorem chart_eq_shear (i : ℕ) (x : Fin 6 → ℝ) (t : ℝ) :
    (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4,
      p.1.2 2 + p.2 * p.1.2 5, p.1.2 3, p.1.2 4, p.1.2 5] : Fin 7 → ℝ)) ((i, x), t) =
      id (shearEquiv (x, t)) := by
  rw [shearEquiv_apply]; rfl

theorem measurable_chart :
    Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (![p.2, p.1.2 0 + p.2 * p.1.2 3,
      p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5, p.1.2 3, p.1.2 4, p.1.2 5] :
      Fin 7 → ℝ)) := by
  apply Measurable.of_eval
  intro l
  fin_cases l <;> simp <;> fun_prop

/-- The frozen observation of o084/o095/o096 is `obsMap`. -/
theorem frozenObs_eq_obsMap (n r u : ℝ) :
    (fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3,
      p.1.2 1 + p.2 * p.1.2 4] : EuclideanSpace ℝ (Fin 3)),
      ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ)))⌋),
      fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j /
        ((2 : ℝ) ^ (-(⌊u * Real.log n / Real.log 2⌋ : ℤ)))⌋)) =
    obsMap ((2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ)))
      ((2 : ℝ) ^ (-(⌊u * Real.log n / Real.log 2⌋ : ℤ))) := by
  funext p
  rfl

/-- **o095** (`k4_native_shear_source_transport`), with its frozen statement. -/
theorem native_shear_source_transport : ∀ (N K : ℕ → ℝ) (ν : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), ((fun N K ν E => (∃ M D : ℕ, ∀ k, MeasureTheory.IsProbabilityMeasure (ν k) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k) ∧ E k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂(ν k), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ K k) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ (((ν k).prod MeasureTheory.volume).restrict (E k)) Set.univ)) : (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → Prop) N K ν E → (∀ (R U : ℝ), 0 < R → 0 < U → ((fun N ν E R U => ∀ k (S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), MeasurableSet S → S ⊆ E k → ∀ (r u : ℝ), 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U → ∃ G : (((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), Measurable G ∧ MeasureTheory.Measure.map (((fun n r u => fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4] : EuclideanSpace ℝ (Fin 3)), ⌊(p.1.2 2 + p.2 * p.1.2 5) / ((2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ)))⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / ((2 : ℝ) ^ (-(⌊u * Real.log n / Real.log 2⌋ : ℤ)))⌋)) : ℝ → ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))) (N k) r u) (((ν k).prod MeasureTheory.volume).restrict S) = ((((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count)) : MeasureTheory.Measure ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))).withDensity G) : (ℕ → ℝ) → (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ℝ → ℝ → Prop) N ν E R U) ∧ ∃ (M D : ℕ) (f : ℕ → (Fin 7 → ℝ) → ℝ), (∀ k, ((fun n M D f => ∃ (m : ℕ) (c : Fin m → ℝ) (A : Fin m → Set (Fin 6 → ℝ)) (B : Fin m → Set (Fin 7 → ℝ)), (m : ℝ) ≤ n ^ M ∧ (∀ j, 0 ≤ c j ∧ c j ≤ n ^ M) ∧ (∀ j, ∃ mA : ℕ, (mA : ℝ) ≤ n ^ M ∧ ∃ pA : Fin mA → MvPolynomial (Fin 6) ℝ, (∀ a, (pA a).totalDegree ≤ D) ∧ ∃ bA : (Fin mA → Bool) → Bool, ∀ a, a ∈ A j ↔ bA (fun l => decide (0 ≤ MvPolynomial.eval a (pA l))) = true) ∧ (∀ j, ∃ mB : ℕ, (mB : ℝ) ≤ n ^ M ∧ ∃ pB : Fin mB → MvPolynomial (Fin 7) ℝ, (∀ a, (pB a).totalDegree ≤ D) ∧ ∃ bB : (Fin mB → Bool) → Bool, ∀ a, a ∈ B j ↔ bB (fun l => decide (0 ≤ MvPolynomial.eval a (pB l))) = true) ∧ (∀ j a, a ∈ A j → ∀ l, |a l| ≤ n ^ M) ∧ (∀ j a, a ∈ B j → a 6 ∈ Set.Icc (0 : ℝ) 1) ∧ f = fun x => ∑ j, @ite ℝ ((![x 1 - x 0 * x 4, x 2 - x 0 * x 5, x 3 - x 0 * x 6, x 4, x 5, x 6] : Fin 6 → ℝ) ∈ A j ∧ Fin.snoc (![x 1 - x 0 * x 4, x 2 - x 0 * x 5, x 3 - x 0 * x 6, x 4, x 5, x 6] : Fin 6 → ℝ) (x 0) ∈ B j) (Classical.propDecidable ((![x 1 - x 0 * x 4, x 2 - x 0 * x 5, x 3 - x 0 * x 6, x 4, x 5, x 6] : Fin 6 → ℝ) ∈ A j ∧ Fin.snoc (![x 1 - x 0 * x 4, x 2 - x 0 * x 5, x 3 - x 0 * x 6, x 4, x 5, x 6] : Fin 6 → ℝ) (x 0) ∈ B j)) (c j) 0) : ℝ → ℕ → ℕ → ((Fin 7 → ℝ) → ℝ) → Prop) (N k) M D (f k)) ∧ ((fun μ f => ∀ k, Measurable (f k) ∧ (∀ x, 0 ≤ f k x) ∧ MeasureTheory.Measure.map ((fun p => ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5, p.1.2 3, p.1.2 4, p.1.2 5]) : ((ℕ × (Fin 6 → ℝ)) × ℝ) → (Fin 7 → ℝ)) (μ k) = MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (f k x))) : (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) → (ℕ → (Fin 7 → ℝ) → ℝ) → Prop) (((fun ν E => fun k => ((ν k).prod MeasureTheory.volume).restrict (E k)) : (ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → (ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → (ℕ → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))) ν E) f := by
  intro N K ν E hfmt
  obtain ⟨M, D, hMD⟩ := hfmt
  have hT : ∀ k, TemperedProblem (N k) M D (K k) (ν k) (E k) := hMD
  refine ⟨?_, ?_⟩
  · intro R U _ _ k S hS _ r u _ _ _ _
    have h := nativeDensityStatement (N k) M D (K k) (ν k) (E k) (hT k) S hS
      ((2 : ℝ) ^ (-(⌊r * Real.log (N k) / Real.log 2⌋ : ℤ)))
      ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))
      (zpow_pos (by norm_num) _) (zpow_pos (by norm_num) _)
    rw [← frozenObs_eq_obsMap] at h
    exact h
  · have h1 := fun k => (hT k).2.1
    choose m hm c i A hA hν using h1
    have hEsub := fun k => (hT k).2.2.2.1
    have hEm := fun k => (hT k).2.2.1
    have hEfmt := fun k => (hT k).2.2.2.2.2.1
    have hAm : ∀ k j, MeasurableSet (A k j) := by
      intro k j
      obtain ⟨-, -, -, ⟨m₀, -, p₀, -, b₀, hb₀⟩, -⟩ := hA k j
      exact measurableSet_of_boolPolyFormat p₀ b₀ hb₀
    let B : (k : ℕ) → Fin (m k) → Set (Fin 7 → ℝ) := fun k j =>
      {x₁ : Fin 7 → ℝ | ((i k j, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E k}
    have hBm : ∀ k j, MeasurableSet (B k j) := by
      intro k j
      have hmeas : Measurable (fun x₁ : Fin 7 → ℝ =>
          ((i k j, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6)) := by fun_prop
      exact hmeas (hEm k)
    let X : (Fin 7 → ℝ) → (Fin 6 → ℝ) := fun x =>
      ![x 1 - x 0 * x 4, x 2 - x 0 * x 5, x 3 - x 0 * x 6, x 4, x 5, x 6]
    have hX : Measurable X := by
      apply Measurable.of_eval
      intro l
      fin_cases l <;> simp [X] <;> fun_prop
    have hmemB : ∀ k j (x : Fin 7 → ℝ),
        Fin.snoc (X x) (x 0) ∈ B k j ↔ ((i k j, X x), x 0) ∈ E k := by
      intro k j x
      simp only [B, Set.mem_ofPred_eq, Fin.snoc_castSucc]
      rfl
    let f : ℕ → (Fin 7 → ℝ) → ℝ := fun k x => ∑ j, @ite ℝ (X x ∈ A k j ∧
      Fin.snoc (X x) (x 0) ∈ B k j)
      (Classical.propDecidable (X x ∈ A k j ∧ Fin.snoc (X x) (x 0) ∈ B k j)) (c k j) 0
    have hf : ∀ k, f k = nativeDensityR (c k) (i k) (A k) (E k) := by
      intro k
      funext x
      simp only [f, nativeDensityR]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hiff : X x ∈ A k j ∧ Fin.snoc (X x) (x 0) ∈ B k j ↔
          x ∈ shearedPiece (A k j) (i k j) (E k) := by
        rw [hmemB]
        simp only [shearedPiece, mem_preimage, Set.mem_ofPred_eq, shearEquiv_symm_apply, X]
      by_cases hx : x ∈ shearedPiece (A k j) (i k j) (E k)
      · have h' := hiff.mpr hx
        simp [h', hx]
      · have h' : ¬ (X x ∈ A k j ∧ Fin.snoc (X x) (x 0) ∈ B k j) := fun h => hx (hiff.mp h)
        simp [h', hx]
    refine ⟨M, D, f, fun k => ?_, fun k => ?_⟩
    · refine ⟨m k, c k, A k, B k, hm k, fun j => ⟨(hA k j).1, (hA k j).2.1⟩,
        fun j => (hA k j).2.2.2.1, fun j => hEfmt k (i k j), fun j => (hA k j).2.2.2.2,
        fun j a ha => ?_, rfl⟩
      exact (hEsub k ha).2
    · have hc : ∀ j, 0 ≤ c k j := fun j => (hA k j).1
      refine ⟨?_, ?_, ?_⟩
      · rw [hf]; exact measurable_nativeDensityR (c k) (i k) (hAm k) (hEm k)
      · intro x; rw [hf]; exact nativeDensityR_nonneg hc (i k) (A k) (E k) x
      · have h := map_native_of_factor _ id measurable_chart measurable_id chart_eq_shear
          (c k) (i k) (hAm k) (hν k) (hEm k)
        rw [Measure.map_id, nativeDensity_eq_ofReal hc] at h
        rw [hf]
        exact h

end Submission.Obl.k4_native_shear_source_transport
