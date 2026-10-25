import Submission.Obl.k4_dk4_smoothed_problem.NativeEvent

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem.Framework

/-- The prior part of the frozen temperedness predicate, without abbreviating
any of its quantitative bounds. -/
def PriorFormat (N : ℝ) (M D : ℕ) (ν : Measure Coefficients) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ N ^ M ∧
    ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)),
      (∀ j, 0 ≤ c j ∧ c j ≤ N ^ M ∧ (i j : ℝ) ≤ N ^ M ∧
        (∃ m₀ : ℕ, (m₀ : ℝ) ≤ N ^ M ∧
          ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ,
            (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧
            ∃ b₀ : (Fin m₀ → Bool) → Bool,
              ∀ x₀, x₀ ∈ A j ↔
                b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧
        (∀ x ∈ A j, ∀ b, |x b| ≤ N ^ M)) ∧
      ν = ∑ j, (ENNReal.ofReal (c j)) •
        Measure.map (fun x => (i j, x)) (volume.restrict (A j))

/-- One scale of the complete tempered single-world native format. -/
def TemperedAt (N K : ℝ) (M D : ℕ) (ν : Measure Coefficients)
    (E : Set (Coefficients × ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧ PriorFormat N M D ν ∧
    MeasurableSet E ∧ E ⊆ univ ×ˢ Icc (0 : ℝ) 1 ∧
    (∀ p ∈ E, (p.1.1 : ℝ) ≤ N ^ M ∧ ∀ e, |p.1.2 e| ≤ N ^ M) ∧
    (∀ i, ∃ m₀ : ℕ, (m₀ : ℝ) ≤ N ^ M ∧
      HasBoolPolynomialFormat id
        {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ E} m₀ D) ∧
    (∀ᵐ l ∂ν, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖planarLine l t‖ + ‖planarVelocity l‖ ≤ K ∧ |trajectoryPoint l t 3| ≤ K) ∧
    ENNReal.ofReal K⁻¹ ≤ (ν.prod volume).restrict E univ

theorem nativePrior_format {n : ℕ} (hn : 0 < n) {r B N : ℝ} (hr : 0 < r)
    (M D : ℕ) (hD : 1 ≤ D) (b s : Fin n → Fin 3 → ℝ)
    (hb : ∀ i j, |b i j| + r ≤ B) (hs : ∀ i j, |s i j| + r ≤ B)
    (hnN : (n : ℝ) ≤ N ^ M) (hheight : componentHeight n r ≤ N ^ M)
    (hatoms : (12 : ℝ) ≤ N ^ M) (hB : B ≤ N ^ M) (hN : 0 ≤ N ^ M) :
    PriorFormat N M D (nativePrior r b s) := by
  let A : Fin n → Set (Fin 6 → ℝ) := fun j =>
    (concatenateCoefficients 3 3).symm ⁻¹'
      (FiniteSmoothing.coordBox r (b j) ×ˢ FiniteSmoothing.coordBox r (s j))
  refine ⟨n, hnN, (fun _ => componentHeight n r), (fun _ => 0), A, ?_, ?_⟩
  · intro j
    refine ⟨(componentHeight_pos hn hr).le, hheight, (by simpa using hN), ?_, ?_⟩
    · refine ⟨12, hatoms, ?_⟩
      exact (native_packed_box_format
        (fun a => b j a - r) (fun a => b j a + r)
        (fun a => s j a - r) (fun a => s j a + r)).mono_degree hD
    · intro a ha e
      have hcube := packLine_mem_cube (b j) (s j) (hb j) (hs j) ha
      have hid : (packLine ((concatenateCoefficients 3 3).symm a)).2 = a := by
        exact (concatenateCoefficients 3 3).apply_symm_apply a
      rw [hid] at hcube
      exact (mem_coefficientCube.mp hcube e).trans hB
  · exact nativePrior_representation hn hr b s

theorem native_tempered {n m : ℕ} (hn : 0 < n) {r δ B N K : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hB0 : 0 ≤ B) (hK : 6 * B ≤ K)
    (M D : ℕ) (hD : 4 ≤ D) (b s : Fin n → Fin 3 → ℝ)
    (hb : ∀ i j, |b i j| + r ≤ B) (hs : ∀ i j, |s i j| + r ≤ B)
    (hnN : (n : ℝ) ≤ N ^ M) (hheight : componentHeight n r ≤ N ^ M)
    (hatoms : (14 + m : ℝ) ≤ N ^ M) (hB : B ≤ N ^ M) (hN : 0 ≤ N ^ M)
    (z : Fin m → EuclideanSpace ℝ (Fin 4))
    (hmass : ENNReal.ofReal K⁻¹ ≤ (nativePrior r b s).prod volume
      (boundedNativeEvent B (⋃ j, Metric.ball (z j) δ))) :
    TemperedAt N K M D (nativePrior r b s)
      (boundedNativeEvent B (⋃ j, Metric.ball (z j) δ)) := by
  refine ⟨nativePrior_probability hn hr b s,
    nativePrior_format hn hr M D (by omega) b s hb hs hnN hheight
      (by linarith [Nat.cast_nonneg (α := ℝ) m]) hB hN,
    measurableSet_boundedNativeEvent B (isOpen_iUnion fun j => Metric.isOpen_ball).measurableSet,
    boundedNativeEvent_subset B _, ?_, ?_,
    nativePrior_native_bounds hr hB0 hK b s hb hs, ?_⟩
  · intro p hp
    have h := boundedNativeEvent_bounds hp
    exact ⟨by rw [h.1]; simpa using hN, fun e => (h.2 e).trans hB⟩
  · intro i
    obtain ⟨m₀, hm₀, hfmt⟩ := boundedNativeEvent_format B z hδ i
    refine ⟨m₀, ?_, hfmt.mono_degree hD⟩
    exact (by exact_mod_cast hm₀ : (m₀ : ℝ) ≤ 14 + m).trans hatoms
  · simpa only [Measure.restrict_apply_univ] using hmass

end Submission.Obl.k4_dk4_smoothed_problem.Framework
