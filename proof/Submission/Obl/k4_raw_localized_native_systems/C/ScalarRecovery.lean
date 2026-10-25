import Submission.Obl.k4_raw_localized_native_systems.C.RecoveryInterface
import Submission.Obl.k4_raw_localized_native_systems.C.ScalarAssignments

/-
Adapted from this LOT tree, o178, session x0596, `ScalarRecovery.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Lib.K4XInterface

noncomputable section

/-- The complete finite scalar output, retaining the unnormalized input law
and the specified original observation in its success assertion. -/
structure ScalarRecovery (N d s c ε : ℝ) (M D : ℕ)
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ)
    (O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ) where
  count : ℕ
  poly : Fin count → MvPolynomial (Fin 2) ℝ
  assignment : Fin count → Set (Fin 5 → ℝ)
  lists : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin count)
  count_bound : (count : ℝ) ≤ N ^ (d * s + ε)
  tests : ∀ i, (poly i).totalDegree ≤ 2 ∧ (∀ e, |(poly i).coeff e| ≤ N ^ ε) ∧
    MeasurableSet (assignment i) ∧ gfmt 5 (N ^ M) D (assignment i) ∧
    ∀ z ∈ assignment i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |scalarX z t - MvPolynomial.eval ![t, scalarY z t] (poly i)| ≤ N ^ (-c)
  disjoint : ∀ i j, i ≠ j → Disjoint (assignment i) (assignment j)
  list_bound : ∀ o, (lists o).card ≤ M
  list_measurable : ∀ i, MeasurableSet {o | i ∈ lists o}
  success : ENNReal.ofReal (1 / 2 : ℝ) * μ Set.univ ≤
    μ {p | ∃ i, b p.1 ∈ assignment i ∧ i ∈ lists (O p)}

/-- Q0's gain and format are common to every packet, and both precede the
small exponent and the choice of a finite sample. -/
theorem FixedBudgetRecovery.parameters (hQ : FixedBudgetRecovery)
    {d s m S U : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hs1 : s < 1)
    (hsm : s < m) (hS : 0 < S) (hU : 0 < U) (hUm : U < m) :
    ∃ c : ℝ, 0 < c ∧ c < min s 1 ∧ ∃ M D : ℕ, 1 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N →
      ∀ (ν : Measure (ℕ × (Fin 6 → ℝ)))
        (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
        (b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ)
        (O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ)
        (base : (EuclideanSpace ℝ (Fin 3) × ℤ) → EuclideanSpace ℝ (Fin 2))
        (signal : (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ),
      ProjectedScalarLaw N η d s m S U ν μ b →
      ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ →
      Measurable O → Measurable base → Measurable signal →
      (∀ᵐ p ∂μ, base (O p) = WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∧
        |scalarX (b p.1) p.2 - signal (O p)| ≤ N ^ (-1 + η)) →
      Nonempty (ScalarRecovery N d s c ε M D μ b O) := by
  obtain ⟨c, hc, hcs, M, D, hM, hQ⟩ := hQ d s m S U hd hd1 hs hs1 hsm hS hU hUm
  refine ⟨c, hc, hcs, M, D, hM, fun ε hε hε1 => ?_⟩
  obtain ⟨η, hη, N₀, hN₀, hrec⟩ := hQ ε hε hε1
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN ν μ b O base signal hadm hmass hO hbase hsignal hobs
  obtain ⟨n, P, A, lst, hn, hP, hdisj, hlist, hmeas, hsuccess⟩ :=
    hrec N hN ν μ b O base signal hadm hmass hO hbase hsignal hobs
  exact ⟨⟨n, P, A, lst, hn, hP, hdisj, hlist, hmeas, hsuccess⟩⟩

/-- Every assigned scalar fit improves the native polynomial throughout its
original block, including all unselected times on the same trajectory. -/
theorem ScalarRecovery.original_fit
    {N d s c ε : ℝ} {M D : ℕ}
    {μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ}
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) (A : Set (ℕ × (Fin 6 → ℝ)))
    (rec : ScalarRecovery N d s c ε M D μ (clippedScalarCoeff P t₀ q a v A) O)
    (i : Fin rec.count) {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ A)
    (hi : clippedScalarCoeff P t₀ q a v A l ∈ rec.assignment i)
    (hq : 0 < q) {t : ℝ} (ht : t ∈ Set.Icc t₀ (t₀ + q)) :
    |MvPolynomial.eval (gx l t)
      (nativeCorrection P (scalarPredictor t₀ q a v (rec.poly i)))| ≤ N ^ (-c) := by
  apply scalar_fit_nativeCorrection P hP t₀ q a v (rec.poly i) l hq _ ht
  intro u hu
  have hh := (rec.tests i).2.2.2.2 (clippedScalarCoeff P t₀ q a v A l) hi u hu
  simpa only [clippedScalarCoeff_eq P t₀ q a v hl, scalarX, scalarY] using hh

end
end Submission.Obl.k4_raw_localized_native_systems.C
