-- Adapted from this LOT tree, o114, session x0680, commit 8cc890dd,
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/NativeGood.lean.
import Submission.Obl.k4_homogeneous_native_pair_preparation.Interface
import Submission.Obl.k4_homogeneous_native_pair_preparation.FiniteCaps

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set

/-- The original native equation supplies a bounded regular hidden sublevel
set at each retained incidence. These are the pointwise inputs to the total
base-density cap and the bounded-velocity estimates. -/
def NativeIncidenceGood (K B : ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (p : (ℕ × (Fin 6 → ℝ)) × ℝ) : Prop :=
  |MvPolynomial.eval (x p.1 p.2) P| ≤ K ∧
    B / K ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ∧
    ‖y p.1 p.2‖ + ‖v p.1‖ ≤ K

/-- Lift the frozen native almost-everywhere bounds to the original selected
incidence law. -/
theorem native_incidence_ae (ν : Measure (ℕ × (Fin 6 → ℝ))) [SFinite ν]
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hEm : MeasurableSet E)
    (hEt : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (K B : ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (hupper : ∀ᵐ l ∂ν, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖y l t‖ + ‖v l‖ ≤ K ∧ |MvPolynomial.eval (x l t) P| ≤ K ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2)
    (hfloor : ∀ᵐ p ∂((ν.prod volume).restrict E),
      B / K ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)|) :
    ∀ᵐ p ∂((ν.prod volume).restrict E), NativeIncidenceGood K B P p := by
  have hprod := (Measure.quasiMeasurePreserving_fst
    (μ := ν) (ν := (volume : Measure ℝ))).ae hupper
  filter_upwards [ae_restrict_of_ae hprod, hfloor, ae_restrict_mem hEm] with p hp hf hpE
  have h := hp p.2 (hEt hpE).2
  exact ⟨h.2.1, hf, h.1⟩

/-- The native conditions may be imposed on a previously chosen cap mask
without any additional discarded mass or measurability requirement on the
native predicate itself. -/
theorem native_pointwise_submask (ν : Measure (ℕ × (Fin 6 → ℝ))) [SFinite ν]
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hEm : MeasurableSet E)
    (hEt : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (K B : ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (hupper : ∀ᵐ l ∂ν, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖y l t‖ + ‖v l‖ ≤ K ∧ |MvPolynomial.eval (x l t) P| ≤ K ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2)
    (hfloor : ∀ᵐ p ∂((ν.prod volume).restrict E),
      B / K ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)|)
    (Good : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hGood : MeasurableSet Good) :
    ∃ F, F ⊆ Good ∧ MeasurableSet F ∧ (∀ p ∈ F, NativeIncidenceGood K B P p) ∧
      ((ν.prod volume).restrict E) Fᶜ = ((ν.prod volume).restrict E) Goodᶜ :=
  ae_good_submask _ Good hGood _ (native_incidence_ae ν E hEm hEt K B P hupper hfloor)

end Submission.Obl.k4_homogeneous_native_pair_preparation
