import Submission.Obl.k4_scalar_candidate_original_return.Defs
import Submission.Obl.k4_native_base_flattening.PolynomialAveraging
import Submission.Obl.k4_native_shear_source_transport.PolyAxis
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ModelReduction

noncomputable section

private lemma sign_eq_of_two_weak_tests {u v : ℝ}
    (hneg : u ≤ 0 ↔ v ≤ 0) (hpos : -u ≤ 0 ↔ -v ≤ 0) :
    SignType.sign u = SignType.sign v := by
  have hnonneg : 0 ≤ u ↔ 0 ≤ v := by simpa only [neg_nonpos] using hpos
  by_cases hu : 0 ≤ u
  · by_cases hu' : u ≤ 0
    · have hu0 : u = 0 := le_antisymm hu' hu
      have hv0 : v = 0 := le_antisymm (hneg.mp hu') (hnonneg.mp hu)
      simp [hu0, hv0]
    · have hv' : ¬v ≤ 0 := fun hv => hu' (hneg.mpr hv)
      rw [sign_pos (lt_of_not_ge hu'), sign_pos (lt_of_not_ge hv')]
  · have hv : ¬0 ≤ v := fun hv => hu (hnonneg.mpr hv)
    rw [sign_neg (lt_of_not_ge hu), sign_neg (lt_of_not_ge hv)]

/-- A bounded function controlled by finitely many polynomial signs admits
partial mesh averaging, with a bound uniform in all polynomial coefficients. -/
theorem flatten_sign_controlled {n m : ℕ} (M R : ℝ) (D : ℕ)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : ∀ x, 0 ≤ f.val x) (hs : supportedInCube f.val R)
    (p : Fin m → MvPolynomial (Fin (n + 1)) ℝ)
    (hp : ∀ j, (p j).totalDegree ≤ D)
    (hcontrol : ∀ x y, (∀ j, SignType.sign (MvPolynomial.eval x (p j)) =
      SignType.sign (MvPolynomial.eval y (p j))) → f.val x = f.val y)
    (L : List (Fin (n + 1))) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M,
      (∀ x, 0 ≤ g.val x) ∧
      (∫⁻ x, ENNReal.ofReal (g.val x)) = (∫⁻ x, ENNReal.ofReal (f.val x)) ∧
      (∀ x y, (∀ i ∉ L, x i = y i) →
        (∀ i ∈ L, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g.val x = g.val y) ∧
      supportedInCube g.val (R + (L.length : ℝ) * ρ) ∧
      densityL1Distance volume g.val f.val ≤
        ENNReal.ofReal ((L.length : ℝ) * (4 * M * ((2 * m * D : ℕ) : ℝ) * ρ) * (2 * R) ^ n) := by
  classical
  let q : Fin (n + 1) → (Fin n → ℝ) → (Fin m × Bool) → Polynomial ℝ :=
    fun i y j => if j.2 then
      k4_native_shear_source_transport.coordinatePolynomial (p j.1) (i.insertNth 0 y) i
    else -k4_native_shear_source_transport.coordinatePolynomial (p j.1) (i.insertNth 0 y) i
  have heval (i : Fin (n + 1)) (y : Fin n → ℝ) (j : Fin m) (t : ℝ) :
      (q i y (j, true)).eval t = MvPolynomial.eval (i.insertNth t y) (p j) := by
    simp only [q, ite_true, k4_native_shear_source_transport.coordinatePolynomial_eval,
      Fin.update_insertNth]
  have hnegative (i : Fin (n + 1)) (y : Fin n → ℝ) (j : Fin m) (t : ℝ) :
      (q i y (j, false)).eval t = -MvPolynomial.eval (i.insertNth t y) (p j) := by
    simp only [q, Bool.false_eq_true, ite_false, Polynomial.eval_neg,
      k4_native_shear_source_transport.coordinatePolynomial_eval, Fin.update_insertNth]
  apply k4_native_base_flattening.partial_polynomial_averaging M R (2 * m * D)
    hM hR f hf hs L q ?_ ?_ hρ
  · intro i hi y t t' htests
    apply hcontrol
    intro j
    apply sign_eq_of_two_weak_tests
    · simpa only [heval] using htests (j, true)
    · simpa only [hnegative] using htests (j, false)
  · intro i hi y
    calc
      ∑ j, (q i y j).natDegree ≤ ∑ _j : Fin m × Bool, D := by
        apply Finset.sum_le_sum
        intro j _
        have hj := (k4_native_shear_source_transport.coordinatePolynomial_natDegree_le
          (p j.1) (i.insertNth 0 y) i).trans (hp j.1)
        rcases j with ⟨j, b⟩
        cases b <;> simpa [q] using hj
      _ = 2 * m * D := by simp [Nat.mul_comm]

/-- A finite polynomial-format partition controls its piecewise constant density. -/
theorem piecewise_density_sign_family {n m D : ℕ} {B : ℝ}
    (C : Fin m → Set (Fin n → ℝ)) (hC : ∀ j, Format n B D (C j))
    (c : Fin m → ℝ) :
    ∃ k : ℕ, (k : ℝ) ≤ (m : ℝ) * B ∧
      ∃ p : Fin k → MvPolynomial (Fin n) ℝ, (∀ i, (p i).totalDegree ≤ D) ∧
      ∀ x y, (∀ i, SignType.sign (MvPolynomial.eval x (p i)) =
        SignType.sign (MvPolynomial.eval y (p i))) →
        (∑ j, c j * (C j).indicator 1 x) = ∑ j, c j * (C j).indicator 1 y := by
  classical
  choose k hk p hp S hS using hC
  let ι := Σ j : Fin m, Fin (k j)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, ?_, fun i => p (e.symm i).1 (e.symm i).2,
    fun i => (hp _ _).1, ?_⟩
  · simp only [ι, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      ∑ j, (k j : ℝ) ≤ ∑ _j : Fin m, B := Finset.sum_le_sum (fun j _ => hk j)
      _ = (m : ℝ) * B := by simp
  · intro x y hxy
    apply Finset.sum_congr rfl
    intro j _
    have hsign : (fun i => SignType.sign (MvPolynomial.eval x (p j i))) =
        (fun i => SignType.sign (MvPolynomial.eval y (p j i))) := by
      funext i
      have he : e.symm (e ⟨j, i⟩) = ⟨j, i⟩ := e.symm_apply_apply _
      have hh := hxy (e ⟨j, i⟩)
      change SignType.sign (MvPolynomial.eval x
        (p (e.symm (e ⟨j, i⟩)).1 (e.symm (e ⟨j, i⟩)).2)) =
        SignType.sign (MvPolynomial.eval y
        (p (e.symm (e ⟨j, i⟩)).1 (e.symm (e ⟨j, i⟩)).2)) at hh
      have hx := congrArg (fun v : ι => SignType.sign (MvPolynomial.eval x (p v.1 v.2))) he
      have hy := congrArg (fun v : ι => SignType.sign (MvPolynomial.eval y (p v.1 v.2))) he
      exact hx.symm.trans (hh.trans hy)
    have hmem : x ∈ C j ↔ y ∈ C j := by
      rw [hS j]
      simp only [mem_ofPred_eq, hsign]
    by_cases hx : x ∈ C j
    · simp [hx, hmem.mp hx]
    · have hy : y ∉ C j := fun hy => hx (hmem.mpr hy)
      simp [hx, hy]

end

end Submission.Obl.k4_scalar_candidate_original_return
