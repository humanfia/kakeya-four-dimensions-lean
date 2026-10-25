/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/ChartCrossing.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/ChartCrossing.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.GridCrossing
import Submission.Obl.k4_balanced_native_packet_transport.CPF.HiddenPolynomial
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices

/-! Observation crossings for the actual quadratic charts in the frozen problem. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MvPolynomial Set

-- The identical hidden polynomial and its four laws are imported from our existing module.
theorem hiddenPolynomial_eval_obs (R : Test) (B a : ℝ) (p : Incidence) :
    (hiddenPolynomial R (obs B a p).1).eval ((x p.1 p.2) 3) = eval (x p.1 p.2) R := by
  rw [hiddenPolynomial_eval]
  apply congrArg (fun v : Fin 4 → ℝ => eval v R)
  funext i
  fin_cases i <;> simp [obs, x]

/-- A crossing uses only the observed base and hidden bin. -/
def ChartCrosses (κ : ℝ) (T : ℕ) (j a B : ℝ) (c u : Spatial) (Q : Frame)
    (R : Test) (m : ℕ) (o : Observation) : Prop :=
  o.1 0 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧
    ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![o.1 1, o.1 2] - c - o.1 0 • u)‖ ≤ κ ∧
    QuadraticCrosses (hiddenPolynomial R o.1) a B κ m o.2

/-- Every selected incidence belongs to the crossing of its own chart. -/
theorem Chart.crosses_of_mem {Nk κ j r B : ℝ} {M D T m : ℕ}
    {E : Set Incidence} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence} {ex : Prop}
    (h : Chart Nk M D κ T j r B E c u Q R A F ex)
    (hB : 0 < B) (hκ : 1 ≤ κ) (hmesh : 4 * κ ^ 2 ≤ (m : ℝ))
    {p : Incidence} (hp : p ∈ F) :
    ChartCrosses κ T j (δ Nk r) B c u Q R m (obs B (δ Nk r) p) := by
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hwhole, hsel, _⟩ := h
  obtain ⟨_, hpA, hpt, hplo⟩ := hsel p hp
  obtain ⟨_, _, htest⟩ := hwhole p.1 hpA
  obtain ⟨hspace, hval, hder, hcurv⟩ := htest p.2 hpt
  refine ⟨?_, ?_, ?_⟩
  · simpa [obs] using hpt
  · simpa [obs, y] using hspace
  · have ha : 0 < δ Nk r := by unfold δ; positivity
    have hv := quadratic_crosses_of_tests (hiddenPolynomial R (obs B (δ Nk r) p).1)
      ((hiddenPolynomial_degree _ _).trans hdeg) ha hB hκ hmesh
      (w := (x p.1 p.2) 3)
    simp only [hiddenPolynomial_derivative, hiddenPolynomial_eval_obs] at hv
    have hbin : (x p.1 p.2) 3 / (δ Nk r / B) = B * (x p.1 p.2) 3 / δ Nk r := by
      field_simp
    simpa only [hbin, obs] using hv hval hplo hder hcurv

/-- The number of crossing hidden bins at any observed base is uniformly bounded. -/
theorem ChartCrosses.finite_bins {κ j a B : ℝ} {T m : ℕ} {c u : Spatial}
    {Q : Frame} {R : Test} (hR : R.totalDegree ≤ 2)
    (ha : 0 < a) (hB : 0 < B) (hκ : 0 < κ) (z : EuclideanSpace ℝ (Fin 3)) :
    {n : ℤ | ChartCrosses κ T j a B c u Q R m (z, n)}.Finite ∧
      ({n : ℤ | ChartCrosses κ T j a B c u Q R m (z, n)}.ncard : ℝ) ≤
        8 * (1 + 4 * κ ^ 2) := by
  have h := quadratic_crossing_bins (hiddenPolynomial R z)
    ((hiddenPolynomial_degree _ _).trans hR) ha hB hκ m
  have hs : {n : ℤ | ChartCrosses κ T j a B c u Q R m (z, n)} ⊆
      {n : ℤ | QuadraticCrosses (hiddenPolynomial R z) a B κ m n} :=
    fun _ hn => hn.2.2
  have hn : ({n : ℤ | ChartCrosses κ T j a B c u Q R m (z, n)}.ncard : ℝ) ≤
      ({n : ℤ | QuadraticCrosses (hiddenPolynomial R z) a B κ m n}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hs h.1
  exact ⟨h.1.subset hs, hn.trans h.2⟩

end Submission.Obl.k4_balanced_native_packet_transport.CPF
