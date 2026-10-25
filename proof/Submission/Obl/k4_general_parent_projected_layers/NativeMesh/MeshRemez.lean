/- Adapted from this LOT tree o222, session x0774, commit 109e510d,
   Submission/Obl/k4_projected_parent_contact_reduction/MeshRemez.lean.
   Existing source attributions are retained below. Accepted mesh-saturation
   results are imported from Submission.Lib.K4AffineMeshCaps.Saturation. -/
import Submission.Lib.K4AffineMeshCaps.Saturation
import Submission.Lib.K4PolynomialRemezThree.Comparison
import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialBounds
import Submission.Obl.k4_scalar_coefficient_clustering.Geometry

/-! Coefficient calibration from one sufficiently fine fixed mesh. -/

namespace Submission.Obl.k4_general_parent_projected_layers.NativeMesh

open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4PolynomialRemezThree
open Submission.Obl.k4_scalar_coefficient_clustering (coeff_norm_le_abs_add)

noncomputable section

private theorem small_coordinates_norm {z : Fin 3 → ℝ}
    (hz : ∀ i, |z i| ≤ (5 : ℝ) / 16) : ‖WithLp.toLp 2 z‖ ≤ 1 := by
  calc
    ‖WithLp.toLp 2 z‖ ≤ |z 0| + |z 1| + |z 2| := coeff_norm_le_abs_add _
    _ ≤ 1 := by linarith [hz 0, hz 1, hz 2]

private theorem coordinate_distance_norm {z w : Fin 3 → ℝ} {delta : ℝ}
    (h : ∀ i, |z i - w i| ≤ delta) :
    ‖WithLp.toLp 2 z - WithLp.toLp 2 w‖ ≤ 3 * delta := by
  calc
    _ ≤ |(WithLp.toLp 2 z - WithLp.toLp 2 w) 0| +
        |(WithLp.toLp 2 z - WithLp.toLp 2 w) 1| +
          |(WithLp.toLp 2 z - WithLp.toLp 2 w) 2| := coeff_norm_le_abs_add _
    _ = |z 0 - w 0| + |z 1 - w 1| + |z 2 - w 2| := rfl
    _ ≤ _ := by linarith [h 0, h 1, h 2]

/-- The mesh resolution is chosen from the degree and original mass ratio,
not from the coefficients of the polynomial being calibrated. -/
theorem finite_mesh_polynomial_remez (D : ℕ) :
    ∃ A L : ℝ, 0 < A ∧ 0 < L ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
        (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
        (delta C eta E : ℝ),
        0 < delta → delta ≤ 1 / 16 → 0 < C → 0 < eta → eta ≤ 1 → 0 ≤ E →
        A * L * (32 * ((D : ℝ) + 1) / eta) ^ (3 * D) * delta ≤ 1 / 2 →
        ∀ (S : Set (Fin 3 → ℝ)),
          S ⊆ Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4) →
          (∀ q : Fin 3 → ℤ,
            μ {p | baseMesh delta (Z p) = q ∧ condition p} ≤
              ENNReal.ofReal (C * delta ^ 3)) →
          ENNReal.ofReal (C * eta) ≤ μ {p | Z p ∈ S ∧ condition p} →
          ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
            (∀ z ∈ S, |eval z P| ≤ E) →
            ∀ e, |P.coeff e| ≤
              2 * A * (32 * ((D : ℝ) + 1) / eta) ^ (3 * D) * E := by
  classical
  obtain ⟨A₀, hA₀, hremez⟩ := exists_coefficient_bound_from_base_mass D
  obtain ⟨L₀, hL₀, hlip⟩ :=
    Submission.Obl.k4_stable_native_signal_oscillation.exists_polynomial_lipschitz_degree D
  let A : ℝ := (((D + 1) ^ 3 : ℕ) : ℝ) * A₀
  let L : ℝ := 3 * L₀
  have hcardpos : 0 < (((D + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hA : 0 < A := mul_pos hcardpos hA₀
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨A, L, hA, hL, ?_⟩
  intro Ω inst μ Z condition delta C eta E hd hd1 hC heta heta1 hE hsmall
    S hS hcap hmass P hP hbound e
  let R : ℝ := (32 * ((D : ℝ) + 1) / eta) ^ (3 * D)
  let M : ℝ := coefficientMass P
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hM : 0 ≤ M := coefficientMass_nonneg P
  have hcoeff (d : Fin 3 →₀ ℕ) : |P.coeff d| ≤ M := abs_coeff_le_coefficientMass P d
  have hcoordinates (z : Fin 3 → ℝ) (hz : z ∈ meshSaturation delta S) (i : Fin 3) :
      0 ≤ z i ∧ z i ≤ (5 : ℝ) / 16 := by
    obtain ⟨w, hw, hdist⟩ := meshSaturation_close hd S hz
    have hwlo : (1 : ℝ) / 8 ≤ w i := (hS hw).1 i
    have hwhi : w i ≤ (1 : ℝ) / 4 := (hS hw).2 i
    have hh := abs_le.mp (hdist i)
    constructor <;> linarith
  have hunit : meshSaturation delta S ⊆ Icc (0 : Fin 3 → ℝ) 1 := by
    intro z hz
    constructor
    · intro i
      exact (hcoordinates z hz i).1
    · intro i
      have := (hcoordinates z hz i).2
      norm_num at ⊢
      linarith
  have hnorm (z : Fin 3 → ℝ) (hz : z ∈ meshSaturation delta S) :
      ‖WithLp.toLp 2 z‖ ≤ 1 := by
    apply small_coordinates_norm
    intro i
    rw [abs_of_nonneg (hcoordinates z hz i).1]
    exact (hcoordinates z hz i).2
  have hvariation (z w : Fin 3 → ℝ) (hz : z ∈ meshSaturation delta S)
      (hw : w ∈ S) (hdist : ∀ i, |z i - w i| ≤ delta) :
      |eval z P - eval w P| ≤ L * M * delta := by
    have hws : w ∈ meshSaturation delta S := subset_meshSaturation delta S hw
    have h := hlip P hP M hM hcoeff (WithLp.toLp 2 z) (WithLp.toLp 2 w)
      (hnorm z hz) (hnorm w hws)
    calc
      _ ≤ L₀ * M * ‖WithLp.toLp 2 z - WithLp.toLp 2 w‖ := h
      _ ≤ L₀ * M * (3 * delta) :=
        mul_le_mul_of_nonneg_left (coordinate_distance_norm hdist) (mul_nonneg hL₀.le hM)
      _ = L * M * delta := by dsimp [L]; ring
  have hsaturated (z : Fin 3 → ℝ) (hz : z ∈ meshSaturation delta S) :
      |eval z P| ≤ E + L * M * delta := by
    obtain ⟨w, hw, hdist⟩ := meshSaturation_close hd S hz
    calc
      _ = |(eval z P - eval w P) + eval w P| := by congr 1; ring
      _ ≤ |eval z P - eval w P| + |eval w P| := abs_add_le _ _
      _ ≤ L * M * delta + E := add_le_add (hvariation z w hz hw hdist) (hbound w hw)
      _ = _ := by ring
  have hvolume : ENNReal.ofReal eta ≤ volume (meshSaturation delta S) :=
    ofReal_le_meshSaturation_volume μ Z condition hd hC hcap S hmass
  have hpoint (d : Fin 3 →₀ ℕ) :
      |P.coeff d| ≤ A₀ * R * (E + L * M * delta) :=
    hremez P hP (meshSaturation delta S) eta (E + L * M * delta)
      heta heta1 (by positivity) hunit hvolume hsaturated d
  have hcard : (P.support.card : ℝ) ≤ (((D + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast card_support_le_degree_box 3 D P hP
  have hmassbound : M ≤ A * R * (E + L * M * delta) := by
    calc
      M = ∑ d ∈ P.support, |P.coeff d| := rfl
      _ ≤ ∑ _d ∈ P.support, A₀ * R * (E + L * M * delta) :=
        Finset.sum_le_sum (fun d hd => hpoint d)
      _ = (P.support.card : ℝ) * (A₀ * R * (E + L * M * delta)) := by simp
      _ ≤ (((D + 1) ^ 3 : ℕ) : ℝ) * (A₀ * R * (E + L * M * delta)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = A * R * (E + L * M * delta) := by dsimp [A]; ring
  change A * L * R * delta ≤ 1 / 2 at hsmall
  have habsorb : A * R * (E + L * M * delta) ≤ A * R * E + M / 2 := by
    calc
      _ = A * R * E + (A * L * R * delta) * M := by ring
      _ ≤ A * R * E + (1 / 2) * M :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall hM)
      _ = _ := by ring
  have hfinal : M ≤ 2 * A * R * E := by linarith [hmassbound.trans habsorb]
  exact (hcoeff e).trans hfinal

end

end Submission.Obl.k4_general_parent_projected_layers.NativeMesh
