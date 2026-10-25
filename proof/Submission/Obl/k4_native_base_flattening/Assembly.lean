import Mathlib
import Submission.Obl.k4_native_base_flattening.Bridge
import Submission.Obl.k4_native_base_flattening.MargSupport
import Submission.Obl.k4_native_base_flattening.ObservationNumerics
import Submission.Obl.k4_native_base_flattening.AveragingBridge
import Submission.Obl.k4_native_base_flattening.Labels

/-!
# Assembly at one resolution

Given an averaged sheared density `h` (bounded, supported in a cube, constant on base mesh cells,
`L¹`-close to the native density), the marginal of `h` is a common floor-label table for every
observation depth. Its factor-two and cutoff exceptions have mass at most `2 L¹ + ε · support`,
for every measurable version of the true observation density.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_native_base_flattening

open Submission.Obl.k4_profile_density_bounds (Observation reference Base State Line observe width
  measurable_observe width_pos)
open Submission.Lib.K4ModelReduction (densityL1Distance supportedInCube)

lemma sigmaFinite_reference : SigmaFinite reference := by
  unfold reference
  infer_instance

/-- The observation density of an averaged sheared density. -/
noncomputable def approxDensity (n r u : ℝ) (h : (Fin 7 → ℝ) → ℝ) : Observation → ℝ≥0∞ :=
  marg (width n r) (width n u) (fun q => ENNReal.ofReal (h (join q)))

/-- The common floor-label table of an averaged sheared density. -/
noncomputable def table (n : ℝ) (H : ℕ) (R U r u : ℝ) (h : (Fin 7 → ℝ) → ℝ)
    (z : Fin 6 → ℤ) : ℝ :=
  (commonLabelTable n H R U r u (approxDensity n r u h) z).toReal

lemma approxDensity_le {n : ℝ} (hn : 2 ≤ n) (M : ℕ) (r u : ℝ) {h : (Fin 7 → ℝ) → ℝ}
    (hb : ∀ x, 0 ≤ h x ∧ h x ≤ n ^ (2 * M)) (hs : supportedInCube h (n ^ (M + 3)))
    (y : Observation) :
    approxDensity n r u h y ≤ ENNReal.ofReal (n ^ (2 * M + 4 * (M + 3) + 4)) :=
  marg_le_polynomial (2 * M) (M + 3) hn _
    (fun q => ENNReal.ofReal_le_ofReal (hb _).2) (joined_density_support h hs) y

lemma table_nonneg (n : ℝ) (H : ℕ) (R U r u : ℝ) (h : (Fin 7 → ℝ) → ℝ) (z : Fin 6 → ℤ) :
    0 ≤ table n H R U r u h z := ENNReal.toReal_nonneg

lemma table_le {n : ℝ} (hn : 2 ≤ n) (M : ℕ) (H : ℕ) (R U r u : ℝ) {h : (Fin 7 → ℝ) → ℝ}
    (hb : ∀ x, 0 ≤ h x ∧ h x ≤ n ^ (2 * M)) (hs : supportedInCube h (n ^ (M + 3)))
    (z : Fin 6 → ℤ) : table n H R U r u h z ≤ n ^ (2 * M + 4 * (M + 3) + 4) := by
  have hn0 : 0 ≤ n := by linarith
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (approxDensity_le hn M r u hb hs _)

/-- The table, evaluated at the common floor label of a state, is the approximant at the
observation of that state. -/
lemma ofReal_table_label {n : ℝ} (hn : 2 ≤ n) (M H : ℕ) {R U r u : ℝ} (hr : 0 ≤ r)
    (hrR : r ≤ R) (hu : 0 ≤ u) (huU : u ≤ U) {h : (Fin 7 → ℝ) → ℝ}
    (hb : ∀ x, 0 ≤ h x ∧ h x ≤ n ^ (2 * M)) (hs : supportedInCube h (n ^ (M + 3)))
    (hcell : ∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
      (∀ i ∈ baseCoordinates, ⌊n ^ H * x i⌋ = ⌊n ^ H * y i⌋) → h x = h y)
    (p : State) :
    ENNReal.ofReal (table n H R U r u h (commonFloorLabel n H R U p)) =
      approxDensity n r u h (observe n r u p) := by
  have hF : ObservationBaseMeshConstant n H (approxDensity n r u h) :=
    marg_base_mesh_constant n H (width n r) (width n u) h hcell
  rw [table, ← common_label_factorization hn H hr hrR hu huU _ hF p]
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (approxDensity_le hn M r u hb hs _))

/-- The exceptions of the table at one resolution and one pair of depths. -/
theorem table_exception_mass {n : ℝ} (hn : 2 ≤ n) (M H : ℕ) {m : ℕ} (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (i : Fin m → ℕ) {A : Fin m → Set (Fin 6 → ℝ)}
    (hA : ∀ j, MeasurableSet (A j)) {E : Set State} (hE : MeasurableSet E)
    {h : (Fin 7 → ℝ) → ℝ} (hh : Measurable h) (hb : ∀ x, 0 ≤ h x ∧ h x ≤ n ^ (2 * M))
    (hcell : ∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
      (∀ i ∈ baseCoordinates, ⌊n ^ H * x i⌋ = ⌊n ^ H * y i⌋) → h x = h y)
    (hs : supportedInCube h (n ^ (M + 3)))
    (he : densityL1Distance volume h
      (fun x => ∑ j, nativeComponentDensity (c j) (A j) (eventFiber E (i j)) x) ≤
        ENNReal.ofReal ((n ^ (10 : ℕ))⁻¹))
    {R U r u : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hu : 0 ≤ u) (huU : u ≤ U) (d e : ℕ)
    (hRd : R ≤ (d : ℝ)) (hUe : U ≤ (e : ℝ)) (C : ℕ)
    (hC : 6 * (M + 3) + d + 2 * e + 12 + 4 ≤ C)
    (G : Observation → ℝ≥0∞) (hG : Measurable G)
    (hmap : Measure.map (observe n r u) (((∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun x => (i j, x)) ((volume : Measure (Fin 6 → ℝ)).restrict (A j))).prod
        (volume : Measure ℝ)).restrict E) = reference.withDensity G) :
    (((∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun x => (i j, x)) ((volume : Measure (Fin 6 → ℝ)).restrict (A j))).prod
        (volume : Measure ℝ)).restrict E)
      {p | G (observe n r u p) <
          (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (table n H R U r u h (commonFloorLabel n H R U p)) ∨
        (2 : ℝ≥0∞) * ENNReal.ofReal (table n H R U r u h (commonFloorLabel n H R U p)) <
          G (observe n r u p) ∨
        ENNReal.ofReal (table n H R U r u h (commonFloorLabel n H R U p)) <
          ENNReal.ofReal (n ^ (-(C : ℝ)))} ≤ ENNReal.ofReal (n ^ (-1 : ℝ)) := by
  set μ := ((∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun x => (i j, x)) ((volume : Measure (Fin 6 → ℝ)).restrict (A j))).prod
        (volume : Measure ℝ)).restrict E with hμ
  set F := approxDensity n r u h with hFdef
  set ε := ENNReal.ofReal (n ^ (-(C : ℝ))) with hε
  have hO := measurable_observe n r u
  have hFm : Measurable F :=
    measurable_marg _ _ (ENNReal.measurable_ofReal.comp (hh.comp measurable_join))
  set Bad : Set Observation := {y | G y < 2⁻¹ * F y ∨ 2 * F y < G y ∨ F y < ε} with hBad
  have hBadm : MeasurableSet Bad :=
    (measurableSet_lt hG (measurable_const.mul hFm)).union
      ((measurableSet_lt (measurable_const.mul hFm) hG).union
        (measurableSet_lt hFm measurable_const))
  have hset : {p | G (observe n r u p) <
          (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (table n H R U r u h (commonFloorLabel n H R U p)) ∨
        (2 : ℝ≥0∞) * ENNReal.ofReal (table n H R U r u h (commonFloorLabel n H R U p)) <
          G (observe n r u p) ∨
        ENNReal.ofReal (table n H R U r u h (commonFloorLabel n H R U p)) < ε} =
      observe n r u ⁻¹' Bad := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, hBad,
      ofReal_table_label hn M H hr hrR hu huU hb hs hcell p]
    rfl
  -- the true density and version uniqueness
  have hG0 := exists_density c i hA hE n r u
  have hG0m : Measurable (marg (width n r) (width n u) (nativeDensity c i A E)) :=
    measurable_marg _ _ (measurable_nativeDensity c i hA hE)
  haveI := sigmaFinite_reference
  have hae : G =ᵐ[reference] marg (width n r) (width n u) (nativeDensity c i A E) :=
    (withDensity_eq_iff_of_sigmaFinite hG.aemeasurable hG0m.aemeasurable).mp
      (hmap.symm.trans hG0)
  have hL1 : ∫⁻ y, ediff (G y) (F y) ∂reference ≤ ENNReal.ofReal ((n ^ (10 : ℕ))⁻¹) := by
    calc
      _ = ∫⁻ y, ediff (marg (width n r) (width n u) (nativeDensity c i A E) y) (F y)
            ∂reference := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with y hy
        rw [hy]
      _ ≤ _ := lintegral_ediff_marg_native_le c hc i hA hE _ _ hh (fun x => (hb x).1)
      _ ≤ _ := he
  have hsupp : reference {y | F y ≠ 0} ≤
      ENNReal.ofReal (n ^ (6 * (M + 3) + d + 2 * e + 12)) :=
    reference_support_marg_power_le (M + 3) d e hn hr (hrR.trans hRd) hu (huU.trans hUe) _
      (joined_density_support h hs)
  rw [hset, ← Measure.map_apply hO hBadm, hmap, withDensity_apply _ hBadm]
  calc
    _ ≤ 2 * ∫⁻ y, ediff (G y) (F y) ∂reference + ε * reference {y | F y ≠ 0} :=
      bad_lintegral_le reference hG hFm ε
    _ ≤ _ := observation_exception_budget hn _ C hC _ _ hL1 hsupp

end Submission.Obl.k4_native_base_flattening
