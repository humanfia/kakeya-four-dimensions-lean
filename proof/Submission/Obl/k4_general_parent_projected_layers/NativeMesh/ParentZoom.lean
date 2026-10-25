/- Adapted from this LOT tree o222, sessions x0776/x0774, commit ab4a4d6b,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentZoom.lean.
   Accepted affine mesh transport is imported from Submission.Lib.K4AffineMeshCaps. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.NativeSignalMesh
import Submission.Lib.K4AffineMeshCaps.Transport

/-! The parent zoom as an affine native-point chart, with the hidden variable retained. -/

namespace Submission.Obl.k4_general_parent_projected_layers.NativeMesh

open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable section

namespace Zoom

variable (Z : Zoom)

def baseMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Z.q⁻¹, 0, 0; 0, Z.q⁻¹, 0; -Z.c₃ / Z.w, -Z.c₄ / Z.w, Z.w⁻¹]

def baseShift : Fin 3 → ℝ := ![-Z.t₀ / Z.q, -Z.z₀ / Z.q, -Z.c₂ / Z.w]

def nativePoint (p : NativePoint) : NativePoint := WithLp.toLp 2 (Z.pos (fun i => p i))

theorem measurable_nativePoint : Measurable Z.nativePoint := by
  unfold nativePoint pos
  fun_prop

theorem nativePoint_base (p : NativePoint) :
    rootBaseCoordinates (Z.nativePoint p) =
      affineBase Z.baseMatrix Z.baseShift (rootBaseCoordinates p) := by
  ext i
  fin_cases i <;>
    simp [rootBaseCoordinates, erBase, nativePoint, pos, affineBase, baseMatrix, baseShift,
      dotProduct, Fin.sum_univ_three, div_eq_mul_inv] <;> ring

theorem baseMatrix_det : Z.baseMatrix.det = (Z.q ^ 2 * Z.w)⁻¹ := by
  simp [baseMatrix, Matrix.det_fin_three]
  ring

theorem baseMatrix_det_ne_zero (hZ : Z.Ok) : Z.baseMatrix.det ≠ 0 := by
  rw [baseMatrix_det]
  exact inv_ne_zero (mul_ne_zero (pow_ne_zero 2 hZ.q_ne) hZ.w_ne)

theorem baseMatrix_abs_det_inv (hq : 0 < Z.q) (hw : 0 < Z.w) :
    |Z.baseMatrix.det|⁻¹ = Z.q ^ 2 * Z.w := by
  rw [baseMatrix_det, abs_of_pos (by positivity : 0 < (Z.q ^ 2 * Z.w)⁻¹), inv_inv]

theorem value_push_nativePoint (hZ : Z.Ok) (P : MvPolynomial (Fin 4) ℝ) (p : NativePoint) :
    value (Z.push P) (Z.nativePoint p) = Z.a⁻¹ * value P p := by
  change eval (Z.pos (fun i => p i)) (Z.push P) = Z.a⁻¹ * eval (fun i => p i) P
  rw [eval_push, unpos_pos hZ]

theorem value_pderiv_push_nativePoint (hZ : Z.Ok) (P : MvPolynomial (Fin 4) ℝ)
    (p : NativePoint) :
    value (pderiv 3 (Z.push P)) (Z.nativePoint p) = value (pderiv 3 P) p := by
  change eval (Z.pos (fun i => p i)) (pderiv 3 (Z.push P)) = eval (fun i => p i) (pderiv 3 P)
  rw [eval_pderiv_push hZ, unpos_pos hZ]

theorem value_second_push_nativePoint (hZ : Z.Ok) (P : MvPolynomial (Fin 4) ℝ)
    (p : NativePoint) :
    value (pderiv 3 (pderiv 3 (Z.push P))) (Z.nativePoint p) =
      Z.a * value (pderiv 3 (pderiv 3 P)) p := by
  change eval (Z.pos (fun i => p i)) (pderiv 3 (pderiv 3 (Z.push P))) =
    Z.a * eval (fun i => p i) (pderiv 3 (pderiv 3 P))
  rw [eval_pderiv_pderiv_push hZ, unpos_pos hZ]

theorem goodSet_nativePoint (hZ : Z.Ok) (haZ : Z.a = 1)
    (P S : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (hS : S.totalDegree ≤ 2)
    {K a : ℝ} {p : NativePoint} (hp : p ∈ goodSet K a P S)
    (hnorm : ‖nativeBase (Z.nativePoint p)‖ ≤ K) :
    Z.nativePoint p ∈ goodSet K a (Z.push P) (Z.push S) := by
  have hc (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2) :
      curvature (Z.push Q) 3 = curvature Q 3 := by
    have h := Z.value_second_push_nativePoint hZ Q p
    rw [haZ, one_mul] at h
    simpa only [value, second_pderiv_eq_curvature (Z.push Q) ((Z.push_degree Q).trans hQ),
      second_pderiv_eq_curvature Q hQ, eval_C] using h
  have hvP : value (Z.push P) (Z.nativePoint p) = value P p := by
    rw [value_push_nativePoint Z hZ, haZ, inv_one, one_mul]
  have hvS : value (Z.push S) (Z.nativePoint p) = value S p := by
    rw [value_push_nativePoint Z hZ, haZ, inv_one, one_mul]
  unfold goodSet at hp ⊢
  simp only [mem_ofPred_eq] at hp ⊢
  rw [hvP, value_pderiv_push_nativePoint Z hZ, hc P hP, hvS,
    value_pderiv_push_nativePoint Z hZ, hc S hS]
  exact ⟨hnorm, hp.2⟩

theorem rootMeshCap_nativePoint {μ : Measure NativePoint} {C delta sigma : ℝ}
    (hZ : Z.Ok) (hd : 0 < delta) (hs : 0 < sigma) (hC : 0 ≤ C)
    (hresolve : ∀ i, (∑ j, |Z.baseMatrix i j| * delta) ≤ sigma)
    (hcap : RootMeshCap μ C delta) :
    RootMeshCap (Measure.map Z.nativePoint μ) (27 * C * |Z.baseMatrix.det|⁻¹) sigma := by
  intro q
  have hm : Measurable (fun p => baseMesh sigma (rootBaseCoordinates p)) :=
    (measurable_baseMesh sigma).comp measurable_rootBaseCoordinates
  have hmeas : MeasurableSet {p | baseMesh sigma (rootBaseCoordinates p) = q} :=
    measurableSet_eq_fun hm measurable_const
  rw [Measure.map_apply Z.measurable_nativePoint hmeas]
  change μ {p | baseMesh sigma (rootBaseCoordinates (Z.nativePoint p)) = q} ≤ _
  simp_rw [nativePoint_base]
  have hf := affine_mesh_cell_cap μ rootBaseCoordinates (fun _ => True)
    Z.baseMatrix Z.baseShift (Z.baseMatrix_det_ne_zero hZ) hd hs hC hresolve
    (fun q => by simpa using hcap q) q
  simpa only [and_true] using hf

end Zoom

theorem norm_nativeBase_le_one_of_small {p : NativePoint}
    (hp : rootBaseCoordinates p ∈
      Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4)) :
    ‖nativeBase p‖ ≤ 1 := by
  have hcoord (i : Fin 3) : |nativeBase p i| ≤ (1 : ℝ) / 4 := by
    have hlo : (1 : ℝ) / 8 ≤ nativeBase p i := hp.1 i
    have hhi : nativeBase p i ≤ (1 : ℝ) / 4 := hp.2 i
    rw [abs_of_nonneg (by linarith)]
    exact hhi
  have hnorm := Submission.Obl.k4_scalar_coefficient_clustering.coeff_norm_le_abs_add (nativeBase p)
  linarith [hcoord 0, hcoord 1, hcoord 2]

/-- A parent box is placed strictly inside the unit base cube. The major
velocity and hidden coordinate are retained. -/
def supportZoom (K q g tmid z₀ : ℝ) (c : Fin 5 → ℝ) : Zoom where
  t₀ := tmid - 6 * K * q
  q := 32 * K * q
  z₀ := z₀ - 6 * K * q
  c₂ := c 2 - 3 * K * q * g
  c₃ := c 3
  c₄ := c 4
  w := 16 * K * q * g
  h₀ := 0
  a := 1

theorem supportZoom_ok {K q g : ℝ} (hK : 0 < K) (hq : 0 < q) (hg : 0 < g)
    (tmid z₀ : ℝ) (c : Fin 5 → ℝ) : (supportZoom K q g tmid z₀ c).Ok := by
  constructor <;> dsimp [supportZoom] <;> positivity

theorem supportZoom_jacobian {K q g : ℝ} (hK : 0 < K) (hq : 0 < q) (hg : 0 < g)
    (tmid z₀ : ℝ) (c : Fin 5 → ℝ) :
    |(supportZoom K q g tmid z₀ c).baseMatrix.det|⁻¹ = 16384 * K ^ 3 * q ^ 3 * g := by
  rw [Zoom.baseMatrix_abs_det_inv _ (by dsimp [supportZoom]; positivity)
    (by dsimp [supportZoom]; positivity)]
  dsimp [supportZoom]
  ring

theorem supportZoom_small {K q g tmid z₀ : ℝ} (hK : 0 < K) (hq : 0 < q) (hg : 0 < g)
    (c : Fin 5 → ℝ) (p : NativePoint)
    (ht : |p 0 - tmid| ≤ 2 * K * q) (hz : |p 1 - z₀| ≤ 2 * K * q)
    (hy : |p 2 - c 2 - c 3 * p 0 - c 4 * p 1| ≤ K * q * g) :
    rootBaseCoordinates ((supportZoom K q g tmid z₀ c).nativePoint p) ∈
      Icc (fun _ => (1 : ℝ) / 8) (fun _ => (1 : ℝ) / 4) := by
  let Z := supportZoom K q g tmid z₀ c
  have hdenq : 0 < 32 * K * q := by positivity
  have hdenw : 0 < 16 * K * q * g := by positivity
  have ht' : |Z.pos (fun i => p i) 0 - 3 / 16| ≤ 1 / 16 := by
    have heq : Z.pos (fun i => p i) 0 - 3 / 16 = (p 0 - tmid) / (32 * K * q) := by
      dsimp [Z, supportZoom, Zoom.pos]
      field_simp [hK.ne', hq.ne']
      ring
    rw [heq, abs_div, abs_of_pos hdenq, div_le_iff₀ hdenq]
    nlinarith
  have hz' : |Z.pos (fun i => p i) 1 - 3 / 16| ≤ 1 / 16 := by
    have heq : Z.pos (fun i => p i) 1 - 3 / 16 = (p 1 - z₀) / (32 * K * q) := by
      dsimp [Z, supportZoom, Zoom.pos]
      field_simp [hK.ne', hq.ne']
      ring
    rw [heq, abs_div, abs_of_pos hdenq, div_le_iff₀ hdenq]
    nlinarith
  have hy' : |Z.pos (fun i => p i) 2 - 3 / 16| ≤ 1 / 16 := by
    have heq : Z.pos (fun i => p i) 2 - 3 / 16 =
        (p 2 - c 2 - c 3 * p 0 - c 4 * p 1) / (16 * K * q * g) := by
      dsimp [Z, supportZoom, Zoom.pos]
      field_simp [hK.ne', hq.ne', hg.ne']
      ring
    rw [heq, abs_div, abs_of_pos hdenw, div_le_iff₀ hdenw]
    nlinarith
  have hcoord (i : Fin 3) : |rootBaseCoordinates (Z.nativePoint p) i - 3 / 16| ≤ 1 / 16 := by
    fin_cases i
    · exact ht'
    · exact hz'
    · exact hy'
  constructor
  · intro i
    have h := abs_le.mp (hcoord i)
    change 1 / 8 ≤ rootBaseCoordinates (Z.nativePoint p) i
    linarith
  · intro i
    have h := abs_le.mp (hcoord i)
    change rootBaseCoordinates (Z.nativePoint p) i ≤ 1 / 4
    linarith

end

end Submission.Obl.k4_general_parent_projected_layers.NativeMesh
