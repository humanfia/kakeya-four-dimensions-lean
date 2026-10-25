import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceTube
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.PhysicalStateCore

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open Submission.Lib.K4ChartLifting
open Submission.Lib.K4OriginalGeometricReference.Analytic

noncomputable section

namespace SourceNormalization

def scale (T : ℕ) (s : ℝ) : ℝ := s*((2:ℝ)^T)⁻¹

def matrix (T : ℕ) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (scale T s)⁻¹ • 1

def inverseMatrix (T : ℕ) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := scale T s • 1

def shift (T j : ℕ) (c u : P2) (s : ℝ) (b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => b i-(scale T s)⁻¹*Broad.parentBaseOrigin T j c u i

def inverseShift (T j : ℕ) (c u : P2) (s : ℝ) (b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => Broad.parentBaseOrigin T j c u i-scale T s*b i

theorem scale_pos (T : ℕ) {s : ℝ} (hs : 0 < s) : 0 < scale T s := by
  dsimp [scale]
  positivity

theorem inverse (T j : ℕ) (c u : P2) {s : ℝ} (hs : 0 < s) (b : Fin 3 → ℝ) :
    inverseMatrix T s*matrix T s = 1 ∧
      ∀ i, inverseShift T j c u s b i =
        -∑ k:Fin 3, inverseMatrix T s i k*shift T j c u s b k := by
  have hn := (scale_pos T hs).ne'
  constructor
  · simp only [matrix,inverseMatrix,Matrix.smul_mul,Matrix.mul_smul,one_mul,smul_smul]
    rw [inv_mul_cancel₀ hn,one_smul]
  · intro i
    simp only [inverseMatrix,shift,inverseShift,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    field_simp
    <;> ring

theorem normalized_base_apply (T j : ℕ) (c u : P2) {s : ℝ} (hs : 0 < s)
    (b : Fin 3 → ℝ) (B : ℝ) (e : Ev) (i : Fin 3) :
    (Analytic.pointOfCoordinates (Analytic.coordinateMap (shift T j c u s b) (matrix T s) B
      (Analytic.graphPoint e.1 e.2))).1 i = b i+packetBase T j c u e i/s := by
  change Analytic.coordinateMap _ _ _ _ i.castSucc = _
  rw [Analytic.coordinateMap_castSucc]
  simp only [shift,matrix,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite,
    mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hsz := hs.ne'
  have hh : (2:ℝ)^T ≠ 0 := by positivity
  fin_cases i <;>
    simp [Broad.parentBaseOrigin,packetBase,Analytic.graphPoint,xp,scale] <;>
    field_simp <;> ring

/-- The normalized potential uses only the bounded source coordinates:
the old physical clock cancels from its affine substitution. -/
def potential (s : ℝ) (b : Fin 3 → ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := bind₁ (fun i => C s*(X i-C (b i))) P

theorem eval_potential (s : ℝ) (b z : Fin 3 → ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    eval z (potential s b P) = eval (fun i => s*(z i-b i)) P := by
  change eval₂Hom (RingHom.id ℝ) z (bind₁ _ P) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun x:Fin 3 → ℝ => eval₂Hom (RingHom.id ℝ) x P)
  funext i
  simp

theorem potential_degree (s : ℝ) (b : Fin 3 → ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    (potential s b P).totalDegree ≤ P.totalDegree := by
  apply Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine
  intro i
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C,zero_add] using
    (totalDegree_sub _ _).trans (by simp)

theorem normalized_potential (T j : ℕ) (c u : P2) {s : ℝ} (hs : 0 < s)
    (b : Fin 3 → ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    Analytic.basePullback (inverseShift T j c u s b) (inverseMatrix T s)
      (Broad.parentPotentialPullback T j c u P) = potential s b P := by
  apply MvPolynomial.funext
  intro z
  rw [Analytic.eval_basePullback,eval_potential,Broad.parentPotentialPullback,
    basePotentialPullback_eval,one_mul]
  apply congrArg (fun x:Fin 3 → ℝ => eval x P)
  funext i
  rw [affineBaseCoordinates_eval]
  simp only [Broad.parentBaseShift,Broad.parentBaseMatrix,inverseShift,inverseMatrix,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite,mul_one,mul_zero,
    ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hh : (2:ℝ)^T ≠ 0 := by positivity
  dsimp [scale]
  field_simp
  <;> ring

/-- Affine source normalization preserves the original factor `h` in the
potential coefficients, even when the parent quadratic has large coefficients. -/
theorem potential_coefficient_bound {q : ℕ} {P : MvPolynomial (Fin 3) ℝ}
    (hP : P.totalDegree ≤ q) {K h s S : ℝ} (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hS : 1 ≤ S) (b : Fin 3 → ℝ) (hc : ∀ m, |P.coeff m| ≤ K*h)
    (hb : ∀ i, |s| * (1+|b i|) ≤ S) (m : Fin 3 →₀ ℕ) :
    |(potential s b P).coeff m| ≤ (((q+1)^3:ℕ):ℝ)*K*S^q*h := by
  have hsubst (i:Fin 3) : coeffL1 (C s*(X i-C (b i)):MvPolynomial (Fin 3) ℝ) ≤ S := by
    apply (coeffL1_C_mul_le _ _).trans
    apply le_trans _ (hb i)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (coeffL1_sub_le _ _).trans (by rw [coeffL1_X,coeffL1_C])
  have hmass := coeffL1_bind₁_le (fun i => C s*(X i-C (b i))) S hS hsubst P
  have hraw := coeffL1_le_of_coeff_le P hP (K*h) hc
  calc
    _ ≤ coeffL1 (potential s b P) := abs_coeff_le_coeffL1 _ _
    _ ≤ coeffL1 P*S^P.totalDegree := hmass
    _ ≤ (((q+1)^3:ℕ):ℝ)*(K*h)*S^q := mul_le_mul hraw
      (pow_le_pow_right₀ hS hP) (by positivity) (by positivity)
    _ = _ := by ring

/-- One fixed isotropic frame places the actual source inside the positive
unit cube and strictly inside the analytic unit ball. -/
theorem source_cube {q T j : ℕ} {ν : Measure Ln} {B a ζ d : ℝ} {c u : P2} {P0 : Po}
    {A : Set Ln} {F H : Set Ev} (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)
    (e : Ev) (he : e ∈ source.S) :
    let z := (Analytic.pointOfCoordinates (Analytic.coordinateMap
      (shift T j c u (8*source.K) (fun _ => 1/8)) (matrix T (8*source.K)) B
      (Analytic.graphPoint e.1 e.2))).1
    (∀ i:Fin 3, z i ∈ Icc (0:ℝ) (1/4)) ∧ ‖z‖ ≤ 3/4 := by
  intro z
  have hK : 0 < source.K := by linarith [source.K_two]
  have hcoord (i:Fin 3) : z i ∈ Icc (0:ℝ) (1/4) := by
    have heq := normalized_base_apply T j c u (by positivity : 0<8*source.K)
      (fun _ => 1/8) B e i
    change z i = _ at heq
    rw [heq]
    have hquot : |packetBase T j c u e i/(8*source.K)| ≤ 1/8 := by
      rw [abs_div,abs_of_pos (by positivity : 0<8*source.K),
        div_le_iff₀ (by positivity : 0<8*source.K)]
      nlinarith [source.coordinate_bound e he i]
    obtain ⟨hl,hu⟩ := abs_le.mp hquot
    constructor <;> linarith
  refine ⟨hcoord,?_⟩
  calc
    _ ≤ ∑ i:Fin 3, |z i| :=
      Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs z
    _ ≤ ∑ _i:Fin 3, (1/4:ℝ) := Finset.sum_le_sum fun i _ =>
      by simpa only [abs_of_nonneg (hcoord i).1] using (hcoord i).2
    _ = _ := by norm_num

theorem normalized_state_distance {q T j : ℕ} {ν : Measure Ln} {B a ζ d : ℝ}
    {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
    (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)
    {s : ℝ} (hs : 0 < s) (b : Fin 3 → ℝ) {e f : Ev}
    (hcode : source.fineState e = source.fineState f) :
    ‖(Analytic.pointOfCoordinates (Analytic.coordinateMap (shift T j c u s b) (matrix T s) B
        (Analytic.graphPoint e.1 e.2))).1-
      (Analytic.pointOfCoordinates (Analytic.coordinateMap (shift T j c u s b) (matrix T s) B
        (Analytic.graphPoint f.1 f.2))).1‖ ≤ 3*source.ε/s := by
  have heq : (Analytic.pointOfCoordinates (Analytic.coordinateMap
        (shift T j c u s b) (matrix T s) B (Analytic.graphPoint e.1 e.2))).1-
      (Analytic.pointOfCoordinates (Analytic.coordinateMap
        (shift T j c u s b) (matrix T s) B (Analytic.graphPoint f.1 f.2))).1 =
      s⁻¹ • (packetBase T j c u e-packetBase T j c u f) := by
    ext i
    simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
      normalized_base_apply T j c u hs]
    ring
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (source.fine_state_close hcode).1 (inv_nonneg.mpr hs.le)

/-- The exact base-potential identity survives the discriminant zoom. -/
theorem zoomed_potential (T j : ℕ) (c u : P2) {s : ℝ} (hs : 0<s) (b cz:Fin 3 → ℝ)
    {lam : ℝ} (hlam : lam ≠ 0) (P:MvPolynomial (Fin 3) ℝ) :
    Analytic.basePullback (Analytic.zoomShift (inverseShift T j c u s b)
      (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam)
      (Broad.parentPotentialPullback T j c u P) =
    Analytic.basePullback cz (lam⁻¹ • 1) (potential s b P) := by
  apply MvPolynomial.funext
  intro z
  rw [Analytic.eval_zoom_potential _ _ _ hlam,normalized_potential T j c u hs,
    Analytic.eval_basePullback]
  apply congrArg (fun x:Fin 3 → ℝ => eval x (potential s b P))
  funext i
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite,mul_one,mul_zero,
    ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  ring

/-- The small physical coefficient factor `h` also survives the zoom. -/
theorem zoomed_potential_coefficient_bound {q T j : ℕ} {P:MvPolynomial (Fin 3) ℝ}
    (hP:P.totalDegree ≤ q) (c u:P2) {K h s S lam:ℝ} (hK:0≤K) (hh:0≤h)
    (hs:0<s) (hS:1≤S) (hlam:1≤lam) (b cz:Fin 3 → ℝ)
    (hc:∀m,|P.coeff m|≤K*h) (hb:∀i,|s| * (1+|b i|)≤S) (hcz:∀i,|cz i|≤1)
    (m:Fin 3 →₀ ℕ) :
    |(Analytic.basePullback (Analytic.zoomShift (inverseShift T j c u s b)
      (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam)
      (Broad.parentPotentialPullback T j c u P)).coeff m| ≤
      (((q+1)^3:ℕ):ℝ)^2*K*(2*S)^q*h := by
  have hLamPos : 0<lam := by linarith
  have hLamInv : |lam⁻¹|≤1 := by
    rw [abs_of_pos (inv_pos.mpr hLamPos)]
    exact (inv_le_one₀ hLamPos).mpr hlam
  have hsubst (i:Fin 3) : coeffL1 (Analytic.baseSubstitution cz (lam⁻¹ • 1) i) ≤ 2 := by
    have heq : Analytic.baseSubstitution cz (lam⁻¹ • 1) i = C (cz i)+C lam⁻¹*X i := by
      simp [Analytic.baseSubstitution,Matrix.smul_apply,Matrix.one_apply,apply_ite,ite_mul]
    rw [heq]
    apply (coeffL1_add_le _ _).trans
    have hx := coeffL1_C_mul_le lam⁻¹ (X i:MvPolynomial (Fin 3) ℝ)
    rw [coeffL1_X,mul_one] at hx
    rw [coeffL1_C]
    linarith [hcz i]
  rw [zoomed_potential T j c u hs b cz hLamPos.ne']
  let n : ℝ := (((q+1)^3:ℕ):ℝ)
  have hraw := coeffL1_le_of_coeff_le (potential s b P) ((potential_degree s b P).trans hP)
    (n*K*S^q*h) (potential_coefficient_bound hP hK hh hS b hc hb)
  have hmass := coeffL1_bind₁_le (Analytic.baseSubstitution cz (lam⁻¹ • 1))
    2 (by norm_num) hsubst (potential s b P)
  calc
    _ ≤ coeffL1 (Analytic.basePullback cz (lam⁻¹ • 1) (potential s b P)) :=
      abs_coeff_le_coeffL1 _ _
    _ ≤ coeffL1 (potential s b P)*2^(potential s b P).totalDegree := hmass
    _ ≤ (n*(n*K*S^q*h))*2^q := mul_le_mul hraw
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) ((potential_degree s b P).trans hP))
      (by positivity) (by positivity)
    _ = _ := by dsimp [n]; rw [mul_pow]; ring

def baseMap (s : ℝ) (b : Fin 3 → ℝ) (z : P3) : P3 := WithLp.toLp 2 b+s⁻¹ • z

theorem measurable_baseMap (s : ℝ) (b : Fin 3 → ℝ) : Measurable (baseMap s b) := by
  unfold baseMap
  fun_prop

theorem volume_preimage_baseMap {s : ℝ} (hs:0<s) (b:Fin 3 → ℝ) (U:Set P3) :
    volume (baseMap s b ⁻¹' U) = ENNReal.ofReal (s^3)*volume U := by
  have heq : baseMap s b = Analytic.zoomMap (-s • WithLp.toLp 2 b) s⁻¹ := by
    funext z
    ext i
    simp [baseMap,Analytic.zoomMap,div_eq_mul_inv]
    field_simp
    <;> ring
  rw [heq,Analytic.volume_preimage_zoomMap _ (inv_pos.mpr hs)]
  simp only [inv_pow,ENNReal.ofReal_inv_of_pos (pow_pos hs 3),inv_inv]

/-- The density cap changes by the explicit isotropic Jacobian and keeps
the same original group mass in its denominator. -/
theorem density_after_normalization {Ω:Type*} [MeasurableSpace Ω]
    (μ:Measure Ω) (G:Set Ω) (Z:Ω → P3) {D s:ℝ} (hD:0≤D) (hs:0<s) (b:Fin 3 → ℝ)
    (hdom:∀U:Set P3,MeasurableSet U →
      μ (G ∩ Z ⁻¹' U) ≤ ENNReal.ofReal D*μ G*volume U) :
    ∀U:Set P3,MeasurableSet U →
      μ (G ∩ (fun e => baseMap s b (Z e)) ⁻¹' U) ≤
        ENNReal.ofReal (D*s^3)*μ G*volume U := by
  intro U hU
  have hx := hdom (baseMap s b ⁻¹' U) ((measurable_baseMap s b) hU)
  rw [volume_preimage_baseMap hs] at hx
  rw [ENNReal.ofReal_mul hD]
  simpa only [Set.preimage_preimage,Function.comp_def,mul_assoc,mul_left_comm,mul_comm] using hx

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
