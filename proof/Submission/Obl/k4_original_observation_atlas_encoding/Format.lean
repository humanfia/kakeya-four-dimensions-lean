import Submission.Lib.K4MeshListRecovery.MeshFormat
import Submission.Obl.k4_horizon_light_cell_mass.Mesh
import Submission.Lib.K4XInterface.Formats
import Submission.Lib.K4XInterface.Charts

namespace Submission.Obl.k4_original_observation_atlas_encoding

open MeasureTheory Set Finset MvPolynomial
open scoped ENNReal
open Submission.Lib.K4XInterface
open Submission.Lib.K4ModelReduction
open Submission.Lib.K4MeshListRecovery
open Submission.Obl.k4_horizon_light_cell_mass

theorem bounded_lookup_format {n k D d : ℕ} {A : Set (Fin n → ℝ)} {H R : ℝ}
    (hA : gfmt n H D A) (p : Fin k → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ d) (T : Set (Fin k → ℤ))
    (hbound : ∀ x ∈ A, ∀ i, |eval x (p i)| ≤ R) :
    gfmt n (H + (2 * k * (meshCodes (Fin k) 1 R).card : ℕ)) (max D d)
      {x | x ∈ A ∧ (fun i => ⌊eval x (p i)⌋) ∈ T} := by
  classical
  let F := meshCodes (Fin k) 1 R
  let tag : (Fin n → ℝ) → (Fin k → ℤ) := fun x i => ⌊eval x (p i) / 1⌋
  let S : Set (Option F) := {o | o.elim False (fun c => c.val ∈ T)}
  have hfmt : gfmt n (2 * k * F.card : ℕ) d
      {x | finiteObservedCode F tag x ∈ S} :=
    polynomial_mesh_lookup_format p hp 1 F S
  have heq : {x | x ∈ A ∧ (fun i => ⌊eval x (p i)⌋) ∈ T} =
      A ∩ {x | finiteObservedCode F tag x ∈ S} := by
    ext x
    by_cases hx : x ∈ A
    · have hmem : tag x ∈ F := meshTag_mem_codes (by norm_num) _ (hbound x hx)
      have hmem' : (fun i => ⌊eval x (p i)⌋) ∈ F := by simpa only [tag, div_one] using hmem
      simp [hx, finiteObservedCode, S, hmem', tag]
    · simp [hx]
  rw [heq]
  exact gfmt_inter hA hfmt

noncomputable def scaledObservationPoly (N : ℝ) (H : ℕ) (B a : ℝ) :
    Fin 4 → MvPolynomial (Fin 7) ℝ :=
  ![C (N ^ H) * X 6,
    C (N ^ H) * (X 0 + X 6 * X 3),
    C (N ^ H) * (X 1 + X 6 * X 4),
    C (B / a) * (X 2 + X 6 * X 5)]

theorem scaledObservationPoly_degree (N : ℝ) (H : ℕ) (B a : ℝ) (i : Fin 4) :
    (scaledObservationPoly N H B a i).totalDegree ≤ 2 := by
  have hX (i : Fin 7) : (X i : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by simp
  have hquad (c : ℝ) (i j k : Fin 7) :
      (C c * (X i + X j * X k) : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_add _ _).trans
    exact max_le (hX _) ((totalDegree_mul _ _).trans (by simp))
  fin_cases i
  · change (C (N ^ H) * X (6 : Fin 7)).totalDegree ≤ 2
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, totalDegree_X]
    norm_num
  · exact hquad _ _ _ _
  · exact hquad _ _ _ _
  · exact hquad _ _ _ _

def codeOfFour (c : Fin 4 → ℤ) : CellCode := (fun i => c i.castSucc, c 3)

theorem scaledObservationPoly_code (N : ℝ) (H : ℕ) (B a : ℝ) (i : ℕ) (x : Fin 7 → ℝ) :
    codeOfFour (fun j => ⌊eval x (scaledObservationPoly N H B a j)⌋) =
      meshCode ![(N ^ H)⁻¹, (N ^ H)⁻¹, (N ^ H)⁻¹]
        (pureMap B a ((i, fun j : Fin 6 => x j.castSucc), x 6)) := by
  apply Prod.ext
  · funext j
    fin_cases j <;> simp [codeOfFour, scaledObservationPoly, meshCode, pureMap,
      div_inv_eq_mul, mul_comm]
  · simp [codeOfFour, scaledObservationPoly, meshCode, pureMap, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]

theorem scaledObservationPoly_bound {N B a : ℝ} (hN : 2 ≤ N) (M Mν H J : ℕ)
    (hB0 : 0 ≤ B) (hB : B ≤ N ^ Mν) (ha : 0 < a) (hai : a⁻¹ ≤ N ^ J)
    (x : Fin 7 → ℝ) (ht : x 6 ∈ Icc (0 : ℝ) 1)
    (hx : ∀ j : Fin 6, |x j.castSucc| ≤ N ^ M) (i : Fin 4) :
    |eval x (scaledObservationPoly N H B a i)| ≤ N ^ (H + Mν + M + J + 2) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have ht' : |x 6| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hpos (i j : Fin 6) : |x i.castSucc + x 6 * x j.castSucc| ≤ 2 * N ^ M := by
    calc
      _ ≤ |x i.castSucc| + |x 6| * |x j.castSucc| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ N ^ M + 1 * N ^ M := by gcongr; exact hx i; exact hx j
      _ = _ := by ring
  have hbase : N ^ H * (2 * N ^ M) ≤ N ^ (H + Mν + M + J + 2) := by
    calc
      _ = 2 * N ^ (H + M) := by rw [pow_add]; ring
      _ ≤ N ^ (H + M + 1) :=
        Submission.Obl.k4_real_conic_restoration.absorb_constant hN (by norm_num)
      _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
  have hhidden : (B * a⁻¹) * (2 * N ^ M) ≤ N ^ (H + Mν + M + J + 2) := by
    calc
      _ ≤ (N ^ Mν * N ^ J) * (2 * N ^ M) := by gcongr
      _ = 2 * N ^ (Mν + J + M) := by simp only [pow_add]; ring
      _ ≤ N ^ (Mν + J + M + 1) :=
        Submission.Obl.k4_real_conic_restoration.absorb_constant hN (by norm_num)
      _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
  fin_cases i <;> simp only [scaledObservationPoly, Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val,
    eval_mul, eval_C, eval_X, eval_add, abs_mul]
  · rw [abs_of_nonneg (pow_nonneg hN0.le _)]
    exact (mul_le_mul_of_nonneg_left (ht'.trans (by
      have := one_le_pow₀ hN1 (n := M); linarith)) (by positivity)).trans hbase
  · rw [abs_of_nonneg (pow_nonneg hN0.le _)]
    exact (mul_le_mul_of_nonneg_left (hpos 0 3) (by positivity)).trans hbase
  · rw [abs_of_nonneg (pow_nonneg hN0.le _)]
    exact (mul_le_mul_of_nonneg_left (hpos 1 4) (by positivity)).trans hbase
  · rw [abs_of_nonneg (div_nonneg hB0 ha.le), div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (hpos 2 5) (by positivity)).trans hhidden

theorem lookup_count_bound {N : ℝ} (hN : 2 ≤ N) (M J : ℕ) :
    N ^ M + (8 * (meshCodes (Fin 4) 1 (N ^ J)).card : ℕ) ≤ N ^ (M + 4 * J + 20) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hJ : 1 ≤ N ^ J := one_le_pow₀ hN1
  have hM : 1 ≤ N ^ M := one_le_pow₀ hN1
  have hcard : ((meshCodes (Fin 4) 1 (N ^ J)).card : ℝ) ≤ 256 * N ^ (4 * J) := by
    calc
      _ ≤ (2 * N ^ J / 1 + 2) ^ 4 := by
        simpa using (meshCodes_card_le (ι := Fin 4) (by norm_num : (0 : ℝ) < 1)
          (by positivity : 0 ≤ N ^ J))
      _ ≤ (4 * N ^ J) ^ 4 := by gcongr <;> linarith
      _ = _ := by rw [show 4 * J = J * 4 by omega, pow_mul, mul_pow]; norm_num
  have hm : N ^ M ≤ N ^ (M + 4 * J) := pow_le_pow_right₀ hN1 (by omega)
  have hj : N ^ (4 * J) ≤ N ^ (M + 4 * J) := pow_le_pow_right₀ hN1 (by omega)
  calc
    _ ≤ 2049 * N ^ (M + 4 * J) := by push_cast; nlinarith
    _ ≤ _ := Submission.Obl.k4_real_conic_restoration.absorb_constant hN (by norm_num)

theorem inv_delta_le {N : ℝ} (hN : 2 ≤ N) (L : ℝ) :
    (gδ N L)⁻¹ ≤ N ^ ⌈|L|⌉₊ := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL : L ≤ (⌈|L|⌉₊ : ℝ) := (le_abs_self L).trans (Nat.le_ceil _)
  have hmin : (N ^ ⌈|L|⌉₊)⁻¹ ≤ gδ N L := by
    calc
      _ = N ^ (-(⌈|L|⌉₊ : ℝ)) := by rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
      _ ≤ N ^ (-L) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ _ := (Submission.Obl.k4_profile_density_bounds.width_bounds hN0 L).1
  have hh := (inv_le_inv₀ (gδ_pos N L) (by positivity : 0 < (N ^ ⌈|L|⌉₊)⁻¹)).2 hmin
  simpa only [inv_inv] using hh

theorem selected_fiber_format {N B a : ℝ} (hN : 2 ≤ N) (M Mν H J D : ℕ)
    (hB0 : 0 ≤ B) (hB : B ≤ N ^ Mν) (ha : 0 < a) (hai : a⁻¹ ≤ N ^ J)
    {F : Set State} (i : ℕ)
    (hF : gfmt 7 (N ^ M) D
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F})
    (ht : ∀ p ∈ F, p.2 ∈ Icc (0 : ℝ) 1)
    (hbd : ∀ p ∈ F, ∀ j, |p.1.2 j| ≤ N ^ M)
    {β : Type*} (table : CellCode → Finset β) (b : β) :
    gfmt 7 (N ^ (M + 4 * (H + Mν + M + J + 2) + 20)) (max D 2)
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F ∧
        b ∈ table (meshCode ![(N ^ H)⁻¹, (N ^ H)⁻¹, (N ^ H)⁻¹]
          (pureMap B a ((i, fun j : Fin 6 => x j.castSucc), x 6)))} := by
  let Z := H + Mν + M + J + 2
  have hbound : ∀ x : Fin 7 → ℝ,
      ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F →
      ∀ j, |eval x (scaledObservationPoly N H B a j)| ≤ N ^ Z := by
    intro x hx j
    exact scaledObservationPoly_bound hN M Mν H J hB0 hB ha hai x
      (ht _ hx) (hbd _ hx) j
  have hh := bounded_lookup_format hF (scaledObservationPoly N H B a)
    (scaledObservationPoly_degree N H B a) {c | b ∈ table (codeOfFour c)} hbound
  have heq : {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F ∧
      b ∈ table (meshCode ![(N ^ H)⁻¹, (N ^ H)⁻¹, (N ^ H)⁻¹]
        (pureMap B a ((i, fun j : Fin 6 => x j.castSucc), x 6)))} =
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F ∧
        (fun j => ⌊eval x (scaledObservationPoly N H B a j)⌋) ∈
          {c | b ∈ table (codeOfFour c)}} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [scaledObservationPoly_code N H B a i x]
  rw [heq]
  exact gfmt_mono (by simpa only [Fintype.card_fin] using lookup_count_bound hN M Z) le_rfl hh

end Submission.Obl.k4_original_observation_atlas_encoding
