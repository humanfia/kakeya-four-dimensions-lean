/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/StripPredicates.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripGeometry
import Submission.Obl.k4_pair_bin_atlas_assembly.FormatOps
import Submission.Obl.k4_coarsened_outer_horizon_composition.FormatRule
import Submission.Lib.K4RepresentativeAssembly.FiniteFormat
import Submission.Lib.K4XInterface.Formats

/-!
The strip eligibility and midpoint-bin predicates use affine polynomials in
the original six trajectory coefficients. Arbitrary finite priority and code
tables use the same atoms, including the exact half-open floor boundaries.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open Set MvPolynomial
open Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

noncomputable section

def pulledRow (Q : Frame) (n : Plane) (j : Fin 2) : ℝ :=
  Q⁻¹ 0 j * n 0 + Q⁻¹ 1 j * n 1

theorem pulledRow_apply (Q : Frame) (n w : Plane) :
    inner ℝ (Matrix.toEuclideanLin Q⁻¹ w) n =
      pulledRow Q n 0 * w 0 + pulledRow Q n 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, Matrix.toLpLin_apply, pulledRow]
  ring

def stripVelocityPoly (q : ℝ) (Q : Frame) (u n : Plane) (β : ℝ) :
    MvPolynomial (Fin 6) ℝ :=
  C (q * pulledRow Q n 0) * (X 3 - C (u 0)) +
    C (q * pulledRow Q n 1) * (X 4 - C (u 1)) - C β

def stripPositionPoly (t : ℝ) (Q : Frame) (c u n : Plane) :
    MvPolynomial (Fin 6) ℝ :=
  C (pulledRow Q n 0) * (X 0 + C t * X 3 - C (c 0 + t * u 0)) +
    C (pulledRow Q n 1) * (X 1 + C t * X 4 - C (c 1 + t * u 1))

private theorem degree_linearTerm {d : ℕ} (a b t : ℝ) (i j : Fin d) :
    (C a * (X i + C t * X j - C b) : MvPolynomial (Fin d) ℝ).totalDegree ≤ 1 := by
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_sub_C_le _ _).trans
  apply (totalDegree_add _ _).trans
  apply max_le (by simp)
  exact (totalDegree_mul _ _).trans (by simp)

theorem stripVelocityPoly_degree (q : ℝ) (Q : Frame) (u n : Plane) (β : ℝ) :
    (stripVelocityPoly q Q u n β).totalDegree ≤ 1 := by
  unfold stripVelocityPoly
  apply (totalDegree_sub_C_le _ _).trans
  apply (totalDegree_add _ _).trans
  apply max_le <;> apply (totalDegree_mul _ _).trans <;>
    simp only [totalDegree_C, zero_add] <;>
    apply (totalDegree_sub_C_le _ _).trans <;> simp

theorem stripPositionPoly_degree (t : ℝ) (Q : Frame) (c u n : Plane) :
    (stripPositionPoly t Q c u n).totalDegree ≤ 1 := by
  exact (totalDegree_add _ _).trans (max_le
    (degree_linearTerm _ _ _ _ _) (degree_linearTerm _ _ _ _ _))

theorem eval_stripVelocityPoly (q : ℝ) (Q : Frame) (u n : Plane) (β : ℝ)
    (i : ℕ) (x : Fin 6 → ℝ) :
    eval x (stripVelocityPoly q Q u n β) =
      inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (gv (i, x) - u)) n - β := by
  rw [real_inner_smul_left, pulledRow_apply]
  simp only [stripVelocityPoly, map_sub, map_add, map_mul, eval_C, eval_X,
    PiLp.sub_apply, gv, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem eval_stripPositionPoly (t : ℝ) (Q : Frame) (c u n : Plane)
    (i : ℕ) (x : Fin 6 → ℝ) :
    eval x (stripPositionPoly t Q c u n) =
      inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy (i, x) t - c - t • u)) n := by
  rw [pulledRow_apply]
  simp [stripPositionPoly, map_add, map_sub, map_mul, eval_C, eval_X,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, gy, gx,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

def stripVelocityCut (q : ℝ) (Q : Frame) (u n : Plane) (β ε : ℝ) : Set Line :=
  {l | |inner ℝ (q • Matrix.toEuclideanLin Q⁻¹ (gv l - u)) n - β| ≤ ε}

def stripMidpointBin (t : ℝ) (Q : Frame) (c u n : Plane) (h : ℝ) (z : ℤ) : Set Line :=
  {l | ⌊inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n / h⌋ = z}

theorem stripVelocityCut_format (q : ℝ) (Q : Frame) (u n : Plane) (β ε : ℝ) (i : ℕ) :
    gfmt 6 2 1 {x | (i, x) ∈ stripVelocityCut q Q u n β ε} := by
  have hfmt : gfmt 6 2 1 {x | |eval x (stripVelocityPoly q Q u n β)| ≤ ε} :=
    k4_pair_bin_atlas_assembly.fmt_abs_le (stripVelocityPoly q Q u n β)
      (stripVelocityPoly_degree q Q u n β) ε
  simpa only [stripVelocityCut, mem_ofPred_eq, eval_stripVelocityPoly q Q u n β i] using hfmt

theorem stripMidpointBin_format (t : ℝ) (Q : Frame) (c u n : Plane) (h : ℝ) (z : ℤ) (i : ℕ) :
    gfmt 6 2 1 {x | (i, x) ∈ stripMidpointBin t Q c u n h z} := by
  have hdeg : (C h⁻¹ * stripPositionPoly t Q c u n).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simpa using stripPositionPoly_degree t Q c u n)
  have hfmt : gfmt 6 2 1 {x | ⌊eval x (C h⁻¹ * stripPositionPoly t Q c u n)⌋ = z} :=
    k4_coarsened_outer_horizon_composition.fmt_floor_eq
      (C h⁻¹ * stripPositionPoly t Q c u n) hdeg z
  simpa only [stripMidpointBin, mem_ofPred_eq, map_mul, eval_C, eval_stripPositionPoly t Q c u n i,
    div_eq_inv_mul] using hfmt

/-- A merged priority cell uses one copy of each original eligibility test.
The candidate identities enter only the finite constant decision table. -/
theorem strip_priority_code_format {m D : ℕ} {H : ℝ} {A : Set Line}
    (hA : ∀ i, gfmt 6 H D {x | (i, x) ∈ A})
    (q ε : ℝ) (Q : Frame) (u : Plane) (n : Fin m → Plane) (β : Fin m → ℝ)
    {Code : Type*} (code : Fin m → Code) (r : Code) (i : ℕ) :
    gfmt 6 (H + 2 * m) (max D 1)
      {x | (i, x) ∈ A ∧ ∃ a : Fin m,
        code a = r ∧ (i, x) ∈ stripVelocityCut q Q u (n a) (β a) ε ∧
          ∀ b : Fin m, b < a → (i, x) ∉ stripVelocityCut q Q u (n b) (β b) ε} := by
  let cuts : Fin m → Set (Fin 6 → ℝ) := fun a =>
    {x | (i, x) ∈ stripVelocityCut q Q u (n a) (β a) ε}
  have hfmt := k4_coarsened_outer_horizon_composition.fmt_rule_uniform cuts 2
    (fun a => stripVelocityCut_format q Q u (n a) (β a) ε i)
    (fun v => ∃ a : Fin m, code a = r ∧ v a ∧ ∀ b : Fin m, b < a → ¬v b)
  have hcount : (Fintype.card (Fin m) : ℝ) * 2 = 2 * m := by simp; ring
  rw [hcount] at hfmt
  exact gfmt_inter (hA i) hfmt

/-- Adding the chosen representative's midpoint bin costs two more affine
tests and does not charge the candidate count to geometric slack. -/
theorem strip_priority_midpoint_format {m D : ℕ} {H : ℝ} {A : Set Line}
    (hA : ∀ i, gfmt 6 H D {x | (i, x) ∈ A})
    (q ε t h : ℝ) (Q : Frame) (c u repr : Plane)
    (n : Fin m → Plane) (β : Fin m → ℝ)
    {Code : Type*} (code : Fin m → Code) (r : Code) (z : ℤ) (i : ℕ) :
    gfmt 6 (H + 2 * m + 2) (max D 1)
      {x | ((i, x) ∈ A ∧ ∃ a : Fin m,
        code a = r ∧ (i, x) ∈ stripVelocityCut q Q u (n a) (β a) ε ∧
          ∀ b : Fin m, b < a → (i, x) ∉ stripVelocityCut q Q u (n b) (β b) ε) ∧
        (i, x) ∈ stripMidpointBin t Q c u repr h z} := by
  simpa only [max_assoc, max_self, Set.ofPred_and] using
    gfmt_inter (strip_priority_code_format hA q ε Q u n β code r i)
      (stripMidpointBin_format t Q c u repr h z i)

/-- The left endpoint of the recorded floor bin is an admissible center for
the full-block strip constructor. -/
theorem stripMidpointBin_error {t h : ℝ} {Q : Frame} {c u n : Plane} {z : ℤ} {l : Line}
    (hh : 0 < h) (hl : l ∈ stripMidpointBin t Q c u n h z) :
    |inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n - (z : ℝ) * h| ≤ h := by
  have hfloor := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hh
    (inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n)
  change ⌊inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n / h⌋ = z at hl
  rwa [hl] at hfloor

theorem stripMidpointBin_center_le {t h κ : ℝ} {Q : Frame} {c u n : Plane} {z : ℤ} {l : Line}
    (hh : 0 < h) (hn : ‖n‖ = 1)
    (hpos : ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)‖ ≤ κ)
    (hl : l ∈ stripMidpointBin t Q c u n h z) : |(z : ℝ) * h| ≤ κ + h := by
  have hinner : |inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n| ≤ κ :=
    (abs_real_inner_le_norm _ n).trans (by simpa only [hn, mul_one] using hpos)
  have herr := stripMidpointBin_error hh hl
  calc
    _ ≤ |inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n| +
        |inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n - (z : ℝ) * h| := by
      convert abs_sub (inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n)
        (inner ℝ (Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)) n - (z : ℝ) * h) using 1
      congr 1
      ring
    _ ≤ κ + h := add_le_add hinner herr

/-- A full assignment predicate can be retained in the seven incidence
coordinates with exactly the same sign atoms. -/
theorem strip_assignment_incidence_format {H : ℝ} {D : ℕ} {A : Set Line}
    (hA : ∀ i, gfmt 6 H D {x | (i, x) ∈ A}) (i : ℕ) :
    gfmt 7 H D {x : Fin 7 → ℝ | (i, fun j : Fin 6 => x j.castSucc) ∈ A} := by
  have hpre : gfmt 7 H D
      ((fun (x : Fin 7 → ℝ) (j : Fin 6) => eval x (X j.castSucc)) ⁻¹' {x | (i, x) ∈ A}) :=
    Submission.Lib.K4RepresentativeAssembly.fmt_affine_preimage (hA i)
      (fun j => X (j.castSucc : Fin 7)) (fun _ => by simp)
  convert hpre using 1
  ext x
  simp

/-- The final counted set retains original parent/deep predicates. Alignment
enters as a finite table, so the arbitrary analytical coverage witnesses need
no sign-format hypothesis. -/
theorem strip_aligned_incidence_format {d D₀ DA Dd : ℕ} {H₀ HA Hd : ℝ}
    {F₀ : Set (Line × ℝ)} {A : Set Line} (Fd : Fin d → Set (Line × ℝ))
    (hF₀ : ∀ i, gfmt 7 H₀ D₀
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F₀})
    (hA : ∀ i, gfmt 6 HA DA {x | (i, x) ∈ A})
    (hFd : ∀ b i, gfmt 7 Hd Dd
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ Fd b})
    (aligned : Fin d → Prop) (i : ℕ) :
    gfmt 7 (H₀ + HA + d * Hd) (max (max D₀ DA) Dd)
      {x : Fin 7 → ℝ |
        (((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F₀ ∧
          (i, fun j : Fin 6 => x j.castSucc) ∈ A) ∧
          ∃ b, aligned b ∧ ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ Fd b} := by
  have hdeep : gfmt 7 (d * Hd) Dd
      {x : Fin 7 → ℝ | ∃ b, aligned b ∧
        ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ Fd b} := by
    have hpre : gfmt 7 ((Fintype.card (Fin d) : ℝ) * Hd) Dd
        {x : Fin 7 → ℝ | ∃ b, aligned b ∧
          ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ Fd b} :=
      k4_coarsened_outer_horizon_composition.fmt_rule_uniform
        (fun b => {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ Fd b})
        Hd (fun b => hFd b i) (fun v => ∃ b, aligned b ∧ v b)
    simpa only [Fintype.card_fin] using hpre
  simpa only [Set.ofPred_and] using
    gfmt_inter (gfmt_inter (hF₀ i) (strip_assignment_incidence_format hA i)) hdeep

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
