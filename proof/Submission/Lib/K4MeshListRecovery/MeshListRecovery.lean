import Submission.Lib.K4MeshListRecovery.SparseTableRecovery
import Submission.Lib.K4MeshListRecovery.JointMeshAveraging
import Submission.Lib.K4ModelReduction.FiniteTable

/-!
Adapted from: here:o064

Combine the two accepted libraries: coordinate averaging and finite mesh
representations from K4ModelReduction, and original-law list maximization from
K4OriginalLists.  The analytical mask and fine posterior rule stay out of the
finite observable code.
-/

namespace Submission.Lib.K4MeshListRecovery

open Finset MeasureTheory Set
open Submission.Lib.K4OriginalLists Submission.Lib.K4ModelReduction

theorem cube_support_zero {ι : Type*} (f : (ι → ℝ) → ℝ) (R : ℝ)
    (hf : supportedInCube f R) (x : ι → ℝ)
    (hx : x ∉ Icc (fun _ => -R) (fun _ => R)) : f x = 0 := by
  by_contra hne
  have hbound : ∀ i, |x i| ≤ R := by
    intro i
    by_contra hi
    exact hne (hf x i (lt_of_not_ge hi))
  exact hx ⟨fun i => (abs_le.mp (hbound i)).1, fun i => (abs_le.mp (hbound i)).2⟩

theorem integrable_cube_density {n : ℕ} (M R : ℝ)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : supportedInCube f.val R) : Integrable f.val volume := by
  let S : Set (Fin (n + 1) → ℝ) := Icc (fun _ => -R) (fun _ => R)
  have hS : MeasurableSet S := measurableSet_Icc
  have hfinite : volume S < ⊤ := isCompact_Icc.measure_lt_top
  have hdom : Integrable (S.indicator (fun _ => M)) volume :=
    (integrable_indicator_iff hS).mpr (integrableOn_const hfinite.ne)
  apply hdom.mono' f.property.1.aestronglyMeasurable
  filter_upwards with x
  by_cases hx : x ∈ S
  · simpa only [indicator_of_mem hx, Real.norm_eq_abs] using f.property.2 x
  · simp only [indicator_of_notMem hx, cube_support_zero f.val R hf x hx, norm_zero, le_refl]

/-- A joint bound for each original coordinate-averaging error gives an actual finite
mesh list table in any base dimension, with original unnormalized success. -/
theorem recover_mesh_original_lists_joint
    {n : ℕ} {o β : Type*} [Fintype o] [Fintype β]
    (M R ρ θ : ℝ) (hρ : 0 < ρ) (hθ : 0 ≤ θ)
    (f : o → β → boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hsupport : ∀ b a, supportedInCube (f b a).val R)
    (hcoordinate : ∀ i : Fin (n + 1),
      (∑ b, ∑ a, densityL1Distance volume
        (coordinateAverage i M hρ (f b a)).val (f b a).val) ≤ ENNReal.ofReal θ)
    (mask : o → (Fin (n + 1) → ℝ) → β → ℝ)
    (hmaskint : ∀ b a, Integrable (fun x => mask b x a) volume)
    (hmask : ∀ b x a, mask b x a ≤ (f b a).val x)
    (allowed : Finset β) (D : ℕ) (L : o → (Fin (n + 1) → ℝ) → Finset β)
    (hLmeas : ∀ b, MeasurableLists (L b))
    (hL : ∀ b x, L b x ⊆ allowed ∧ (L b x).card ≤ D)
    (mass : ℝ) (hsuccess : mass ≤ ∑ b, ∫ x, ∑ a ∈ L b x, mask b x a) :
    let F := meshCodes (Fin (n + 1)) ρ (R + ((n + 1 : ℕ) : ℝ) * ρ)
    ∃ table : (Option F × o) → Finset β,
      (∀ c, table c ⊆ allowed ∧ (table c).card ≤ D) ∧
      mass - 2 * (((n + 1 : ℕ) : ℝ) * θ) ≤
        ∑ b, ∫ x, ∑ a ∈ table (finiteObservedCode F (meshTag ρ) x, b), (f b a).val x := by
  classical
  let coords := List.finRange (n + 1)
  let G : o → β → boundedMeasurableFunctions (Fin (n + 1) → ℝ) M :=
    fun b a => coords.foldr (fun i g => coordinateAverage i M hρ g) (f b a)
  let R' := R + ((n + 1 : ℕ) : ℝ) * ρ
  let F := meshCodes (Fin (n + 1)) ρ R'
  let S : Set (Fin (n + 1) → ℝ) := Icc (fun _ => -R') (fun _ => R')
  let e := ((n + 1 : ℕ) : ℝ) * θ
  have hGsupport (b : o) (a : β) : supportedInCube (G b a).val R' := by
    simpa only [coords, List.length_finRange] using
      coordinate_averaging_support M R hρ coords (f b a) (hsupport b a)
  have hfint (b : o) (a : β) : Integrable (f b a).val volume :=
    integrable_cube_density M R _ (hsupport b a)
  have hGint (b : o) (a : β) : Integrable (G b a).val volume :=
    integrable_cube_density M R' _ (hGsupport b a)
  have herrint (b : o) (a : β) :
      Integrable (fun x => |(f b a).val x - (G b a).val x|) volume :=
    ((hfint b a).sub (hGint b a)).abs
  have hjoint : (∑ b, ∑ a, densityL1Distance volume (G b a).val (f b a).val) ≤
      ENNReal.ofReal e := by
    calc
      _ = ∑ c : o × β, densityL1Distance volume (G c.1 c.2).val (f c.1 c.2).val :=
        (Fintype.sum_prod_type _).symm
      _ ≤ ∑ i : Fin (n + 1), ∑ c : o × β, densityL1Distance volume
          (coordinateAverage i M hρ (f c.1 c.2)).val (f c.1 c.2).val :=
        coordinate_averaging_joint_error M hρ (fun c : o × β => f c.1 c.2)
      _ = ∑ i : Fin (n + 1), ∑ b, ∑ a, densityL1Distance volume
          (coordinateAverage i M hρ (f b a)).val (f b a).val := by
        simp only [Fintype.sum_prod_type]
      _ ≤ ∑ _i : Fin (n + 1), ENNReal.ofReal θ := sum_le_sum (fun i _ => hcoordinate i)
      _ = ENNReal.ofReal e := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, e,
          ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)), ENNReal.ofReal_natCast]
  have herror : (∑ b, ∫ x, ∑ a, |(f b a).val x - (G b a).val x|) ≤ e := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ e)).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ =>
      integral_nonneg (fun x => sum_nonneg (fun a _ => abs_nonneg _)))]
    simp_rw [ofReal_integral_joint_error volume (fun a => (f _ a).val)
      (fun a => (G _ a).val) (fun a => hfint _ a) (fun a => hGint _ a)]
    simpa only [densityL1Distance, abs_sub_comm] using hjoint
  have htable := recover_original_sparse_table volume F (meshTag ρ)
    (fun c => measurableSet_meshTag ρ c) S measurableSet_Icc isCompact_Icc.measure_lt_top
    (fun b x a => (f b a).val x) mask (fun b x a => (G b a).val x)
    (fun c b a => (G b a).val (meshRepresentative ρ c)) hfint hmaskint hmask
    (fun b x a => by
      simpa only [coords, List.length_finRange] using
        coordinate_averaging_finite_table M R hρ coords (fun i => List.mem_finRange i)
          (f b a) (hsupport b a) x)
    (fun b x a hx => cube_support_zero (G b a).val R' (hGsupport b a) x hx)
    e mass herror allowed D L hLmeas hL hsuccess
  exact htable

/-- A fixed bound for each original coordinate-averaging error gives an actual finite
mesh list table in any base dimension, with original unnormalized success. -/
theorem recover_mesh_original_lists
    {n : ℕ} {o β : Type*} [Fintype o] [Fintype β]
    (M R ρ θ : ℝ) (hρ : 0 < ρ) (hθ : 0 ≤ θ)
    (f : o → β → boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hsupport : ∀ b a, supportedInCube (f b a).val R)
    (hcoordinate : ∀ b a (i : Fin (n + 1)),
      densityL1Distance volume (coordinateAverage i M hρ (f b a)).val (f b a).val ≤ ENNReal.ofReal θ)
    (mask : o → (Fin (n + 1) → ℝ) → β → ℝ)
    (hmaskint : ∀ b a, Integrable (fun x => mask b x a) volume)
    (hmask : ∀ b x a, mask b x a ≤ (f b a).val x)
    (allowed : Finset β) (D : ℕ) (L : o → (Fin (n + 1) → ℝ) → Finset β)
    (hLmeas : ∀ b, MeasurableLists (L b))
    (hL : ∀ b x, L b x ⊆ allowed ∧ (L b x).card ≤ D)
    (mass : ℝ) (hsuccess : mass ≤ ∑ b, ∫ x, ∑ a ∈ L b x, mask b x a) :
    let F := meshCodes (Fin (n + 1)) ρ (R + ((n + 1 : ℕ) : ℝ) * ρ)
    ∃ table : (Option F × o) → Finset β,
      (∀ c, table c ⊆ allowed ∧ (table c).card ≤ D) ∧
      mass - 2 * ((Fintype.card o : ℝ) * (Fintype.card β : ℝ) * ((n + 1 : ℕ) : ℝ) * θ) ≤
        ∑ b, ∫ x, ∑ a ∈ table (finiteObservedCode F (meshTag ρ) x, b), (f b a).val x := by
  have hjoint (i : Fin (n + 1)) :
      (∑ b, ∑ a, densityL1Distance volume
        (coordinateAverage i M hρ (f b a)).val (f b a).val) ≤
      ENNReal.ofReal ((Fintype.card o : ℝ) * (Fintype.card β : ℝ) * θ) := by
    calc
      _ ≤ ∑ _b : o, ∑ _a : β, ENNReal.ofReal θ :=
        sum_le_sum (fun b _ => sum_le_sum (fun a _ => hcoordinate b a i))
      _ = _ := by simp [ENNReal.ofReal_mul, nsmul_eq_mul, mul_assoc]
  have h := recover_mesh_original_lists_joint M R ρ
    ((Fintype.card o : ℝ) * (Fintype.card β : ℝ) * θ) hρ (by positivity)
    f hsupport hjoint mask hmaskint hmask allowed D L hLmeas hL mass hsuccess
  simpa only [mul_assoc, mul_left_comm ((n + 1 : ℕ) : ℝ)] using h

/-- The table's total number of label entries has an explicit polynomial grid bound. -/
theorem mesh_list_table_entries_le
    {n : ℕ} {o β : Type*} [Fintype o] [Fintype β]
    (R ρ : ℝ) (hR : 0 ≤ R) (hρ : 0 < ρ) (D : ℕ)
    (table : (Option (meshCodes (Fin (n + 1)) ρ (R + ((n + 1 : ℕ) : ℝ) * ρ)) × o) → Finset β)
    (htable : ∀ c, (table c).card ≤ D) :
    (∑ c, ((table c).card : ℝ)) ≤
      ((2 * R / ρ + 2 * ((n + 1 : ℕ) : ℝ) + 2) ^ (n + 1) + 1) *
        (Fintype.card o : ℝ) * (D : ℝ) := by
  classical
  let F := meshCodes (Fin (n + 1)) ρ (R + ((n + 1 : ℕ) : ℝ) * ρ)
  have hcount : (∑ c, ((table c).card : ℝ)) ≤
      (Fintype.card (Option F × o) : ℝ) * D := by
    calc
      _ ≤ ∑ _c : Option F × o, (D : ℝ) := sum_le_sum fun c _ => by exact_mod_cast htable c
      _ = _ := by simp
  have hcard : (Fintype.card (Option F × o) : ℝ) = ((F.card : ℝ) + 1) * Fintype.card o := by
    simp [Fintype.card_coe]
  rw [hcard] at hcount
  apply hcount.trans
  gcongr
  simpa only [F, Fintype.card_fin] using
    averaging_meshCodes_card_le (ι := Fin (n + 1)) hρ hR (n + 1)

end Submission.Lib.K4MeshListRecovery
