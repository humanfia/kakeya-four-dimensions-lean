-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativeCoreEntries, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativeCoreEntries.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativeCoreEntries.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCoreEntries.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCoreEntries.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.OriginalNativeBranches
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeBranchSigns
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.EntryCompletion
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCoreCoordinates

/-! # Heavy original core/sign entries with one coherent branch per label -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric MvPolynomial
open Analytic k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

def nativeCoreSign (b : Bool) : ℝ := if b then -1 else 1

/-- Original raw entries, their retained heavy parts, and fixed branches
indexed by an actual center code and one of the two root signs. -/
def NativeCoreEntryFamily {Ω : Type*} [MeasurableSpace Ω]
    (e R : ℕ) (K : ℝ) (P : Poly) (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin 4)) (G : Set Ω) (θ : ENNReal) : Prop :=
  ∃ codes : Finset (Fin 3 → ℤ), ∃ center : (Fin 3 → ℤ) → Base,
  ∃ F : (↥codes × Bool) → EuclideanSpace ℂ (Fin 3) → ℂ,
  ∃ f : (↥codes × Bool) → Base → ℝ,
  ∃ U V : (↥codes × Bool) → Set Ω,
    (codes.card : ℝ) ≤ K ^ (3 * R + 18) ∧
    (∀ c ∈ codes, (fun j => center c j) ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
      ((K ^ e)⁻¹) ^ 2 ≤ eval (fun j => center c j) (baseDiscriminant P) ∧
      ∀ j, ⌊center c j / ((K ^ R)⁻¹ / 12)⌋ = c j) ∧
    (∀ i, MeasurableSet (U i) ∧ MeasurableSet (V i)) ∧
    Pairwise (fun i j => Disjoint (V i) (V j)) ∧
    (∀ i, V i ⊆ U i ∧ U i ⊆ G) ∧
    (∀ i, (U i).Nonempty → LocalNativeBranchData 5186 P (fun j => center i.1.1 j)
      (K ^ R)⁻¹ (nativeCoreSign i.2) (F i) (f i)) ∧
    (∀ i p, p ∈ U i →
      ‖(K ^ R) • (nativeBase (X p) - center i.1.1)‖ ≤ 1 / 4 ∧
      0 < value (pderiv 3 P) (rootLift P (X p)) * nativeCoreSign i.2 ∧
      rootLift P (X p) 3 = f i ((K ^ R) • (nativeBase (X p) - center i.1.1))) ∧
    (∀ i, (V i).Nonempty → θ ≤ μ (U i)) ∧
    μ (⋃ i, V i)ᶜ ≤ ENNReal.ofReal (2 * K ^ (3 * R + 18)) * θ

/-- A coded branch cover and the ORIGINAL source tests produce actual
measurable core/sign entries and one fixed branch on every nonempty entry.
Heavy-entry pruning retains EARLIER original floors. Its measure is the
given unnormalized law (or its FULL-prior scalar multiple), without a
selected-entry probability denominator. -/
theorem heavy_original_native_core_entries
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EuclideanSpace ℝ (Fin 4)) (hX : Measurable X)
    (G : Set Ω) (hG : MeasurableSet G) (hsupp : ∀ᵐ p ∂μ, p ∈ G)
    (P : Poly) (hP : P.totalDegree ≤ 2)
    {e R : ℕ} {K a : ℝ} (hK : 2 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hcurv : |curvature P 3| ≤ (K ^ 5 * a)⁻¹)
    (hsource : ∀ p ∈ G, |value P (X p)| ≤ K * a ∧ K⁻¹ ≤ |value (pderiv 3 P) (X p)|)
    (hcover : NativeQuarterBranchCover e R K P μ (fun p j => X p j.castSucc))
    (θ : ENNReal) :
      NativeCoreEntryFamily e R K P μ X G θ := by
  classical
  obtain ⟨codes, center, hcard, hcenters, hcovered⟩ := hcover
  let I := ↥codes × Bool
  let z : I → Ω → Base := fun i p => (K ^ R) • (nativeBase (X p) - center i.1.1)
  let valid : I → Prop := fun i => curvature P 3 = 0 →
    0 < eval (fun j => center i.1.1 j) (restrictBase (pderiv 3 P)) * nativeCoreSign i.2
  have hσne (i : I) : nativeCoreSign i.2 ≠ 0 := by cases i.2 <;> norm_num [nativeCoreSign]
  have hchoose (i : I) : ∃ F f,
      valid i → LocalNativeBranchData 5186 P (fun j => center i.1.1 j)
        (K ^ R)⁻¹ (nativeCoreSign i.2) F f := by
    by_cases hi : valid i
    · obtain ⟨F, f, hdata⟩ := (hcenters i.1.1 i.1.2).2.2.2 (nativeCoreSign i.2) (hσne i) hi
      exact ⟨F, f, fun _ => hdata⟩
    · exact ⟨0, 0, fun hi' => False.elim (hi hi')⟩
  choose F f hdata using hchoose
  let φ : Ω → ℝ := fun p => value (pderiv 3 P) (rootLift P (X p))
  have hφ : Measurable φ := (continuous_value _).measurable.comp ((measurable_rootLift P).comp hX)
  have hz (i : I) : Measurable (z i) :=
    (((measurable_nativeBase.comp hX).sub_const (center i.1.1)).const_smul (K ^ R))
  let U : I → Set Ω := fun i => if valid i then
    G ∩ {p | ‖z i p‖ ≤ 1 / 4 ∧ 0 < φ p * nativeCoreSign i.2} else ∅
  have hUm (i : I) : MeasurableSet (U i) := by
    by_cases hi : valid i
    · simpa only [U, ite_eq_left hi, Set.setOf_and] using hG.inter
        ((measurableSet_le (hz i).norm measurable_const).inter
          (measurableSet_lt measurable_const (hφ.mul_const _)))
    · simp only [U, ite_eq_right hi, MeasurableSet.empty]
  have hmem (i : I) (p : Ω) (hp : p ∈ U i) :
      valid i ∧ p ∈ G ∧ ‖z i p‖ ≤ 1 / 4 ∧ 0 < φ p * nativeCoreSign i.2 := by
    by_cases hi : valid i
    · exact ⟨hi, by simpa only [U, ite_eq_left hi, Set.mem_inter_iff, Set.mem_setOf_eq] using hp⟩
    · simp only [U, ite_eq_right hi, mem_empty_iff_false] at hp
  have hKp : 0 < K := by linarith
  have hroot (p : Ω) (hp : p ∈ G) :
      value P (rootLift P (X p)) = 0 ∧ φ p ≠ 0 := by
    obtain ⟨hr, hd⟩ := hsource p hp
    have hh := rootLift_spec P 0 hP (by simp) hK ha ha1 hcurv (X p) hr hd
      (by simpa [value] using hKp.le) (by simpa [curvature] using hKp.le)
    exact ⟨hh.1, hh.2.1⟩
  have hcoords (i : I) (p : Ω) :
      Fin.snoc (fun j => center i.1.1 j + (K ^ R)⁻¹ * z i p j) (rootLift P (X p) 3) =
        fun j => rootLift P (X p) j :=
    power_core_rootLift_coordinates P hKp R (center i.1.1) (X p)
  have hpoint (i : I) (p : Ω) (hp : p ∈ U i) :
      ‖z i p‖ ≤ 1 / 4 ∧ 0 < φ p * nativeCoreSign i.2 ∧ rootLift P (X p) 3 = f i (z i p) := by
    obtain ⟨hi, hpG, hzsmall, hs⟩ := hmem i p hp
    refine ⟨hzsmall, hs, ?_⟩
    apply (hdata i hi).exact_signed_root hP (z i p)
      (by rw [mem_ball, dist_zero_right]; linarith) (rootLift P (X p) 3)
    · rw [hcoords]
      exact (hroot p hpG).1
    · rw [hcoords]
      exact hs
  have hcov : ∀ᵐ p ∂μ, p ∈ ⋃ i : I, U i := by
    filter_upwards [hsupp, hcovered] with p hpG hpcover
    obtain ⟨c, hc, hnear⟩ := hpcover
    have hbase : WithLp.toLp 2 (fun j : Fin 3 => X p j.castSucc) = nativeBase (X p) := by
      ext j
      fin_cases j <;> rfl
    rw [hbase] at hnear
    have hdisc : 0 < eval (fun j => center c j) (baseDiscriminant P) :=
      (show 0 < ((K ^ e)⁻¹) ^ 2 by positivity).trans_le (hcenters c hc).2.1
    have hv (b : Bool) (hs : 0 < φ p * nativeCoreSign b) : valid (⟨c, hc⟩, b) := by
      apply native_core_sign_admissible P hP (fun j => center c j) (K ^ R)⁻¹ hdisc
        (hcenters c hc).2.2.2 (z (⟨c, hc⟩, b) p)
        (by rw [mem_ball, dist_zero_right]; exact lt_of_le_of_lt hnear (by norm_num))
        (rootLift P (X p) 3) (nativeCoreSign b)
      rw [hcoords (⟨c, hc⟩, b) p]
      exact hs
    rcases lt_or_gt_of_ne (hroot p hpG).2 with hn | hp
    · have hs : 0 < φ p * nativeCoreSign true := by simp only [nativeCoreSign, ite_true]; linarith
      refine mem_iUnion.mpr ⟨(⟨c, hc⟩, true), ?_⟩
      simpa only [U, ite_eq_left (hv true hs), Set.mem_inter_iff, Set.mem_setOf_eq, z] using
        And.intro hpG (And.intro hnear hs)
    · have hs : 0 < φ p * nativeCoreSign false := by simpa [nativeCoreSign] using hp
      refine mem_iUnion.mpr ⟨(⟨c, hc⟩, false), ?_⟩
      simpa only [U, ite_eq_left (hv false hs), Set.mem_inter_iff, Set.mem_setOf_eq, z] using
        And.intro hpG (And.intro hnear hs)
  let eqv := Fintype.equivFin I
  have hfiniteCov : μ (⋃ n, U (eqv.symm n))ᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hcov] with p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨eqv i, by simpa only [Equiv.symm_apply_apply] using hi⟩
  obtain ⟨V, hVm, hVd, hVU, hfloor, hloss⟩ := retain_heavy_cover μ (fun n => U (eqv.symm n))
    (fun n => hUm _) θ 0 (by rw [hfiniteCov])
  have hUnion : (⋃ i : I, V (eqv i)) = ⋃ n, V n := by
    ext p
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨eqv i, hi⟩, fun ⟨n, hn⟩ =>
      ⟨eqv.symm n, by simpa only [Equiv.apply_symm_apply] using hn⟩⟩
  refine ⟨codes, center, F, f, U, (fun i => V (eqv i)), hcard,
    (fun c hc => ⟨(hcenters c hc).1, (hcenters c hc).2.1, (hcenters c hc).2.2.1⟩),
    (fun i => ⟨hUm i, hVm _⟩), ?_, ?_, ?_, hpoint, ?_, ?_⟩
  · intro i j hij
    apply hVd
    intro heq
    exact hij (eqv.injective heq)
  · intro i
    refine ⟨?_, fun p hp => (hmem i p hp).2.1⟩
    simpa only [Equiv.symm_apply_apply] using hVU (eqv i)
  · intro i hi
    exact hdata i ((hmem i hi.choose hi.choose_spec).1)
  · intro i hi
    simpa only [Equiv.symm_apply_apply] using hfloor (eqv i) hi
  · rw [hUnion]
    apply (show μ (⋃ n, V n)ᶜ ≤ (Fintype.card I : ENNReal) * θ by
      simpa only [zero_add] using hloss).trans
    apply mul_le_mul_of_nonneg_right _ zero_le
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    simp only [I, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
