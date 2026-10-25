-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric
open scoped NNReal ENNReal

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Triple := Plane × Plane × Plane

/-- A finite cover in the convention of the frozen theorem. -/
def Covers {X : Type*} [PseudoMetricSpace X] (r : ℝ) (S : Set X)
    {m : ℕ} (c : Fin m → X) : Prop :=
  S ⊆ ⋃ j, Metric.closedBall (c j) r

/-- A real lower bound for the number of closed balls in any finite cover. -/
def CoverLower {X : Type*} [PseudoMetricSpace X] (r : ℝ) (S : Set X) (N : ℝ) : Prop :=
  ∀ (m : ℕ) (c : Fin m → X), Covers r S c → N ≤ (m : ℝ)

section Cover

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable {r s N M : ℝ} {S T : Set X} {U : Set Y}

theorem Covers.mono_set {m : ℕ} {c : Fin m → X} (h : Covers r T c)
    (hST : S ⊆ T) : Covers r S c := hST.trans h

theorem Covers.mono_radius {m : ℕ} {c : Fin m → X} (h : Covers r S c)
    (hrs : r ≤ s) : Covers s S c := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h hx)
  exact Set.mem_iUnion.mpr ⟨i, hi.trans hrs⟩

theorem Covers.prod {m n : ℕ} {c : Fin m → X} {d : Fin n → Y}
    (hS : Covers r S c) (hU : Covers r U d) :
    Covers r (S ×ˢ U)
      (fun i : Fin (m * n) =>
        (c (finProdFinEquiv.symm i).1, d (finProdFinEquiv.symm i).2)) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hS hx)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hU hy)
  refine Set.mem_iUnion.mpr ⟨finProdFinEquiv (i, j), ?_⟩
  simpa [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] using And.intro hi hj

theorem CoverLower.mono_set (h : CoverLower r S N) (hST : S ⊆ T) :
    CoverLower r T N := fun m c hc => h m c (hc.mono_set hST)

theorem CoverLower.mono_radius (h : CoverLower r S N) (hsr : s ≤ r) :
    CoverLower s S N := fun m c hc => h m c (hc.mono_radius hsr)

theorem CoverLower.weaken (h : CoverLower r S N) (hMN : M ≤ N) :
    CoverLower r S M := fun m c hc => hMN.trans (h m c hc)

theorem CoverLower.nonempty (h : CoverLower r S N) (hN : 0 < N) : S.Nonempty := by
  by_contra hS
  have h0 := h 0 (fun i => Fin.elim0 i) (by simp [Covers, Set.not_nonempty_iff_eq_empty.mp hS])
  exact not_le_of_gt hN (by simpa using h0)

theorem coverLower_of_nonempty (hS : S.Nonempty) (hN : N ≤ 1) : CoverLower r S N := by
  intro m c hc
  obtain ⟨x, hx⟩ := hS
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hc hx)
  have hm : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i.isLt)
  exact hN.trans (by exact_mod_cast hm)

theorem coverLower_one_iff : CoverLower r S 1 ↔ S.Nonempty :=
  ⟨fun h => h.nonempty zero_lt_one, fun h => coverLower_of_nonempty h le_rfl⟩

theorem coverLower_empty_iff : CoverLower r (∅ : Set X) N ↔ N ≤ 0 := by
  constructor
  · intro h
    simpa using h 0 (fun i => Fin.elim0 i) (by simp [Covers])
  · intro h m c hc
    exact h.trans (Nat.cast_nonneg m)

/-- A totally bounded set has a finite internal net whose distinct points have
distance strictly greater than the radius. -/
theorem exists_separated_cover (hS : TotallyBounded S) (hr : 0 < r) :
    ∃ (m : ℕ) (c : Fin m → X),
      (∀ i, c i ∈ S) ∧
      (∀ i j, i ≠ j → r < dist (c i) (c j)) ∧ Covers r S c := by
  classical
  let ε : ℝ≥0 := ⟨r, hr.le⟩
  have hε : ε / 2 ≠ 0 := by
    apply ne_of_gt
    exact div_pos hr (by norm_num)
  obtain ⟨A, hAS, hAfin, hAcov⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded hε hS
  have hpack : Metric.packingNumber ε S ≠ ⊤ := by
    apply ne_top_of_le_ne_top hAfin.encard_lt_top.ne
    calc Metric.packingNumber ε S
        = Metric.packingNumber (2 * (ε / 2)) S := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε / 2) S :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ A.encard := hAcov.externalCoveringNumber_le_encard
  let D := Metric.maximalSeparatedSet ε S
  have hDfin : D.Finite := Set.encard_ne_top_iff.mp (by
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack)
  let : Fintype D := hDfin.fintype
  let e := Fintype.equivFin D
  let c : Fin (Fintype.card D) → X := fun i => (e.symm i).val
  refine ⟨Fintype.card D, c, ?_, ?_, ?_⟩
  · intro i
    exact Metric.maximalSeparatedSet_subset (e.symm i).property
  · intro i j hij
    have hcne : c i ≠ c j := by
      intro hc
      exact hij (e.symm.injective (Subtype.ext hc))
    have hdist := Metric.isSeparated_maximalSeparatedSet
      (ε := ε) (A := S) (e.symm i).property (e.symm j).property hcne
    have hreal := (ENNReal.toReal_lt_toReal (by simp) (edist_ne_top _ _)).mpr hdist
    rw [ENNReal.coe_toReal, ← dist_edist] at hreal
    exact hreal
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.isCover_maximalSeparatedSet hpack hx
    refine Set.mem_iUnion.mpr ⟨e ⟨y, hy⟩, ?_⟩
    have hxy' : dist x y ≤ r := by
      have hreal := ENNReal.toReal_mono (by simp) hxy
      rw [ENNReal.coe_toReal, ← dist_edist] at hreal
      exact hreal
    simpa [c, Metric.mem_closedBall] using hxy'

/-- The lower-cover hypothesis gives a finite separated witness of the same size. -/
theorem CoverLower.exists_separated (h : CoverLower r S N) (hS : TotallyBounded S)
    (hr : 0 < r) :
    ∃ (m : ℕ) (c : Fin m → X), N ≤ (m : ℝ) ∧
      (∀ i, c i ∈ S) ∧
      (∀ i j, i ≠ j → r < dist (c i) (c j)) ∧ Covers r S c := by
  obtain ⟨m, c, hcS, hcsep, hcov⟩ := exists_separated_cover hS hr
  exact ⟨m, c, h m c hcov, hcS, hcsep, hcov⟩

end Cover

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
