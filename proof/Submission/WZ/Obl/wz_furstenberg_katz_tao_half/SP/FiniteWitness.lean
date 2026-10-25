-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.FiniteWitness.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Basic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

section Compactness

variable {X : Type*} [MetricSpace X] [ProperSpace X] [Nonempty X]

/-- For a bounded set in a proper metric space, coverability by a fixed number
of closed balls is determined by its finite subsets. -/
theorem exists_cover_of_finite_subsets {r : ℝ} (hr : 0 ≤ r) {S : Set X}
    (hS : Bornology.IsBounded S) (m : ℕ)
    (hfinite : ∀ T : Finset X, (↑T : Set X) ⊆ S →
      ∃ c : Fin m → X, Covers r (↑T : Set X) c) :
    ∃ c : Fin m → X, Covers r S c := by
  classical
  let x₀ : X := Classical.arbitrary X
  obtain ⟨R, hR, hSR⟩ := hS.subset_closedBall_lt 0 x₀
  let K : Set X := Metric.closedBall x₀ (R + r)
  have hK : IsCompact K := isCompact_closedBall _ _
  let C : Set (Fin m → X) := Set.pi Set.univ (fun _ => K)
  have hC : IsCompact C := isCompact_univ_pi (fun _ => hK)
  let A (x : S) : Set (Fin m → X) := {c | ∃ i, dist x.val (c i) ≤ r}
  have hA : ∀ x, IsClosed (A x) := by
    intro x
    have heq : A x = ⋃ i : Fin m, {c | dist x.val (c i) ≤ r} := by
      ext c
      simp [A]
    rw [heq]
    exact isClosed_iUnion_of_finite (fun i => isClosed_le
      (continuous_const.dist (continuous_apply i)) continuous_const)
  have hFIP : ∀ u : Finset S, (C ∩ ⋂ x ∈ u, A x).Nonempty := by
    intro u
    let T : Finset X := u.image Subtype.val
    have hTS : (↑T : Set X) ⊆ S := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact y.property
    obtain ⟨c, hc⟩ := hfinite T hTS
    let c' : Fin m → X := fun i =>
      if (∃ x ∈ T, dist x (c i) ≤ r) then c i else x₀
    have hc'K : ∀ i, c' i ∈ K := by
      intro i
      by_cases hi : ∃ x ∈ T, dist x (c i) ≤ r
      · obtain ⟨x, hx, hxc⟩ := hi
        have hxR : dist x x₀ ≤ R := hSR (hTS hx)
        change dist (c' i) x₀ ≤ R + r
        rw [show c' i = c i from ite_eq_left ⟨x, hx, hxc⟩]
        calc dist (c i) x₀ ≤ dist (c i) x + dist x x₀ := dist_triangle _ _ _
          _ ≤ R + r := by rw [dist_comm (c i) x]; linarith
      · change dist (c' i) x₀ ≤ R + r
        rw [show c' i = x₀ from ite_eq_right hi, dist_self]
        linarith
    refine ⟨c', ?_, ?_⟩
    · exact Set.mem_pi.mpr (fun i _ => hc'K i)
    · refine Set.mem_iInter.mpr (fun x => Set.mem_iInter.mpr (fun hx => ?_))
      have hxT : x.val ∈ T := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hxT)
      refine ⟨i, ?_⟩
      rw [show c' i = c i from ite_eq_left ⟨x.val, hxT, hi⟩]
      exact hi
  obtain ⟨c, hcC, hcA⟩ := hC.inter_iInter_nonempty A hA hFIP
  refine ⟨c, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iInter.mp hcA ⟨x, hx⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

omit [ProperSpace X] in
theorem Covers.extend {r : ℝ} {S : Set X} {n m : ℕ} {c : Fin n → X}
    (h : Covers r S c) (hnm : n ≤ m) : ∃ d : Fin m → X, Covers r S d := by
  classical
  let d : Fin m → X := fun j => if hj : j.val < n then c ⟨j.val, hj⟩ else Classical.arbitrary X
  refine ⟨d, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h hx)
  refine Set.mem_iUnion.mpr ⟨⟨i.val, lt_of_lt_of_le i.isLt hnm⟩, ?_⟩
  simpa [d, i.isLt] using hi

/-- Exact finite witnesses for real lower bounds on external covering numbers.
Neither the radius nor the lower bound is weakened. -/
theorem CoverLower.exists_finite_subset {r N : ℝ} {S : Set X}
    (h : CoverLower r S N) (hr : 0 ≤ r) (hS : Bornology.IsBounded S) :
    ∃ T : Finset X, (↑T : Set X) ⊆ S ∧ CoverLower r (↑T : Set X) N := by
  classical
  by_cases hN : N ≤ 0
  · refine ⟨∅, by simp, ?_⟩
    simpa using (coverLower_empty_iff (X := X) (r := r) (N := N)).mpr hN
  have hNpos : 0 < N := lt_of_not_ge hN
  let m := Nat.ceil N - 1
  have hm : (m : ℝ) < N := by
    apply Nat.lt_ceil.mp
    have hceil := Nat.ceil_pos.mpr hNpos
    dsimp [m]
    omega
  have hnocover : ¬ ∃ c : Fin m → X, Covers r S c := by
    rintro ⟨c, hc⟩
    exact hm.not_ge (h m c hc)
  have hnotall : ¬ ∀ T : Finset X, (↑T : Set X) ⊆ S →
      ∃ c : Fin m → X, Covers r (↑T : Set X) c :=
    fun H => hnocover (exists_cover_of_finite_subsets hr hS m H)
  push Not at hnotall
  obtain ⟨T, hTS, hT⟩ := hnotall
  refine ⟨T, hTS, ?_⟩
  intro n c hc
  by_contra hn
  have hnceil : n < Nat.ceil N := Nat.lt_ceil.mpr (lt_of_not_ge hn)
  have hnm : n ≤ m := by dsimp [m]; omega
  obtain ⟨d, hd⟩ := hc.extend hnm
  exact hT d hd

end Compactness

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
