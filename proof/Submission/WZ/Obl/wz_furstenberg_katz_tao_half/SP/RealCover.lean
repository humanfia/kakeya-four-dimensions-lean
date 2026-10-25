-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RealCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Basic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

/-- An interval of radius `(n+1)r` is covered by `n+1` closed intervals of radius `r`. -/
theorem real_closedBall_mul_cover (r : ℝ) (n : ℕ) :
    ∃ c : Fin (n + 1) → ℝ,
      Covers r (Metric.closedBall 0 (((n + 1 : ℕ) : ℝ) * r)) c := by
  induction n with
  | zero =>
      refine ⟨fun _ => 0, ?_⟩
      intro x hx
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      let d : Fin (n + 1 + 1) → ℝ := Fin.snoc (fun i => c i - r) (((n + 1 : ℕ) : ℝ) * r)
      refine ⟨d, ?_⟩
      intro x hx
      have hx' : -(((n + 2 : ℕ) : ℝ) * r) ≤ x ∧ x ≤ ((n + 2 : ℕ) : ℝ) * r := by
        simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] using hx
      by_cases hleft : x ≤ (n : ℝ) * r
      · have hxr : x + r ∈ Metric.closedBall 0 (((n + 1 : ℕ) : ℝ) * r) := by
          simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le, Nat.cast_add,
            Nat.cast_one, Nat.cast_ofNat] at hx' ⊢
          constructor <;> nlinarith
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hxr)
        refine Set.mem_iUnion.mpr ⟨i.castSucc, ?_⟩
        simpa [d, Metric.mem_closedBall, Real.dist_eq, sub_sub_eq_add_sub] using hi
      · refine Set.mem_iUnion.mpr ⟨Fin.last (n + 1), ?_⟩
        simp only [d, Fin.snoc_last, Metric.mem_closedBall, Real.dist_eq, abs_le,
          Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hx' ⊢
        constructor <;> nlinarith

theorem real_closedBall_nine_cover (r c : ℝ) :
    ∃ d : Fin 9 → ℝ, Covers r (Metric.closedBall c (9 * r)) d := by
  obtain ⟨u, hu⟩ := real_closedBall_mul_cover r 8
  refine ⟨fun i => c + u i, ?_⟩
  intro x hx
  have hx' : x - c ∈ Metric.closedBall 0 (((8 + 1 : ℕ) : ℝ) * r) := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hu hx')
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  simpa [Metric.mem_closedBall, Real.dist_eq, sub_sub, add_comm] using hi

theorem Covers.refine {X : Type*} [PseudoMetricSpace X] {r R : ℝ} {S : Set X}
    {m n : ℕ} {c : Fin m → X} (h : Covers R S c)
    (d : Fin m → Fin n → X) (hd : ∀ i, Covers r (Metric.closedBall (c i) R) (d i)) :
    Covers r S (fun j : Fin (m * n) =>
      d (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h hx)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hd i hi)
  exact Set.mem_iUnion.mpr ⟨finProdFinEquiv (i, j), by simpa using hj⟩

theorem Covers.refine_nine {r : ℝ} {S : Set ℝ} {m : ℕ} {c : Fin m → ℝ}
    (h : Covers (9 * r) S c) : ∃ d : Fin (m * 9) → ℝ, Covers r S d := by
  choose d hd using fun i : Fin m => real_closedBall_nine_cover r (c i)
  exact ⟨_, h.refine d hd⟩

/-- A perturbation by at most eight radii loses at most a factor nine in a
one-dimensional external-cover lower bound. -/
theorem CoverLower.transfer_close {r N : ℝ} {S T : Set ℝ}
    (h : CoverLower r S N) (hclose : ∀ x ∈ S, ∃ y ∈ T, dist x y ≤ 8 * r) :
    CoverLower r T (N / 9) := by
  intro m c hc
  have hbig : Covers (9 * r) S c := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hclose x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hy)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change dist x (c i) ≤ 9 * r
    have hdist := dist_triangle x y (c i)
    have hi' : dist y (c i) ≤ r := hi
    linarith
  obtain ⟨d, hd⟩ := hbig.refine_nine
  have hm := h (m * 9) d hd
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 9)).mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hm

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
