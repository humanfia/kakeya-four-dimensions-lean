-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RadiusTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealCover

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

theorem real_closedBall_radius_cover {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ n : ℕ, (n : ℝ) ≤ 3 * (R / r) ∧
      ∀ c : ℝ, ∃ d : Fin n → ℝ, Covers r (Metric.closedBall c R) d := by
  let n := Nat.ceil (R / r)
  have hR : 0 < R := hr.trans_le hrR
  have hratio : 1 ≤ R / r := (le_div_iff₀ hr).mpr (by simpa using hrR)
  have hn : R / r ≤ (n : ℝ) := Nat.le_ceil _
  have hn' : (n : ℝ) < R / r + 1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨n + 1, ?_, ?_⟩
  · push_cast
    linarith
  · intro c
    obtain ⟨u, hu⟩ := real_closedBall_mul_cover r n
    refine ⟨fun i => c + u i, ?_⟩
    intro x hx
    have hx' : x - c ∈ Metric.closedBall 0 (((n + 1 : ℕ) : ℝ) * r) := by
      have hxR : |x - c| ≤ R := by simpa [Metric.mem_closedBall, Real.dist_eq] using hx
      have hR' : R ≤ (n : ℝ) * r := (div_le_iff₀ hr).mp hn
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, Nat.cast_add, Nat.cast_one]
      nlinarith
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hu hx')
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_sub, add_comm] using hi

theorem Covers.refine_radius {r R : ℝ} {S : Set ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {m : ℕ} {c : Fin m → ℝ} (h : Covers R S c) :
    ∃ (n : ℕ) (d : Fin n → ℝ), Covers r S d ∧ (n : ℝ) ≤ (m : ℝ) * (3 * (R / r)) := by
  obtain ⟨k, hk, hcover⟩ := real_closedBall_radius_cover hr hrR
  choose d hd using fun i : Fin m => hcover (c i)
  refine ⟨m * k, _, h.refine d hd, ?_⟩
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg m)

/-- Coarsening an external-cover lower bound in the real line loses only the
ratio of the two scales, up to the explicit factor three. -/
theorem CoverLower.coarsen {r R N : ℝ} {S : Set ℝ}
    (h : CoverLower r S N) (hr : 0 < r) (hrR : r ≤ R) :
    CoverLower R S (N / (3 * (R / r))) := by
  intro m c hc
  obtain ⟨n, d, hd, hn⟩ := hc.refine_radius hr hrR
  have hR : 0 < R := hr.trans_le hrR
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (R / r))).mpr ((h n d hd).trans hn)

theorem real_dist_affine (k u x y : ℝ) :
    dist (k * x + u) (k * y + u) = |k| * dist x y := by
  rw [Real.dist_eq, Real.dist_eq]
  have h : k * x + u - (k * y + u) = k * (x - y) := by ring
  rw [h, abs_mul]

/-- Positive affine changes of coordinates preserve covering numbers at the
correspondingly scaled radius. -/
theorem CoverLower.affine_image {r N k u : ℝ} {S : Set ℝ}
    (h : CoverLower r S N) (hk : 0 < k) :
    CoverLower (k * r) ((fun x : ℝ => k * x + u) '' S) N := by
  intro m c hc
  let d : Fin m → ℝ := fun i => (c i - u) / k
  apply h m d
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc ⟨x, hx, rfl⟩)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hdi : k * d i + u = c i := by dsimp [d]; field_simp; ring
  have hid : dist (k * x + u) (c i) = k * dist x (d i) := by
    rw [← hdi, real_dist_affine, abs_of_pos hk]
  change dist (k * x + u) (c i) ≤ k * r at hi
  rw [hid] at hi
  exact (mul_le_mul_iff_right₀ hk).mp hi

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
