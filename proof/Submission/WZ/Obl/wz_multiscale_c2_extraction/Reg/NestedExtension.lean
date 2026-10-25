-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.NestedExtension.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.MultiscaleExtension

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set

/-- A set of heights with positive Lebesgue measure contains two quantitatively
separated points. No regularity of the set beyond the volume bound is required. -/
theorem exists_separated_heights {D : Set ℝ} {m : ℝ} (hm : 0 < m)
    (hD : ENNReal.ofReal m ≤ MeasureTheory.volume D) :
    ∃ z₁ ∈ D, ∃ z₂ ∈ D, m / 4 ≤ z₂ - z₁ := by
  have hpos : 0 < MeasureTheory.volume D := (ENNReal.ofReal_pos.mpr hm).trans_le hD
  have hne : D.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, MeasureTheory.measure_empty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨x, hx⟩ := hne
  have hex : ∃ y ∈ D, m / 4 ≤ |y - x| := by
    by_contra h
    push Not at h
    have hsub : D ⊆ Metric.ball x (m / 4) := by
      intro y hy
      exact Metric.mem_ball.mpr (by simpa only [Real.dist_eq] using h y hy)
    have hvol := hD.trans (MeasureTheory.measure_mono hsub)
    rw [Real.volume_ball] at hvol
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2 * (m / 4))).mp hvol
    linarith
  obtain ⟨y, hy, hdist⟩ := hex
  rcases le_total x y with hxy | hyx
  · exact ⟨x, hx, y, hy, by simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hdist⟩
  · exact ⟨y, hy, x, hx, by simpa only [abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub] using hdist⟩

/-- Two separated points control an affine function throughout their ambient interval.
The points need not be the endpoints of the interval. -/
theorem affine_bound_of_two_points {l u z₁ z₂ b s H r : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hz₁ : z₁ ∈ Icc l u) (_hz₂ : z₂ ∈ Icc l u)
    (hsep : r ≤ z₂ - z₁) (h₁ : |b + s * z₁| ≤ H) (h₂ : |b + s * z₂| ≤ H) :
    |s| ≤ 2 * H / r ∧
      ∀ z ∈ Icc l u, |b + s * z| ≤ H + 2 * H / r * (u - l) := by
  have hdiff : |s| * (z₂ - z₁) ≤ 2 * H := by
    calc |s| * (z₂ - z₁) = |(b + s * z₂) - (b + s * z₁)| := by
          rw [show (b + s * z₂) - (b + s * z₁) = s * (z₂ - z₁) by ring,
            abs_mul, abs_of_pos (hr.trans_le hsep)]
      _ ≤ |b + s * z₂| + |b + s * z₁| := abs_sub _ _
      _ ≤ 2 * H := by linarith
  have hs : |s| ≤ 2 * H / r := (le_div_iff₀ hr).mpr
    ((mul_le_mul_of_nonneg_left hsep (abs_nonneg _)).trans hdiff)
  refine ⟨hs, ?_⟩
  intro z hz
  have hzdist : |z - z₁| ≤ u - l := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2, hz₁.1, hz₁.2]
  calc |b + s * z| = |(b + s * z₁) + s * (z - z₁)| := by congr 1; ring
    _ ≤ |b + s * z₁| + |s| * |z - z₁| := by
      simpa only [abs_mul] using abs_add_le (b + s * z₁) (s * (z - z₁))
    _ ≤ H + 2 * H / r * (u - l) :=
      add_le_add h₁ (mul_le_mul hs hzdist (abs_nonneg _) (by positivity))

/-- Endpoint error controls both derivative budgets for a padded affine correction. -/
theorem affine_correction_budgets {l u a y s H : ℝ}
    (ha : 0 < a) (hlen : a ≤ u - l) (hH : 0 ≤ H)
    (hl : |y| ≤ H) (hu : |y + s * (u - l)| ≤ H) :
    (|y| + |y + s * (u - l)|) / a + |s| ≤ 4 * (H / a) ∧
      (|y| + |y + s * (u - l)|) / a ^ 2 + |s| / a ≤ 4 * (H / a ^ 2) := by
  have hlu : l < u := by linarith
  have hs : |s| ≤ 2 * H / a := by
    refine (affine_slope_bound_of_endpoints hlu hl hu).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) ha hlen
  constructor
  · calc (|y| + |y + s * (u - l)|) / a + |s|
        ≤ (2 * H) / a + (2 * H) / a :=
          add_le_add (div_le_div_of_nonneg_right (by linarith) ha.le) hs
      _ = 4 * (H / a) := by ring
  · calc (|y| + |y + s * (u - l)|) / a ^ 2 + |s| / a
        ≤ (2 * H) / a ^ 2 + (2 * H / a) / a :=
          add_le_add (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))
            (div_le_div_of_nonneg_right hs ha.le)
      _ = 4 * (H / a ^ 2) := by ring

/-- When two affine axes approximate the same slope on a sufficiently large set
of heights, their difference is controlled on the whole interval. This supplies
endpoint bounds for a nested correction without assuming the endpoints are retained. -/
theorem affine_difference_bound_of_common_samples
    {l u b₁ b₂ s₁ s₂ ε₁ ε₂ m : ℝ} {D : Set ℝ} {f : ℝ → ℝ}
    (hm : 0 < m) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hDI : D ⊆ Icc l u)
    (hD : ENNReal.ofReal m ≤ MeasureTheory.volume D)
    (hfit₁ : ∀ z ∈ D, |f z - (b₁ + s₁ * z)| ≤ ε₁)
    (hfit₂ : ∀ z ∈ D, |f z - (b₂ + s₂ * z)| ≤ ε₂) :
    ∀ z ∈ Icc l u, |(b₁ + s₁ * z) - (b₂ + s₂ * z)| ≤
      (ε₁ + ε₂) + 8 * (ε₁ + ε₂) / m * (u - l) := by
  obtain ⟨z₁, hz₁, z₂, hz₂, hsep⟩ := exists_separated_heights hm hD
  have hfit : ∀ z ∈ D, |(b₁ - b₂) + (s₁ - s₂) * z| ≤ ε₁ + ε₂ := by
    intro z hz
    calc |(b₁ - b₂) + (s₁ - s₂) * z|
        = |(b₁ + s₁ * z) - (b₂ + s₂ * z)| := by congr 1; ring
      _ ≤ |(b₁ + s₁ * z) - f z| + |f z - (b₂ + s₂ * z)| := abs_sub_le _ _ _
      _ ≤ ε₁ + ε₂ := add_le_add (by simpa only [abs_sub_comm] using hfit₁ z hz) (hfit₂ z hz)
  have hbound := (affine_bound_of_two_points (by positivity : 0 < m / 4)
    (add_nonneg hε₁ hε₂) (hDI hz₁) (hDI hz₂) hsep (hfit z₁ hz₁) (hfit z₂ hz₂)).2
  intro z hz
  convert hbound z hz using 1 <;> congr 1 <;> ring

/-- Successive differences telescope along a finite chain. -/
theorem sum_affine_differences {N : ℕ} (A : Fin (N + 1) → ℝ) :
    (∑ k : Fin N, (A k.succ - A k.castSucc)) = A (Fin.last N) - A 0 := by
  rw [Finset.sum_sub_distrib]
  have hleft := Fin.sum_univ_succ A
  have hright := Fin.sum_univ_castSucc A
  linarith

/-- Smooth gluing for a finite hierarchy of affine axes. The correction at a child
is its axis minus its parent's. On a selected nested chain these corrections telescope.
Derivative losses depend on the errors and padding at each scale, not on the number
of intervals. This is the analytic part of the nested-trapezoid construction. -/
theorem exists_smooth_nested_extension : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (I : Fin (N + 1) → Type) [∀ k, Fintype (I k)]
      (parent : (k : Fin N) → I k.succ → I k.castSucc)
      (b s : (k : Fin (N + 1)) → I k → ℝ)
      (l u : (k : Fin N) → I k.succ → ℝ) (a H : Fin N → ℝ)
      (D : Set ℝ) (f : ℝ → ℝ) (δ : ℝ),
      (∀ k, 0 < a k) → (∀ k, 0 ≤ H k) →
      (∀ k i, a k ≤ u k i - l k i) →
      (∀ k, Pairwise fun i j => Disjoint (Icc (l k i - a k) (u k i + a k))
        (Icc (l k j - a k) (u k j + a k))) →
      (∀ i, b 0 i = 0 ∧ s 0 i = 0) →
      (∀ k i,
        |(b k.succ i + s k.succ i * l k i) -
          (b k.castSucc (parent k i) + s k.castSucc (parent k i) * l k i)| ≤ H k ∧
        |(b k.succ i + s k.succ i * u k i) -
          (b k.castSucc (parent k i) + s k.castSucc (parent k i) * u k i)| ≤ H k) →
      (∀ z ∈ D, ∃ path : (k : Fin (N + 1)) → I k,
        (∀ k, parent k (path k.succ) = path k.castSucc) ∧
        (∀ k, z ∈ Icc (l k (path k.succ)) (u k (path k.succ))) ∧
        |f z - (b (Fin.last N) (path (Fin.last N)) +
          s (Fin.last N) (path (Fin.last N)) * z)| ≤ δ) →
      ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
        (∀ z ∈ D, |f z - g z| ≤ δ) ∧
        (∀ z, |deriv g z| ≤ C * ∑ k, H k / a k) ∧
        (∀ z, |deriv (deriv g) z| ≤ C * ∑ k, H k / (a k) ^ 2) := by
  obtain ⟨C, hC, hext⟩ := exists_smooth_multiscale_extension
  refine ⟨4 * C, by positivity, ?_⟩
  intro N I _ parent b s l u a H D f δ ha hH hlen hsep hzero herrors hpath
  let y : (k : Fin N) → I k.succ → ℝ := fun k i =>
    (b k.succ i + s k.succ i * l k i) -
      (b k.castSucc (parent k i) + s k.castSucc (parent k i) * l k i)
  let t : (k : Fin N) → I k.succ → ℝ := fun k i =>
    s k.succ i - s k.castSucc (parent k i)
  have hcorrection : ∀ k i z, y k i + t k i * (z - l k i) =
      (b k.succ i + s k.succ i * z) -
        (b k.castSucc (parent k i) + s k.castSucc (parent k i) * z) := by
    intro k i z
    dsimp [y, t]
    ring
  have hbudgets : ∀ k i,
      (|y k i| + |y k i + t k i * (u k i - l k i)|) / a k + |t k i| ≤
          4 * (H k / a k) ∧
      (|y k i| + |y k i + t k i * (u k i - l k i)|) / (a k) ^ 2 + |t k i| / a k ≤
          4 * (H k / (a k) ^ 2) := by
    intro k i
    exact affine_correction_budgets (ha k) (hlen k i) (hH k) (herrors k i).1
      (by simpa only [hcorrection] using (herrors k i).2)
  have hsumapprox : ∀ z ∈ D, ∃ path : (k : Fin N) → I k.succ,
      (∀ k, z ∈ Icc (l k (path k)) (u k (path k))) ∧
        |f z - ∑ k, (y k (path k) + t k (path k) * (z - l k (path k)))| ≤ δ := by
    intro z hz
    obtain ⟨path, hparent, hmem, hfinal⟩ := hpath z hz
    refine ⟨(fun k => path k.succ), hmem, ?_⟩
    have heq : (∑ k : Fin N, (y k (path k.succ) +
        t k (path k.succ) * (z - l k (path k.succ)))) =
        b (Fin.last N) (path (Fin.last N)) + s (Fin.last N) (path (Fin.last N)) * z := by
      simp_rw [hcorrection, hparent]
      rw [sum_affine_differences (fun k => b k (path k) + s k (path k) * z)]
      simp only [(hzero (path 0)).1, (hzero (path 0)).2, zero_mul, zero_add, sub_zero]
    rwa [heq]
  obtain ⟨g, hg, hgf, hg₁, hg₂⟩ := hext (Fin N) (fun k => I k.succ) l u
    (fun k _ => a k) y t (fun k => 4 * (H k / a k)) (fun k => 4 * (H k / (a k) ^ 2))
    D f δ (fun k _ => ha k) hsep
    (fun k => mul_nonneg (by norm_num) (div_nonneg (hH k) (ha k).le))
    (fun k => mul_nonneg (by norm_num) (div_nonneg (hH k) (sq_nonneg _)))
    (fun k i => (hbudgets k i).1) (fun k i => (hbudgets k i).2) hsumapprox
  refine ⟨g, hg, hgf, ?_, ?_⟩
  · intro z
    simpa only [← Finset.mul_sum, mul_left_comm, mul_assoc] using hg₁ z
  · intro z
    simpa only [← Finset.mul_sum, mul_left_comm, mul_assoc] using hg₂ z

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
