-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod.BorsukUlam.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_polynomial_grains_partition.PolyMethod.Tucker

/-!
# Borsuk–Ulam from Tucker's lemma

We derive the Borsuk–Ulam theorem (for the sup norm) from the grid form of Tucker's lemma.

* `exists_zero_of_tucker`: a continuous map `G : ℝⁿ → ℝⁿ` which is odd on the unit sphere has a
  zero in the closed unit ball. Otherwise `‖G‖ ≥ c > 0` on the ball; label a grid point `x` of
  `{-M, …, M}ⁿ` by an index of a maximal coordinate of `G (x / M)` together with its sign. The
  labelling is antipodal on the boundary, and for `M` large two adjacent grid points cannot carry
  opposite labels by uniform continuity.
* `borsukUlam_of_tucker`: compose `F` with the map `y ↦ (y, 1 - ‖y‖) / ‖(y, 1 - ‖y‖)‖` from the
  closed unit ball of `ℝⁿ` to the unit sphere of `ℝⁿ⁺¹`, which is odd on the unit sphere.
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod

/-- The grid point `x ∈ ℤⁿ` scaled by `1 / M`. -/
private noncomputable def gridPt {n : ℕ} (M : ℕ) (x : Fin n → ℤ) (i : Fin n) : ℝ :=
  (x i : ℝ) / M

private lemma norm_gridPt_le {n M : ℕ} (hM : 1 ≤ M) (x : Fin n → ℤ)
    (hx : ∀ i, |x i| ≤ (M : ℤ)) : ‖gridPt M x‖ ≤ 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [gridPt, Real.norm_eq_abs, abs_div, Nat.abs_cast, div_le_one hMpos]
  exact_mod_cast hx i

private lemma norm_gridPt_eq_one {n M : ℕ} (hM : 1 ≤ M) (x : Fin n → ℤ)
    (hx : ∀ i, |x i| ≤ (M : ℤ)) (hx' : ∃ i, |x i| = (M : ℤ)) : ‖gridPt M x‖ = 1 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  refine le_antisymm (norm_gridPt_le hM x hx) ?_
  obtain ⟨i, hi⟩ := hx'
  have hi' : |(x i : ℝ)| = M := by exact_mod_cast hi
  calc (1 : ℝ) = ‖gridPt M x i‖ := by
        rw [gridPt, Real.norm_eq_abs, abs_div, Nat.abs_cast, hi', div_self hMpos.ne']
    _ ≤ ‖gridPt M x‖ := norm_le_pi_norm _ i

private lemma gridPt_neg {n : ℕ} (M : ℕ) (x : Fin n → ℤ) :
    gridPt M (-x) = -gridPt M x := by
  funext i
  simp [gridPt, neg_div]

private lemma dist_gridPt_le {n M : ℕ} (hM : 1 ≤ M) (x y : Fin n → ℤ)
    (hxy : ∀ i, |x i - y i| ≤ 1) : dist (gridPt M x) (gridPt M y) ≤ 1 / M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Pi.sub_apply, gridPt, gridPt, ← sub_div, Real.norm_eq_abs, abs_div, Nat.abs_cast]
  gcongr
  exact_mod_cast hxy i

/-- Tucker's lemma implies: a continuous map `ℝⁿ → ℝⁿ` (sup norm) which is odd on the unit sphere
has a zero in the closed unit ball. -/
private lemma exists_zero_of_tucker (hT : TuckerStatement) (n : ℕ)
    (G : (Fin n → ℝ) → (Fin n → ℝ)) (hG : Continuous G)
    (hodd : ∀ y, ‖y‖ = 1 → G (-y) = -G y) : ∃ y, ‖y‖ ≤ 1 ∧ G y = 0 := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hKc : IsCompact (Metric.closedBall (0 : Fin n → ℝ) 1) := isCompact_closedBall 0 1
  have h0K : (0 : Fin n → ℝ) ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
    Metric.mem_closedBall_self zero_le_one
  -- the minimum `c > 0` of `‖G‖` on the ball
  obtain ⟨y0, hy0K, hy0min⟩ := hKc.exists_isMinOn ⟨0, h0K⟩ hG.norm.continuousOn
  have hcpos : 0 < ‖G y0‖ := norm_pos_iff.2 (hcon y0 (mem_closedBall_zero_iff.1 hy0K))
  have hcle : ∀ y : Fin n → ℝ, ‖y‖ ≤ 1 → ‖G y0‖ ≤ ‖G y‖ := fun y hy =>
    isMinOn_iff.1 hy0min y (mem_closedBall_zero_iff.2 hy)
  -- uniform continuity on the ball
  have hUC := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hG.continuousOn)
  obtain ⟨η, hηpos, hη⟩ := hUC _ hcpos
  obtain ⟨M, hM1, hMη⟩ : ∃ M : ℕ, 1 ≤ M ∧ 1 / (M : ℝ) < η := by
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hηpos
    exact ⟨m + 1, by omega, by push_cast; exact hm⟩
  -- `Fin n` is nonempty since `G 0 ≠ 0`
  have hne : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hcon 0 (by simp) (funext fun i => h.elim i)
  -- an index of maximal absolute value, depending only on the absolute values
  choose Φ hΦ using fun a : Fin n → ℝ => Finite.exists_max a
  have key : ∀ g : Fin n → ℝ, ‖g‖ ≤ |g (Φ fun i => |g i|)| := by
    intro g
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_
    rw [Real.norm_eq_abs]
    exact hΦ (fun i => |g i|) j
  have hbig : ∀ x : Fin n → ℤ, (∀ i, |x i| ≤ (M : ℤ)) →
      ‖G y0‖ ≤ |G (gridPt M x) (Φ fun i => |G (gridPt M x) i|)| := fun x hx =>
    (hcle _ (norm_gridPt_le hM1 x hx)).trans (key _)
  -- the labelling
  let lab : (Fin n → ℤ) → Fin n × Bool := fun x =>
    (Φ fun i => |G (gridPt M x) i|, decide (0 < G (gridPt M x) (Φ fun i => |G (gridPt M x) i|)))
  have hlab : ∀ x : Fin n → ℤ, (∀ i, |x i| ≤ (M : ℤ)) → (∃ i, |x i| = (M : ℤ)) →
      lab (-x) = ((lab x).1, !(lab x).2) := by
    intro x hx hx'
    have hneg : G (gridPt M (-x)) = -G (gridPt M x) := by
      rw [gridPt_neg, hodd _ (norm_gridPt_eq_one hM1 x hx hx')]
    have hb := hbig x hx
    simp only [lab, hneg, Pi.neg_apply, abs_neg]
    set g := G (gridPt M x)
    set i := Φ fun j => |g j|
    have hgi : g i ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hb
      linarith
    refine Prod.ext rfl ?_
    rcases lt_or_gt_of_ne hgi with h | h
    · simp [neg_pos.2 h, not_lt.2 h.le]
    · simp [h, not_lt.2 h.le]
  obtain ⟨x, y, hx, hy, hxy, hlxy⟩ := hT n M hM1 lab hlab
  have hidx : (Φ fun i => |G (gridPt M y) i|) = Φ fun i => |G (gridPt M x) i| :=
    congrArg Prod.fst hlxy
  have hsgn : decide (0 < G (gridPt M y) (Φ fun i => |G (gridPt M y) i|)) =
      !decide (0 < G (gridPt M x) (Φ fun i => |G (gridPt M x) i|)) :=
    congrArg Prod.snd hlxy
  have hbx := hbig x hx
  have hby := hbig y hy
  have hdist : dist (G (gridPt M x)) (G (gridPt M y)) < ‖G y0‖ :=
    hη _ (mem_closedBall_zero_iff.2 (norm_gridPt_le hM1 x hx))
      _ (mem_closedBall_zero_iff.2 (norm_gridPt_le hM1 y hy))
      ((dist_gridPt_le hM1 x y hxy).trans_lt hMη)
  rw [hidx] at hsgn hby
  set gx := G (gridPt M x)
  set gy := G (gridPt M y)
  set i := Φ fun j => |gx j|
  set c := ‖G y0‖
  have hdi : |gx i - gy i| < c := by
    calc |gx i - gy i| = ‖(gx - gy) i‖ := by rw [Pi.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖gx - gy‖ := norm_le_pi_norm _ i
      _ = dist gx gy := (dist_eq_norm _ _).symm
      _ < c := hdist
  rw [abs_lt] at hdi
  by_cases hpos : 0 < gx i
  · have hy0 : ¬ 0 < gy i := by simpa [hpos] using hsgn
    rw [abs_of_pos hpos] at hbx
    rw [abs_of_nonpos (not_lt.1 hy0)] at hby
    linarith
  · have hy0 : 0 < gy i := by simpa [hpos] using hsgn
    rw [abs_of_nonpos (not_lt.1 hpos)] at hbx
    rw [abs_of_pos hy0] at hby
    linarith

theorem borsukUlam_of_tucker (hT : TuckerStatement) : BorsukUlamStatement := by
  intro n F hF hFodd
  -- `w y = (y, 1 - ‖y‖)` never vanishes
  let w : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun y => Fin.snoc y (1 - ‖y‖)
  have hw : Continuous w := Continuous.finSnoc continuous_id (continuous_const.sub continuous_norm)
  have hw0 : ∀ y, w y ≠ 0 := by
    intro y hy
    have hlast : 1 - ‖y‖ = 0 := by
      simpa [w] using congrFun hy (Fin.last n)
    have hy0 : y = 0 := by
      funext k
      simpa [w] using congrFun hy (Fin.castSucc k)
    rw [hy0, norm_zero] at hlast
    norm_num at hlast
  have hwodd : ∀ y : Fin n → ℝ, ‖y‖ = 1 → w (-y) = -w y := by
    intro y hy
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [w, hy]
    · simp [w]
  -- normalise to the unit sphere
  let h : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun y => ‖w y‖⁻¹ • w y
  have hh : Continuous h := (hw.norm.inv₀ fun y => norm_ne_zero_iff.2 (hw0 y)).smul hw
  have hh1 : ∀ y, ‖h y‖ = 1 := by
    intro y
    simp only [h, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hw0 y))
  have hhodd : ∀ y : Fin n → ℝ, ‖y‖ = 1 → h (-y) = -h y := by
    intro y hy
    simp only [h, hwodd y hy, norm_neg, smul_neg]
  obtain ⟨y, -, hy⟩ := exists_zero_of_tucker hT n (F ∘ h) (hF.comp hh) fun y hy => by
    simp only [Function.comp_apply, hhodd y hy, hFodd]
  exact ⟨h y, hh1 y, hy⟩

/-- The Borsuk–Ulam theorem (sup norm): a continuous odd map `ℝ^(n+1) → ℝ^n` has a zero on the
unit sphere. -/
theorem borsukUlam : BorsukUlamStatement := borsukUlam_of_tucker Tucker.tucker

end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
