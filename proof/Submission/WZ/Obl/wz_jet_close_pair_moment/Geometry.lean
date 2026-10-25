-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The sum of the three absolute jet differences. -/
noncomputable def jetDistance (f g : ℝ → ℝ) (z : ℝ) : ℝ :=
  |f z - g z| + |deriv f z - deriv g z| +
    |deriv (deriv f) z - deriv (deriv g) z|

/-- Exactly the jet predicate occurring in the frozen theorem. -/
def JetControlled {n : ℕ} (q : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : Fin n → ℝ → ℝ) : Prop :=
  ∀ i j z, z ∈ Set.Icc (-1 : ℝ) 1 →
    dist (q i) (q j) ≤ 30 * jetDistance (g i) (g j) z ∧
      jetDistance (g i) (g j) z ≤ 19 * dist (q i) (q j)

theorem jetDistance_nonneg (f g : ℝ → ℝ) (z : ℝ) : 0 ≤ jetDistance f g z := by
  unfold jetDistance
  positivity

theorem value_le_jetDistance (f g : ℝ → ℝ) (z : ℝ) :
    |f z - g z| ≤ jetDistance f g z := by
  unfold jetDistance
  linarith [abs_nonneg (deriv f z - deriv g z),
    abs_nonneg (deriv (deriv f) z - deriv (deriv g) z)]

theorem deriv_le_jetDistance (f g : ℝ → ℝ) (z : ℝ) :
    |deriv f z - deriv g z| ≤ jetDistance f g z := by
  unfold jetDistance
  linarith [abs_nonneg (f z - g z),
    abs_nonneg (deriv (deriv f) z - deriv (deriv g) z)]

theorem deriv2_le_jetDistance (f g : ℝ → ℝ) (z : ℝ) :
    |deriv (deriv f) z - deriv (deriv g) z| ≤ jetDistance f g z := by
  unfold jetDistance
  linarith [abs_nonneg (f z - g z), abs_nonneg (deriv f z - deriv g z)]

/-- The cinematic nondegeneracy constant is uniform in the family. -/
theorem JetControlled.jetDistance_le_cross {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (i j : Fin n) {z w : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hw : w ∈ Set.Icc (-1 : ℝ) 1) :
    jetDistance (g i) (g j) z ≤ 570 * jetDistance (g i) (g j) w := by
  have hz' := (hjet i j z hz).2
  have hw' := (hjet i j w hw).1
  linarith

/-- The coefficient ball yields a uniform C2 diameter. -/
theorem JetControlled.jetDistance_le_380 {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hq : ∀ i, ‖q i‖ ≤ 10)
    (i j : Fin n) {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    jetDistance (g i) (g j) z ≤ 380 := by
  have hd := dist_le_norm_add_norm (q i) (q j)
  have hj := (hjet i j z hz).2
  linarith [hq i, hq j]

/-- Distinct coefficient parameters have distinct jets at every time. -/
theorem JetControlled.jet_injective {n : ℕ} {δ : ℝ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (q i) (q j))
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    Function.Injective (fun i => (g i z, deriv (g i) z, deriv (deriv (g i)) z)) := by
  intro i j hij
  by_contra hne
  have he0 := congrArg Prod.fst hij
  have he1 := congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) hij
  have he2 := congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) hij
  dsimp only at he0 he1 he2
  have hd := (hjet i j z hz).1
  simp only [jetDistance, he0, he1, he2, sub_self, abs_zero, add_zero, mul_zero] at hd
  linarith [hsep i j hne]

/-- Small value and slope differences force curvature separation. -/
theorem JetControlled.curvature_separation {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (i j : Fin n) {z : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1)
    (hsmall : |g i z - g j z| + |deriv (g i) z - deriv (g j) z| ≤
      dist (q i) (q j) / 60) :
    dist (q i) (q j) / 60 ≤ |deriv (deriv (g i)) z - deriv (deriv (g j)) z| := by
  have h := (hjet i j z hz).1
  unfold jetDistance at h
  linarith

private theorem differentiable_deriv_of_contDiff_two {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) : Differentiable ℝ (deriv f) := by
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv' (n := 1)
  exact hf'.differentiable (by norm_num)

theorem deriv_sub_of_contDiff_two {f h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) :
    deriv (f - h) = deriv f - deriv h := by
  funext z
  exact deriv_sub ((hf.differentiable (by norm_num)) z)
    ((hh.differentiable (by norm_num)) z)

theorem deriv2_sub_of_contDiff_two {f h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) :
    deriv (deriv (f - h)) = deriv (deriv f) - deriv (deriv h) := by
  rw [deriv_sub_of_contDiff_two hf hh]
  funext z
  exact deriv_sub ((differentiable_deriv_of_contDiff_two hf) z)
    ((differentiable_deriv_of_contDiff_two hh) z)

theorem jetDistance_sub_reference {f g h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (z : ℝ) :
    jetDistance (f - h) (g - h) z = jetDistance f g z := by
  unfold jetDistance
  rw [deriv2_sub_of_contDiff_two hf hh, deriv2_sub_of_contDiff_two hg hh]
  simp only [deriv_sub_of_contDiff_two hf hh, deriv_sub_of_contDiff_two hg hh,
    Pi.sub_apply, sub_sub_sub_cancel_right]

theorem JetControlled.sub_reference {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) :
    JetControlled q (fun i => g i - h) := by
  intro i j z hz
  simpa only [jetDistance_sub_reference (hg i) (hg j) hh] using hjet i j z hz

/-- A uniform Lipschitz estimate for differences of curve values. -/
theorem JetControlled.value_difference_lipschitz {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (i j : Fin n) {z w : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hw : w ∈ Set.Icc (-1 : ℝ) 1) :
    |(g i z - g j z) - (g i w - g j w)| ≤ 19 * dist (q i) (q j) * |z - w| := by
  have hd : Differentiable ℝ (g i - g j) :=
    ((hg i).sub (hg j)).differentiable (by norm_num)
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hd x) (C := 19 * dist (q i) (q j)) (by
      intro x hx
      rw [deriv_sub_of_contDiff_two (hg i) (hg j)]
      exact (deriv_le_jetDistance (g i) (g j) x).trans (hjet i j x hx).2) hw hz
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using h

/-- A uniform Lipschitz estimate for differences of slopes; only C2 is used. -/
theorem JetControlled.slope_difference_lipschitz {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (i j : Fin n) {z w : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (hw : w ∈ Set.Icc (-1 : ℝ) 1) :
    |(deriv (g i) z - deriv (g j) z) - (deriv (g i) w - deriv (g j) w)| ≤
      19 * dist (q i) (q j) * |z - w| := by
  have hdi := differentiable_deriv_of_contDiff_two (hg i)
  have hdj := differentiable_deriv_of_contDiff_two (hg j)
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (hdi.sub hdj) x) (C := 19 * dist (q i) (q j)) (by
      intro x hx
      rw [deriv_sub (hdi x) (hdj x)]
      exact (deriv2_le_jetDistance (g i) (g j) x).trans (hjet i j x hx).2) hw hz
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using h

/-- On a fixed short interval, a pair is uniformly separated either in value,
in slope, or in curvature. This uses no modulus of continuity for the second
derivatives. -/
theorem JetControlled.local_alternative {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (i j : Fin n) {w : ℝ} (hw : w ∈ Set.Icc (-1 : ℝ) 1) :
    (∀ z ∈ Set.Icc (-1 : ℝ) 1, |z - w| ≤ 1 / 10000 →
      dist (q i) (q j) / 480 ≤ |g i z - g j z|) ∨
    (∀ z ∈ Set.Icc (-1 : ℝ) 1, |z - w| ≤ 1 / 10000 →
      dist (q i) (q j) / 480 ≤ |deriv (g i) z - deriv (g j) z|) ∨
    (∀ z ∈ Set.Icc (-1 : ℝ) 1, |z - w| ≤ 1 / 10000 →
      dist (q i) (q j) / 60 ≤ |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) := by
  have hd := dist_nonneg (x := q i) (y := q j)
  have hval : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |z - w| ≤ 1 / 10000 →
      |(g i z - g j z) - (g i w - g j w)| ≤ 19 * dist (q i) (q j) / 10000 := by
    intro z hz hzw
    exact (hjet.value_difference_lipschitz hg i j hz hw).trans (by nlinarith)
  have hslope : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |z - w| ≤ 1 / 10000 →
      |(deriv (g i) z - deriv (g j) z) - (deriv (g i) w - deriv (g j) w)| ≤
        19 * dist (q i) (q j) / 10000 := by
    intro z hz hzw
    exact (hjet.slope_difference_lipschitz hg i j hz hw).trans (by nlinarith)
  by_cases ha : dist (q i) (q j) / 240 ≤ |g i w - g j w|
  · left
    intro z hz hzw
    have h := hval z hz hzw
    have hb := abs_sub_abs_le_abs_sub (g i w - g j w) (g i z - g j z)
    rw [abs_sub_comm (g i w - g j w)] at hb
    linarith
  by_cases hb : dist (q i) (q j) / 240 ≤ |deriv (g i) w - deriv (g j) w|
  · right; left
    intro z hz hzw
    have h := hslope z hz hzw
    have hc := abs_sub_abs_le_abs_sub (deriv (g i) w - deriv (g j) w)
      (deriv (g i) z - deriv (g j) z)
    rw [abs_sub_comm (deriv (g i) w - deriv (g j) w)] at hc
    linarith
  · right; right
    intro z hz hzw
    apply hjet.curvature_separation i j hz
    have hva := hval z hz hzw
    have hsa := hslope z hz hzw
    have hvb := abs_sub_abs_le_abs_sub (g i z - g j z) (g i w - g j w)
    have hsb := abs_sub_abs_le_abs_sub (deriv (g i) z - deriv (g j) z)
      (deriv (g i) w - deriv (g j) w)
    push Not at ha hb
    linarith

end WangZahlLot.Obl.wz_jet_close_pair_moment
