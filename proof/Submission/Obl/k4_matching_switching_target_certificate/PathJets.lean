-- Adapted from this LOT tree, o040, session x0118, Submission/Obl/k4_matching_refinement_exponent/PathJets.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Jets

/-!
# Jets of an alternating path with constant controls

An alternating path follows arm `ψ p` with an (approximately) constant top
derivative `u p` from the switch time `τ p` to the next switch time `τ (p + 1)`.
The exact constant-control path is the polynomial `pathJet m c u τ L 0`; its
`j`-th derivative is `pathJet m c u τ L j`. We prove that the jets of the actual
last arm differ from those of the exact path by the accumulated control and
switching errors. Switch times need not be ordered.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- The `j`-th derivative of the exact constant-control path with initial jet `c` at
time `τ 0`, first control `u 0`, and control changes `u (q + 1) - u q` at the
switch times `τ (q + 1)`, `q < L`. -/
noncomputable def pathJet (m : ℕ) (c u τ : ℕ → ℝ) (L j : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m - j), c (j + i) * (x - τ 0) ^ i / (i.factorial : ℝ)
    + u 0 * ((x - τ 0) ^ (m - j) / ((m - j).factorial : ℝ))
    + ∑ q ∈ Finset.range L,
        (u (q + 1) - u q) * ((x - τ (q + 1)) ^ (m - j) / ((m - j).factorial : ℝ))

lemma hasDerivAt_pow_div_factorial (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => (x - a) ^ (n + 1) / ((n + 1).factorial : ℝ))
      ((x - a) ^ n / (n.factorial : ℝ)) x := by
  have h1 : HasDerivAt (fun x => (x - a) ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * (x - a) ^ n) x := by
    have := (hasDerivAt_pow (n + 1) (x - a)).comp x ((hasDerivAt_id x).sub_const a)
    simp only [Function.comp_def, id] at this
    convert this using 1
    push_cast
    ring
  have h2 := h1.div_const ((n + 1).factorial : ℝ)
  refine h2.congr_deriv ?_
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

lemma hasDerivAt_taylorSum (a : ℕ → ℝ) (y : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => ∑ i ∈ Finset.range (k + 1), a i * (x - y) ^ i / (i.factorial : ℝ))
      (∑ i ∈ Finset.range k, a (i + 1) * (x - y) ^ i / (i.factorial : ℝ)) x := by
  have hfun : (fun x => ∑ i ∈ Finset.range (k + 1), a i * (x - y) ^ i / (i.factorial : ℝ)) =
      fun x => (∑ i ∈ Finset.range k,
        a (i + 1) * ((x - y) ^ (i + 1) / ((i + 1).factorial : ℝ))) + a 0 := by
    funext x
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfun]
  refine HasDerivAt.add_const (a 0) ?_
  have := HasDerivAt.fun_sum (u := Finset.range k)
    (A := fun i x => a (i + 1) * ((x - y) ^ (i + 1) / ((i + 1).factorial : ℝ)))
    (A' := fun i => a (i + 1) * ((x - y) ^ i / (i.factorial : ℝ))) (x := x)
    (fun i _ => (hasDerivAt_pow_div_factorial y i x).const_mul (a (i + 1)))
  convert this using 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma hasDerivAt_pathJet (m : ℕ) (c u τ : ℕ → ℝ) (L j : ℕ) (hj : j < m) (x : ℝ) :
    HasDerivAt (pathJet m c u τ L j) (pathJet m c u τ L (j + 1) x) x := by
  obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
  have hk' : m - (j + 1) = k := by omega
  have hfun : pathJet m c u τ L j = fun x =>
      (∑ i ∈ Finset.range (k + 1), c (j + i) * (x - τ 0) ^ i / (i.factorial : ℝ))
      + u 0 * ((x - τ 0) ^ (k + 1) / ((k + 1).factorial : ℝ))
      + ∑ q ∈ Finset.range L,
        (u (q + 1) - u q) * ((x - τ (q + 1)) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
    funext x
    simp only [pathJet, hk]
  rw [hfun]
  have h1 := hasDerivAt_taylorSum (fun i => c (j + i)) (τ 0) k x
  have h2 := (hasDerivAt_pow_div_factorial (τ 0) k x).const_mul (u 0)
  have h3 := HasDerivAt.fun_sum (u := Finset.range L)
    (A := fun q x => (u (q + 1) - u q) * ((x - τ (q + 1)) ^ (k + 1) / ((k + 1).factorial : ℝ)))
    (A' := fun q => (u (q + 1) - u q) * ((x - τ (q + 1)) ^ k / (k.factorial : ℝ))) (x := x)
    (fun q _ => (hasDerivAt_pow_div_factorial (τ (q + 1)) k x).const_mul (u (q + 1) - u q))
  convert (h1.add h2).add h3 using 1
  simp only [pathJet, hk']
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show j + (i + 1) = j + 1 + i by ring]

lemma deriv_pathJet (m : ℕ) (c u τ : ℕ → ℝ) (L j : ℕ) (hj : j < m) :
    deriv (pathJet m c u τ L j) = pathJet m c u τ L (j + 1) :=
  funext fun x => (hasDerivAt_pathJet m c u τ L j hj x).deriv

lemma iteratedDeriv_pathJet (m : ℕ) (c u τ : ℕ → ℝ) (L : ℕ) {j : ℕ} (hj : j ≤ m) :
    iteratedDeriv j (pathJet m c u τ L 0) = pathJet m c u τ L j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih (by omega), deriv_pathJet m c u τ L j (by omega)]

lemma pathJet_top (m : ℕ) (c u τ : ℕ → ℝ) (L : ℕ) (x : ℝ) :
    pathJet m c u τ L m x = u L := by
  simp only [pathJet, Nat.sub_self, Finset.range_zero, Finset.sum_empty, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, mul_one, zero_add]
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ← add_assoc, ih]; ring

lemma contDiff_pathJet (m : ℕ) (c u τ : ℕ → ℝ) (L j : ℕ) :
    ContDiff ℝ ⊤ (pathJet m c u τ L j) := by
  unfold pathJet
  fun_prop

lemma pathJet_start (m : ℕ) (c u τ : ℕ → ℝ) {j : ℕ} (hj : j < m) :
    pathJet m c u τ 0 j (τ 0) = c j := by
  obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
  simp only [pathJet, hk, sub_self, Finset.range_zero, Finset.sum_empty, add_zero]
  rw [Finset.sum_range_succ']
  simp

lemma pathJet_switch (m : ℕ) (c u τ : ℕ → ℝ) (L : ℕ) {j : ℕ} (hj : j < m) :
    pathJet m c u τ (L + 1) j (τ (L + 1)) = pathJet m c u τ L j (τ (L + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
  simp only [pathJet, hk, Finset.sum_range_succ, sub_self]
  simp

/-- The exact constant-control path is its own Taylor expansion with control `u L`. -/
lemma pathJet_taylor (m : ℕ) (c u τ : ℕ → ℝ) (L : ℕ) {j : ℕ} (hj : j < m) (x y : ℝ) :
    pathJet m c u τ L j x = ∑ i ∈ Finset.range (m - j),
        pathJet m c u τ L (j + i) y * (x - y) ^ i / (i.factorial : ℝ)
      + u L * (x - y) ^ (m - j) / ((m - j).factorial : ℝ) := by
  have hP : ContDiffOn ℝ (m : WithTop ℕ∞) (pathJet m c u τ L 0) univ :=
    ((contDiff_pathJet m c u τ L 0).of_le le_top).contDiffOn
  obtain ⟨ξ, -, heq⟩ := taylor_iteratedDeriv_lagrange isOpen_univ hP
    (subset_univ (uIcc y x)) hj
  rw [iteratedDeriv_pathJet m c u τ L hj.le, iteratedDeriv_pathJet m c u τ L le_rfl,
    pathJet_top] at heq
  have hsum : ∑ i ∈ Finset.range (m - j),
      iteratedDeriv (j + i) (pathJet m c u τ L 0) y * (x - y) ^ i / (i.factorial : ℝ) =
      ∑ i ∈ Finset.range (m - j),
        pathJet m c u τ L (j + i) y * (x - y) ^ i / (i.factorial : ℝ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [iteratedDeriv_pathJet m c u τ L (by have := Finset.mem_range.mp hi; omega)]
  rw [hsum] at heq
  linarith

lemma sum_two_pow_div_factorial_le (k : ℕ) :
    ∑ i ∈ Finset.range k, (2 : ℝ) ^ i / (i.factorial : ℝ) ≤ 8 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 2) (by norm_num) k
  have h2 : Real.exp 2 ≤ 8 := by
    have he := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith [Real.exp_pos 1]
  exact h1.trans h2

lemma abs_sub_le_two {lo hi x y : ℝ} (hlh : hi - lo ≤ 2) (hx : x ∈ Icc lo hi)
    (hy : y ∈ Icc lo hi) : |x - y| ≤ 2 := by
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- One traversal transports a bound on the low-jet defect of an arm against an exact
constant-control path: the Taylor shift on `[-1, 1]` multiplies it by at most `8`, and
the control error adds at most `2^m e`. -/
lemma defect_transport {m : ℕ} {V : Set ℝ} {lo hi : ℝ} (hV : IsOpen V) (hIV : Icc lo hi ⊆ V)
    (hlh : hi - lo ≤ 2)
    {ψ P : ℕ → ℝ → ℝ} (hψ : ContDiffOn ℝ m (ψ 0) V) {u e M : ℝ} (hM : 0 ≤ M)
    (hctrl : ∀ x ∈ Icc lo hi, |iteratedDeriv m (ψ 0) x - u| ≤ e)
    (hP : ∀ j, j < m → ∀ x y : ℝ, P j x = ∑ i ∈ Finset.range (m - j),
        P (j + i) y * (x - y) ^ i / (i.factorial : ℝ)
      + u * (x - y) ^ (m - j) / ((m - j).factorial : ℝ))
    {x y : ℝ} (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi)
    (hdef : ∀ j, j < m → |iteratedDeriv j (ψ 0) y - P j y| ≤ M)
    {j : ℕ} (hj : j < m) :
    |iteratedDeriv j (ψ 0) x - P j x| ≤ 8 * M + 2 ^ m * e := by
  have he : 0 ≤ e := (abs_nonneg _).trans (hctrl x hx)
  have hseg : uIcc y x ⊆ V := (uIcc_subset_Icc hy hx).trans hIV
  have hT := taylor_iteratedDeriv_control hV hψ hseg
    (fun z hz => hctrl z (uIcc_subset_Icc hy hx hz)) hj
  rw [hP j hj x y]
  have hxy : |x - y| ≤ 2 := abs_sub_le_two hlh hx hy
  set R := iteratedDeriv j (ψ 0) x - ∑ i ∈ Finset.range (m - j),
      iteratedDeriv (j + i) (ψ 0) y * (x - y) ^ i / (i.factorial : ℝ)
      - u * (x - y) ^ (m - j) / ((m - j).factorial : ℝ) with hR
  have hsplit : iteratedDeriv j (ψ 0) x - (∑ i ∈ Finset.range (m - j),
        P (j + i) y * (x - y) ^ i / (i.factorial : ℝ)
      + u * (x - y) ^ (m - j) / ((m - j).factorial : ℝ)) =
      ∑ i ∈ Finset.range (m - j), (iteratedDeriv (j + i) (ψ 0) y - P (j + i) y) *
        (x - y) ^ i / (i.factorial : ℝ) + R := by
    have hdist : ∑ i ∈ Finset.range (m - j), (iteratedDeriv (j + i) (ψ 0) y - P (j + i) y) *
        (x - y) ^ i / (i.factorial : ℝ) =
        ∑ i ∈ Finset.range (m - j), iteratedDeriv (j + i) (ψ 0) y * (x - y) ^ i / (i.factorial : ℝ)
        - ∑ i ∈ Finset.range (m - j), P (j + i) y * (x - y) ^ i / (i.factorial : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hdist, hR]
    ring
  rw [hsplit]
  have hsum : |∑ i ∈ Finset.range (m - j), (iteratedDeriv (j + i) (ψ 0) y - P (j + i) y) *
        (x - y) ^ i / (i.factorial : ℝ)| ≤ 8 * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range (m - j), |(iteratedDeriv (j + i) (ψ 0) y - P (j + i) y) *
          (x - y) ^ i / (i.factorial : ℝ)|
        ≤ ∑ i ∈ Finset.range (m - j), M * ((2 : ℝ) ^ i / (i.factorial : ℝ)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_div, abs_mul, abs_pow, Nat.abs_cast, mul_div_assoc]
          have hi' : j + i < m := by have := Finset.mem_range.mp hi; omega
          gcongr
          · exact hdef (j + i) hi'
      _ = M * ∑ i ∈ Finset.range (m - j), (2 : ℝ) ^ i / (i.factorial : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ M * 8 := by gcongr; exact sum_two_pow_div_factorial_le _
      _ = 8 * M := by ring
  have hrem : |R| ≤ 2 ^ m * e := by
    refine hT.trans ?_
    have hfac : (1 : ℝ) ≤ ((m - j).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpow : |x - y| ^ (m - j) ≤ 2 ^ m :=
      (pow_le_pow_left₀ (abs_nonneg _) hxy _).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le m j))
    calc e * |x - y| ^ (m - j) / ((m - j).factorial : ℝ) ≤ e * |x - y| ^ (m - j) :=
          div_le_self (by positivity) hfac
      _ ≤ e * 2 ^ m := by gcongr
      _ = 2 ^ m * e := by ring
  exact (abs_add_le _ _).trans (add_le_add hsum hrem)

/-- **Alternating path estimate.** Arm `ψ p` is followed from `τ p` to `τ (p + 1)`, all
times in an interval `[lo, hi]` of length at most `2`. Its top derivative stays within `e`
of the control `u p`, and at the switch time `τ (p + 1)` the low jets of `ψ (p + 1)` and
`ψ p` differ by at most `δ`. Then the low jets of the arm `ψ L` are those of the exact
constant-control path, up to `9^(L+1) (8 δ + 2^m e)`, at every time of `[lo, hi]`.
Times need not be ordered. Only the arms `p ≤ L` are used. -/
theorem path_jet_error {m : ℕ} {V : Set ℝ} {lo hi : ℝ} (hV : IsOpen V)
    (hIV : Icc lo hi ⊆ V) (hlh : hi - lo ≤ 2)
    (ψ : ℕ → ℝ → ℝ) (u τ : ℕ → ℝ) {e δ : ℝ} (he : 0 ≤ e) (hδ : 0 ≤ δ) (L : ℕ)
    (hψ : ∀ p, p ≤ L → ContDiffOn ℝ m (ψ p) V)
    (hctrl : ∀ p, p ≤ L → ∀ x ∈ Icc lo hi, |iteratedDeriv m (ψ p) x - u p| ≤ e)
    (hτ : ∀ p, p ≤ L → τ p ∈ Icc lo hi)
    (hjump : ∀ p, p < L → ∀ j, j < m →
      |iteratedDeriv j (ψ (p + 1)) (τ (p + 1)) - iteratedDeriv j (ψ p) (τ (p + 1))| ≤ δ)
    {x : ℝ} (hx : x ∈ Icc lo hi) {j : ℕ} (hj : j < m) :
    |iteratedDeriv j (ψ L) x - pathJet m (fun i => iteratedDeriv i (ψ 0) (τ 0)) u τ L j x|
      ≤ 9 ^ (L + 1) * (8 * δ + 2 ^ m * e) := by
  set c : ℕ → ℝ := fun i => iteratedDeriv i (ψ 0) (τ 0)
  set A := 8 * δ + 2 ^ m * e with hA
  have hA0 : 0 ≤ A := by positivity
  have htay : ∀ L, ∀ j, j < m → ∀ x y : ℝ, pathJet m c u τ L j x = ∑ i ∈ Finset.range (m - j),
      pathJet m c u τ L (j + i) y * (x - y) ^ i / (i.factorial : ℝ)
      + u L * (x - y) ^ (m - j) / ((m - j).factorial : ℝ) :=
    fun L j hj x y => pathJet_taylor m c u τ L hj x y
  suffices H : ∀ L', L' ≤ L → ∀ x ∈ Icc lo hi, ∀ j, j < m →
      |iteratedDeriv j (ψ L') x - pathJet m c u τ L' j x| ≤ 9 ^ (L' + 1) * A from
    H L le_rfl x hx j hj
  intro L' hL'
  induction L' with
  | zero =>
    intro x hx j hj
    have h := defect_transport (ψ := fun _ => ψ 0) (P := pathJet m c u τ 0) hV hIV hlh
      (hψ 0 (Nat.zero_le _)) le_rfl (hctrl 0 (Nat.zero_le _)) (htay 0) hx
      (hτ 0 (Nat.zero_le _)) (fun j hj => by simp [c, pathJet_start m c u τ hj]) hj
    calc _ ≤ 8 * 0 + 2 ^ m * e := h
      _ ≤ 9 ^ (0 + 1) * A := by
        have h2e : 0 ≤ 2 ^ m * e := mul_nonneg (pow_nonneg (by norm_num) m) he
        rw [hA, zero_add, pow_one]
        nlinarith
  | succ L' ih =>
    intro x hx j hj
    have ih' := ih (by omega)
    have hdef : ∀ j, j < m → |iteratedDeriv j (ψ (L' + 1)) (τ (L' + 1)) -
        pathJet m c u τ (L' + 1) j (τ (L' + 1))| ≤ δ + 9 ^ (L' + 1) * A := by
      intro j hj
      rw [pathJet_switch m c u τ L' hj]
      calc _ = |(iteratedDeriv j (ψ (L' + 1)) (τ (L' + 1)) - iteratedDeriv j (ψ L') (τ (L' + 1)))
              + (iteratedDeriv j (ψ L') (τ (L' + 1)) - pathJet m c u τ L' j (τ (L' + 1)))| := by
            ring_nf
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hjump L' (by omega) j hj)
            (ih' _ (hτ (L' + 1) hL') j hj))
    have h := defect_transport (ψ := fun _ => ψ (L' + 1)) (P := pathJet m c u τ (L' + 1)) hV
      hIV hlh (hψ (L' + 1) hL') (by positivity) (hctrl (L' + 1) hL') (htay (L' + 1)) hx
      (hτ (L' + 1) hL') hdef hj
    calc _ ≤ 8 * (δ + 9 ^ (L' + 1) * A) + 2 ^ m * e := h
      _ ≤ 9 ^ (L' + 1 + 1) * A := by
        have h9 : (1 : ℝ) ≤ 9 ^ (L' + 1) := one_le_pow₀ (by norm_num)
        rw [hA] at *
        nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) m, pow_succ (9 : ℝ) (L' + 1)]

/-- The endpoint polynomial of the frozen endpoint estimate (o039): final time and the
low jets, in reverse derivative order, contributed by the controls `U` from the start
time `s₀` and the internal switch times `x.2`. -/
noncomputable def endpointMap (m : ℕ) (U : Fin (m + 1) → ℝ) (s₀ : ℝ) :
    ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ) :=
  fun x => (x.1, fun j : Fin m => (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) +
    ∑ p : Fin m, (U p.succ - U p.castSucc) * (x.1 - x.2 p) ^ ((j : ℕ) + 1)) /
      (((j : ℕ) + 1).factorial : ℝ))

/-- The free evolution of an initial jet `c` at time `s₀`, in reverse derivative order. -/
noncomputable def freeJet (m : ℕ) (c : ℕ → ℝ) (s₀ : ℝ) (σ : ℝ) (j : Fin m) : ℝ :=
  ∑ i ∈ Finset.range ((j : ℕ) + 1), c (m - 1 - (j : ℕ) + i) * (σ - s₀) ^ i / (i.factorial : ℝ)

/-- The jets of the exact path after all `m` switches are the free evolution plus the
endpoint polynomial of the frozen endpoint estimate. -/
lemma pathJet_eq_endpointMap (m : ℕ) (c u τ : ℕ → ℝ) (σ : ℝ) (j : Fin m) :
    pathJet m c u τ m (m - 1 - (j : ℕ)) σ =
      freeJet m c (τ 0) σ j +
        (endpointMap m (fun p => u p) (τ 0) (σ, fun p => τ ((p : ℕ) + 1))).2 j := by
  have hj := j.isLt
  have hmj : m - (m - 1 - (j : ℕ)) = (j : ℕ) + 1 := by omega
  simp only [pathJet, freeJet, endpointMap, hmj]
  rw [add_assoc]
  congr 1
  rw [add_div, mul_div_assoc]
  congr 1
  rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range
    (fun q => (u (q + 1) - u q) * ((σ - τ (q + 1)) ^ ((j : ℕ) + 1) /
      (((j : ℕ) + 1).factorial : ℝ))) m]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Fin.val_succ, Fin.val_castSucc]
  ring

/-- **Endpoint of an alternating path.** With `m` switches, the low jets of the last arm
at the final time `σ = τ (m + 1)`, after subtracting the free evolution of the first
arm's initial jet, are within `9^(m+1) (8 δ + 2^m e)` of the frozen endpoint polynomial
evaluated at `(σ, (τ 1, ..., τ m))`. Coordinate `j` is the derivative of order
`m - 1 - j`. Only the arms `p ≤ m` and the times `p ≤ m + 1` are used. -/
theorem alternating_path_endpoint {m : ℕ} {V : Set ℝ} {lo hi : ℝ} (hV : IsOpen V)
    (hIV : Icc lo hi ⊆ V) (hlh : hi - lo ≤ 2)
    (ψ : ℕ → ℝ → ℝ) (u τ : ℕ → ℝ) {e δ : ℝ} (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hψ : ∀ p, p ≤ m → ContDiffOn ℝ m (ψ p) V)
    (hctrl : ∀ p, p ≤ m → ∀ x ∈ Icc lo hi, |iteratedDeriv m (ψ p) x - u p| ≤ e)
    (hτ : ∀ p, p ≤ m + 1 → τ p ∈ Icc lo hi)
    (hjump : ∀ p, p < m → ∀ j, j < m →
      |iteratedDeriv j (ψ (p + 1)) (τ (p + 1)) - iteratedDeriv j (ψ p) (τ (p + 1))| ≤ δ)
    (j : Fin m) :
    |(iteratedDeriv (m - 1 - (j : ℕ)) (ψ m) (τ (m + 1))
        - freeJet m (fun i => iteratedDeriv i (ψ 0) (τ 0)) (τ 0) (τ (m + 1)) j)
      - (endpointMap m (fun p => u p) (τ 0) (τ (m + 1), fun p => τ ((p : ℕ) + 1))).2 j|
      ≤ 9 ^ (m + 1) * (8 * δ + 2 ^ m * e) := by
  have h := path_jet_error hV hIV hlh ψ u τ he hδ m hψ hctrl
    (fun p hp => hτ p (by omega)) hjump (hτ (m + 1) le_rfl)
    (j := m - 1 - (j : ℕ)) (by have := j.isLt; omega)
  rw [pathJet_eq_endpointMap] at h
  calc _ = |iteratedDeriv (m - 1 - (j : ℕ)) (ψ m) (τ (m + 1)) -
        (freeJet m (fun i => iteratedDeriv i (ψ 0) (τ 0)) (τ 0) (τ (m + 1)) j +
          (endpointMap m (fun p => u p) (τ 0) (τ (m + 1), fun p => τ ((p : ℕ) + 1))).2 j)| := by
        ring_nf
    _ ≤ _ := h

end Submission.Obl.k4_matching_switching_target_certificate
