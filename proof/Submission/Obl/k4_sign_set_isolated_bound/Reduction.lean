import Mathlib

/-!
# Reduction of `k4_sign_set_isolated_bound` to isolated zeros of sums of squares

Let `T = {s | (sign (p i s))ᵢ ∈ B}` and let `s` be an isolated point of `T`. Put
`Z = {i | p i s = 0}` and `f_Z = ∑_{i ∈ Z} (p i)²`. Near `s` every `p i` with `i ∉ Z` keeps its
sign, so a zero `z` of `f_Z` close to `s` has the sign vector of `s`, lies in `T`, and is `s`.
Hence `s` is an isolated zero of the nonnegative polynomial `f_Z`, of degree `≤ 2d`.

Given a uniform bound `M` for the isolated zeros of nonnegative polynomials of degree `≤ 2d`
(`IsoZeroBound`), sorting the isolated points of `T` by their vanishing set `Z` (one of `2 ^ m`)
bounds every finite set of them by `M * 2 ^ m`; so they are finitely many, at most `M * 2 ^ m`.
-/

namespace Submission.Obl.k4_sign_set_isolated_bound

open MvPolynomial

/-- `s` is an isolated zero of the polynomial `f` on `ℝ³`. -/
def IsIsolatedZero (f : MvPolynomial (Fin 3) ℝ) (s : EuclideanSpace ℝ (Fin 3)) : Prop :=
  MvPolynomial.eval (fun k => s k) f = 0 ∧ ∃ r : ℝ, 0 < r ∧
    ∀ z : EuclideanSpace ℝ (Fin 3), dist z s < r → MvPolynomial.eval (fun k => z k) f = 0 → z = s

/-- The analytic input: nonnegative polynomials of degree `≤ D` on `ℝ³` have uniformly
boundedly many isolated zeros. -/
def IsoZeroBound : Prop :=
  ∀ D : ℕ, ∃ M : ℕ, ∀ f : MvPolynomial (Fin 3) ℝ, f.totalDegree ≤ D →
    (∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ MvPolynomial.eval (fun k => x k) f) →
    ∀ S : Finset (EuclideanSpace ℝ (Fin 3)), (∀ s ∈ S, IsIsolatedZero f s) → S.card ≤ M

/-- The sum of the squares of the `p i`, `i ∈ Z`. -/
noncomputable def sqSum {m : ℕ} (p : Fin m → MvPolynomial (Fin 3) ℝ) (Z : Finset (Fin m)) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ i ∈ Z, p i ^ 2

lemma eval_sqSum {m : ℕ} (p : Fin m → MvPolynomial (Fin 3) ℝ) (Z : Finset (Fin m))
    (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (sqSum p Z) = ∑ i ∈ Z, MvPolynomial.eval x (p i) ^ 2 := by
  simp [sqSum, map_sum, map_pow]

lemma eval_sqSum_nonneg {m : ℕ} (p : Fin m → MvPolynomial (Fin 3) ℝ) (Z : Finset (Fin m))
    (x : Fin 3 → ℝ) : 0 ≤ MvPolynomial.eval x (sqSum p Z) := by
  rw [eval_sqSum]
  positivity

lemma totalDegree_sqSum_le {m d : ℕ} (p : Fin m → MvPolynomial (Fin 3) ℝ) (Z : Finset (Fin m))
    (hp : ∀ i, (p i).totalDegree ≤ d) : (sqSum p Z).totalDegree ≤ 2 * d := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hp i))

/-- The indices `i` with `p i s = 0`. -/
noncomputable def zeroIdx {m : ℕ} (p : Fin m → MvPolynomial (Fin 3) ℝ)
    (s : EuclideanSpace ℝ (Fin 3)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => MvPolynomial.eval (fun k => s k) (p i) = 0

lemma mem_zeroIdx {m : ℕ} (p : Fin m → MvPolynomial (Fin 3) ℝ) (s : EuclideanSpace ℝ (Fin 3))
    (i : Fin m) : i ∈ zeroIdx p s ↔ MvPolynomial.eval (fun k => s k) (p i) = 0 := by
  classical
  simp [zeroIdx]

lemma continuous_eval_euclid (q : MvPolynomial (Fin 3) ℝ) :
    Continuous fun z : EuclideanSpace ℝ (Fin 3) => MvPolynomial.eval (fun k => z k) q :=
  (MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)

/-- Near `s`, every `p i` that does not vanish at `s` keeps its sign. -/
lemma eventually_sign_eq {m : ℕ} (p : Fin m → MvPolynomial (Fin 3) ℝ)
    (s : EuclideanSpace ℝ (Fin 3)) :
    ∀ᶠ z in nhds s, ∀ i, MvPolynomial.eval (fun k => s k) (p i) ≠ 0 →
      SignType.sign (MvPolynomial.eval (fun k => z k) (p i)) =
        SignType.sign (MvPolynomial.eval (fun k => s k) (p i)) := by
  rw [Filter.eventually_all]
  intro i
  have hc := (continuous_eval_euclid (p i)).continuousAt (x := s)
  rcases lt_trichotomy (MvPolynomial.eval (fun k => s k) (p i)) 0 with hneg | h0 | hpos
  · filter_upwards [hc.eventually_lt continuousAt_const hneg] with z hz _
    rw [sign_neg hz, sign_neg hneg]
  · exact Filter.Eventually.of_forall fun _ h => absurd h0 h
  · filter_upwards [continuousAt_const.eventually_lt hc hpos] with z hz _
    rw [sign_pos hz, sign_pos hpos]

/-- An isolated point of a sign set is an isolated zero of the sum of the squares of the
polynomials vanishing at it. -/
theorem isIsolatedZero_sqSum {m : ℕ} (p : Fin m → MvPolynomial (Fin 3) ℝ)
    (B : Set (Fin m → SignType)) (s : EuclideanSpace ℝ (Fin 3))
    (hs : (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => s k) (p i))) ∈ B)
    (ε : ℝ) (hε : 0 < ε)
    (hiso : ∀ z : EuclideanSpace ℝ (Fin 3),
      (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => z k) (p i))) ∈ B →
        dist z s < ε → z = s) :
    IsIsolatedZero (sqSum p (zeroIdx p s)) s := by
  refine ⟨?_, ?_⟩
  · rw [eval_sqSum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [(mem_zeroIdx p s i).1 hi]
    ring
  · obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.1 (eventually_sign_eq p s)
    refine ⟨min ε r, lt_min hε hr, fun z hz hz0 => ?_⟩
    refine hiso z ?_ (lt_of_lt_of_le hz (min_le_left _ _))
    have hzZ : ∀ i ∈ zeroIdx p s, MvPolynomial.eval (fun k => z k) (p i) = 0 := by
      rw [eval_sqSum, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at hz0
      exact fun i hi => pow_eq_zero_iff two_ne_zero |>.1 (hz0 i hi)
    have hsign : (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => z k) (p i))) =
        fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => s k) (p i)) := by
      funext i
      by_cases h0 : MvPolynomial.eval (fun k => s k) (p i) = 0
      · rw [hzZ i ((mem_zeroIdx p s i).2 h0), h0]
      · exact hr' (lt_of_lt_of_le hz (min_le_right _ _)) i h0
    rw [hsign]
    exact hs

/-- A finite set of isolated points of a sign set has at most `M * 2 ^ m` points, if
nonnegative polynomials of degree `≤ 2 d` have at most `M` isolated zeros. -/
theorem card_le_of_isolated {m d M : ℕ}
    (hM : ∀ f : MvPolynomial (Fin 3) ℝ, f.totalDegree ≤ 2 * d →
      (∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ MvPolynomial.eval (fun k => x k) f) →
      ∀ S : Finset (EuclideanSpace ℝ (Fin 3)), (∀ s ∈ S, IsIsolatedZero f s) → S.card ≤ M)
    (p : Fin m → MvPolynomial (Fin 3) ℝ) (hp : ∀ i, (p i).totalDegree ≤ d)
    (B : Set (Fin m → SignType)) (S : Finset (EuclideanSpace ℝ (Fin 3)))
    (hS : ∀ s ∈ S, (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => s k) (p i))) ∈ B ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
        (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => z k) (p i))) ∈ B →
          dist z s < ε → z = s) :
    S.card ≤ M * 2 ^ m := by
  classical
  calc S.card ≤ M * (S.image (zeroIdx p)).card := by
        refine Finset.card_le_mul_card_image S M fun Z _ => ?_
        refine hM (sqSum p Z) (totalDegree_sqSum_le p Z hp)
          (fun x => eval_sqSum_nonneg p Z _) _ fun s hs => ?_
        rw [Finset.mem_filter] at hs
        rw [← hs.2]
        obtain ⟨hsB, ε, hε, hiso⟩ := hS s hs.1
        exact isIsolatedZero_sqSum p B s hsB ε hε hiso
    _ ≤ M * 2 ^ m := by
        refine Nat.mul_le_mul_left M ((Finset.card_le_univ _).trans ?_)
        simp [Fintype.card_finset]

/-- The frozen statement of `k4_sign_set_isolated_bound`, from the analytic input
`IsoZeroBound`. -/
theorem main_of_isoZeroBound (H : IsoZeroBound) :
    ∀ m d : ℕ, ∃ N : ℕ, 0 < N ∧ ∀ (p : Fin m → MvPolynomial (Fin 3) ℝ)
      (B : Set (Fin m → SignType)) (T : Set (EuclideanSpace ℝ (Fin 3))),
      (∀ i, (p i).totalDegree ≤ d) →
      T = {s : EuclideanSpace ℝ (Fin 3) |
        (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => s k) (p i))) ∈ B} →
      {s : EuclideanSpace ℝ (Fin 3) | s ∈ T ∧ ∃ ε : ℝ, 0 < ε ∧
          ∀ z ∈ T, dist z s < ε → z = s}.Finite ∧
        {s : EuclideanSpace ℝ (Fin 3) | s ∈ T ∧ ∃ ε : ℝ, 0 < ε ∧
          ∀ z ∈ T, dist z s < ε → z = s}.ncard ≤ N := by
  intro m d
  obtain ⟨M, hM⟩ := H (2 * d)
  refine ⟨M * 2 ^ m + 1, Nat.succ_pos _, ?_⟩
  intro p B T hp hT
  subst hT
  set I := {s : EuclideanSpace ℝ (Fin 3) |
    s ∈ {s : EuclideanSpace ℝ (Fin 3) |
      (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => s k) (p i))) ∈ B} ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ {s : EuclideanSpace ℝ (Fin 3) |
      (fun i => SignType.sign (MvPolynomial.eval (fun k : Fin 3 => s k) (p i))) ∈ B},
        dist z s < ε → z = s} with hI
  have key : ∀ S : Finset (EuclideanSpace ℝ (Fin 3)), (↑S : Set _) ⊆ I → S.card ≤ M * 2 ^ m :=
    fun S hS => card_le_of_isolated hM p hp B S fun s hs => hS hs
  have hfin : I.Finite := by
    by_contra hinf
    obtain ⟨S, hSI, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (M * 2 ^ m + 1)
    have := key S hSI
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card I hfin]
  exact (key hfin.toFinset (by simp)).trans (Nat.le_succ _)

end Submission.Obl.k4_sign_set_isolated_bound
