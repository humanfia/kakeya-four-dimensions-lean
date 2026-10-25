import Submission.Obl.k4_sign_set_isolated_bound.AlgebraicCount
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.Wongkew

noncomputable section

namespace Submission.Obl.k4_sign_set_isolated_bound

open MvPolynomial Set Metric Filter
open scoped BigOperators Topology

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Polynomial evaluation in Euclidean coordinates. -/
def peval (p : MvPolynomial (Fin 3) ℝ) (x : Space) : ℝ :=
  MvPolynomial.eval (fun i => x i) p

lemma continuous_peval (p : MvPolynomial (Fin 3) ℝ) : Continuous (peval p) :=
  p.continuous_eval.comp (PiLp.continuous_ofLp 2 _)

/-- Fermat's rule in Euclidean coordinates. -/
lemma pderiv_eq_zero_of_localMin (p : MvPolynomial (Fin 3) ℝ) {x : Space}
    (hx : IsLocalMin (peval p) x) (i : Fin 3) : peval (pderiv i p) x = 0 := by
  let g : ℝ → Space := fun t => WithLp.toLp 2 (Function.update (fun j => x j) i t)
  have hg : Continuous g :=
    (PiLp.continuous_toLp 2 _).comp (continuous_const.update i continuous_id)
  have hgx : g (x i) = x := by simp [g, Function.update_eq_self]
  have hm : IsLocalMin (fun t => MvPolynomial.eval
      (Function.update (fun j => x j) i t) p) (x i) := by
    have := (hgx.symm ▸ hx).comp_continuous hg.continuousAt
    exact this
  have hd := WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod.Wongkew.ExtremumAux.hasDerivAt_eval_update
    p (fun j => x j) i (x i)
  simpa [peval, Function.update_eq_self] using hm.hasDerivAt_eq_zero hd

/-- A positive boundary gap keeps a local minimum inside a ball under a small perturbation. -/
lemma exists_localMin_perturb (f h : Space → ℝ) (hf : Continuous f) (hh : Continuous h)
    (hh0 : ∀ x, 0 ≤ h x) (a : Space) {r : ℝ} (hr : 0 < r)
    (ha : f a = 0) (hboundary : ∀ x ∈ sphere a r, 0 < f x) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ x ∈ ball a r, IsLocalMin (fun x => f x + δ * h x) x := by
  obtain ⟨b, hb, hbmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hf.continuousOn
  have hfb : 0 < f b := hboundary b hb
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_pos_mul_lt hfb (h a)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδlt
  apply (isCompact_closedBall a r).exists_isLocalMin_mem_open ball_subset_closedBall
    (hf.add (continuous_const.mul hh)).continuousOn (mem_closedBall_self hr.le) ?_ isOpen_ball
  intro z hz
  have hzsp : z ∈ sphere a r := by rwa [closedBall_sdiff_ball] at hz
  have hbgap : f b ≤ f z := hbmin hzsp
  have hδa : δ * h a < f b := by
    calc δ * h a ≤ δ₀ * h a := mul_le_mul_of_nonneg_right hδlt.le (hh0 a)
         _ = h a * δ₀ := mul_comm _ _
         _ < f b := hsmall
  have hδz : 0 ≤ δ * h z := mul_nonneg hδ.le (hh0 z)
  change f a + δ * h a < f z + δ * h z
  rw [ha]
  linarith

/-- The polynomial used to make the critical equations have pure highest powers. -/
def powerSum (d : ℕ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i, X i ^ (2 * d + 2)

lemma powerSum_nonneg (d : ℕ) (x : Space) : 0 ≤ peval (powerSum d) x := by
  simp only [peval, powerSum, map_sum, map_pow, eval_X]
  apply Finset.sum_nonneg
  intro i _
  rw [show 2 * d + 2 = (d + 1) * 2 by omega, pow_mul]
  exact sq_nonneg _

lemma pderiv_powerSum (d : ℕ) (i : Fin 3) :
    pderiv i (powerSum d) = C (2 * (d : ℝ) + 2) * X i ^ (2 * d + 1) := by
  classical
  simp [powerSum, pderiv_X, Pi.single_apply, Finset.sum_ite_eq',
    Nat.cast_add, Nat.cast_mul, mul_ite]
  have hc : (C (2 : ℝ) : MvPolynomial (Fin 3) ℝ) = 2 := by
    exact_mod_cast (map_natCast (C : ℝ →+* MvPolynomial (Fin 3) ℝ) 2)
  rw [hc]

/-- The local minima of a polynomial with a positive pure-power perturbation have bounded count. -/
lemma card_localMin_perturb {ι : Type*} [Fintype ι] (d : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.totalDegree ≤ 2 * d)
    {δ : ℝ} (hδ : 0 < δ) (v : ι → Space) (hv : Function.Injective v)
    (hmin : ∀ a, IsLocalMin (peval (p + C δ * powerSum d)) (v a)) :
    Fintype.card ι ≤ Module.finrank ℝ (MvPolynomial.restrictDegree (Fin 3) ℝ (2 * d + 1)) := by
  let q : Fin 3 → MvPolynomial (Fin 3) ℝ :=
    fun i => C (-(δ * (2 * (d : ℝ) + 2))⁻¹) * pderiv i p
  apply card_le_of_pure_power_relations (2 * d + 1) q ?_
    (fun a i => v a i) ?_ ?_
  · intro i
    have hd := WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod.Wongkew.CountAux.totalDegree_pderiv_le
      p i (D := 2 * d) (hp.trans (Nat.le_succ _))
    have hc := MvPolynomial.totalDegree_mul (C (-(δ * (2 * (d : ℝ) + 2))⁻¹)) (pderiv i p)
    simp only [totalDegree_C, zero_add] at hc
    exact lt_of_le_of_lt (hc.trans hd) (Nat.lt_succ_self _)
  · intro a b h
    apply hv
    exact PiLp.ext (congrFun h)
  · intro a i
    have hc := pderiv_eq_zero_of_localMin _ (hmin a) i
    simp only [map_add, pderiv_C_mul, pderiv_powerSum, peval, map_mul, eval_C, eval_X,
      map_pow] at hc
    have hn : δ * (2 * (d : ℝ) + 2) ≠ 0 := ne_of_gt (mul_pos hδ (by positivity))
    dsimp [q]
    simp only [map_mul, eval_C]
    field_simp
    nlinarith [hc]

/-- Isolated points of a polynomial zero set. -/
def isolatedZeros (p : MvPolynomial (Fin 3) ℝ) : Set Space :=
  {x | peval p x = 0 ∧ ∃ ε : ℝ, 0 < ε ∧
    ∀ z, peval p z = 0 → dist z x < ε → z = x}

/-- Every finite family of isolated zeros produces as many distinct perturbed minima. -/
theorem card_isolatedZeros {ι : Type*} [Fintype ι] (d : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.totalDegree ≤ 2 * d)
    (hp0 : ∀ x, 0 ≤ peval p x)
    (a : ι → Space) (hinj : Function.Injective a) (ha : ∀ i, a i ∈ isolatedZeros p) :
    Fintype.card ι ≤ Module.finrank ℝ (MvPolynomial.restrictDegree (Fin 3) ℝ (2 * d + 1)) := by
  classical
  choose ε hε hεiso using fun i => (ha i).2
  obtain ⟨s, hs, hsdist⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : {ij : ι × ι // ij.1 ≠ ij.2} => (0 : ℝ))
    (y := fun ij => dist (a ij.val.1) (a ij.val.2) / 3)
    (fun ij => div_pos (dist_pos.mpr (fun h => ij.property (hinj h))) (by norm_num))
  let r : ι → ℝ := fun i => min (ε i / 2) s
  have hr (i : ι) : 0 < r i := lt_min (half_pos (hε i)) hs
  have hre (i : ι) : r i < ε i :=
    (min_le_left _ _).trans_lt (half_lt_self (hε i))
  have hpos (i : ι) (x : Space) (hx : x ∈ sphere (a i) (r i)) : 0 < peval p x := by
    apply lt_of_le_of_ne (hp0 x)
    intro h
    have heq := hεiso i x h.symm ((mem_sphere.mp hx).trans_lt (hre i))
    subst x
    have := mem_sphere.mp hx
    rw [dist_self] at this
    exact (hr i).ne this
  have hpert (i : ι) := exists_localMin_perturb (peval p) (peval (powerSum d))
    (continuous_peval p) (continuous_peval _) (powerSum_nonneg d) (a i) (hr i)
    (ha i).1 (hpos i)
  choose δ₀ hδ₀ hδmin using hpert
  obtain ⟨δ, hδ, hδsmall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : ι => (0 : ℝ)) (y := δ₀) hδ₀
  choose v hvball hvmin using fun i => hδmin i δ hδ (by simpa using hδsmall i)
  have hvinj : Function.Injective v := by
    intro i j hv
    by_contra hij
    have hdist := hsdist ⟨(i, j), hij⟩
    have hi : dist (a i) (v i) < s := by
      rw [dist_comm]
      exact (mem_ball.mp (hvball i)).trans_le (min_le_right _ _)
    have hj : dist (v i) (a j) < s := by
      rw [hv]
      exact (mem_ball.mp (hvball j)).trans_le (min_le_right _ _)
    have ht := dist_triangle (a i) (v i) (a j)
    dsimp at hdist
    linarith
  apply card_localMin_perturb d p hp hδ v hvinj
  intro i
  change IsLocalMin (fun x => peval (p + C δ * powerSum d) x) (v i)
  simpa only [peval, map_add, map_mul, eval_C] using hvmin i

/-- A nonnegative polynomial has uniformly finitely many isolated real zeros. -/
theorem isolatedZeros_bound (d : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.totalDegree ≤ 2 * d) (hp0 : ∀ x, 0 ≤ peval p x) :
    (isolatedZeros p).Finite ∧ (isolatedZeros p).ncard ≤
      Module.finrank ℝ (MvPolynomial.restrictDegree (Fin 3) ℝ (2 * d + 1)) := by
  have hsub (s : Set Space) (hs : s ⊆ isolatedZeros p) (hsf : s.Finite) :
      s.ncard ≤ Module.finrank ℝ (MvPolynomial.restrictDegree (Fin 3) ℝ (2 * d + 1)) := by
    let := hsf.fintype
    simpa only [Set.fintypeCard_eq_ncard] using
      card_isolatedZeros d p hp hp0 (fun x : s => (x : Space)) Subtype.val_injective
        (fun x => hs x.property)
  have hfin : (isolatedZeros p).Finite := by
    by_contra hinf
    obtain ⟨s, hs, hsf, hscard⟩ := Set.Infinite.exists_subset_ncard_eq hinf
      (Module.finrank ℝ (MvPolynomial.restrictDegree (Fin 3) ℝ (2 * d + 1)) + 1)
    have := hsub s hs hsf
    omega
  exact ⟨hfin, hsub _ Subset.rfl hfin⟩

end Submission.Obl.k4_sign_set_isolated_bound
