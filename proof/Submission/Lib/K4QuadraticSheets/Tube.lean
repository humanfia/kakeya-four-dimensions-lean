import Mathlib
import Submission.Lib.K4QuadraticSheets.QuadTest
import Submission.Lib.K4QuadraticSheets.Branch
import Submission.Lib.K4QuadraticSheets.Slit

/-!
# Simple sheets on tubes around broken segments

Restricted to a complex line, the discriminant of a quadratic test is a polynomial of degree at
most two in the line parameter.  When its roots avoid a segment and the discriminant moves little
across a thin tube around the segment, a rotated principal square root is holomorphic on the whole
tube.  Two such square roots on the tubes of the two pieces of a broken segment agree up to sign
on their convex overlap, so they glue.  The root branch built from the glued square root is then a
simple holomorphic sheet on the tube used by the continuation input.
-/

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial Polynomial

section Line

variable {σ : Type*}

/-- The affine line `s ↦ v + s w` in coordinates, as polynomials in `s`. -/
noncomputable def linePoly (v w : σ → ℂ) (i : σ) : Polynomial ℂ :=
  Polynomial.C (v i) + Polynomial.X * Polynomial.C (w i)

/-- A polynomial restricted to the line `s ↦ v + s w`. -/
noncomputable def lineRestr (Q : MvPolynomial σ ℂ) (v w : σ → ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (linePoly v w) Q

theorem eval_lineRestr (Q : MvPolynomial σ ℂ) (v w : σ → ℂ) (s : ℂ) :
    (lineRestr Q v w).eval s = MvPolynomial.eval (fun i => v i + s * w i) Q := by
  rw [lineRestr, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  simp only [MvPolynomial.eval]
  congr 1
  · ext r
    simp
  · ext i
    simp only [linePoly, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Function.comp_apply]

theorem natDegree_lineRestr_le (Q : MvPolynomial σ ℂ) (v w : σ → ℂ) :
    (lineRestr Q v w).natDegree ≤ Q.totalDegree := by
  classical
  rw [lineRestr]
  conv_lhs => rw [Q.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have hQ : ∀ i, (linePoly v w i).natDegree ≤ 1 := by
    intro i
    rw [linePoly]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · apply (Polynomial.natDegree_mul_le).trans
      simp
  calc
    (m.prod fun i e => linePoly v w i ^ e).natDegree ≤
        m.sum (fun i e => (linePoly v w i ^ e).natDegree) := Polynomial.natDegree_prod_le _ _
    _ ≤ m.sum (fun _ e => e) := by
        apply Finset.sum_le_sum
        intro i _
        apply (Polynomial.natDegree_pow_le).trans
        calc m i * (linePoly v w i).natDegree ≤ m i * 1 := Nat.mul_le_mul_left _ (hQ i)
          _ = m i := mul_one _
    _ ≤ Q.totalDegree := le_totalDegree hm

end Line

section DiscLine

variable {n : ℕ}

/-- The discriminant of a test along the complex line `s ↦ v + s w`, as a polynomial in `s`. -/
noncomputable def discLine (P : MvPolynomial (Fin (n + 1)) ℂ) (v w : Fin n → ℂ) :
    Polynomial ℂ :=
  lineRestr (pderiv (Fin.last n) P) (Fin.snoc v 0) (Fin.snoc w 0) ^ 2 -
    Polynomial.C (2 * qc P) * lineRestr P (Fin.snoc v 0) (Fin.snoc w 0)

theorem snoc_line (v w : Fin n → ℂ) (s : ℂ) :
    (fun i => (Fin.snoc v 0 : Fin (n + 1) → ℂ) i + s * (Fin.snoc w 0 : Fin (n + 1) → ℂ) i) =
      (Fin.snoc (fun j => v j + s * w j) 0 : Fin (n + 1) → ℂ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

theorem eval_discLine (P : MvPolynomial (Fin (n + 1)) ℂ) (v w : Fin n → ℂ) (s : ℂ) :
    (discLine P v w).eval s = qdisc P (fun j => v j + s * w j) := by
  rw [discLine, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_C, eval_lineRestr, eval_lineRestr, snoc_line, qdisc, qb, qg]

theorem natDegree_discLine_le {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    (v w : Fin n → ℂ) : (discLine P v w).natDegree ≤ 2 := by
  have h1 : (pderiv (Fin.last n) P).totalDegree ≤ 1 := totalDegree_pderiv_le' P _ hP
  rw [discLine]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_pow_le).trans
    have := (natDegree_lineRestr_le (pderiv (Fin.last n) P) (Fin.snoc v 0) (Fin.snoc w 0)).trans
      h1
    omega
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    exact (natDegree_lineRestr_le P _ _).trans hP

end DiscLine

section SegmentTube

variable {n : ℕ}

local notation "E" => EuclideanSpace ℂ (Fin n)

/-- The point `a + s (b - a)` of a complex line, in coordinates. -/
theorem coord_line (a b : E) (s : ℝ) (j : Fin n) :
    (a + (s : ℝ) • (b - a)) j = a j + (s : ℂ) * (b j - a j) := by
  simp [Complex.real_smul]

/-- **Square root on a segment tube.**  If the roots of the discriminant along the line through
`a` and `b` stay `ρ`-far from the parameter segment `[0, 1]`, and the discriminant moves little
relative to its size across the `r`-tube, then it has a holomorphic square root on the tube. -/
theorem exists_sqrt_on_segment_tube {P : MvPolynomial (Fin (n + 1)) ℂ} (a b : E) {ρ r : ℝ}
    (hρ : 0 < ρ) (hq : discLine P (fun j => a j) (fun j => b j - a j) ≠ 0)
    (hfar : ∀ x ∈ (discLine P (fun j => a j) (fun j => b j - a j)).roots,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ρ ≤ ‖(s : ℂ) - x‖)
    (hdeg : (discLine P (fun j => a j) (fun j => b j - a j)).natDegree ≤ 2)
    (hpert : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : E, dist z (a + s • (b - a)) < r →
      ‖qdisc P (fun j => z j) - qdisc P (fun j => (a + s • (b - a)) j)‖ *
          (2 * (1 + 1 / ρ) ^ 2) < ‖qdisc P (fun j => (a + s • (b - a)) j)‖) :
    ∃ S : E → ℂ, AnalyticOnNhd ℂ S (Metric.thickening r (segment ℝ a b)) ∧
      ∀ z ∈ Metric.thickening r (segment ℝ a b),
        S z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0 := by
  obtain ⟨lam, hlam0, hslit⟩ := exists_slit_rotation _ hq hdeg hρ hfar
  set μ : ℂ := lam ^ (1 / 2 : ℂ) with hμ
  have hμ2 : μ ^ 2 = lam := by
    have := Complex.cpow_nat_inv_pow lam (n := 2) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    rw [hμ, one_div]
    exact this
  -- every point of the tube is close to a point of the segment
  have hmem : ∀ z ∈ Metric.thickening r (segment ℝ a b),
      qdisc P (fun j => z j) / lam ∈ Complex.slitPlane := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := Metric.mem_thickening_iff.mp hz
    rw [segment_eq_image'] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    apply hslit s hs
    have hval : (discLine P (fun j => a j) (fun j => b j - a j)).eval (s : ℂ) =
        qdisc P (fun j => (a + s • (b - a)) j) := by
      rw [eval_discLine]
      simp only [coord_line]
    rw [hval]
    exact hpert s hs z hzy
  refine ⟨fun z => rotSqrt lam μ (qdisc P (fun j => z j)), ?_, ?_⟩
  · exact analyticOnNhd_rotSqrt (fun z _ => analyticAt_qdisc P z) hmem
  · intro z hz
    refine ⟨rotSqrt_sq hlam0 hμ2 _, ?_⟩
    intro h0
    have := hmem z hz
    rw [h0, zero_div] at this
    exact Complex.slitPlane_ne_zero this rfl

end SegmentTube

section Glue

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

omit [NormedSpace ℂ X] in
/-- Two holomorphic square roots of a nonvanishing function agree up to one global sign on a
preconnected overlap. -/
theorem sqrt_sign_constant {d S₁ S₂ : X → ℂ} {s : Set X} (hs : IsPreconnected s)
    (h₁ : ContinuousOn S₁ s) (h₂ : ContinuousOn S₂ s) (hS₁ : ∀ z ∈ s, S₁ z ^ 2 = d z)
    (hS₂ : ∀ z ∈ s, S₂ z ^ 2 = d z) (hd : ∀ z ∈ s, d z ≠ 0) {b : X} (hb : b ∈ s)
    (hbeq : S₁ b = S₂ b) : ∀ z ∈ s, S₁ z = S₂ z := by
  have hsq : ∀ z ∈ s, S₁ z = S₂ z ∨ S₁ z = -S₂ z := by
    intro z hz
    have : (S₁ z - S₂ z) * (S₁ z + S₂ z) = 0 := by
      have := (hS₁ z hz).trans (hS₂ z hz).symm
      linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hne : ∀ z ∈ s, S₂ z ≠ 0 := by
    intro z hz h0
    apply hd z hz
    rw [← hS₂ z hz, h0]
    ring
  -- the two sign sets are relatively open
  let u : Set X := {z | S₁ z + S₂ z ≠ 0}
  let v : Set X := {z | S₁ z - S₂ z ≠ 0}
  have hcont_add : ContinuousOn (fun z => S₁ z + S₂ z) s := h₁.add h₂
  have hcont_sub : ContinuousOn (fun z => S₁ z - S₂ z) s := h₁.sub h₂
  obtain ⟨u', hu'o, hu'⟩ := (continuousOn_iff'.mp hcont_add) {0}ᶜ isOpen_compl_singleton
  obtain ⟨v', hv'o, hv'⟩ := (continuousOn_iff'.mp hcont_sub) {0}ᶜ isOpen_compl_singleton
  have hcover : s ⊆ u' ∪ v' := by
    intro z hz
    rcases hsq z hz with h | h
    · left
      have : z ∈ (fun z => S₁ z + S₂ z) ⁻¹' {0}ᶜ ∩ s := by
        refine ⟨?_, hz⟩
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, h]
        intro h0
        apply hne z hz
        linear_combination h0 / 2
      rw [hu'] at this
      exact this.1
    · right
      have : z ∈ (fun z => S₁ z - S₂ z) ⁻¹' {0}ᶜ ∩ s := by
        refine ⟨?_, hz⟩
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, h]
        intro h0
        apply hne z hz
        linear_combination -h0 / 2
      rw [hv'] at this
      exact this.1
  have hdisj : ∀ z ∈ s, z ∈ u' → z ∈ v' → False := by
    intro z hz hzu hzv
    have h1 : z ∈ (fun z => S₁ z + S₂ z) ⁻¹' {0}ᶜ ∩ s := by rw [hu']; exact ⟨hzu, hz⟩
    have h2 : z ∈ (fun z => S₁ z - S₂ z) ⁻¹' {0}ᶜ ∩ s := by rw [hv']; exact ⟨hzv, hz⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] at h1 h2
    rcases hsq z hz with h | h
    · exact h2.1 (by rw [h]; ring)
    · exact h1.1 (by rw [h]; ring)
  have hbu : b ∈ u' := by
    have : b ∈ (fun z => S₁ z + S₂ z) ⁻¹' {0}ᶜ ∩ s := by
      refine ⟨?_, hb⟩
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, hbeq]
      intro h0
      apply hne b hb
      linear_combination h0 / 2
    rw [hu'] at this
    exact this.1
  have hsub : s ⊆ u' := by
    intro z hz
    by_contra hzu
    have hzv : z ∈ v' := (hcover hz).resolve_left hzu
    obtain ⟨y, hys, hyu, hyv⟩ := hs u' v' hu'o hv'o hcover ⟨b, hb, hbu⟩ ⟨z, hz, hzv⟩
    exact hdisj y hys hyu hyv
  intro z hz
  rcases hsq z hz with h | h
  · exact h
  · exfalso
    have hzu : z ∈ u' := hsub hz
    have h1 : z ∈ (fun z => S₁ z + S₂ z) ⁻¹' {0}ᶜ ∩ s := by rw [hu']; exact ⟨hzu, hz⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] at h1
    exact h1.1 (by rw [h]; ring)

/-- **Gluing square roots.**  Holomorphic square roots of a nonvanishing function on two open
sets with preconnected overlap glue to one on their union. -/
theorem glue_sqrt {d S₁ S₂ : X → ℂ} {U₁ U₂ : Set X} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hpre : IsPreconnected (U₁ ∩ U₂)) {b : X} (hb : b ∈ U₁ ∩ U₂)
    (hS₁d : AnalyticOnNhd ℂ S₁ U₁) (hS₂d : AnalyticOnNhd ℂ S₂ U₂)
    (hS₁ : ∀ z ∈ U₁, S₁ z ^ 2 = d z) (hS₂ : ∀ z ∈ U₂, S₂ z ^ 2 = d z)
    (hd : ∀ z ∈ U₁ ∪ U₂, d z ≠ 0) :
    ∃ S : X → ℂ, AnalyticOnNhd ℂ S (U₁ ∪ U₂) ∧ ∀ z ∈ U₁ ∪ U₂, S z ^ 2 = d z := by
  classical
  -- fix the sign of the second root at `b`
  have hS₂b : S₂ b ≠ 0 := by
    intro h0
    apply hd b (Or.inl hb.1)
    rw [← hS₂ b hb.2, h0]
    ring
  have hsign : S₁ b = S₂ b ∨ S₁ b = -S₂ b := by
    have : (S₁ b - S₂ b) * (S₁ b + S₂ b) = 0 := by
      have := (hS₁ b hb.1).trans (hS₂ b hb.2).symm
      linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  obtain ⟨T₂, hT₂d, hT₂, hT₂b⟩ : ∃ T₂ : X → ℂ, AnalyticOnNhd ℂ T₂ U₂ ∧
      (∀ z ∈ U₂, T₂ z ^ 2 = d z) ∧ S₁ b = T₂ b := by
    rcases hsign with h | h
    · exact ⟨S₂, hS₂d, hS₂, h⟩
    · refine ⟨fun z => -S₂ z, hS₂d.neg, fun z hz => by rw [neg_sq]; exact hS₂ z hz, h⟩
  have hagree : ∀ z ∈ U₁ ∩ U₂, S₁ z = T₂ z :=
    sqrt_sign_constant hpre (hS₁d.continuousOn.mono Set.inter_subset_left)
      (hT₂d.continuousOn.mono Set.inter_subset_right)
      (fun z hz => hS₁ z hz.1) (fun z hz => hT₂ z hz.2)
      (fun z hz => hd z (Or.inl hz.1)) hb hT₂b
  refine ⟨fun z => if z ∈ U₁ then S₁ z else T₂ z, ?_, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · have heq : (fun z => if z ∈ U₁ then S₁ z else T₂ z) =ᶠ[nhds z] S₁ := by
        filter_upwards [hU₁.mem_nhds hz] with y hy
        simp [hy]
      exact (hS₁d z hz).congr heq.symm
    · have heq : (fun z => if z ∈ U₁ then S₁ z else T₂ z) =ᶠ[nhds z] T₂ := by
        filter_upwards [hU₂.mem_nhds hz] with y hy
        by_cases hy1 : y ∈ U₁
        · simp only [hy1, ite_true]
          exact hagree y ⟨hy1, hy⟩
        · simp [hy1]
      exact (hT₂d z hz).congr heq.symm
  · intro z hz
    by_cases hz1 : z ∈ U₁
    · simp only [hz1, ite_true]
      exact hS₁ z hz1
    · simp only [hz1, ite_false]
      rcases hz with hz | hz
      · exact absurd hz hz1
      · exact hT₂ z hz

end Glue

end Submission.Lib.K4QuadraticSheets
