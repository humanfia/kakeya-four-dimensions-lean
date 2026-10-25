import Submission.Obl.k4_balanced_native_packet_transport.Definitions

/-!
Transport of the earlier window certificate through refinements of packets.
The common reference probabilities and their weights stay fixed.  All packet
splits are charged together by the original weighted incidence law.
-/
namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Set
noncomputable section

/-- Contracting an affine coordinate preserves an absolute window. -/
theorem affine_window_le {a q x y σ : ℝ} (hq : |q| ≤ 1) (hxy : |x - y| ≤ σ) :
    |(a + q * x) - (a + q * y)| ≤ σ := by
  calc
    |(a + q * x) - (a + q * y)| = |q| * |x - y| := by
      rw [show (a + q * x) - (a + q * y) = q * (x - y) by ring, abs_mul]
    _ ≤ 1 * |x - y| := mul_le_mul_of_nonneg_right hq (abs_nonneg _)
    _ ≤ σ := by simpa only [one_mul] using hxy

/-- A certificate survives splitting and contracting blocks whenever the new
weighted incidence laws are globally dominated by the old ones.  The target
signal agrees with the old native signal on the retained good set. -/
theorem WindowCertificate.transport
    {N χ d s m : ℝ} {C C' : ℕ}
    {R : Fin C → ENNReal} {μ : Fin C → Measure Inc}
    {b : Fin C → Traj → Fin 5 → ℝ}
    (hcert : WindowCertificate N χ d s m C R μ b)
    (parent : Fin C' → Fin C) (expand : Fin C' → Inc → Inc)
    (hexpand : ∀ i, Measurable (expand i))
    (R' : Fin C' → ENNReal) (μ' : Fin C' → Measure Inc)
    (b' : Fin C' → Traj → Fin 5 → ℝ)
    (F : Fin C' → Set Inc) (hF : ∀ i, MeasurableSet (F i))
    (hsupport : ∀ i, μ' i (F i)ᶜ = 0)
    (hpositive : ∀ i, 0 < R' i)
    (hdom : ∀ A : Fin C → Set Inc, (∀ a, MeasurableSet (A a)) →
      (∑ i, R' i * μ' i (expand i ⁻¹' A (parent i))) ≤
        ∑ a, R a * μ a (A a))
    (t₀ y₀ q : Fin C' → ℝ) (hq : ∀ i, |q i| ≤ 1)
    (hcoord : ∀ i p, p ∈ F i →
      (expand i p).2 = t₀ i + q i * p.2 ∧
      scalarY (b (parent i) (expand i p).1) (expand i p).2 =
        y₀ i + q i * scalarY (b' i p.1) p.2)
    (hsignal : ∀ i p, p ∈ F i →
      scalarX (b' i p.1) p.2 =
        scalarX (b (parent i) (expand i p).1) (expand i p).2) :
    WindowCertificate N χ d s m C' R' μ' b' := by
  classical
  obtain ⟨J, w, Λ, P, S, tag, A, z, hw, hN, href, hA, hcharge,
    hX, hcount, hclose⟩ := hcert
  let tag' := fun i => tag (parent i) ∘ expand i
  let z' := fun i e => z (parent i) e ∘ expand i
  let F' := fun i => F i ∩ expand i ⁻¹' A (parent i)
  have hnull (i : Fin C') : μ' i (expand i ⁻¹' (A (parent i))ᶜ) = 0 := by
    have h := hdom (fun a => (A a)ᶜ) (fun a => (hA a).2.2.1.compl)
    simp only [(hA _).2.2.2.1, mul_zero, Finset.sum_const_zero] at h
    have hi : R' i * μ' i (expand i ⁻¹' (A (parent i))ᶜ) = 0 :=
      le_antisymm ((Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans h)
        bot_le
    exact (mul_eq_zero.mp hi).resolve_left (hpositive i).ne'
  have hmem (i : Fin C') (p : Inc) (hp : p ∈ F' i) :
      expand i p ∈ A (parent i) := hp.2
  refine ⟨J, w, Λ, P, S, tag', F', z', hw, hN, href, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hpositive i, (hA (parent i)).2.1.comp (hexpand i),
      (hF i).inter ((hA (parent i)).2.2.1.preimage (hexpand i)), ?_,
      fun e => ((hA (parent i)).2.2.2.2 e).comp (hexpand i)⟩
    exact measure_mono_null (by simp only [F', compl_inter, preimage_compl]; rfl)
      (measure_union_null (hsupport i) (hnull i))
  · intro e
    apply Measure.le_iff.mpr
    intro U hU
    let B : Fin C → Set Inc := fun a =>
      {p | p ∈ A a ∧ tag a p = e ∧ z a e p ∈ U}
    have hB (a : Fin C) : MeasurableSet (B a) :=
      (hA a).2.2.1.inter (((hA a).2.1 (measurableSet_singleton e)).inter
        (hU.preimage ((hA a).2.2.2.2 e)))
    have hleft : (∑ i, R' i • Measure.map (z' i e)
        ((μ' i).restrict {p | p ∈ F' i ∧ tag' i p = e})) U ≤
        ∑ i, R' i * μ' i (expand i ⁻¹' B (parent i)) := by
      rw [Measure.finsetSum_apply]
      apply Finset.sum_le_sum
      intro i _
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply (((hA (parent i)).2.2.2.2 e).comp (hexpand i)) hU,
        Measure.restrict_apply
          (hU.preimage (((hA (parent i)).2.2.2.2 e).comp (hexpand i)))]
      apply mul_le_mul' le_rfl
      apply measure_mono
      intro p hp
      exact ⟨hmem i p hp.2.1, hp.2.2, hp.1⟩
    have hright : (∑ a, R a * μ a (B a)) =
        (∑ a, R a • Measure.map (z a e)
          ((μ a).restrict {p | p ∈ A a ∧ tag a p = e})) U := by
      rw [Measure.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply ((hA a).2.2.2.2 e) hU,
        Measure.restrict_apply (hU.preimage ((hA a).2.2.2.2 e))]
      congr 2
      ext p
      simp only [B, mem_ofPred_eq, mem_inter_iff, mem_preimage]
      tauto
    exact hleft.trans ((hdom B hB).trans (hright.le.trans (hcharge e U)))
  · intro i p hp
    exact (hsignal i p hp.1).trans (hX (parent i) (expand i p) (hmem i p hp))
  · intro i t y
    have hsub :
        (Finset.univ.filter (fun e => ∃ p ∈ F' i, |p.2 - t| ≤ N ^ (-m) ∧
          |scalarY (b' i p.1) p.2 - y| ≤ N ^ (-m) ∧ tag' i p = e)) ⊆
        (Finset.univ.filter (fun e => ∃ p ∈ A (parent i),
          |p.2 - (t₀ i + q i * t)| ≤ N ^ (-m) ∧
          |scalarY (b (parent i) p.1) p.2 - (y₀ i + q i * y)| ≤ N ^ (-m) ∧
          tag (parent i) p = e)) := by
      intro e he
      obtain ⟨_, p, hp, ht, hy, he⟩ := Finset.mem_filter.mp he
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, expand i p, hmem i p hp, ?_, ?_, he⟩
      · rw [(hcoord i p hp.1).1]
        exact affine_window_le (hq i) ht
      · rw [(hcoord i p hp.1).2]
        exact affine_window_le (hq i) hy
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (hcount (parent i) (t₀ i + q i * t) (y₀ i + q i * y))
  · intro i p hp p' hp' htag ht hy
    apply hclose (parent i) (expand i p) (hmem i p hp)
      (expand i p') (hmem i p' hp') htag
    · rw [(hcoord i p hp.1).1, (hcoord i p' hp'.1).1]
      exact affine_window_le (hq i) ht
    · rw [(hcoord i p hp.1).2, (hcoord i p' hp'.1).2]
      exact affine_window_le (hq i) hy

end
end Submission.Obl.k4_balanced_native_packet_transport
