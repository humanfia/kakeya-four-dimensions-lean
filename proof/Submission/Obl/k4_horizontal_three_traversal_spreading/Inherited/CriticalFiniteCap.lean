-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/CriticalFiniteCap.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CriticalFiniteCap.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalJitter
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.TraversalReference

/-! The finite critical endpoint cap with its grid scale canceled explicitly. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- The critical cell cap for a finite conditional path experiment. The final
bound is independent of the auxiliary time-grid length d. -/
theorem critical_finite_traversal_cell_cap_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω Sf Sc Ar Iv Pal Tc : Type*) [Fintype Ω] [DecidableEq Sf]
      [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
      [Fintype Tc] [DecidableEq Tc] (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
      (_hP : ∀ e, 0 ≤ X.P e) (prior : Bool → Ar → ℝ) (π : Pal → ℝ)
      (vel : Pal → ℝ) (I : Tc → Set ℝ) (center : Tc → ℝ)
      (d δ K r Kp H lam : ℝ),
      0 < d → 0 ≤ δ → 2 ≤ K → 0 ≤ r → 0 ≤ Kp → 0 ≤ H → 0 < lam →
      (∀ z, 0 ≤ π z) → (∑ z, π z) ≤ 1 →
      (∀ a, MeasurableSet (I a)) → Pairwise (fun a b => Disjoint (I a) (I b)) →
      (∀ a, volume (I a) = ENNReal.ofReal d) →
      (∀ a, I a ⊆ Set.Icc (0 : ℝ) 1) →
      (∀ a, center a ∈ Set.Icc (0 : ℝ) 1) →
      (∀ a s, s ∈ I a → |s - center a| ≤ δ) →
      (2 * K)⁻¹ + 2 * δ ≤ K⁻¹ → 20 * K ^ 2 * δ ≤ r →
      (∀ κ a t, fiberMass X.P (fun e => (X.arm e κ, X.cell e)) (a, t) ≤
        prior κ a * (H * d)) →
      (∀ e z, (∑ er ∈ univ.filter (fun er => X.Z er = z),
        condKey X.P X.fine e er) ≤ Kp * π z) →
      ∀ (q u : Fin 3 → ℝ), |q 0| ≤ K → |q 1| ≤ K →
      ∀ (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
        (τ : Ω → List (Pal × Tc) → ℝ) (F : List (Pal × Tc) → ℝ),
      (∀ l, 0 ≤ F l) → (∀ e l, τ e l ≤ F l) →
      (∀ (zs : Fin 3 → Pal) (ts : Fin 3 → Tc),
        F (List.ofFn (fun i => (zs i, ts i))) ≤
          if ((∀ i, |vel (zs i)| ≤ K) ∧
              (∀ i : Fin 2, K⁻¹ ≤ |vel (zs i.succ) - vel (zs i.castSucc)|)) ∧
            (K⁻¹ ≤ |center (ts 1) - center (ts 0)| ∧
              ∀ i, |criticalEndpoint (fun j => vel (zs j)) q
                (center (ts 2), fun j : Fin 2 => center (ts j.castSucc)) i - u i| ≤ r)
          then 1 else 0) →
      ∀ e, finiteTraversalValue X prior lam allowed τ 3 e [] ≤
        C * K ^ 24 * r ^ 3 * (Kp * H / lam) ^ 3 := by
  obtain ⟨C, hC, hbox⟩ := critical_endpoint_time_box_count
  refine ⟨C, hC, ?_⟩
  intro Ω Sf Sc Ar Iv Pal Tc _ _ _ _ _ _ _ _ _ X hP prior π vel I center d δ K r Kp H lam hd hδ hK hr hKp hH hlam hπ hπ1
    hIm hId hIv hIunit hcenter hnear hmargin herror hcell hpal q u hq0 hq1
    allowed τ F hF hτ hlegal e
  have hcount (zs : Fin 3 → Pal) :
      (∑ ts : Fin 3 → Tc, F (List.ofFn (fun i => (zs i, ts i)))) ≤
        C * K ^ 24 * r ^ 3 / d ^ 3 := by
    by_cases hc : (∀ i, |vel (zs i)| ≤ K) ∧
        (∀ i : Fin 2, K⁻¹ ≤ |vel (zs i.succ) - vel (zs i.castSucc)|)
    · let Q : Finset (Fin 3 → Tc) := univ.filter (fun ts =>
        K⁻¹ ≤ |center (ts 1) - center (ts 0)| ∧
          ∀ i, |criticalEndpoint (fun j => vel (zs j)) q
            (center (ts 2), fun j : Fin 2 => center (ts j.castSucc)) i - u i| ≤ r)
      have hcard : (Q.card : ℝ) * d ^ 3 ≤ C * K ^ 24 * r ^ 3 :=
        hbox Tc I center hIm hId d δ K r hd hδ hK hr hIv hIunit hcenter hnear hmargin herror
          (fun j => vel (zs j)) q u hc.1 hc.2 hq0 hq1 Q
          (fun ts hts => (mem_filter.mp hts).2)
      have hsum : (∑ ts : Fin 3 → Tc, F (List.ofFn (fun i => (zs i, ts i)))) ≤ (Q.card : ℝ) := by
        calc
          _ ≤ ∑ ts : Fin 3 → Tc, if ts ∈ Q then (1 : ℝ) else 0 := by
            apply sum_le_sum
            intro ts _
            simpa [Q, hc.1, hc.2] using hlegal zs ts
          _ = _ := by simp
      exact hsum.trans ((le_div_iff₀ (pow_pos hd 3)).mpr hcard)
    · calc
        _ ≤ ∑ _ts : Fin 3 → Tc, (0 : ℝ) := by
          apply sum_le_sum
          intro ts _
          simpa only [hc, false_and, ite_false] using hlegal zs ts
        _ = 0 := by simp
        _ ≤ _ := by positivity
  have ha : 0 ≤ Kp * (H * d / lam) := by positivity
  have hfree : finiteTraversalFree π (Kp * (H * d / lam)) F 3 [] ≤
      (Kp * (H * d / lam)) ^ 3 * (C * K ^ 24 * r ^ 3 / d ^ 3) :=
    finiteTraversalFree_le_time_count_subprob π _ F hπ hπ1 ha 3 [] _ (by positivity) (by
      intro zs
      simpa only [List.nil_append] using hcount zs)
  have hvalue := finiteTraversalValue_le_free X hP prior π Kp lam (H * d) hKp hπ hlam
    (by positivity) hcell (finite_refresh_palette_test_bound X π Kp hpal)
    allowed τ F hF hτ 3 e []
  refine hvalue.trans (hfree.trans_eq ?_)
  field_simp [hd.ne', hlam.ne']


variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

theorem critical_finite_traversal_cell_cap :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
      (_hP : ∀ e, 0 ≤ X.P e) (prior : Bool → Ar → ℝ) (π : Pal → ℝ)
      (vel : Pal → ℝ) (I : Tc → Set ℝ) (center : Tc → ℝ)
      (d δ K r Kp H lam : ℝ),
      0 < d → 0 ≤ δ → 2 ≤ K → 0 ≤ r → 0 ≤ Kp → 0 ≤ H → 0 < lam →
      (∀ z, 0 ≤ π z) → (∑ z, π z) ≤ 1 →
      (∀ a, MeasurableSet (I a)) → Pairwise (fun a b => Disjoint (I a) (I b)) →
      (∀ a, volume (I a) = ENNReal.ofReal d) →
      (∀ a, I a ⊆ Set.Icc (0 : ℝ) 1) →
      (∀ a, center a ∈ Set.Icc (0 : ℝ) 1) →
      (∀ a s, s ∈ I a → |s - center a| ≤ δ) →
      (2 * K)⁻¹ + 2 * δ ≤ K⁻¹ → 20 * K ^ 2 * δ ≤ r →
      (∀ κ a t, fiberMass X.P (fun e => (X.arm e κ, X.cell e)) (a, t) ≤
        prior κ a * (H * d)) →
      (∀ e z, (∑ er ∈ univ.filter (fun er => X.Z er = z),
        condKey X.P X.fine e er) ≤ Kp * π z) →
      ∀ (q u : Fin 3 → ℝ), |q 0| ≤ K → |q 1| ≤ K →
      ∀ (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
        (τ : Ω → List (Pal × Tc) → ℝ) (F : List (Pal × Tc) → ℝ),
      (∀ l, 0 ≤ F l) → (∀ e l, τ e l ≤ F l) →
      (∀ (zs : Fin 3 → Pal) (ts : Fin 3 → Tc),
        F (List.ofFn (fun i => (zs i, ts i))) ≤
          if ((∀ i, |vel (zs i)| ≤ K) ∧
              (∀ i : Fin 2, K⁻¹ ≤ |vel (zs i.succ) - vel (zs i.castSucc)|)) ∧
            (K⁻¹ ≤ |center (ts 1) - center (ts 0)| ∧
              ∀ i, |criticalEndpoint (fun j => vel (zs j)) q
                (center (ts 2), fun j : Fin 2 => center (ts j.castSucc)) i - u i| ≤ r)
          then 1 else 0) →
      ∀ e, finiteTraversalValue X prior lam allowed τ 3 e [] ≤
        C * K ^ 24 * r ^ 3 * (Kp * H / lam) ^ 3 := by
  obtain ⟨C, hC, h⟩ := critical_finite_traversal_cell_cap_uniform
  exact ⟨C, hC, h Ω Sf Sc Ar Iv Pal Tc⟩

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
