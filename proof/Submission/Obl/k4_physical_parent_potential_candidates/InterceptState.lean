-- Adapted from this LOT tree, o286, branch x1021, commit 128bb7e2,
-- Submission/Obl/k4_native_field_original_candidates/InterceptState.lean.
-- Original session x1021. Accepted helper results remain imported.
import Submission.Obl.k4_physical_parent_potential_candidates.InterceptCensus
import Submission.Lib.K4StateFractionKeep

open Set MeasureTheory

namespace Submission.Obl.k4_physical_parent_potential_candidates

/-- Bounded variation of a group label on each state gives a uniformly
finite menu even when the set of states itself is infinite. -/
theorem exists_state_group_menu {Ω I : Type*} (S : Set Ω) (state : Ω → I) (group : Ω → ℤ)
    (C : ℕ)
    (hlocal : ∀ e ∈ S, ∀ f ∈ S, state e = state f →
      group e ∈ Finset.Icc (group f-(C : ℤ)) (group f+(C : ℤ))) :
    ∃ menu : I → Finset ℤ, (∀ i, (menu i).card ≤ 2*C+1) ∧
      ∀ e ∈ S, group e ∈ menu (state e) := by
  classical
  have hmenu (i : I) : ∃ F : Finset ℤ, F.card ≤ 2*C+1 ∧
      ∀ e ∈ S, state e = i → group e ∈ F := by
    by_cases hi : ∃ f ∈ S, state f = i
    · obtain ⟨f, hf, hfi⟩ := hi
      refine ⟨Finset.Icc (group f-(C : ℤ)) (group f+(C : ℤ)), ?_, ?_⟩
      · rw [Int.card_Icc]
        omega
      · intro e he hei
        exact hlocal e he f hf (hei.trans hfi.symm)
    · refine ⟨∅, by simp, ?_⟩
      intro e he hei
      exact (hi ⟨e, he, hei⟩).elim
  choose menu hcard hcover using hmenu
  exact ⟨menu, hcard, fun e he => hcover (state e) e he rfl⟩

/-- At the original fine physical state, at most nine own-intercept bins
can occur at any wider signal scale. -/
theorem fine_intercept_menus {Ω : Type*}
    (S : Set Ω) (z : Ω → Fin 3 → ℝ) (X intercept : Ω → ℝ) (P : (Fin 3 → ℝ) → ℝ)
    (ε w θ Lip : ℝ) (hε : 0 < ε) (hw : 0 < w) (hLip0 : 0 ≤ Lip)
    (hεw : ε ≤ w) (hθ : θ ≤ w) (hmesh : Lip*ε ≤ w)
    (hfit : ∀ e ∈ S, |X e-P (z e)-intercept e| ≤ θ)
    (hLip : ∀ e ∈ S, ∀ f ∈ S, |P (z e)-P (z f)| ≤ Lip*‖z e-z f‖) :
    ∃ menu : ((Fin 3 → ℤ) × ℤ) → Finset ℤ, (∀ i, (menu i).card ≤ 9) ∧
      ∀ e ∈ S, ⌊intercept e/w⌋ ∈ menu ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋) := by
  apply exists_state_group_menu S (fun e => ((fun i => ⌊z e i/ε⌋), ⌊X e/ε⌋))
    (fun e => ⌊intercept e/w⌋) 4
  intro e he f hf hcode
  have hheight : |X e-X f| ≤ w :=
    (Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell hε
      (congrArg Prod.snd hcode)).trans hεw
  have hbase : ‖z e-z f‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε.le).mpr
    intro i
    exact Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell hε
      (congrArg (fun k : (Fin 3 → ℤ) × ℤ => k.1 i) hcode)
  have hpol : |P (z e)-P (z f)| ≤ w :=
    (hLip e he f hf).trans ((mul_le_mul_of_nonneg_left hbase hLip0).trans hmesh)
  have hclose : |intercept e-intercept f| ≤ (4 : ℝ)*w := by
    obtain ⟨he₁, he₂⟩ := abs_le.mp (hfit e he)
    obtain ⟨hf₁, hf₂⟩ := abs_le.mp (hfit f hf)
    obtain ⟨hh₁, hh₂⟩ := abs_le.mp hheight
    obtain ⟨hp₁, hp₂⟩ := abs_le.mp hpol
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact floor_mem_interval_of_close 4 hw hclose

/-- A finite menu at each original state bounds the sum of all label
charges under that same original measure. -/
theorem finite_menu_overlap_sum_le {Ω I J : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] [DecidableEq J]
    (μ : Measure Ω) (state : Ω → I) (hstate : Measurable state)
    (menu : I → Finset J) (M : ℕ) (hM : ∀ i, (menu i).card ≤ M) (G : Finset J) :
    (∑ g ∈ G, μ {e | g ∈ menu (state e)}) ≤ (M : ENNReal)*μ univ := by
  classical
  let E (g : J) : Set Ω := {e | g ∈ menu (state e)}
  have hE (g : J) : MeasurableSet (E g) :=
    hstate (Set.to_countable {i | g ∈ menu i}).measurableSet
  calc
    _ = ∑ g ∈ G, ∫⁻ e, (E g).indicator (fun _ => (1 : ENNReal)) e ∂μ := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [lintegral_indicator_const (hE g), one_mul]
    _ = ∫⁻ e, ∑ g ∈ G, (E g).indicator (fun _ => (1 : ENNReal)) e ∂μ :=
      (lintegral_finset_sum G (fun g _ => measurable_const.indicator (hE g))).symm
    _ ≤ ∫⁻ _e, (M : ENNReal) ∂μ := by
      apply lintegral_mono
      intro e
      simp only [Set.indicator_apply, E, Set.mem_setOf_eq, Finset.sum_boole]
      have hsub : (G.filter (fun g => g ∈ menu (state e))) ⊆ menu (state e) :=
        fun g hg => (Finset.mem_filter.mp hg).2
      exact_mod_cast (Finset.card_le_card hsub).trans (hM (state e))
    _ = _ := lintegral_const _

noncomputable def sourceGroupKeep {Ω I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) (state : Ω → I) (S : Set Ω) (group : Ω → ℤ)
    (f : ENNReal) (g : ℤ) : Set Ω :=
  Submission.Lib.K4StateFractionKeep.fractionKeep μ state (S ∩ group ⁻¹' {g}) f

/-- Keeping each intercept group where it is an original state fraction
loses at most `M*f` times the original total mass across ALL groups. -/
theorem group_fraction_keep_budget {Ω I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) (state : Ω → I) (hstate : Measurable state)
    (S : Set Ω) (hS : MeasurableSet S) (group : Ω → ℤ) (hgroup : Measurable group)
    (menu : I → Finset ℤ) (M : ℕ) (hM : ∀ i, (menu i).card ≤ M)
    (hmenu : ∀ e ∈ S, group e ∈ menu (state e))
    (G : Finset ℤ) (hG : ∀ e ∈ S, group e ∈ G) (f : ENNReal) :
    (∀ g, MeasurableSet (sourceGroupKeep μ state S group f g)) ∧
      μ S ≤ (∑ g ∈ G, μ (sourceGroupKeep μ state S group f g)) + (M : ENNReal)*f*μ univ := by
  classical
  let groupSet (g : ℤ) := S ∩ group ⁻¹' {g}
  have hgroupSet (g : ℤ) : MeasurableSet (groupSet g) := hS.inter (hgroup (measurableSet_singleton g))
  refine ⟨fun g => Submission.Lib.K4StateFractionKeep.measurableSet_fractionKeep hstate (hgroupSet g) f, ?_⟩
  have hdel (g : ℤ) : μ (groupSet g \ sourceGroupKeep μ state S group f g) ≤
      f*μ {e | g ∈ menu (state e)} := by
    apply (Submission.Lib.K4StateFractionKeep.measure_diff_fractionKeep_le μ hstate (groupSet g) f).trans
    apply mul_le_mul' le_rfl (measure_mono _)
    intro e he
    obtain ⟨x, hxG, hxi⟩ := he
    have hxi' : state x = state e := hxi
    have hxg : group x = g := hxG.2
    have hm := hmenu x hxG.1
    rwa [hxg, hxi'] at hm
  have hdelSum : (∑ g ∈ G, μ (groupSet g \ sourceGroupKeep μ state S group f g)) ≤
      f*((M : ENNReal)*μ univ) := by
    calc
      _ ≤ ∑ g ∈ G, f*μ {e | g ∈ menu (state e)} := Finset.sum_le_sum (fun g _ => hdel g)
      _ = f*(∑ g ∈ G, μ {e | g ∈ menu (state e)}) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul' le_rfl (finite_menu_overlap_sum_le μ state hstate menu M hM G)
  have hcover : S ⊆ ⋃ g ∈ G, groupSet g := by
    intro e he
    exact mem_iUnion₂.mpr ⟨group e, hG e he, he, rfl⟩
  calc
    _ ≤ μ (⋃ g ∈ G, groupSet g) := measure_mono hcover
    _ ≤ ∑ g ∈ G, μ (groupSet g) := measure_biUnion_finset_le _ _
    _ ≤ ∑ g ∈ G, (μ (sourceGroupKeep μ state S group f g)+
        μ (groupSet g \ sourceGroupKeep μ state S group f g)) := by
      apply Finset.sum_le_sum
      intro g hg
      calc
        _ ≤ μ (sourceGroupKeep μ state S group f g ∪
            (groupSet g \ sourceGroupKeep μ state S group f g)) := measure_mono (by
          intro e he
          by_cases hk : e ∈ sourceGroupKeep μ state S group f g
          · exact Or.inl hk
          · exact Or.inr ⟨he, hk⟩)
        _ ≤ _ := measure_union_le _ _
    _ = (∑ g ∈ G, μ (sourceGroupKeep μ state S group f g)) +
        ∑ g ∈ G, μ (groupSet g \ sourceGroupKeep μ state S group f g) := Finset.sum_add_distrib
    _ ≤ (∑ g ∈ G, μ (sourceGroupKeep μ state S group f g))+f*((M : ENNReal)*μ univ) :=
      add_le_add le_rfl hdelSum
    _ = _ := by ac_rfl

end Submission.Obl.k4_physical_parent_potential_candidates
