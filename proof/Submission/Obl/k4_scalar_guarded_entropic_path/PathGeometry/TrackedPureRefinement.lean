/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrackedPureRefinement.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementSubfamilies
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathBudgets
import Submission.Obl.k4_scalar_normalized_exact_refinement.PureRestriction
import Submission.Obl.k4_scalar_pure_multiworld_homogenization

/-! A stronger form of the accepted pure-restriction construction, retaining
its chosen-atlas data. Adapted from: here:o166, accepted lib336f0b704ef5,
Submission/Obl/k4_scalar_normalized_exact_refinement/PureRestriction.lean.
All component estimates are imported from that accepted module. Its public
existential stage does not retain the original assignment/map identities;
the conclusion here records them through RetainedRefinement. The budget
positivity/lower estimates use the existing o093 witness and path APIs.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_normalized_exact_refinement

noncomputable section

/-- Homogenize incidences inside the supplied atlas. The returned worlds
are an injected subfamily of its full original assignments and maps. -/
theorem exists_pure_retained_refinement {p q : Code} {r b h : ℝ}
    (hp₀ : Exact p) (hq : Spec.RawScalar q) (w : RefinementWitness p q r b h) :
    ∃ a : RetainedRefinement w, Spec.RawScalar a.code ∧ Spec.PureProfile a.code ∧
      L a.code = L q ∧ d a.code = d q ∧ S a.code = S q ∧ U a.code = U q := by
  classical
  have hp : Spec.RawScalar p := ⟨hp₀.1, hp₀.2.1⟩
  have hhom : Stages.PureHomogenization := Submission.k4_scalar_pure_multiworld_homogenization
  obtain ⟨ψ, Kh, Mh, Dh, E', ρ', F, hψ, hEsub, hraw, hpure⟩ := hhom q hq
  let qh : Code := ⟨(fun k => W q (ψ k)), (fun k => N q (ψ k)), Kh, Mh, Dh,
    L q, d q, S q, U q, (fun k => ω q (ψ k)), (fun k => ν q (ψ k)), E', ρ',
    (fun _ _ _ _ => 0), F⟩
  change Spec.RawScalar qh at hraw
  change Spec.PureProfile qh at hpure
  let φ := w.sample
  let ε := w.loss
  let B := w.exponent
  let T := w.T
  let γ := w.world
  let j := w.block
  let A := w.assignment
  let C := w.selected
  let u := w.center
  let v := w.speed
  let J := w.width
  let P := w.polynomial
  let Λ := w.lists
  let θ := w.trajectory
  have hφ := w.sample_strictMono
  have hεpos := w.loss_pos
  have hεlim := w.loss_tendsto
  have hB := w.exponent_one
  have hchart := w.charts
  have hθ := w.maps
  have hweights := w.weights
  let dt : ℕ → ℝ := fun k => ((2 : ℝ) ^ T k)⁻¹
  let t₀ := fun k i => ((j k i : ℕ) : ℝ) * dt k
  let Φ := fun k i (z : Line × ℝ) => (θ k i z.1, (z.2 - t₀ k i) / dt k)
  have hdt (k : ℕ) : 0 < dt k := by dsimp [dt]; positivity
  have hΦ (k : ℕ) (i : Fin (W q k)) : Measurable (Φ k i) :=
    ((hθ k i).1.comp measurable_fst).prodMk
      ((measurable_snd.sub_const (t₀ k i)).div_const (dt k))
  have hθeq (k : ℕ) (i : Fin (W q k)) :
      θ k i = normalizeLine (P k i) (t₀ k i) (dt k) (u k i) (v k i) (J k i) (N p (φ k) ^ (-r)) := by
    have hpiece := (hchart k).2.2.2.2.2.2.1 i
    exact normalizeLine_unique (P k i) hpiece.2.2.2.2.2.1 _ _ _ _ _ _
      (hdt k).ne' (θ k i) (hθ k i).2.1 (hθ k i).2.2.1 (hθ k i).2.2.2.1
  let m := WorldSelection.positiveWorldCount qh
  let e : (k : ℕ) → Fin (m k) ↪ Fin (W q (ψ k)) :=
    fun k => WorldSelection.positiveWorldEmbedding qh k
  have hNp0 (k : ℕ) : 0 < N p (φ k) := by
    have hN : 2 ≤ N p (φ k) := hp.1.1 (φ k)
    linarith
  have hKh0 (k : ℕ) : 0 < Kh k := by
    have hK : 1 ≤ Kh k := hraw.1.2.2.1.1 k
    linarith
  let C' := fun k (i : Fin (m k)) => C (ψ k) (e k i) ∩ Φ (ψ k) (e k i) ⁻¹' E' k (e k i)
  have hCm (k : ℕ) (i : Fin (m k)) : MeasurableSet (C' k i) :=
    ((hchart (ψ k)).2.2.2.1 (e k i)).2.inter
      ((hΦ (ψ k) (e k i)) ((hraw.2 k).2.2.2.1 (e k i)).2.2.2.1)
  have hμh (k : ℕ) (i : Fin (W qh k)) :
      mu qh k i = (mu q (ψ k) i).restrict (E' k i) := by
    change ((ν q (ψ k) i).prod volume).restrict (E' k i) =
      (((ν q (ψ k) i).prod volume).restrict (E q (ψ k) i)).restrict (E' k i)
    exact (Measure.restrict_restrict_of_subset (hEsub k i)).symm
  have hlaw (k : ℕ) (i : Fin (m k)) :
      mu qh k (e k i) =
        (ENNReal.ofReal (dt (ψ k)) * ν p (φ (ψ k)) (γ (ψ k) (e k i)) (A (ψ k) (e k i)))⁻¹ •
          ((mu p (φ (ψ k)) (γ (ψ k) (e k i))).restrict (C' k i)).map (Φ (ψ k) (e k i)) := by
    rw [hμh k (e k i), (hθ (ψ k) (e k i)).2.2.2.2.2]
    exact restrict_transported_selected _ _ _ (hΦ (ψ k) (e k i)) _ _
      ((hraw.2 k).2.2.2.1 (e k i)).2.2.2.1
  have hCpos (k : ℕ) (i : Fin (m k)) :
      0 < mu p (φ (ψ k)) (γ (ψ k) (e k i)) (C' k i) := by
    have hpos := WorldSelection.positive_selected_pos qh k i
    change 0 < mu qh k (e k i) univ at hpos
    rw [hlaw] at hpos
    by_contra hnot
    have hz : mu p (φ (ψ k)) (γ (ψ k) (e k i)) (C' k i) = 0 := le_zero_iff.mp (not_lt.mp hnot)
    have hzero : (mu p (φ (ψ k)) (γ (ψ k) (e k i))).restrict (C' k i) = 0 :=
      Measure.restrict_eq_zero.mpr hz
    simp [hzero] at hpos
  have hpriorpos (k : ℕ) (i : Fin (W q k)) :
      0 < (ν p (φ k) (γ k i) (A k i)).toReal :=
    ENNReal.toReal_pos (w.assignment_mass_pos k i).ne' (w.assignment_mass_ne_top hp₀ k i)
  let a := fun k (i : Fin (W q k)) => dt k * (ν p (φ k) (γ k i) (A k i)).toReal
  let budget := fun k (i : Fin (W q k)) => ω p (φ k) (γ k i) * a k i
  let Z := fun k => ∑ i, budget k i
  let Z' := fun k => ∑ i : Fin (m k), budget (ψ k) (e k i)
  have hapos (k : ℕ) (i : Fin (W q k)) : 0 < a k i := mul_pos (hdt k) (hpriorpos k i)
  have hZpos (k : ℕ) : 0 < Z k := by
    simpa only [Z, budget, a, mul_assoc, dt, φ, γ, A, T, RefinementData.duration] using
      (hweights k).1
  have hwformula (k : ℕ) (i : Fin (W q k)) : ω q k i = budget k i / Z k := by
    simpa only [Z, budget, a, mul_assoc, dt, φ, γ, A, T, RefinementData.duration] using
      (hweights k).2 i
  have hZlower (k : ℕ) : N p (φ k) ^ (-ε k) ≤ Z k := by
    simpa only [Z, budget, a, φ, ε, γ, A, dt, T, RefinementData.duration,
      PathMeasures.normalizer, mul_assoc] using PathMeasures.normalizer_lower w hp₀ k
  have hZ'lower (k : ℕ) : N p (φ (ψ k)) ^ (-ε (ψ k)) / Kh k ≤ Z' k := by
    apply retained_assignment_normalizer_lower (budget (ψ k)) (e k) (Z (ψ k))
      _ (Kh k) (hZpos (ψ k)).ne' (Real.rpow_nonneg (hNp0 (ψ k)).le _)
      (hZlower (ψ k)) (hKh0 k)
    have hret := (WorldSelection.positiveWorldBudget_bounds qh hraw k).1
    change (Kh k)⁻¹ ≤ ∑ i, ω q (ψ k) (e k i) at hret
    simpa only [hwformula] using hret
  have hZ'pos (k : ℕ) : 0 < Z' k :=
    (div_pos (Real.rpow_pos_of_pos (hNp0 (ψ k)) _)
      (hKh0 k)).trans_le (hZ'lower k)
  have hwfinal (k : ℕ) (i : Fin (m k)) :
      ω (WorldSelection.positiveCode qh) k i = budget (ψ k) (e k i) / Z' k := by
    change (∑ j, ω q (ψ k) (e k j))⁻¹ * ω q (ψ k) (e k i) = _
    simp_rw [hwformula]
    exact renormalized_subset_weight (budget (ψ k)) (e k) (Z (ψ k))
      (hZpos (ψ k)).ne' (hZ'pos k).ne' i
  have haENN (k : ℕ) (i : Fin (W q k)) : ENNReal.ofReal (a k i) =
      ENNReal.ofReal (dt k) * ν p (φ k) (γ k i) (A k i) := by
    let : IsProbabilityMeasure (ν p (φ k) (γ k i)) := ((hp.2 (φ k)).2.2.2.1 (γ k i)).1
    dsimp only [a]
    rw [ENNReal.ofReal_mul (hdt k).le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hlawmass (k : ℕ) (i : Fin (m k)) : mu qh k (e k i) univ =
      (ENNReal.ofReal (a (ψ k) (e k i)))⁻¹ * mu p (φ (ψ k)) (γ (ψ k) (e k i)) (C' k i) := by
    rw [hlaw k i, Measure.smul_apply, Measure.map_apply (hΦ (ψ k) (e k i)) MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ, haENN]
    rfl
  have hsuccess (k : ℕ) : ENNReal.ofReal ((Kh k)⁻¹) ≤ ∑ i : Fin (m k),
      ENNReal.ofReal (budget (ψ k) (e k i) / Z' k) *
        ((ENNReal.ofReal (a (ψ k) (e k i)))⁻¹ * mu p (φ (ψ k)) (γ (ψ k) (e k i)) (C' k i)) := by
    calc
      _ ≤ ∑ i : Fin (m k), ENNReal.ofReal (ω (WorldSelection.positiveCode qh) k i) *
          mu qh k (e k i) univ := WorldSelection.positive_success qh hraw k
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hwfinal k i, hlawmass k i]
  let Λ' := fun k => restrictedChartList (e k) (Λ (ψ k))
  let obs := fun k (z : Line × ℝ) =>
    ((![z.2, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y z.1 z.2] : Fin 2 → ℝ),
      (⌊Submission.Obl.k4_scalar_linear_critical_extremizers.Split.x z.1 z.2 /
        N p (φ (ψ k)) ^ (-b)⌋ : ℤ))
  have hcard (k : ℕ) (g : Fin (W p (φ (ψ k)))) (z : Line × ℝ) :
      ((Λ' k g (obs k z)).card : ℝ) ≤ N p (φ (ψ k)) ^ ε (ψ k) := by
    calc
      _ ≤ ((Λ (ψ k) g (obs k z)).card : ℝ) := by
        exact_mod_cast restrictedChartList_card (e k) (Λ (ψ k)) g (obs k z)
      _ ≤ _ := (hchart (ψ k)).2.2.2.2.2.2.2.1 g (obs k z)
  have hrec (k : ℕ) (i : Fin (m k)) :
      mu p (φ (ψ k)) (γ (ψ k) (e k i))
        {z | z ∈ C' k i ∧ i ∉ Λ' k (γ (ψ k) (e k i)) (obs k z)} = 0 := by
    apply le_antisymm _ zero_le
    rw [← (hchart (ψ k)).2.2.2.2.2.2.2.2.2.1 (e k i)]
    apply measure_mono
    intro z hz
    exact ⟨hz.1.1, by simpa only [Λ', restrictedChartList, Finset.mem_filter,
      Finset.mem_univ, true_and, obs, φ, γ, Λ] using hz.2⟩
  have hunion (k : ℕ) : ENNReal.ofReal (Z' k / Kh k / N p (φ (ψ k)) ^ ε (ψ k)) ≤
      ∑ g, ENNReal.ofReal (ω p (φ (ψ k)) g) *
        mu p (φ (ψ k)) g {z | ∃ i : Fin (m k), γ (ψ k) (e k i) = g ∧ z ∈ C' k i} := by
    apply normalized_sparse_union_lower_bound (mu p (φ (ψ k))) (ω p (φ (ψ k)))
      (γ (ψ k) ∘ e k) (C' k) (hCm k) (fun g z => Λ' k g (obs k z))
      (fun i => a (ψ k) (e k i)) (Z' k) (Kh k) (N p (φ (ψ k)) ^ ε (ψ k))
      (hp.2 (φ (ψ k))).2.1 (fun i => hapos (ψ k) (e k i)) (hZ'pos k) (hKh0 k)
      (Real.rpow_pos_of_pos (hNp0 (ψ k)) _) (hcard k) (hrec k)
    exact hsuccess k
  have hNeq (k : ℕ) : N qh k = N p (φ (ψ k)) := (hchart (ψ k)).1
  let ε' := restrictionLoss (N qh) Kh (ε ∘ ψ)
  have hε'pos (k : ℕ) : 0 < ε' k :=
    (restrictionLoss_bounds (N qh) Kh (ε ∘ ψ) hraw.1.1 hraw.1.2.2.1.1
      (fun k => hεpos (ψ k)) k).1
  have hεle (k : ℕ) : ε (ψ k) ≤ ε' k :=
    (restrictionLoss_bounds (N qh) Kh (ε ∘ ψ) hraw.1.1 hraw.1.2.2.1.1
      (fun k => hεpos (ψ k)) k).2
  have hε'lim : Tendsto ε' atTop (nhds 0) :=
    restrictionLoss_tendsto_zero (N qh) Kh (ε ∘ ψ) hraw.1.2.1 hraw.1.2.2.1.1
      hraw.1.2.2.1.2 (hεlim.comp hψ.tendsto_atTop)
  have hcoverage (k : ℕ) : ENNReal.ofReal (N p (φ (ψ k)) ^ (-ε' k)) ≤
      ∑ g, ENNReal.ofReal (ω p (φ (ψ k)) g) *
        mu p (φ (ψ k)) g {z | ∃ i : Fin (m k), γ (ψ k) (e k i) = g ∧ z ∈ C' k i} := by
    apply le_trans _ (hunion k)
    apply ENNReal.ofReal_le_ofReal
    have heq := restrictionLoss_power (N qh) Kh (ε ∘ ψ) hraw.1.1 hraw.1.2.2.1.1 k
    change N qh k ^ (-ε' k) = N qh k ^ (-2 * ε (ψ k)) / Kh k ^ (2 : ℕ) at heq
    rw [hNeq k] at heq
    have hpdiv : N p (φ (ψ k)) ^ (-ε (ψ k)) / N p (φ (ψ k)) ^ ε (ψ k) =
        N p (φ (ψ k)) ^ (-2 * ε (ψ k)) := by
      rw [← Real.rpow_sub (hNp0 (ψ k))]
      congr 1
      ring
    calc
      _ = (N p (φ (ψ k)) ^ (-ε (ψ k)) / Kh k) / Kh k /
          N p (φ (ψ k)) ^ ε (ψ k) := by
        rw [heq, ← hpdiv]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (hZ'lower k) (hKh0 k).le)
        (Real.rpow_nonneg (hNp0 (ψ k)).le _)
  let B' : ℕ := B + Mh + 2 * Dh + 1
  have hBB' : B ≤ B' := by dsimp [B']; omega
  have hB' : 1 ≤ B' := hB.trans hBB'
  have hcount : max (B : ℝ) (Mh : ℝ) + 1 ≤ (B' : ℝ) := by
    have hh : max B Mh + 1 ≤ B' := by dsimp [B']; omega
    exact_mod_cast hh
  have hdeg : max B (2 * Dh) ≤ B' := by dsimp [B']; omega
  have hfmt (k : ℕ) (i : Fin (m k)) : ∀ label,
      Format 6 (N p (φ (ψ k)) ^ (B' : ℝ)) B'
        {z | coefficientState label z ∈ C' k i} := by
    have hN : 2 ≤ N p (φ (ψ k)) := hp.1.1 (φ (ψ k))
    have hc := (hchart (ψ k)).2.2.2.2.2.2.1 (e k i)
    have hF : ∀ label, Format 6 (N p (φ (ψ k)) ^ (Mh : ℝ)) Dh
        {z | coefficientState label z ∈ E' k (e k i)} := by
      intro label
      have hh := ((hraw.2 k).2.2.2.1 (e k i)).2.2.2.2.2.2 label
      change Format 6 (N qh k ^ (Mh : ℝ)) Dh
        {z | coefficientState label z ∈ E' k (e k i)} at hh
      rwa [hNeq k] at hh
    have hh := formatted_chart_pullback hN hcount hdeg (C (ψ k) (e k i)) (E' k (e k i))
      hc.2.2.2.2.2.2.2.2.2.1 hF (P (ψ k) (e k i)) hc.2.2.2.2.2.1
      (t₀ (ψ k) (e k i)) (dt (ψ k)) (u (ψ k) (e k i)) (v (ψ k) (e k i))
      (J (ψ k) (e k i)) (N p (φ (ψ k)) ^ (-r)) (hdt (ψ k)).ne' hc.2.1.ne'
      (Real.rpow_pos_of_pos (hNp0 (ψ k)) _).ne'
    dsimp only [C', Φ]
    rw [hθeq (ψ k) (e k i)]
    exact hh
  have hcharts (k : ℕ) :
      ChartData p B' r b (h + ε' k) (ε' k) false (φ (ψ k)) (T (ψ k)) (m k)
        (γ (ψ k) ∘ e k) (j (ψ k) ∘ e k) (A (ψ k) ∘ e k) (C' k)
        (u (ψ k) ∘ e k) (v (ψ k) ∘ e k) (J (ψ k) ∘ e k) (P (ψ k) ∘ e k) (Λ' k) := by
    have hN : 1 ≤ N p (φ (ψ k)) := by have hh : 2 ≤ N p (φ (ψ k)) := hp.1.1 _; linarith
    exact chartData_shrink_restrict (hchart (ψ k)).2 hN hBB'
      (by linarith [hεle k]) (hεle k) (e k) (C' k) (hCm k)
      (fun i => inter_subset_left) (hCpos k) (hfmt k) (hcoverage k)
  let q' := WorldSelection.positiveCode qh
  let w' : RefinementWitness p q' r b h :=
    { toRefinementData := w.toRefinementData.subfamily q' ψ e ε' B' C' Λ'
      sample_strictMono := hφ.comp hψ
      loss_pos := hε'pos
      loss_tendsto := hε'lim
      exponent_one := hB'
      charts := fun k => ⟨hNeq k, hcharts k⟩
      maps := by
        intro k i
        have ht := hθ (ψ k) (e k i)
        exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, hlaw k i⟩
      weights := by
        intro k
        constructor
        · change 0 < ∑ i : Fin (m k), ω p (φ (ψ k)) (γ (ψ k) (e k i)) * dt (ψ k) *
            (ν p (φ (ψ k)) (γ (ψ k) (e k i)) (A (ψ k) (e k i))).toReal
          simpa only [Z', budget, a, mul_assoc] using hZ'pos k
        · intro i
          change ω (WorldSelection.positiveCode qh) k i =
            (ω p (φ (ψ k)) (γ (ψ k) (e k i)) * dt (ψ k) *
              (ν p (φ (ψ k)) (γ (ψ k) (e k i)) (A (ψ k) (e k i))).toReal) /
            ∑ j : Fin (m k), ω p (φ (ψ k)) (γ (ψ k) (e k j)) * dt (ψ k) *
              (ν p (φ (ψ k)) (γ (ψ k) (e k j)) (A (ψ k) (e k j))).toReal
          simpa only [Z', budget, a, mul_assoc] using hwfinal k i }
  refine ⟨⟨q', ψ, hψ, e, Λ', w', rfl, ?_⟩,
    WorldSelection.positive_raw qh hraw, WorldSelection.positive_pure qh hraw hpure,
    rfl, rfl, rfl, rfl⟩
  exact fun _ _ => inter_subset_left

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
