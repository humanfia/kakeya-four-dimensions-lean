import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Selected
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.ProfileAssembly
import Submission.Obl.k4_tempered_grid_selection.AnalyticSelection

/-!
# Whole-cell type selection over worlds

Given the per-world table approximation of the flattening step, select a common
heaviest type of quantized table exponents at the first rational depths (paper
Lemma 2.4). The state space tags each incidence with its world, so one type is
chosen for all worlds with their original weights. Each selected event is the
original event intersected with a boxed set of common labels; it keeps the
frozen polynomial format. The retained mass loses a subpower factor, and the
band transfer of o085 gives typical densities at every rational depth.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- All worlds, each incidence tagged by its world index. -/
def taggedLaw (p : Problem) (k : ℕ) : Measure (ℕ × Incidence) :=
  ∑ a : Fin (p.1 k), ENNReal.ofReal (weight p k a) •
    (law p k a).map (fun z => ((a : ℕ), z))

theorem taggedLaw_apply (p : Problem) (k : ℕ) {S : Set (ℕ × Incidence)}
    (hS : MeasurableSet S) :
    taggedLaw p k S = ∑ a : Fin (p.1 k), ENNReal.ofReal (weight p k a) *
      law p k a {z | ((a : ℕ), z) ∈ S} := by
  simp only [taggedLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Measure.map_apply (by fun_prop) hS]
  rfl

/-- The world-tagged common label. -/
def tagLabel (n : ℝ) (H : ℕ) (w : ℕ × Incidence) : ℕ × (Fin 3 → ℤ) :=
  (w.1, scalarLabel n H w.2)

/-- The clamped table exponent at the `j`-th rational depth. -/
def tableExponent (p : Problem) (C : ℕ)
    (g : (k : ℕ) → Fin (p.1 k) → ℝ → (Fin 3 → ℤ) → ℝ) (e : ℕ → ℚ)
    (k j : ℕ) (l : ℕ × (Fin 3 → ℤ)) : ℝ :=
  if h : l.1 < p.1 k then
    Submission.Obl.k4_tempered_grid_selection.boundedExponent (C : ℝ) (resolution p k)
      (g k ⟨l.1, h⟩ (clamp (length p) (e j)) l.2)
  else 0

theorem abs_tableExponent_le (p : Problem) (C : ℕ)
    (g : (k : ℕ) → Fin (p.1 k) → ℝ → (Fin 3 → ℤ) → ℝ) (e : ℕ → ℚ)
    (k j : ℕ) (l : ℕ × (Fin 3 → ℤ)) : |tableExponent p C g e k j l| ≤ (C : ℝ) := by
  unfold tableExponent
  split_ifs
  · exact Submission.Obl.k4_tempered_grid_selection.abs_boundedExponent _ _ _ (Nat.cast_nonneg C)
  · simp

/-- Numerical budget of the selected formats. -/
theorem format_budget {n : ℝ} (hn : 2 ≤ n) (M H : ℕ) :
    n ^ (M : ℝ) + 3 * (2 * ((labelRadius n (n ^ (M : ℝ)) H : ℕ) : ℝ) + 2) ≤
      n ^ ((M + H + 6 : ℕ) : ℝ) := by
  have hn1 : 1 ≤ n := by linarith
  have hn0 : 0 < n := by linarith
  have hR : ((labelRadius n (n ^ (M : ℝ)) H : ℕ) : ℝ) ≤ 3 * (n ^ H * n ^ M) + 2 := by
    simp only [labelRadius, Nat.cast_add, Nat.cast_one]
    rw [Real.rpow_natCast]
    have := Nat.ceil_lt_add_one (show 0 ≤ 3 * n ^ H * n ^ M by positivity)
    have h3 : 3 * n ^ H * n ^ M = 3 * (n ^ H * n ^ M) := by ring
    linarith
  generalize ((labelRadius n (n ^ (M : ℝ)) H : ℕ) : ℝ) = R at hR ⊢
  rw [Real.rpow_natCast, Real.rpow_natCast]
  set P := n ^ H * n ^ M with hP
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1) (one_le_pow₀ hn1)
  have hMP : n ^ M ≤ P := le_mul_of_one_le_left (pow_nonneg hn0.le _) (one_le_pow₀ hn1)
  have h64 : (64 : ℝ) ≤ n ^ 6 := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ n ^ 6 := pow_le_pow_left₀ (by norm_num) hn 6
  have hpow : n ^ (M + H + 6) = P * n ^ 6 := by
    rw [hP, pow_add, pow_add]
    ring
  rw [hpow]
  nlinarith

/-- The selected events: the old event inside a boxed set of selected labels. -/
def selectedEvent (p : Problem) (H : ℕ) (T : ℕ → Set (ℕ × (Fin 3 → ℤ)))
    (k : ℕ) (a : Fin (p.1 k)) : Set Incidence :=
  event p k a ∩ scalarLabel (resolution p k) H ⁻¹'
    {l | ((a : ℕ), l) ∈ T k ∧ ∀ c, |l c| ≤
      (labelRadius (resolution p k) (resolution p k ^ (sizeBudget p : ℝ)) H : ℤ)}

theorem measurableSet_selectedEvent (p : Problem) (hp : RawScalar p) (H : ℕ)
    (T : ℕ → Set (ℕ × (Fin 3 → ℤ))) (k : ℕ) (a : Fin (p.1 k)) :
    MeasurableSet (selectedEvent p H T k a) :=
  ((hp.2 k).2.2.2.1 a).2.2.2.1.inter
    ((Set.to_countable _).measurableSet.preimage (measurable_scalarLabel _ _))

theorem selectedEvent_subset (p : Problem) (H : ℕ) (T : ℕ → Set (ℕ × (Fin 3 → ℤ)))
    (k : ℕ) (a : Fin (p.1 k)) : selectedEvent p H T k a ⊆ event p k a :=
  inter_subset_left

/-- The selected law loses nothing on the label box. -/
theorem selected_mass_eq (p : Problem) (hp : RawScalar p) (H : ℕ)
    (T : ℕ → Set (ℕ × (Fin 3 → ℤ))) (k : ℕ) (a : Fin (p.1 k)) :
    ((prior p k a).prod volume) (selectedEvent p H T k a) =
      law p k a {z | ((a : ℕ), scalarLabel (resolution p k) H z) ∈ T k} := by
  have hEm : MeasurableSet (event p k a) := ((hp.2 k).2.2.2.1 a).2.2.2.1
  have hlab : Measurable (scalarLabel (resolution p k) H) := measurable_scalarLabel _ _
  have hbox := ae_label_box p hp k a H (subset_refl _) hEm
  set R := (labelRadius (resolution p k) (resolution p k ^ (sizeBudget p : ℝ)) H : ℤ)
  have hm1 : MeasurableSet (scalarLabel (resolution p k) H ⁻¹'
      {l | ((a : ℕ), l) ∈ T k ∧ ∀ c, |l c| ≤ R}) :=
    (Set.to_countable _).measurableSet.preimage hlab
  have hm2 : MeasurableSet {z | ((a : ℕ), scalarLabel (resolution p k) H z) ∈ T k} :=
    ((Set.to_countable {l : Fin 3 → ℤ | ((a : ℕ), l) ∈ T k}).measurableSet.preimage hlab)
  change ((prior p k a).prod volume) (event p k a ∩ _) = _
  rw [inter_comm, ← Measure.restrict_apply hm1]
  apply measure_congr
  filter_upwards [hbox] with z hz
  apply propext
  change (((a : ℕ), scalarLabel (resolution p k) H z) ∈ T k ∧ _) ↔ _
  exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩

/-- Whole-cell selection: semialgebraic sub-events with inverse-subpower mass and
typical densities at every clamped rational depth. -/
theorem whole_cell_selection (p : Problem) (hp : RawScalar p) {C H : ℕ}
    {g : (k : ℕ) → Fin (p.1 k) → ℝ → (Fin 3 → ℤ) → ℝ}
    (happ : ScalarApproximation p C H g) :
    ∃ (K : ℕ → ℝ) (M D : ℕ) (E : (k : ℕ) → Fin (p.1 k) → Set Incidence),
      (∀ k a, E k a ⊆ event p k a) ∧ RawScalar (withEvents p K M D E) ∧
        HasDensities (withEvents p K M D E) ∧ GridData (withEvents p K M D E) := by
  classical
  have hN : ∀ k, 2 ≤ resolution p k := hp.1.1
  have hNt : Tendsto (resolution p) atTop atTop := hp.1.2.1
  have hK : Submission.Obl.k4_tempered_grid_selection.Subpower (resolution p) (loss p) :=
    hp.1.2.2.1
  have hL : 0 ≤ length p := hp.1.2.2.2.2.2.1.le
  obtain ⟨e, he⟩ := exists_surjective_nat ℚ
  choose index hindex using he
  obtain ⟨B, T, a', δ, hB, hBsub, ha', hδpos, hδ, hfit, hmass⟩ :=
    Submission.Obl.k4_tempered_grid_selection.countable_type_selection
      (resolution p) hN hNt (taggedLaw p) (fun k => tagLabel (resolution p k) H)
      (tableExponent p C g e) (C : ℝ) (Nat.cast_nonneg C)
      (abs_tableExponent_le p C g e)
  let K' : ℕ → ℝ := fun k => loss p k * (B k : ℝ)
  let M' : ℕ := sizeBudget p + H + 6
  let D' : ℕ := max (degreeBudget p) 3
  let E' : (k : ℕ) → Fin (p.1 k) → Set Incidence := selectedEvent p H T
  have hE'sub : ∀ k a, E' k a ⊆ event p k a := selectedEvent_subset p H T
  have hKK' : ∀ k, loss p k ≤ K' k := by
    intro k
    have hb : (1 : ℝ) ≤ B k := by exact_mod_cast Nat.succ_le_iff.mpr (hB k)
    have hk1 : 1 ≤ loss p k := hp.1.2.2.1.1 k
    dsimp [K']
    nlinarith
  refine ⟨K', M', D', E', hE'sub, ?_, hasDensities_withEvents p hp K' M' D' E' hE'sub, ?_⟩
  · -- the selected problem is raw
    have hMM : ∀ k, resolution p k ^ (sizeBudget p : ℝ) ≤ resolution p k ^ (M' : ℝ) := by
      intro k
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [hN k])
      exact_mod_cast (show sizeBudget p ≤ M' by omega)
    refine ⟨⟨hp.1.1, hp.1.2.1,
      Submission.Obl.k4_tempered_grid_selection.subpower_mul
        (fun k => show 0 < resolution p k by linarith [hN k]) hK hBsub,
      (show 1 ≤ sizeBudget p + H + 6 by omega),
      (show 1 ≤ max (degreeBudget p) 3 from le_trans (by norm_num) (le_max_right _ _)),
      hp.1.2.2.2.2.2⟩, ?_⟩
    intro k
    obtain ⟨hW, hω0, hω1, hworld, hmass0⟩ := hp.2 k
    refine ⟨hW.trans (hMM k), hω0, hω1, ?_, ?_⟩
    · intro a
      obtain ⟨hprob, ⟨n, hn, h, i, Bs, hBs, hν⟩, hae, hEm, hEsub, hlab, hfmt⟩ := hworld a
      refine ⟨hprob, ⟨n, hn.trans (hMM k), h, i, Bs, ?_, hν⟩, ?_,
        measurableSet_selectedEvent p hp H T k a, (hE'sub k a).trans hEsub,
        fun z hz => (hlab z (hE'sub k a hz)).trans (hMM k), ?_⟩
      · intro j
        obtain ⟨h0, h1, h2, h3, h4⟩ := hBs j
        exact ⟨h0, h1.trans (hMM k), h2.trans (hMM k),
          Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.mono h3 (hMM k)
            (le_max_left _ _),
          fun b hb e => (h4 b hb e).trans (hMM k)⟩
      · filter_upwards [hae] with l hl e
        exact (hl e).trans (hKK' k)
      · intro i'
        have hA := hfmt i'
        have hT := format_label_selection (resolution p k) H
          (labelRadius (resolution p k) (resolution p k ^ (sizeBudget p : ℝ)) H)
          {l | ((a : ℕ), l) ∈ T k ∧ ∀ c, |l c| ≤
            (labelRadius (resolution p k) (resolution p k ^ (sizeBudget p : ℝ)) H : ℤ)}
          (fun l hl => hl.2) i'
        have hNM1 : 1 ≤ resolution p k ^ (sizeBudget p : ℝ) :=
          Real.one_le_rpow (by linarith [hN k]) (Nat.cast_nonneg _)
        have hR1 : (1 : ℝ) ≤ 3 * (2 * ((labelRadius (resolution p k)
            (resolution p k ^ (sizeBudget p : ℝ)) H : ℕ) : ℝ) + 2) := by
          have : (0 : ℝ) ≤ ((labelRadius (resolution p k)
            (resolution p k ^ (sizeBudget p : ℝ)) H : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have hI := Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.inter hA hT
          hNM1 hR1
        exact Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.mono hI
          (format_budget (hN k) (sizeBudget p) H) le_rfl
    · -- inverse-subpower retained mass
      have hlo : ENNReal.ofReal ((loss p k)⁻¹) ≤ taggedLaw p k univ := by
        rw [taggedLaw_apply p k MeasurableSet.univ]
        exact hmass0
      have hm : MeasurableSet (tagLabel (resolution p k) H ⁻¹' T k) :=
        (Set.to_countable _).measurableSet.preimage
          (measurable_fst.prodMk ((measurable_scalarLabel _ _).comp measurable_snd))
      have hsel : taggedLaw p k (tagLabel (resolution p k) H ⁻¹' T k) =
          ∑ a, ENNReal.ofReal (weight p k a) * law (withEvents p K' M' D' E') k a univ := by
        rw [taggedLaw_apply p k hm]
        apply Finset.sum_congr rfl
        intro a _
        rw [law_withEvents, Measure.restrict_apply_univ, selected_mass_eq p hp H T k a]
        rfl
      show ENNReal.ofReal (K' k)⁻¹ ≤
        ∑ a, ENNReal.ofReal (weight p k a) * law (withEvents p K' M' D' E') k a univ
      rw [← hsel]
      exact Submission.Obl.k4_tempered_grid_selection.inverse_mass_after_finite_loss
        (by linarith [hp.1.2.2.1.1 k]) (hB k) hlo (hmass k)
  · -- typical windows at every clamped rational depth
    refine ⟨(C : ℝ), fun k q => a' k (index q), fun k q => ha' k (index q), ?_⟩
    intro q τ hτ
    let d : ℝ := min 1 (τ / 4)
    let c : ℝ := d / 2
    have hd : 0 < d := lt_min (by norm_num) (by linarith)
    have hc : 0 < c := by dsimp [c]; positivity
    have hsmall : ∀ᶠ k in atTop, 2 * resolution p k ^ (-d) < resolution p k ^ (-c) :=
      Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
        (by dsimp [c]; linarith) 2
    have herr : ∀ᶠ k in atTop,
        resolution p k ^ (-1 : ℝ) + resolution p k ^ (-(τ / 4)) ≤ resolution p k ^ (-c) := by
      filter_upwards [hsmall] with k hk
      have hn1 : 1 ≤ resolution p k := by linarith [hN k]
      have h1 : resolution p k ^ (-1 : ℝ) ≤ resolution p k ^ (-d) :=
        Real.rpow_le_rpow_of_exponent_le hn1
          (by dsimp [d]; linarith [min_le_left (1 : ℝ) (τ / 4)])
      have h2 : resolution p k ^ (-(τ / 4)) ≤ resolution p k ^ (-d) :=
        Real.rpow_le_rpow_of_exponent_le hn1
          (by dsimp [d]; linarith [min_le_right (1 : ℝ) (τ / 4)])
      linarith
    have hδτ : ∀ᶠ k in atTop, δ k < τ / 4 :=
      hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < τ / 4))
    have hfactor : ∀ᶠ k in atTop, 2 ≤ resolution p k ^ (τ / 4) :=
      ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < τ / 4)).comp hNt).eventually
        (eventually_ge_atTop 2)
    refine ⟨c, hc, ?_⟩
    filter_upwards [hfit (index q), hδτ, hfactor, herr, happ] with k hkfit hkδ hkfactor hkerr
      hkapp
    set r := clamp (length p) q with hrdef
    have hr : r ∈ Icc 0 (length p) :=
      Submission.Obl.k4_native_grid_profile_extension.clamp_mem hL q
    have hd' := hasDensities_withEvents p hp K' M' D' E' hE'sub
    have hm : MeasurableSet {z : WorldState (withEvents p K' M' D' E') k |
        sampledDensity (withEvents p K' M' D' E') r k z <
            ENNReal.ofReal (resolution p k ^ (-(a' k (index q)) - τ)) ∨
          ENNReal.ofReal (resolution p k ^ (-(a' k (index q)) + τ)) <
            sampledDensity (withEvents p K' M' D' E') r k z} :=
      (measurableSet_lt (measurable_sampledDensity hd' _ hr.1 hr.2) measurable_const).union
        (measurableSet_lt measurable_const (measurable_sampledDensity hd' _ hr.1 hr.2))
    show worldLaw (withEvents p K' M' D' E') k {z : WorldState (withEvents p K' M' D' E') k |
        sampledDensity (withEvents p K' M' D' E') r k z <
            ENNReal.ofReal (resolution p k ^ (-(a' k (index q)) - τ)) ∨
          ENNReal.ofReal (resolution p k ^ (-(a' k (index q)) + τ)) <
            sampledDensity (withEvents p K' M' D' E') r k z} ≤
      ENNReal.ofReal (resolution p k ^ (-c))
    rw [worldLaw_apply _ k hm]
    have hworld : ∀ a : Fin (p.1 k),
        law (withEvents p K' M' D' E') k a
          {z | ((a, z) : WorldState (withEvents p K' M' D' E') k) ∈
            {z : WorldState (withEvents p K' M' D' E') k |
              sampledDensity (withEvents p K' M' D' E') r k z <
                  ENNReal.ofReal (resolution p k ^ (-(a' k (index q)) - τ)) ∨
                ENNReal.ofReal (resolution p k ^ (-(a' k (index q)) + τ)) <
                  sampledDensity (withEvents p K' M' D' E') r k z}} ≤
          ENNReal.ofReal (resolution p k ^ (-1 : ℝ)) +
            ENNReal.ofReal (resolution p k ^ (-(τ / 4))) := by
      intro a
      obtain ⟨hv, happrox⟩ := hkapp a r hr.1 hr.2
      have hEm : MeasurableSet (event p k a) := ((hp.2 k).2.2.2.1 a).2.2.2.1
      have hG := obsDensity_sub p hp k a (subset_refl (event p k a)) (resolution p k) r
      have hG₀ := obsDensity_sub p hp k a (hE'sub k a) (resolution p k) r
      have hfit₀ : ∀ᵐ z ∂(law (withEvents p K' M' D' E') k a),
          |Submission.Obl.k4_tempered_grid_selection.boundedExponent (C : ℝ) (resolution p k)
              (g k a r (scalarLabel (resolution p k) H z)) - a' k (index q)| ≤ δ k := by
        filter_upwards [ae_restrict_mem (measurableSet_selectedEvent p hp H T k a)] with z hz
        have hzT : tagLabel (resolution p k) H ((a : ℕ), z) ∈ T k := hz.2.1
        have h := hkfit _ hzT
        simp only [tableExponent, tagLabel, a.isLt, dite_eq_left, Fin.eta, hindex q] at h
        exact h.le
      have hband := Submission.Obl.k4_tempered_grid_selection.approximation_band_transfer
        reference (law p k a) (law (withEvents p K' M' D' E') k a)
        (Measure.restrict_mono_set _ (hE'sub k a)) (law_le_one hp k a)
        (observe (resolution p k) r) (measurable_observe _ _) _ _ hG.1 hG₀.1 hG.2 hG₀.2
        (resolution p k) (C : ℝ) (a' k (index q)) (δ k) τ (by linarith [hN k]) hτ hkδ.le
        hkfactor (fun z => g k a r (scalarLabel (resolution p k) H z)) (fun z => hv _) hfit₀
        (ENNReal.ofReal (resolution p k ^ (-1 : ℝ))) (happrox _ hG.1 hG.2)
      exact hband
    calc ∑ a, ENNReal.ofReal (weight p k a) * law (withEvents p K' M' D' E') k a _
        ≤ ∑ a : Fin (p.1 k), ENNReal.ofReal (weight p k a) *
            (ENNReal.ofReal (resolution p k ^ (-1 : ℝ)) +
              ENNReal.ofReal (resolution p k ^ (-(τ / 4)))) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_right (hworld a) _
      _ = (∑ a : Fin (p.1 k), ENNReal.ofReal (weight p k a)) *
            (ENNReal.ofReal (resolution p k ^ (-1 : ℝ)) +
              ENNReal.ofReal (resolution p k ^ (-(τ / 4)))) := by
          rw [Finset.sum_mul]
      _ = ENNReal.ofReal (resolution p k ^ (-1 : ℝ)) +
            ENNReal.ofReal (resolution p k ^ (-(τ / 4))) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (hp.2 k).2.1 a), (hp.2 k).2.2.1,
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (resolution p k ^ (-c)) := by
          rw [← ENNReal.ofReal_add (Real.rpow_nonneg (by linarith [hN k]) _)
            (Real.rpow_nonneg (by linarith [hN k]) _)]
          exact ENNReal.ofReal_le_ofReal hkerr

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
