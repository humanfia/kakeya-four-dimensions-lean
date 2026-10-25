import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.PoolSetup
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.PoolAbstract

/-!
# Palette pooling over deep labels split by signal groups

Adapted from accepted o248 (`k4_wide_velocity_lists_scalar_preparation/Pool.lean`,
`pooled_of_setup`). The abstract pooling `pooled_terminal` of o248 is reused. The
pooled law is the frame law outside the bad set of the deep confinement; the
pieces are deep label regions inside one signal group, so every label is counted
at most twice in the reference budget.
-/

set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_wide_velocity_lists_scalar_preparation (pooled_terminal)

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

namespace ListFrame

variable {k : ℕ} {r v m ε : ℝ} (f : p.ListFrame k r v m ε)

/-- Almost every frame event is good. -/
theorem ae_goodSet (h : p.Valid) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤) :
    ∀ᵐ ω ∂f.law, ω ∈ f.goodSet := by
  have hρμ : p.ρ k ≤ p.μ k := (h.basic k).2.2.2.2.1
  have hbase := f.ae_of_original hρμ h0 ht (h.base_bound_ae k)
  have hsupp : ∀ᵐ ω ∂f.law, ω ∈ (univ : Set α) ×ˢ Icc (0 : ℝ) 1 :=
    ae_iff.mpr f.time_support
  have hone : ∀ᵐ ω ∂f.law, ω.2 ≠ 1 := by
    apply ae_iff.mpr
    have := f.law_time_countable_null (Set.countable_singleton (1 : ℝ))
    simpa using this
  filter_upwards [f.good_ae, hbase, hsupp, hone] with ω hg hb hs h1
  exact ⟨hg, ⟨hs.2.1, lt_of_le_of_ne hs.2.2 h1⟩, hb⟩

/-- The deep labels cover almost every frame event. -/
theorem ae_cover (h : p.Valid) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤) {s : ℝ}
    (hcov : ∀ᵐ ω ∂p.μ k, ∃ i, ω.1 ∈ p.B k s i ∧ ω.2 ∈ block (p.T k s) (p.j k s i)) :
    ∀ᵐ ω ∂f.law, ∃ i, ω ∈ f.region s i := by
  have hρμ : p.ρ k ≤ p.μ k := (h.basic k).2.2.2.2.1
  have h1 := f.ae_of_original hρμ h0 ht hcov
  have h2 : ∀ᵐ ω ∂f.law, ∀ j : ℕ, f.t₀ + f.q * ω.2 ≠ ((j : ℝ) + 1) / 2 ^ p.T k s := by
    apply ae_iff.mpr
    apply measure_mono_null _ (f.law_time_countable_null
      (Set.countable_range (fun j : ℕ => (((j : ℝ) + 1) / 2 ^ p.T k s - f.t₀) / f.q)))
    intro ω hω
    simp only [not_forall, not_not, mem_ofPred_eq] at hω
    obtain ⟨j, hj⟩ := hω
    refine ⟨j, ?_⟩
    simp only
    rw [← hj]
    field_simp [f.q_pos.ne']
    ring
  filter_upwards [h1, h2] with ω hω hne
  obtain ⟨i, hB, hI⟩ := hω
  exact ⟨i, hB, hI.1, lt_of_le_of_ne hI.2 (hne _)⟩

/-- The deep velocity bins of one deep label are dominated by its full original
reference weight relative to the parent reference, times the original palette. -/
theorem region_vel_le (h : p.Valid) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤) {s : ℝ}
    (hB : ∀ i, MeasurableSet (p.B k s i))
    (hvel : ∀ (i : Fin (p.n k s)) (v₀ : ℤ), p.μ k {ω | ω.1 ∈ p.B k s i ∧
      ω.2 ∈ block (p.T k s) (p.j k s i) ∧ ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k s)⁻¹) * p.ν k (p.A k s i) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀})
    (i : Fin (p.n k s)) (a : ℤ) :
    f.law (f.region s i ∩ p.velBin k m ⁻¹' {a}) ≤
      (f.weight⁻¹ * ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k s)⁻¹) *
        p.ν k (p.A k s i)) * p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = a} := by
  have hρμ : p.ρ k ≤ p.μ k := (h.basic k).2.2.2.2.1
  have hvelm : Measurable (p.velBin k m) :=
    (((measurable_pi_apply 3).comp ((h.basic k).1.comp measurable_fst)).div_const _).floor
  set E : Set (α × ℝ) := {ω | ω.1 ∈ p.B k s i ∧
    ω.2 ∈ block (p.T k s) (p.j k s i) ∧ ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = a} with hE
  have hEm : MeasurableSet E := by
    refine ((hB i).preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter ?_)
    exact hvelm (measurableSet_singleton a)
  have hsub : f.region s i ∩ p.velBin k m ⁻¹' {a} ⊆ f.timeMap ⁻¹' E := by
    rintro ω ⟨hωR, hωa⟩
    exact ⟨hωR.1, Ico_subset_Icc_self hωR.2, hωa⟩
  calc _ ≤ f.law (f.timeMap ⁻¹' E) := measure_mono hsub
    _ ≤ f.weight⁻¹ * p.μ k E := f.law_preimage_le hρμ h0 ht hEm
    _ ≤ f.weight⁻¹ * (ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k s)⁻¹) *
          p.ν k (p.A k s i) * p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = a}) := by
        gcongr
        exact hvel i a
    _ = _ := by ring

/-- Pooling at one deep depth `s`, given the original assignment facts used and
the native-signal confinement of the deep labels in two groups outside a small
bad set. -/
theorem pooled_of_setup (h : p.Valid) {s : ℝ}
    (hAr : ∀ i i', i ≠ i' → p.j k r i = p.j k r i' →
      Disjoint (p.A k r i) (p.A k r i'))
    (hBAr : ∀ i, p.B k r i ⊆ p.A k r i)
    (hνpar : p.ν k (p.A k r f.parent) ≠ 0)
    (hmeas : ∀ i, MeasurableSet (p.A k s i) ∧ MeasurableSet (p.B k s i) ∧
      p.B k s i ⊆ p.A k s i)
    (hdisjs : ∀ i i', i ≠ i' → p.j k s i = p.j k s i' →
      Disjoint (p.A k s i) (p.A k s i'))
    (hvel : ∀ (i : Fin (p.n k s)) (v₀ : ℤ), p.μ k {ω | ω.1 ∈ p.B k s i ∧
      ω.2 ∈ block (p.T k s) (p.j k s i) ∧ ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k s)⁻¹) * p.ν k (p.A k s i) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀})
    (hcov : ∀ᵐ ω ∂p.μ k, ∃ i, ω.1 ∈ p.B k s i ∧ ω.2 ∈ block (p.T k s) (p.j k s i))
    (hnest : ∀ i : Fin (p.n k s), ∃ h : Fin (p.n k r), p.A k s i ⊆ p.A k r h ∧
      block (p.T k s) (p.j k s i) ⊆ block (p.T k r) (p.j k r h))
    {D : ℝ} (hD0 : 0 ≤ D)
    (hdiam : ∀ i : Fin (p.n k s), ∀ l ∈ p.B k s i, ∀ l' ∈ p.B k s i,
      ∀ τ ∈ block (p.T k s) (p.j k s i), ∀ τ' ∈ block (p.T k s) (p.j k s i),
      ∀ e : Fin 3, |p.base k l τ e - p.base k l' τ' e| ≤ D)
    (hN2 : 2 * D * (p.N k ^ (m / 10)) ^ 2 ≤ p.N k ^ (-m))
    (hN3 : 216 * p.N k ^ (m / 10) * (2 * p.K k) ^ 2 * D ≤ p.N k ^ (-(r + v)) / 2)
    (hN4 : D ≤ 1)
    (grp : α × ℝ → Fin 2) (hgrp : Measurable grp)
    (bad : Set (α × ℝ)) (hbad : MeasurableSet bad)
    (hbadmass : f.law bad ≤ ENNReal.ofReal (p.N k ^ (-ε) / 4))
    (hsig : ∀ (i : Fin (p.n k s)) (ω ω' : α × ℝ),
      ω.1 ∈ p.B k s i → ω'.1 ∈ p.B k s i →
      f.t₀ + f.q * ω.2 ∈ block (p.T k s) (p.j k s i) →
      f.t₀ + f.q * ω'.2 ∈ block (p.T k s) (p.j k s i) →
      ω ∉ bad → ω' ∉ bad → grp ω = grp ω' →
      |p.signal k ω.1 (f.t₀ + f.q * ω.2) - p.signal k ω'.1 (f.t₀ + f.q * ω'.2)| ≤
        p.N k ^ (-(r + v)) / 2) :
    ∃ τ : Measure (α × ℝ), τ ≤ f.law ∧
      ENNReal.ofReal (p.N k ^ (-ε) / 2) ≤ τ univ ∧
      ∃ terminal : Finset ((Fin 2 → ℤ) × ℤ),
        (terminal.card : ℝ) * (p.N k ^ (-m)) ^ 2 ≤
          216 * p.K k * p.N k ^ (2 * ε) * p.N k ^ (p.d * v) ∧
        ∀ᵐ ω ∂τ, f.outState ω ∈ terminal := by
  classical
  have hK1 : 1 ≤ p.K k := h.subpower.1 k
  have hKpos : 0 < p.K k := by linarith
  have hNpos : 0 < p.N k := by linarith [h.scale k]
  have hνprob : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  have hπprob : IsProbabilityMeasure (p.π k) := (h.basic k).2.2.1
  have h0 : f.weight ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr f.q_pos).ne' hνpar
  have ht : f.weight ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hfin : IsFiniteMeasure f.law := f.isFiniteMeasure_law
  set law' : Measure (α × ℝ) := f.law.restrict badᶜ with hlaw'
  have hfin' : IsFiniteMeasure law' := by rw [hlaw']; infer_instance
  have hle' : law' ≤ f.law := by rw [hlaw']; exact Measure.restrict_le_self
  have hnotbad : ∀ᵐ ω ∂law', ω ∉ bad := by
    rw [hlaw']
    exact ae_restrict_mem hbad.compl
  have hσm : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hNpos _
  -- the binned palette
  have hbin : Measurable (fun w : ℝ => ⌊w / p.N k ^ (-m)⌋) :=
    (measurable_id.div_const _).floor
  let πb : Measure ℤ := (p.π k).map (fun w : ℝ => ⌊w / p.N k ^ (-m)⌋)
  have hπb : ∀ a : ℤ, πb {a} = p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = a} := by
    intro a
    rw [Measure.map_apply hbin (measurableSet_singleton a)]
    rfl
  have hπuniv : πb univ ≤ 1 := by
    rw [Measure.map_apply hbin MeasurableSet.univ, preimage_univ, measure_univ]
  have hvelm : Measurable (p.velBin k m) :=
    (((measurable_pi_apply 3).comp ((h.basic k).1.comp measurable_fst)).div_const _).floor
  have hgood := f.ae_goodSet h h0 ht
  have hcover := f.ae_cover h h0 ht hcov
  -- the pieces, indexed through `Fin (n * 2)`
  let e : Fin (p.n k s) × Fin 2 ≃ Fin (p.n k s * 2) := finProdFinEquiv
  let R : Fin (p.n k s * 2) → Set (α × ℝ) := fun j => f.piece s grp (e.symm j)
  let opts : Fin (p.n k s * 2) → Finset ((Fin 2 → ℤ) × ℤ) :=
    fun j => f.pieceOptions s grp bad (e.symm j)
  let Wl : Fin (p.n k s) → ℝ≥0∞ := fun i =>
    f.weight⁻¹ * ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k s)⁻¹) * p.ν k (p.A k s i)
  let W : Fin (p.n k s * 2) → ℝ≥0∞ := fun j => Wl (e.symm j).1
  have hR : ∀ j, MeasurableSet (R j) := fun j =>
    f.measurableSet_piece (fun i => (hmeas i).2.1) hgrp _
  have hdisj : Pairwise (fun j j' => Disjoint (R j) (R j')) := by
    intro j j' hjj'
    exact f.piece_disjoint (fun i => (hmeas i).2.2) hdisjs grp
      (fun hh => hjj' (e.symm.injective hh))
  have hcover' : ∀ᵐ ω ∂law', ∃ j, ω ∈ R j := by
    filter_upwards [ae_mono hle' hcover] with ω hω
    obtain ⟨i, hi⟩ := hω
    refine ⟨e (i, grp ω), ?_⟩
    show ω ∈ f.piece s grp (e.symm (e (i, grp ω)))
    rw [Equiv.symm_apply_apply]
    exact Set.mem_inter hi rfl
  have hopt : ∀ j, ∀ᵐ ω ∂law', ω ∈ R j → f.outState ω ∈ opts j := by
    intro j
    filter_upwards [ae_mono hle' hgood, hnotbad] with ω hωG hωb hωR
    have hωR' : ω ∈ f.piece s grp (e.symm j) := hωR
    have hx : ∃ ω', ω' ∈ f.piece s grp (e.symm j) ∧ ω' ∈ f.goodSet ∧ ω' ∉ bad :=
      ⟨ω, hωR', hωG, hωb⟩
    show f.outState ω ∈ f.pieceOptions s grp bad (e.symm j)
    simp only [pieceOptions, hx, ↓reduceDIte]
    obtain ⟨hR₀, hG₀, hb₀⟩ := Classical.choose_spec hx
    apply f.outState_mem_stateBox hK1 hNpos hD0 hdiam hN2 hN3 hN4 hωR'.1 hωG hR₀.1 hG₀
    apply hsig (e.symm j).1 ω _ hωR'.1.1 hR₀.1.1 (Ico_subset_Icc_self hωR'.1.2)
      (Ico_subset_Icc_self hR₀.1.2) hωb hb₀
    have h1 : grp ω = (e.symm j).2 := hωR'.2
    have h2 : grp (Classical.choose hx) = (e.symm j).2 := hR₀.2
    exact h1.trans h2.symm
  have hW : ∀ j a, law' (R j ∩ p.velBin k m ⁻¹' {a}) ≤ W j * πb {a} := by
    intro j a
    calc law' (R j ∩ p.velBin k m ⁻¹' {a})
        ≤ f.law (f.region s (e.symm j).1 ∩ p.velBin k m ⁻¹' {a}) :=
          (hle' _).trans (measure_mono (inter_subset_inter_left _ inter_subset_left))
      _ ≤ _ := f.region_vel_le h h0 ht (fun i => (hmeas i).2.1) hvel _ a
      _ = W j * πb {a} := by rw [hπb]
  -- the velocity-wise lists
  set M : ℝ := p.N k ^ ε * p.N k ^ (p.d * v) / (p.N k ^ (-m)) ^ 2 with hMdef
  have hL : ∀ a, (((f.lists a).card : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal M := by
    intro a
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    rw [hMdef, le_div_iff₀ (by positivity)]
    exact f.lists_bound a
  set δ : ℝ := p.N k ^ (-ε) / (216 * p.K k) with hδdef
  have hδpos : 0 < δ := by positivity
  obtain ⟨τ, hτ, hmass, terminal, hcard, hae⟩ := pooled_terminal law' f.outState
    f.measurable_outState (p.velBin k m) hvelm πb hπuniv R hR hdisj hcover' opts hopt W hW
    f.lists (ENNReal.ofReal M) ENNReal.ofReal_ne_top hL (ae_mono hle' f.lists_ae)
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδpos).ne' ENNReal.ofReal_ne_top
  refine ⟨τ, hτ.trans hle', ?_, terminal, ?_, hae⟩
  · -- the reference budget: each deep label is counted once per group
    have hbudget : ∑ j, ((opts j).card : ℝ≥0∞) * W j ≤ ENNReal.ofReal (54 * p.K k) := by
      have hre : ∑ j, ((opts j).card : ℝ≥0∞) * W j =
          ∑ x : Fin (p.n k s) × Fin 2,
            ((f.pieceOptions s grp bad x).card : ℝ≥0∞) * Wl x.1 :=
        Equiv.sum_comp e.symm
          (fun x => ((f.pieceOptions s grp bad x).card : ℝ≥0∞) * Wl x.1)
      rw [hre]
      let P : Fin (p.n k s) → Prop := fun i => ∃ ω, ω ∈ f.region s i ∧ ω ∈ f.goodSet
      have hterm : ∀ x : Fin (p.n k s) × Fin 2,
          ((f.pieceOptions s grp bad x).card : ℝ≥0∞) * Wl x.1 ≤
            if P x.1 then 27 * Wl x.1 else 0 := by
        intro x
        obtain ⟨hc27, hne⟩ := f.pieceOptions_card_le s grp bad x
        by_cases hP : P x.1
        · simp only [hP, ↓reduceIte]
          exact mul_le_mul' (by exact_mod_cast hc27) le_rfl
        · simp only [hP, ↓reduceIte]
          have hempty : f.pieceOptions s grp bad x = ∅ := by
            by_contra hne'
            exact hP (hne (Finset.nonempty_iff_ne_empty.mpr hne'))
          simp [hempty]
      have hS := f.deep_weight_budget hAr hBAr (fun i => (hmeas i).2.2) (fun i => (hmeas i).1)
        hdisjs hnest hKpos.le h0 ht (Finset.univ.filter P)
        (fun i hi => (Finset.mem_filter.mp hi).2)
      calc _ ≤ ∑ x : Fin (p.n k s) × Fin 2, (if P x.1 then 27 * Wl x.1 else 0) :=
            Finset.sum_le_sum (fun x _ => hterm x)
        _ = ∑ i : Fin (p.n k s), ∑ _g : Fin 2, (if P i then 27 * Wl i else 0) :=
            Fintype.sum_prod_type _
        _ = ∑ i : Fin (p.n k s), 2 * (if P i then 27 * Wl i else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
        _ = 54 * ∑ i ∈ Finset.univ.filter P, Wl i := by
            rw [Finset.sum_filter, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs
            · ring
            · simp
        _ ≤ 54 * ENNReal.ofReal (p.K k) := by gcongr
        _ = ENNReal.ofReal (54 * p.K k) := by
            rw [ENNReal.ofReal_mul (by norm_num)]
            norm_num
    have hcost : ENNReal.ofReal δ * ENNReal.ofReal (54 * p.K k) =
        ENNReal.ofReal (p.N k ^ (-ε) / 4) := by
      rw [← ENNReal.ofReal_mul hδpos.le, hδdef]
      congr 1
      field_simp
      ring
    have h1 : law' univ ≤ τ univ + ENNReal.ofReal (p.N k ^ (-ε) / 4) := by
      calc law' univ ≤ _ := hmass
        _ ≤ τ univ + ENNReal.ofReal δ * ENNReal.ofReal (54 * p.K k) := by gcongr
        _ = _ := by rw [hcost]
    have h2 : f.law univ ≤ ENNReal.ofReal (p.N k ^ (-ε) / 4) + law' univ := by
      rw [hlaw', Measure.restrict_apply_univ]
      exact (measure_univ_le_add_compl bad).trans (add_le_add hbadmass le_rfl)
    have h3 : ENNReal.ofReal (p.N k ^ (-ε)) ≤
        τ univ + ENNReal.ofReal (p.N k ^ (-ε) / 2) := by
      calc ENNReal.ofReal (p.N k ^ (-ε)) ≤ f.law univ := f.mass_lower
        _ ≤ ENNReal.ofReal (p.N k ^ (-ε) / 4) +
            (τ univ + ENNReal.ofReal (p.N k ^ (-ε) / 4)) :=
            h2.trans (add_le_add le_rfl h1)
        _ = τ univ + (ENNReal.ofReal (p.N k ^ (-ε) / 4) +
            ENNReal.ofReal (p.N k ^ (-ε) / 4)) := by ring
        _ = τ univ + ENNReal.ofReal (p.N k ^ (-ε) / 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 2
            ring
    have hsum : ENNReal.ofReal (p.N k ^ (-ε)) =
        ENNReal.ofReal (p.N k ^ (-ε) / 2) + ENNReal.ofReal (p.N k ^ (-ε) / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [hsum] at h3
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h3
  · have hc : (terminal.card : ℝ≥0∞) ≤ ENNReal.ofReal (δ⁻¹ * M) := by
      rw [ENNReal.ofReal_mul (inv_pos.mpr hδpos).le, ENNReal.ofReal_inv_of_pos hδpos]
      exact hcard
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hc
    have hδinv : δ⁻¹ = 216 * p.K k * p.N k ^ ε := by
      rw [hδdef, inv_div, Real.rpow_neg hNpos.le, div_inv_eq_mul]
    have hξ2 : (p.N k ^ (-m)) ^ 2 ≠ 0 := by positivity
    have h2ε : p.N k ^ (2 * ε) = p.N k ^ ε * p.N k ^ ε := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    calc (terminal.card : ℝ) * (p.N k ^ (-m)) ^ 2 ≤ δ⁻¹ * M * (p.N k ^ (-m)) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 216 * p.K k * p.N k ^ ε * (p.N k ^ ε * p.N k ^ (p.d * v)) := by
          rw [hδinv, hMdef, mul_assoc, div_mul_cancel₀ _ hξ2]
      _ = 216 * p.K k * p.N k ^ (2 * ε) * p.N k ^ (p.d * v) := by
          rw [h2ε]
          ring

end ListFrame

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
