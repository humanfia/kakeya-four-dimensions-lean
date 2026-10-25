-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.NativePool.Core; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- The pooling below follows `ListFrame.pooled_of_setup` of this checkout
   (`Lists/Pool.lean`, itself adapted from accepted o248), with the original incidence measure of
   one original block in place of a list frame and the native fine state in place of the scalar
   output state. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.NativePool.Geometry

/-!
# Native fine-state pruning inside one original block, at one index

Fix an index `k`, an original block `Q` at depth `r`, an intermediate depth `s` whose true
blocks carry two native-signal groups `E`, and a deep depth `t`. The pieces are the deep labels
at depth `t` inside one physical group. Off a bad set (the physical bad set of the groups,
dyadic times, and the complement of the block), two incidences of one piece have native
states within one step in each coordinate, so each piece lists at most `81` states; the deep
original palette caps dominate the velocity bins of each piece by `K q_t ν(A_D)`; and the deep
labels met in the block pack into its reference `q_r ν(A_Q)`. Pruning (accepted o236) then gives
conditional palette domination with constant `324 K / ϑ` at a loss of `ϑ / 2` times the
reference, and the bad set costs at most another `ϑ / 2` times the reference.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α]

/-- A native pooling piece: a deep label region inside one signal group. -/
def nativePiece (p : Parent α) (k : ℕ) (t : ℝ) (grp : α × ℝ → Fin 2)
    (x : Fin (p.n k t) × Fin 2) : Set (α × ℝ) :=
  p.physRegion k t x.1 ∩ grp ⁻¹' {x.2}

/-- **Native fine-state pruning at one index.** -/
theorem Valid.nativePrune_core {p : Parent α} (h : p.Valid) {k : ℕ}
    {r s t R δb δs mv ϑ : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hϑ : 0 < ϑ) (hδb : 0 < δb) (hδs : 0 < δs)
    (hat_r : p.AtDepth k r R) (hat_s : p.AtDepth k s R) (hat_t : p.AtDepth k t R)
    (hnest_rs : ∀ i : Fin (p.n k s), ∃ h : Fin (p.n k r), p.A k s i ⊆ p.A k r h ∧
      block (p.T k s) (p.j k s i) ⊆ block (p.T k r) (p.j k r h))
    (hnest_rt : ∀ i : Fin (p.n k t), ∃ h : Fin (p.n k r), p.A k t i ⊆ p.A k r h ∧
      block (p.T k t) (p.j k t i) ⊆ block (p.T k r) (p.j k r h))
    (hnest_st : ∀ i : Fin (p.n k t), ∃ h : Fin (p.n k s), p.A k t i ⊆ p.A k s h ∧
      block (p.T k t) (p.j k t i) ⊆ block (p.T k s) (p.j k s h))
    (E : Fin (p.n k s) → Fin 2 → Set (α × ℝ)) (hEm : ∀ i e, MeasurableSet (E i e))
    (hEsub : ∀ i e, E i e ⊆ p.B k s i ×ˢ block (p.T k s) (p.j k s i))
    {η : ℝ≥0∞}
    (hEloss : ∀ i, p.μ k ((p.B k s i ×ˢ block (p.T k s) (p.j k s i)) \ ⋃ e, E i e) ≤
      p.μ k (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) * η)
    (hloss : ENNReal.ofReal (p.K k) * η ≤ ENNReal.ofReal (ϑ / 2))
    (hsig : ∀ (i : Fin (p.n k s)) (e : Fin 2), ∀ z ∈ E i e, ∀ z' ∈ E i e,
      (∀ c : Fin 3, |p.base k z.1 z.2 c - p.base k z'.1 z'.2 c| ≤
        6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) →
      |p.signal k z.1 z.2 - p.signal k z'.1 z'.2| ≤ δs)
    (hbase : 3 * p.K k * (6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) / p.blockWidth k r ≤ δb)
    (hcap : ∀ (i : Fin (p.n k t)) (a : ℤ), p.μ k {ω | ω.1 ∈ p.B k t i ∧
      ω.2 ∈ block (p.T k t) (p.j k t i) ∧ ⌊p.b k ω.1 3 / (p.N k ^ (-mv))⌋ = a} ≤
      ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k t)⁻¹) * p.ν k (p.A k t i) *
        p.π k {x : ℝ | ⌊x / (p.N k ^ (-mv))⌋ = a})
    (Q : Fin (p.n k r)) (θ : Measure (α × ℝ)) (hθ : θ ≤ p.μ k)
    (hθsupp : ∀ᵐ ω ∂θ, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q)) :
    ∃ θ' : Measure (α × ℝ), θ' ≤ θ ∧
      θ univ ≤ θ' univ +
        ENNReal.ofReal ϑ * (ENNReal.ofReal (p.blockLen k r) * p.ν k (p.A k r Q)) ∧
      ∀ (σ : Fin 4 → ℤ) (j : ℤ),
        θ' {ω | p.nativeState k r Q δb δs ω = σ ∧ ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋ = j} ≤
          ENNReal.ofReal (324 * p.K k / ϑ) *
            θ' {ω | p.nativeState k r Q δb δs ω = σ} *
            p.π k {x | ⌊x / p.N k ^ (-mv)⌋ = j} := by
  classical
  have hK1 : 1 ≤ p.K k := h.subpower.1 k
  have hKpos : 0 < p.K k := by linarith
  have hN1 : 1 ≤ p.N k := by linarith [h.scale k]
  have hNpos : 0 < p.N k := by linarith
  have hb : Measurable (p.b k) := (h.basic k).1
  have hℓ := h.transverse_pos
  have hνprob : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  have hmeas_r := hat_r.2.2.1
  have hdisj_r := hat_r.2.2.2.1
  have hmeas_s := hat_s.2.2.1
  have hdisj_s := hat_s.2.2.2.1
  have hmeas_t := hat_t.2.2.1
  have hdisj_t := hat_t.2.2.2.1
  have hBA_s : ∀ i, p.B k s i ⊆ p.A k s i := fun i => (hmeas_s i).2.2
  have hBA_t : ∀ i, p.B k t i ⊆ p.A k t i := fun i => (hmeas_t i).2.2
  -- the parent region and the bad set
  set Par : Set (α × ℝ) := p.B k r Q ×ˢ block (p.T k r) (p.j k r Q) with hParDef
  have hParm : MeasurableSet Par := (hmeas_r Q).2.1.prod measurableSet_Icc
  set Dy : Set (α × ℝ) :=
    {z | z.2 ∈ dyadicTimes (p.T k r)} ∪ {z | z.2 ∈ dyadicTimes (p.T k t)} with hDyDef
  have hDym : MeasurableSet Dy := (measurableSet_dyadic _).union (measurableSet_dyadic _)
  have hDy0 : p.μ k Dy = 0 := measure_union_null (h.dyadic_null k _) (h.dyadic_null k _)
  set bad : Set (α × ℝ) := (p.physBad k s E ∪ Dy) ∪ Parᶜ with hbadDef
  have hbadm : MeasurableSet bad :=
    ((measurableSet_physBad (fun i => (hmeas_s i).2.1) hEm).union hDym).union hParm.compl
  set law' : Measure (α × ℝ) := θ.restrict badᶜ with hlaw'
  have hle' : law' ≤ θ := Measure.restrict_le_self
  have hnotbad : ∀ᵐ ω ∂law', ω ∉ bad := ae_restrict_mem hbadm.compl
  -- the native state and the velocity bin
  have hst : Measurable (p.nativeState k r Q δb δs) := p.measurable_nativeState hb r Q δb δs
  have hvel : Measurable (fun ω : α × ℝ => ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋) :=
    (((measurable_pi_apply 3).comp (hb.comp measurable_fst)).div_const _).floor
  have hbin : Measurable (fun x : ℝ => ⌊x / p.N k ^ (-mv)⌋) :=
    (measurable_id.div_const _).floor
  let πb : Measure ℤ := (p.π k).map (fun x : ℝ => ⌊x / p.N k ^ (-mv)⌋)
  have hπb : ∀ a : ℤ, πb {a} = p.π k {x : ℝ | ⌊x / p.N k ^ (-mv)⌋ = a} := by
    intro a
    rw [Measure.map_apply hbin (measurableSet_singleton a)]
    rfl
  -- the pieces
  have hpiecem : ∀ x, MeasurableSet (p.nativePiece k t (physGrp E) x) := fun x =>
    (measurableSet_physRegion (fun i => (hmeas_t i).2.1) x.1).inter
      ((measurable_physGrp hEm) (measurableSet_singleton x.2))
  have hpiecedisj : Pairwise (fun x x' =>
      Disjoint (p.nativePiece k t (physGrp E) x) (p.nativePiece k t (physGrp E) x')) := by
    intro x x' hxx'
    rw [Set.disjoint_left]
    intro ω hω hω'
    by_cases hi : x.1 = x'.1
    · have hg : x.2 ≠ x'.2 := fun hg => hxx' (Prod.ext hi hg)
      have h1 : physGrp E ω = x.2 := hω.2
      have h2 : physGrp E ω = x'.2 := hω'.2
      exact hg (h1.symm.trans h2)
    · exact Set.disjoint_left.mp (physRegion_disjoint hBA_t hdisj_t hi) hω.1 hω'.1
  -- two incidences of one piece outside the bad set have nearby native states
  have hbox : ∀ x, ∀ ω ω₀, ω ∈ p.nativePiece k t (physGrp E) x → ω ∉ bad →
      ω₀ ∈ p.nativePiece k t (physGrp E) x → ω₀ ∉ bad →
      p.nativeState k r Q δb δs ω ∈ NativePool.nativeBox (p.nativeState k r Q δb δs ω₀) := by
    intro x ω ω₀ hω hωb hω₀ hω₀b
    have hωP : ω ∉ p.physBad k s E := fun hh => hωb (Or.inl (Or.inl hh))
    have hω₀P : ω₀ ∉ p.physBad k s E := fun hh => hω₀b (Or.inl (Or.inl hh))
    have hωR : ω ∈ p.physRegion k t x.1 := hω.1
    have hω₀R : ω₀ ∈ p.physRegion k t x.1 := hω₀.1
    have hωB : ω.1 ∈ p.B k t x.1 := hωR.1
    have hω₀B : ω₀.1 ∈ p.B k t x.1 := hω₀R.1
    have hωI : ω.2 ∈ block (p.T k t) (p.j k t x.1) := Ico_subset_Icc_self hωR.2
    have hω₀I : ω₀.2 ∈ block (p.T k t) (p.j k t x.1) := Ico_subset_Icc_self hω₀R.2
    obtain ⟨h', hA', hI'⟩ := hnest_st x.1
    have hz : ω ∈ E h' (physGrp E ω) :=
      mem_physGrp hBA_s hdisj_s hEsub (hA' (hBA_t x.1 hωB)) (hI' hωI) hωP
    have hz₀ : ω₀ ∈ E h' (physGrp E ω₀) :=
      mem_physGrp hBA_s hdisj_s hEsub (hA' (hBA_t x.1 hω₀B)) (hI' hω₀I) hω₀P
    have hgrp : physGrp E ω₀ = physGrp E ω := by
      have h1 : physGrp E ω = x.2 := hω.2
      have h2 : physGrp E ω₀ = x.2 := hω₀.2
      rw [h1, h2]
    rw [hgrp] at hz₀
    have hdiam : ∀ c : Fin 3, |p.base k ω.1 ω.2 c - p.base k ω₀.1 ω₀.2 c| ≤
        6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹ := fun c =>
      hat_t.base_diameter hN1 hK1 hℓ ht x.1 (hBA_t x.1 hωB) (hBA_t x.1 hω₀B) hωI hω₀I c
    have hs := hsig h' (physGrp E ω) ω hz ω₀ hz₀ hdiam
    have hc : ∀ e, |p.c k r Q e| ≤ p.K k := (hat_r.2.2.2.2.1 Q).2.2.2.1
    have hq : 0 < p.blockLen k r := by unfold blockLen; positivity
    have hg : 0 < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hNpos _
    have hg1 : p.N k ^ (-p.ℓ * r) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith)
    obtain ⟨hτ, hζ, hu⟩ := p.normalized_diff_le k r Q hK1 hc hq hg hg1 (by positivity) hdiam
    exact p.nativeState_mem_nativeBox k r Q hδb hδs (hτ.trans hbase) (hζ.trans hbase)
      (hu.trans hbase) hs
  -- the pieces, indexed through `Fin (n * 2)`
  let e : Fin (p.n k t) × Fin 2 ≃ Fin (p.n k t * 2) := finProdFinEquiv
  let Rp : Fin (p.n k t * 2) → Set (α × ℝ) := fun j => p.nativePiece k t (physGrp E) (e.symm j)
  let opts : Fin (p.n k t * 2) → Finset (Fin 4 → ℤ) := fun j =>
    NativePool.pieceBox (p.nativePiece k t (physGrp E) (e.symm j)) bad (p.nativeState k r Q δb δs)
  let Wl : Fin (p.n k t) → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k t)⁻¹) * p.ν k (p.A k t i)
  let W : Fin (p.n k t * 2) → ℝ≥0∞ := fun j => Wl (e.symm j).1
  have hR : ∀ j, MeasurableSet (Rp j) := fun j => hpiecem _
  have hdisj : Pairwise (fun j j' => Disjoint (Rp j) (Rp j')) := fun j j' hjj' =>
    hpiecedisj (fun hh => hjj' (e.symm.injective hh))
  have hcov_t := hat_t.2.2.2.2.2.1
  have hcover : ∀ᵐ ω ∂law', ∃ j, ω ∈ Rp j := by
    filter_upwards [ae_mono hle' (ae_mono hθ hcov_t), hnotbad] with ω hω hωb
    obtain ⟨i, hB, hI⟩ := hω
    have hD : ω.2 ∉ dyadicTimes (p.T k t) := fun hd => hωb (Or.inl (Or.inr (Or.inr hd)))
    refine ⟨e (i, physGrp E ω), ?_⟩
    show ω ∈ p.nativePiece k t (physGrp E) (e.symm (e (i, physGrp E ω)))
    rw [Equiv.symm_apply_apply]
    exact ⟨mem_physRegion hB hI hD, rfl⟩
  have hopt : ∀ j, ∀ᵐ ω ∂law', ω ∈ Rp j → p.nativeState k r Q δb δs ω ∈ opts j := by
    intro j
    filter_upwards [hnotbad] with ω hωb hωR
    exact NativePool.mem_pieceBox (hbox (e.symm j)) hωR hωb
  have hW : ∀ j a, law' (Rp j ∩ (fun ω : α × ℝ => ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋) ⁻¹' {a}) ≤
      W j * πb {a} := by
    intro j a
    have hsub : Rp j ∩ (fun ω : α × ℝ => ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋) ⁻¹' {a} ⊆
        {ω | ω.1 ∈ p.B k t (e.symm j).1 ∧ ω.2 ∈ block (p.T k t) (p.j k t (e.symm j).1) ∧
          ⌊p.b k ω.1 3 / (p.N k ^ (-mv))⌋ = a} := by
      rintro ω ⟨hωR, hωa⟩
      have hωR' : ω ∈ p.physRegion k t (e.symm j).1 := hωR.1
      exact ⟨hωR'.1, Ico_subset_Icc_self hωR'.2, hωa⟩
    refine (hle' _).trans ((hθ _).trans ((measure_mono hsub).trans ?_))
    rw [hπb]
    exact hcap (e.symm j).1 a
  -- pruning
  set δ : ℝ := ϑ / (324 * p.K k) with hδdef
  have hδpos : 0 < δ := by positivity
  obtain ⟨θ', hθ', hmass, hdom⟩ := NativePool.pooled_domination law'
    (p.nativeState k r Q δb δs) hst (fun ω : α × ℝ => ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋) hvel πb
    Rp hR hdisj hcover opts hopt W hW (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.mpr hδpos).ne' ENNReal.ofReal_ne_top
  refine ⟨θ', hθ'.trans hle', ?_, ?_⟩
  · set Wq : ℝ≥0∞ := ENNReal.ofReal (p.blockLen k r) * p.ν k (p.A k r Q) with hWqDef
    -- the reference budget: deep labels met in the block, each counted once per group
    have hbudget : ∑ j, ((opts j).card : ℝ≥0∞) * W j ≤ ENNReal.ofReal (162 * p.K k) * Wq := by
      have hre : ∑ j, ((opts j).card : ℝ≥0∞) * W j =
          ∑ x : Fin (p.n k t) × Fin 2,
            ((NativePool.pieceBox (p.nativePiece k t (physGrp E) x) bad
              (p.nativeState k r Q δb δs)).card : ℝ≥0∞) * Wl x.1 :=
        Equiv.sum_comp e.symm (fun x => ((NativePool.pieceBox (p.nativePiece k t (physGrp E) x)
          bad (p.nativeState k r Q δb δs)).card : ℝ≥0∞) * Wl x.1)
      rw [hre]
      let P : Fin (p.n k t) → Prop := fun i => ∃ ω, ω ∈ p.physRegion k t i ∧ ω ∉ bad
      have hterm : ∀ x : Fin (p.n k t) × Fin 2,
          ((NativePool.pieceBox (p.nativePiece k t (physGrp E) x) bad
            (p.nativeState k r Q δb δs)).card : ℝ≥0∞) * Wl x.1 ≤
            if P x.1 then 81 * Wl x.1 else 0 := by
        intro x
        obtain ⟨hc81, hne⟩ := NativePool.pieceBox_card_le (p.nativePiece k t (physGrp E) x) bad
          (p.nativeState k r Q δb δs)
        by_cases hP : P x.1
        · simp only [hP, ↓reduceIte]
          exact mul_le_mul' (by exact_mod_cast hc81) le_rfl
        · simp only [hP, ↓reduceIte]
          have hempty : NativePool.pieceBox (p.nativePiece k t (physGrp E) x) bad
              (p.nativeState k r Q δb δs) = ∅ := by
            by_contra hne'
            obtain ⟨ω, hω, hωb⟩ := hne (Finset.nonempty_iff_ne_empty.mpr hne')
            exact hP ⟨ω, hω.1, hωb⟩
          simp [hempty]
      -- the deep labels with an incidence outside the bad set are nested in `Q`
      have hnestQ : ∀ i, P i → p.A k t i ⊆ p.A k r Q ∧
          block (p.T k t) (p.j k t i) ⊆ block (p.T k r) (p.j k r Q) := by
        rintro i ⟨ω, hω, hωb⟩
        have hωPar : ω ∈ Par := by
          by_contra hc
          exact hωb (Or.inr hc)
        have hDr : ω.2 ∉ dyadicTimes (p.T k r) := fun hd => hωb (Or.inl (Or.inr (Or.inl hd)))
        obtain ⟨h', hA', hI'⟩ := hnest_rt i
        have hh' : h' = Q :=
          block_eq_of_mem hdisj_r (hA' (hBA_t i hω.1)) ((hmeas_r Q).2.2 hωPar.1)
            (hI' (Ico_subset_Icc_self hω.2)) hωPar.2 hDr
        rw [hh'] at hA' hI'
        exact ⟨hA', hI'⟩
      have hpack : ∑ i ∈ Finset.univ.filter P,
          ENNReal.ofReal ((2 : ℝ) ^ p.T k t)⁻¹ * p.ν k (p.A k t i) ≤ Wq := by
        have h1 := nested_packing (p.ν k) (fun i => (hmeas_t i).1) hdisj_t
          (P := p.A k r Q) (I := block (p.T k r) (p.j k r Q)) (Finset.univ.filter P) (by
            intro i hi
            exact hnestQ i (Finset.mem_filter.mp hi).2)
        rw [volume_block] at h1
        exact h1
      have hWl : ∀ i, Wl i = ENNReal.ofReal (p.K k) *
          (ENNReal.ofReal ((2 : ℝ) ^ p.T k t)⁻¹ * p.ν k (p.A k t i)) := by
        intro i
        simp only [Wl]
        rw [ENNReal.ofReal_mul hKpos.le, mul_assoc]
      calc _ ≤ ∑ x : Fin (p.n k t) × Fin 2, (if P x.1 then 81 * Wl x.1 else 0) :=
            Finset.sum_le_sum (fun x _ => hterm x)
        _ = ∑ i : Fin (p.n k t), ∑ _g : Fin 2, (if P i then 81 * Wl i else 0) :=
            Fintype.sum_prod_type _
        _ = ∑ i : Fin (p.n k t), 2 * (if P i then 81 * Wl i else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
        _ = 162 * ∑ i ∈ Finset.univ.filter P, Wl i := by
            rw [Finset.sum_filter, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs
            · ring
            · simp
        _ = 162 * (ENNReal.ofReal (p.K k) * ∑ i ∈ Finset.univ.filter P,
              ENNReal.ofReal ((2 : ℝ) ^ p.T k t)⁻¹ * p.ν k (p.A k t i)) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [hWl]
        _ ≤ 162 * (ENNReal.ofReal (p.K k) * Wq) := by gcongr
        _ = ENNReal.ofReal (162 * p.K k) * Wq := by
            rw [ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
            norm_num
    -- the bad set
    have hbad_le : θ bad ≤ ENNReal.ofReal (p.K k) * Wq * η := by
      have hsub : bad ⊆ (p.physBad k s E ∩ Par) ∪ Dy ∪ Parᶜ := by
        rintro z ((hz | hz) | hz)
        · by_cases hzP : z ∈ Par
          · exact Or.inl (Or.inl ⟨hz, hzP⟩)
          · exact Or.inr hzP
        · exact Or.inl (Or.inr hz)
        · exact Or.inr hz
      have hPar0 : θ Parᶜ = 0 := ae_iff.mp hθsupp
      calc θ bad ≤ θ ((p.physBad k s E ∩ Par) ∪ Dy ∪ Parᶜ) := measure_mono hsub
        _ ≤ θ ((p.physBad k s E ∩ Par) ∪ Dy) + θ Parᶜ := measure_union_le _ _
        _ ≤ (θ (p.physBad k s E ∩ Par) + θ Dy) + θ Parᶜ := by
            gcongr
            exact measure_union_le _ _
        _ ≤ (p.μ k (p.physBad k s E ∩ Par) + p.μ k Dy) + 0 := by
            rw [hPar0]
            gcongr
        _ = p.μ k (p.physBad k s E ∩ Par) := by rw [hDy0, add_zero, add_zero]
        _ ≤ _ := h.physBad_parent_le hat_r hat_s hnest_rs hEloss Q
    have hlaw'univ : law' univ = θ badᶜ := Measure.restrict_apply_univ _
    have hcost : ENNReal.ofReal δ * (ENNReal.ofReal (162 * p.K k) * Wq) =
        ENNReal.ofReal (ϑ / 2) * Wq := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hδpos.le, hδdef]
      congr 2
      field_simp
      ring
    have hhalf : ϑ / 2 + ϑ / 2 = ϑ := by ring
    calc θ univ ≤ θ bad + θ badᶜ := measure_univ_le_add_compl bad
      _ = θ bad + law' univ := by rw [hlaw'univ]
      _ ≤ ENNReal.ofReal (p.K k) * Wq * η +
          (θ' univ + ENNReal.ofReal δ * ∑ j, ((opts j).card : ℝ≥0∞) * W j) :=
          add_le_add hbad_le hmass
      _ ≤ ENNReal.ofReal (p.K k) * Wq * η +
          (θ' univ + ENNReal.ofReal δ * (ENNReal.ofReal (162 * p.K k) * Wq)) := by
          gcongr
      _ = θ' univ + (ENNReal.ofReal (p.K k) * η * Wq + ENNReal.ofReal (ϑ / 2) * Wq) := by
          rw [hcost]
          ring
      _ ≤ θ' univ + (ENNReal.ofReal (ϑ / 2) * Wq + ENNReal.ofReal (ϑ / 2) * Wq) := by
          gcongr
      _ = θ' univ + ENNReal.ofReal ϑ * Wq := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), hhalf]
  · intro σ j
    have h1 := hdom σ j
    rw [hπb] at h1
    have hδinv : (ENNReal.ofReal δ)⁻¹ = ENNReal.ofReal (324 * p.K k / ϑ) := by
      rw [← ENNReal.ofReal_inv_of_pos hδpos, hδdef, inv_div]
    rw [hδinv] at h1
    refine h1.trans (le_of_eq ?_)
    ring

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
