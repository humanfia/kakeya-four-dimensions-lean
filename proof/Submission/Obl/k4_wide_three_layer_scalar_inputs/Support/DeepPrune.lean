import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Blocks
import Submission.Lib.K4OutputReferenceMenus

set_option linter.unusedVariables false

/-!
# Deep true blocks as end histories

The original atlas at a deep depth `s_e` consists of true blocks whose velocity laws are
dominated by the original palette (`BlocksAt.palette`) and whose reference weights
`q_e ν(A_j)` sum, over the deep blocks nested in a fixed coarse block `i`, to at most
`q ν(A_i)`.  Whenever a state of the incidences is determined, up to a finite menu, by the deep
block containing them, the accepted output-reference pruning gives a restriction with
conditional velocity domination at every state, losing only the cutoff times `q ν(A_i)`.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation
open Function

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-! ### Velocity bins -/

/-- The velocity bin at resolution `δ`. -/
def vbin (δ w : ℝ) : ℤ := ⌊w / δ⌋

theorem measurable_vbin (δ : ℝ) : Measurable (vbin δ) :=
  (measurable_id.div_const δ).floor

/-- The palette pushed to velocity bins. -/
def paletteBins (π : Measure ℝ) (δ : ℝ) : Measure ℤ := π.map (vbin δ)

theorem paletteBins_singleton (π : Measure ℝ) (δ : ℝ) (a : ℤ) :
    paletteBins π δ {a} = π {w : ℝ | ⌊w / δ⌋ = a} := by
  rw [paletteBins, Measure.map_apply (measurable_vbin δ) (measurableSet_singleton a)]
  rfl

theorem vbin_set_eq {δ : ℝ} (hδ : 0 < δ) (a : ℤ) :
    {w : ℝ | ⌊w / δ⌋ = a} = Ico ((a : ℝ) * δ) (((a : ℝ) + 1) * δ) := by
  ext w
  simp only [mem_ofPred_eq, mem_Ico, Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]

/-- Bin-wise caps integrate to caps for every set of bins. -/
theorem bin_cap_of_singletons {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω)
    (vel : Ω → ℝ) (π : Measure ℝ) (δ : ℝ) (c : ℝ≥0∞)
    (hcap : ∀ a : ℤ, μ {p | p ∈ E ∧ ⌊vel p / δ⌋ = a} ≤ c * π {w : ℝ | ⌊w / δ⌋ = a})
    (A : Set ℤ) :
    μ {p | p ∈ E ∧ vbin δ (vel p) ∈ A} ≤ c * paletteBins π δ A := by
  have hsplit : {p | p ∈ E ∧ vbin δ (vel p) ∈ A} =
      ⋃ a ∈ A, {p | p ∈ E ∧ ⌊vel p / δ⌋ = a} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, vbin, exists_prop]
    constructor
    · rintro ⟨hE, hA⟩; exact ⟨_, hA, hE, rfl⟩
    · rintro ⟨a, ha, hE, rfl⟩; exact ⟨hE, ha⟩
  have hbins : paletteBins π δ A = ∑' a : A, π {w : ℝ | ⌊w / δ⌋ = (a : ℤ)} := by
    rw [paletteBins, Measure.map_apply (measurable_vbin δ) (Set.to_countable A).measurableSet]
    have hpre : vbin δ ⁻¹' A = ⋃ a ∈ A, {w : ℝ | ⌊w / δ⌋ = a} := by
      ext w; simp [vbin]
    rw [hpre, measure_biUnion (Set.to_countable A)]
    · intro a _ b _ hab
      exact Set.disjoint_left.mpr fun w h1 h2 => hab (h1.symm.trans h2)
    · intro a _
      exact (measurable_vbin δ) (measurableSet_singleton a)
  rw [hsplit, hbins]
  calc μ (⋃ a ∈ A, {p | p ∈ E ∧ ⌊vel p / δ⌋ = a})
      ≤ ∑' a : A, μ {p | p ∈ E ∧ ⌊vel p / δ⌋ = (a : ℤ)} :=
        measure_biUnion_le μ (Set.to_countable A) _
    _ ≤ ∑' a : A, c * π {w : ℝ | ⌊w / δ⌋ = (a : ℤ)} := ENNReal.tsum_le_tsum fun a => hcap a
    _ = c * ∑' a : A, π {w : ℝ | ⌊w / δ⌋ = (a : ℤ)} := ENNReal.tsum_mul_left

/-! ### Dyadic time intervals -/

theorem volume_I (T : ℕ) (j : Fin (2 ^ T)) :
    volume (Data.I T j) = ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ := by
  rw [Data.I, Real.volume_Icc]
  congr 1
  field_simp
  ring

/-- Two different dyadic intervals of the same level meet in at most one endpoint. -/
theorem I_inter_subset {T : ℕ} {j j' : Fin (2 ^ T)} (h : j ≠ j') :
    Data.I T j ∩ Data.I T j' ⊆ {t | ∃ m : ℤ, t = m / (2 : ℝ) ^ T} := by
  intro t ⟨h1, h2⟩
  simp only [Data.I, mem_Icc] at h1 h2
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hlt | hlt
  · -- j < j': then t = j'/2^T
    have hle : ((j : ℕ) : ℝ) + 1 ≤ ((j' : ℕ) : ℝ) := by exact_mod_cast hlt
    refine ⟨((j' : ℕ) : ℤ), ?_⟩
    have ha : ((j' : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ t := h2.1
    have hb : t ≤ (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T := h1.2
    have hc : (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T ≤ ((j' : ℕ) : ℝ) / (2 : ℝ) ^ T :=
      div_le_div_of_nonneg_right hle hT.le
    push_cast
    linarith
  · have hle : ((j' : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
    refine ⟨((j : ℕ) : ℤ), ?_⟩
    have ha : ((j : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ t := h1.1
    have hb : t ≤ (((j' : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T := h2.2
    have hc : (((j' : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T ≤ ((j : ℕ) : ℝ) / (2 : ℝ) ^ T :=
      div_le_div_of_nonneg_right hle hT.le
    push_cast
    linarith

theorem volume_dyadic_points (T : ℕ) : volume {t : ℝ | ∃ m : ℤ, t = m / (2 : ℝ) ^ T} = 0 := by
  have hc : {t : ℝ | ∃ m : ℤ, t = m / (2 : ℝ) ^ T}.Countable := by
    have : {t : ℝ | ∃ m : ℤ, t = m / (2 : ℝ) ^ T} = range (fun m : ℤ => (m : ℝ) / (2 : ℝ) ^ T) := by
      ext t; simp [eq_comm]
    rw [this]; exact countable_range _
  exact hc.measure_zero volume

/-- A law dominated by the prior times time does not charge any countable set of times. -/
theorem dominated_time_null {μ : Measure (α × ℝ)} {ν : Measure α} [SFinite ν] {K : ℝ}
    (hμ : μ ≤ ENNReal.ofReal K • ν.prod volume) {D : Set ℝ} (hD : volume D = 0) :
    μ {p | p.2 ∈ D} = 0 := by
  apply le_antisymm _ zero_le
  have hset : {p : α × ℝ | p.2 ∈ D} = univ ×ˢ D := by ext p; simp
  calc μ {p | p.2 ∈ D} ≤ (ENNReal.ofReal K • ν.prod volume) {p | p.2 ∈ D} := hμ _
    _ = 0 := by
      rw [Measure.smul_apply, hset, Measure.prod_prod, hD, mul_zero, smul_zero]

/-! ### Reference sums of nested deep blocks -/

/-- The deep blocks nested in one coarse block have reference sum at most its own. -/
theorem nested_reference_sum {cfg : Data α} {k : ℕ} {s s_e R : ℝ}
    (hν : IsProbabilityMeasure (cfg.ν k)) (hBe : BlocksAt cfg k s_e R)
    (i : Fin (cfg.n k s)) (hAi : MeasurableSet (cfg.A k s i)) (S : Finset (Fin (cfg.n k s_e)))
    (hS : ∀ j ∈ S, cfg.A k s_e j ⊆ cfg.A k s i ∧
      Data.I (cfg.T k s_e) (cfg.j k s_e j) ⊆ Data.I (cfg.T k s) (cfg.j k s i)) :
    ∑ j ∈ S, ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s_e)⁻¹ * cfg.ν k (cfg.A k s_e j) ≤
      ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i) := by
  set m := (cfg.ν k).prod (volume : Measure ℝ)
  have hterm : ∀ j : Fin (cfg.n k s_e), m (cfg.A k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j)) =
      ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s_e)⁻¹ * cfg.ν k (cfg.A k s_e j) := by
    intro j
    rw [Measure.prod_prod, volume_I, mul_comm]
  have hdisj : Set.Pairwise (↑S) (AEDisjoint m on fun j =>
      cfg.A k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j)) := by
    intro j _ j' _ hjj'
    show m ((cfg.A k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j)) ∩
      (cfg.A k s_e j' ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j'))) = 0
    rw [prod_inter_prod, Measure.prod_prod]
    by_cases hslot : cfg.j k s_e j = cfg.j k s_e j'
    · have hd := hBe.disj j j' hjj' hslot
      rw [Disjoint.inter_eq hd, measure_empty, zero_mul]
    · have hz : volume (Data.I (cfg.T k s_e) (cfg.j k s_e j) ∩
          Data.I (cfg.T k s_e) (cfg.j k s_e j')) = 0 :=
        measure_mono_null (I_inter_subset hslot) (volume_dyadic_points _)
      rw [hz, mul_zero]
  calc ∑ j ∈ S, ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s_e)⁻¹ * cfg.ν k (cfg.A k s_e j)
      = ∑ j ∈ S, m (cfg.A k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j)) :=
        Finset.sum_congr rfl fun j _ => (hterm j).symm
    _ = m (⋃ j ∈ S, cfg.A k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j)) :=
        (measure_biUnion_finset₀ hdisj fun j _ =>
          (((hBe.sets j).1).prod measurableSet_Icc).nullMeasurableSet).symm
    _ ≤ m (cfg.A k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)) := by
        apply measure_mono
        intro p hp
        simp only [mem_iUnion, exists_prop] at hp
        obtain ⟨j, hj, hp1, hp2⟩ := hp
        exact ⟨(hS j hj).1 hp1, (hS j hj).2 hp2⟩
    _ = _ := by rw [Measure.prod_prod, volume_I, mul_comm]


/-! ### Coverage by nested deep blocks -/

/-- Almost every incidence of a coarse block lies in a deep block whose (chosen) parent is
that coarse block. -/
theorem cover_nested {cfg : Data α} {k : ℕ} {s s_e R : ℝ} [SFinite (cfg.ν k)]
    (hμ : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k s_e R)
    (par : Fin (cfg.n k s_e) → Fin (cfg.n k s))
    (hpar : ∀ j, cfg.A k s_e j ⊆ cfg.A k s (par j) ∧
      Data.I (cfg.T k s_e) (cfg.j k s_e j) ⊆ Data.I (cfg.T k s) (cfg.j k s (par j)))
    (i : Fin (cfg.n k s)) :
    ∀ᵐ p ∂cfg.μ k, p.1 ∈ cfg.B k s i → p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) →
      ∃ j, par j = i ∧ p.1 ∈ cfg.B k s_e j ∧ p.2 ∈ Data.I (cfg.T k s_e) (cfg.j k s_e j) := by
  have hnull : ∀ᵐ p ∂cfg.μ k, p.2 ∉ {t : ℝ | ∃ m : ℤ, t = m / (2 : ℝ) ^ cfg.T k s} := by
    have h0 := dominated_time_null hμ (volume_dyadic_points (cfg.T k s))
    rw [measure_eq_zero_iff_ae_notMem] at h0
    exact h0
  filter_upwards [hBe.cover, hnull] with p hcov hnd hpB hpI
  obtain ⟨j, hj1, hj2⟩ := hcov
  refine ⟨j, ?_, hj1, hj2⟩
  by_contra hne
  have hpA : p.1 ∈ cfg.A k s (par j) :=
    (hpar j).1 ((hBe.sets j).2.2 hj1)
  have hpAi : p.1 ∈ cfg.A k s i := (hB.sets i).2.2 hpB
  by_cases hslot : cfg.j k s (par j) = cfg.j k s i
  · exact Set.disjoint_left.mp (hB.disj (par j) i hne hslot) hpA hpAi
  · exact hnd (I_inter_subset hslot ⟨(hpar j).2 hj2, hpI⟩)

/-! ### Pruning against nested deep blocks -/

/-- **Deep-block pruning.**  If a measurable state of the incidences of block `i` takes, on each
deep block, values in a menu of at most `D` states, then a restriction of the law has
conditional velocity domination at every state with constant `K/δp`, at a mass cost of
`δp D q ν(A_i)`. -/
theorem deep_prune {cfg : Data α} {k : ℕ} {s s_e R v' : ℝ}
    (hν : IsProbabilityMeasure (cfg.ν k)) (hK1 : 1 ≤ cfg.K k)
    (hμ : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k s_e R)
    (par : Fin (cfg.n k s_e) → Fin (cfg.n k s))
    (hpar : ∀ j, cfg.A k s_e j ⊆ cfg.A k s (par j) ∧
      Data.I (cfg.T k s_e) (cfg.j k s_e j) ⊆ Data.I (cfg.T k s) (cfg.j k s (par j)))
    (hv'1 : R⁻¹ ≤ v') (hv'2 : v' ≤ R)
    (i : Fin (cfg.n k s)) (θ : Measure (α × ℝ)) (hθ : θ ≤ cfg.μ k)
    (hθsupp : ∀ᵐ p ∂θ, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i))
    {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (state : α × ℝ → Q) (hstate : Measurable state) (D : ℕ)
    (menu : Fin (cfg.n k s_e) → Finset Q) (hcard : ∀ j, (menu j).card ≤ D)
    (hmenu : ∀ᵐ p ∂θ, ∀ j, p.1 ∈ cfg.B k s_e j → p.2 ∈ Data.I (cfg.T k s_e) (cfg.j k s_e j) →
      state p ∈ menu j)
    (δp : ℝ≥0∞) (hδ0 : δp ≠ 0) (hδtop : δp ≠ ⊤) :
    ∃ θ' : Measure (α × ℝ), θ' ≤ θ ∧
      θ univ ≤ θ' univ + δp * ((D : ℝ≥0∞) *
        (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i))) ∧
      ∀ (Q₀ : Q) (A : Set ℤ),
        θ' {p | state p = Q₀ ∧ vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3) ∈ A} ≤
          (ENNReal.ofReal (cfg.K k) / δp) * θ' (state ⁻¹' {Q₀}) *
            paletteBins (cfg.π k) (cfg.N k ^ (-v')) A := by
  classical
  set δv := cfg.N k ^ (-v') with hδv
  let E : Fin (cfg.n k s_e) → Set (α × ℝ) := fun j =>
    if par j = i then cfg.B k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j) else ∅
  let w : Fin (cfg.n k s_e) → ℝ≥0∞ := fun j =>
    if par j = i then ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s_e)⁻¹ * cfg.ν k (cfg.A k s_e j) else 0
  have hac : θ ≪ cfg.μ k := Measure.absolutelyContinuous_of_le hθ
  have hcover : ∀ᵐ p ∂θ, ∃ j, p ∈ E j := by
    have h1 := hac.ae_le (cover_nested hμ hB hBe par hpar i)
    filter_upwards [h1, hθsupp] with p hp hs
    obtain ⟨j, hj, hj1, hj2⟩ := hp hs.1 hs.2
    exact ⟨j, by simp only [E, hj, ite_true]; exact ⟨hj1, hj2⟩⟩
  have hmenu' : ∀ᵐ p ∂θ, ∀ j, p ∈ E j → state p ∈ menu j := by
    filter_upwards [hmenu] with p hp j hj
    simp only [E] at hj
    split_ifs at hj with hpj
    · exact hp j hj.1 hj.2
    · exact hj.elim
  have hcap : ∀ j (A : Set ℤ), MeasurableSet A →
      cfg.μ k {p | p ∈ E j ∧ vbin δv (cfg.b k p.1 3) ∈ A} ≤
        ENNReal.ofReal (cfg.K k) * w j * paletteBins (cfg.π k) δv A := by
    intro j A _
    by_cases hpj : par j = i
    · simp only [E, w, hpj, ite_true]
      have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK1
      have h := bin_cap_of_singletons (cfg.μ k) (cfg.B k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j))
        (fun p => cfg.b k p.1 3) (cfg.π k) δv
        (ENNReal.ofReal (cfg.K k * ((2 : ℝ) ^ cfg.T k s_e)⁻¹) * cfg.ν k (cfg.A k s_e j))
        (fun a => by
          have h0 := hBe.palette j v' a hv'1 hv'2
          have hset : {p : α × ℝ | p ∈ cfg.B k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j) ∧
              ⌊cfg.b k p.1 3 / δv⌋ = a} = {p | p.1 ∈ cfg.B k s_e j ∧
              p.2 ∈ Data.I (cfg.T k s_e) (cfg.j k s_e j) ∧
              ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v'))⌋ = a} := by
            ext p; simp only [mem_ofPred_eq, mem_prod, and_assoc, hδv]
          rw [hset]; exact h0) A
      calc cfg.μ k {p | p ∈ cfg.B k s_e j ×ˢ Data.I (cfg.T k s_e) (cfg.j k s_e j) ∧
            vbin δv (cfg.b k p.1 3) ∈ A}
          ≤ ENNReal.ofReal (cfg.K k * ((2 : ℝ) ^ cfg.T k s_e)⁻¹) * cfg.ν k (cfg.A k s_e j) *
              paletteBins (cfg.π k) δv A := h
        _ = _ := by rw [ENNReal.ofReal_mul hK0]; ring
    · simp only [E, w, hpj, ite_false]
      simp
  obtain ⟨θ', hθ'le, hθ'mass, hθ'dom⟩ :=
    Submission.Lib.K4OutputReferenceMenus.exists_pruned_output_palette (cfg.μ k) θ hθ E state
      hstate (fun p => vbin δv (cfg.b k p.1 3)) (paletteBins (cfg.π k) δv) menu w
      (ENNReal.ofReal (cfg.K k)) δp hδ0 hδtop D hcard hcover hmenu' hcap
  have hsum : ∑ j, w j ≤ ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i) := by
    calc ∑ j, w j = ∑ j ∈ Finset.univ.filter (fun j => par j = i),
          ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s_e)⁻¹ * cfg.ν k (cfg.A k s_e j) := by
          rw [Finset.sum_filter]
      _ ≤ _ := nested_reference_sum hν hBe i (hB.sets i).1 _ (by
          intro j hj
          have hj' : par j = i := (Finset.mem_filter.mp hj).2
          rw [← hj']
          exact hpar j)
  refine ⟨θ', hθ'le, hθ'mass.trans (add_le_add le_rfl (mul_le_mul' le_rfl
    (mul_le_mul' le_rfl hsum))), ?_⟩
  intro Q₀ A
  exact hθ'dom Q₀ A (Set.to_countable A).measurableSet

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
