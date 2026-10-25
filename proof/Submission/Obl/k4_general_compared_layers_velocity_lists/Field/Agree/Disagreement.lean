-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Disagreement; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.SourceCap
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.PairMass
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Palette

/-!
# The disagreement mass of the conditional pair law (paper Prop. 8.4)

For a submeasure `θ` of the sample law with conditional palette domination at the combined
states (fine velocity bins of mesh `δb`, constant `Cdom`), the pairs of the conditional redraw
`statePair θ agStF` whose coarse transverse pairs disagree by more than `E / 2` at the state's
representative point carry mass at most
`Cdom · 45 H⁴ · 4200 K² H² · L`, with `L` the length bound of the matching sets
(`disagreement_le`): the disagreeing pairs are covered by (source ∩ matching set) × (target
label) rectangles (pointwise claims), each rectangle costs its target's palette weight times the
source mass on the matching set (conditional domination), the source mass on the matching set is
its interval density times the matching length, the targets of one source have palette weight
`≤ 45 H⁴`, and the source weights sum to `≤ 4200 K² H²`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial Kernels
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

namespace ComparedSample

variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

/-- A agGood incidence has a combined state in the box and a coarse label. -/
theorem agree_good_state {R : ℝ} (hat : p.AtDepth k r R) (hN : 0 < p.N k) (hK1 : 1 ≤ p.K k)
    {δb δs : ℝ} (hδb : 0 < δb) (hδs : 0 < δs) {M : ℕ}
    (hM : p.K k / δb + p.K k / δs + 1 ≤ M) {ω : α × ℝ} (hω : ω ∈ s.agGood)
    {e : Fin (s.count 0)} (he : ω ∈ s.event 0 e) :
    ∃ h : p.nativeState k r (s.parent 0 e) δb δs ω ∈ agStateBox M,
      s.agStF δb δs M ω = some (s.parent 0 e, ⟨_, h⟩) ∧ s.agEntF ω = some (s.coarse 0 e) := by
  obtain ⟨hgood, hB, ht, hC, hF⟩ := s.agree_event_data0 he
  obtain ⟨hτ0, hτ1⟩ := agree_tauN_mem_unit (p := p) ht
  obtain ⟨hζ, hU⟩ := hat.agree_normalized_le hN _ hB ht
  have hX : |p.signal k ω.1 ω.2| ≤ p.K k := hω.2
  have hK0 : 0 ≤ p.K k := by linarith
  have hb1 : p.K k / δb + 1 ≤ M := by
    have : 0 ≤ p.K k / δs := div_nonneg hK0 hδs.le
    linarith
  have hb2 : p.K k / δs + 1 ≤ M := by
    have : 0 ≤ p.K k / δb := div_nonneg hK0 hδb.le
    linarith
  have hτ : |p.tauN k r (s.parent 0 e) ω| ≤ p.K k := by
    rw [abs_of_nonneg hτ0]
    linarith
  have hbox : p.nativeState k r (s.parent 0 e) δb δs ω ∈ agStateBox M := by
    unfold agStateBox
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · exact agree_floor_div_mem_Icc hδb hτ M hb1
    · exact agree_floor_div_mem_Icc hδb hζ M hb1
    · exact agree_floor_div_mem_Icc hδb hU M hb1
    · exact agree_floor_div_mem_Icc hδs hX M hb2
  exact ⟨hbox, s.agree_stF_of_mem (s.agree_mem_evQ_of_mem_event he) hbox,
    s.agree_entF_eq_some_iff.mpr hC⟩

/-- The normalized time cell of a agGood incidence is among `0, …, ⌊1 / δb⌋`. -/
theorem agree_cell_mem {δb : ℝ} (hδb : 0 < δb) {e : Fin (s.count 0)} {ω : α × ℝ}
    (he : ω ∈ s.event 0 e) :
    ⌊p.tauN k r (s.parent 0 e) ω / δb⌋ ∈ Finset.Icc (0 : ℤ) ⌊1 / δb⌋ := by
  obtain ⟨-, -, ht, -, -⟩ := s.agree_event_data0 he
  obtain ⟨hτ0, hτ1⟩ := agree_tauN_mem_unit (p := p) ht
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_nonneg.mpr (div_nonneg hτ0 hδb.le)
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right hτ1 hδb.le)

/-- The targets of one source have palette weight at most `45 H⁴`. -/
theorem agree_sum_pal3_tgtList_le (hπ : IsProbabilityMeasure (p.π k)) (hN : 0 < p.N k)
    (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) :
    ∑ y ∈ s.agTgtList δb e c, p.agPal3 k (p.N k ^ (-m)) ((s.layers 0).tag y 0) ≤
      ENNReal.ofReal (45 * H ^ 4) := by
  classical
  have hH0 : 0 ≤ H ^ 4 := by positivity
  have h := agree_sum_tagged_le (s.agTgtList δb e c) (s.layers 0).tag (s.coarseChoices (s.parent 0 e))
    (s.agTagCenter δb e c) hH0 (fun g => s.coarse_card _ g)
    (by
      intro i hi
      unfold agTgtList at hi
      rw [Finset.mem_filter] at hi
      exact hi.2)
    (fun a => p.agPal3 k (p.N k ^ (-m)) a)
  refine h.trans ?_
  have h3 := p.agree_sum_pal3_le k (Real.rpow_pos_of_pos hN (-m))
    ((s.agTgtList δb e c).image fun i => (s.layers 0).tag i 0)
  calc _ ≤ ENNReal.ofReal (15 * H ^ 4) * 3 := by gcongr
    _ = ENNReal.ofReal (45 * H ^ 4) := by
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **The disagreement mass of the conditional pair law.** -/
theorem disagreement_le (hbase : p.Basic) {R : ℝ} (hat : p.AtDepth k r R) (hN : 1 < p.N k)
    (hK1 : 1 ≤ p.K k) (hKH : p.K k ≤ H) (hℓr : 0 ≤ p.ℓ * r) (hm : 0 ≤ m) (hru : 0 ≤ r + u)
    (hd0 : 0 ≤ p.d) (hd1 : p.d ≤ 1)
    {δb : ℝ} (hδb : 0 < δb) (hδb1 : δb ≤ 1) (hχ1 : p.N k ^ (-m) ≤ 1)
    (hδbχ' : δb ≤ p.N k ^ (-m))
    (hfz : 8000000 * p.K k ^ 11 * p.N k ^ (m / 1000) * (δb + p.N k ^ (-m)) ≤
      p.N k ^ (-(r + u)))
    (hδbχ : 2 * (p.K k + 1) * δb ≤ p.N k ^ (-m))
    {E : ℝ} (haE : p.N k ^ (-(r + u)) ≤ E)
    {rm : ℝ} (hrm1 : p.N k ^ (-rm) ≤ p.blockLen k r * δb / 2)
    (hrm2 : 3 * p.K k ^ 2 * p.N k ^ (-rm) ≤ p.N k ^ (-m))
    (hrm3 : 54 * p.N k ^ (m / 1000) * (p.K k + 1) ^ 4 * p.N k ^ (-rm) ≤ p.N k ^ (-(r + u)))
    (hcapk : ∀ s' : ℝ, 0 ≤ s' → s' ≤ r + u → ∀ (q : Fin 3 → ℤ) (a v' : ℤ),
      p.μ k {ω | p.z k (p.N k) rm ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s'))⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v'} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * rm - p.d * s')) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v'})
    {M : ℕ} (hM : p.K k / δb + p.K k / p.N k ^ (-(r + u)) + 1 ≤ M)
    {θ' : ℝ} (hθ' : 0 < θ') (hθ'E : θ' ≤ E / 8)
    (θ : Measure (α × ℝ)) [IsFiniteMeasure θ] (hθ : θ ≤ s.law) {Cdom : ℝ} (hCdom : 0 ≤ Cdom)
    (hdom : ∀ q (j : ℤ),
      θ (s.agStF δb (p.N k ^ (-(r + u))) M ⁻¹' {q} ∩ {ω | ⌊p.b k ω.1 3 / δb⌋ = j}) ≤
        ENNReal.ofReal Cdom * θ (s.agStF δb (p.N k ^ (-(r + u))) M ⁻¹' {q}) *
          p.π k {x | ⌊x / δb⌋ = j}) :
    statePair θ (s.agStF δb (p.N k ^ (-(r + u))) M)
        {pp | ¬ s.agreeRel δb E M (s.agStF δb (p.N k ^ (-(r + u))) M pp.1) (s.agEntF pp.1)
          (s.agEntF pp.2)} ≤
      ENNReal.ofReal Cdom * ENNReal.ofReal (45 * H ^ 4) *
        ENNReal.ofReal (4200 * p.K k ^ 2 * H * H) *
        ENNReal.ofReal (2 * θ' * (4 * p.K k + 2) / (E / 4) +
          8 * (H ^ 4 * p.N k ^ (p.d * u)) * (6 * H * p.N k ^ (-(r + u))) / θ' +
          (2 * (H ^ 4 * p.N k ^ (p.d * u)) + 1) *
            (4 * p.K k * p.N k ^ (-m) / p.blockWidth k r)) := by
  classical
  have hNpos : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := hN.le
  have ha : 0 < p.N k ^ (-(r + u)) := Real.rpow_pos_of_pos hNpos _
  have hE : 0 < E := lt_of_lt_of_le ha haE
  have hb : Measurable (p.b k) := (hbase k).1
  have hπ : IsProbabilityMeasure (p.π k) := (hbase k).2.2.1
  have hH1 : 1 ≤ H := by linarith [s.loss_one]
  have hK0 : 0 ≤ p.K k := by linarith
  have hw := agree_blockWidth_pos (p := p) r hNpos
  set a₁ := p.N k ^ (-(r + u)) with ha₁_def
  set st := s.agStF δb a₁ M with hst_def
  set Lbr := 2 * θ' * (4 * p.K k + 2) / (E / 4) +
    8 * (H ^ 4 * p.N k ^ (p.d * u)) * (6 * H * a₁) / θ' +
    (2 * (H ^ 4 * p.N k ^ (p.d * u)) + 1) * (4 * p.K k * p.N k ^ (-m) / p.blockWidth k r)
    with hLbr_def
  have hs : ∀ q, MeasurableSet (st ⁻¹' {q}) := s.agree_measurableSet_stF hb δb a₁ M
  have hG : MeasurableSet s.agGood := s.agree_measurableSet_good hb
  have hnull : θ s.agGoodᶜ = 0 :=
    le_antisymm ((hθ _).trans (s.agree_law_good_compl hbase).le) zero_le
  let S : Finset (Fin (s.count 0) × ℤ) :=
    (Finset.univ : Finset (Fin (s.count 0))) ×ˢ Finset.Icc (0 : ℤ) ⌊1 / δb⌋
  let T : Fin (s.count 0) × ℤ → Finset (Fin (s.layers 0).count) := fun x =>
    (s.agTgtList δb x.1 x.2).filter fun i' =>
      E / 4 ≤ coeffGap (s.agSrcPoly δb x.1 x.2) (s.agTgtPoly δb x.1 x.2 i')
  let Eset : Fin (s.count 0) × ℤ → Fin (s.layers 0).count → Set (α × ℝ) := fun x y =>
    s.agSrc δb x.1 x.2 ∩ s.agGood ∩ p.uN k r (s.parent 0 x.1) ⁻¹'
      matchSet (s.agSrcPoly δb x.1 x.2) (s.agTgtPoly δb x.1 x.2 y) (s.agTgtOffsets x.1 y)
        (6 * H * a₁) (p.K k)
  let V : Fin (s.layers 0).count → Set (α × ℝ) := fun y => {ω | ω.1 ∈ (s.layers 0).C y}
  let cfun : Fin (s.layers 0).count → ℝ≥0∞ := fun y =>
    ENNReal.ofReal Cdom * p.agPal3 k (p.N k ^ (-m)) ((s.layers 0).tag y 0)
  have hEm : ∀ x y, MeasurableSet (Eset x y) := by
    intro x y
    exact ((s.agree_measurableSet_src δb x.1 x.2).inter hG).inter
      ((p.measurable_uN hb r _) (agree_measurableSet_matchSet _ _ _ _ _))
  have hVm : ∀ y, MeasurableSet (V y) := fun y =>
    measurable_fst ((s.layer_valid 0).2.2.2.1 y)
  have hcap : ∀ y q, θ (V y ∩ st ⁻¹' {q}) ≤ cfun y * θ (st ⁻¹' {q}) := by
    intro y q
    have h := agree_bin_le_pal3_of_fine θ (p.π k) (fun ω => p.b k ω.1 3) (st ⁻¹' {q}) hδb hδbχ'
      (ENNReal.ofReal Cdom) (fun j => hdom q j) ((s.layers 0).tag y 0)
    calc θ (V y ∩ st ⁻¹' {q}) ≤
          θ (st ⁻¹' {q} ∩ {ω | ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = (s.layers 0).tag y 0}) :=
          measure_mono fun ω hω => ⟨hω.2, (s.agree_coarse_tags hω.1).1⟩
      _ ≤ _ := h
      _ = cfun y * θ (st ⁻¹' {q}) := by
          simp only [cfun, agPal3]
          ring
  have hcover : ∀ ω ∈ s.agGood, ∀ ω' ∈ s.agGood, st ω = st ω' →
      (ω, ω') ∈ {pp : (α × ℝ) × (α × ℝ) | ¬ s.agreeRel δb E M (st pp.1) (s.agEntF pp.1)
        (s.agEntF pp.2)} →
      ∃ x ∈ S, ∃ y ∈ T x, ω ∈ Eset x y ∧ ω' ∈ V y := by
    intro ω hω ω' hω' hstate hD
    obtain ⟨e, he⟩ := s.agree_good_event hω
    obtain ⟨hbox, hstω, hentω⟩ := s.agree_good_state hat hNpos hK1 hδb ha hM hω he
    obtain ⟨e', he'⟩ := s.agree_good_event hω'
    obtain ⟨-, -, hentω'⟩ := s.agree_good_state hat hNpos hK1 hδb ha hM hω' he'
    have hbad : ¬ s.agreeRel δb E M (some (s.parent 0 e, ⟨_, hbox⟩)) (some (s.coarse 0 e))
        (some (s.coarse 0 e')) := by
      have hD' : ¬ s.agreeRel δb E M (s.agStF δb a₁ M ω) (s.agEntF ω) (s.agEntF ω') := hD
      rw [hstω, hentω, hentω'] at hD'
      exact hD'
    have hq' : s.agStF δb a₁ M ω' = some (s.parent 0 e, ⟨_, hbox⟩) := hstate.symm.trans hstω
    set c := ⌊p.tauN k r (s.parent 0 e) ω / δb⌋ with hc_def
    have hsrc : ω ∈ s.agSrc δb e c := ⟨he, rfl⟩
    have hC' : ω'.1 ∈ (s.layers 0).C (s.coarse 0 e') := (s.agree_event_data0 he').2.2.2.1
    refine ⟨(e, c), Finset.mem_product.mpr ⟨Finset.mem_univ _, s.agree_cell_mem hδb he⟩,
      s.coarse 0 e', ?_, ⟨⟨hsrc, hω⟩, ?_⟩, hC'⟩
    · rw [Finset.mem_filter]
      exact ⟨s.agree_claim_target hat hN1 hδb hχ1 hδbχ ha hsrc hω' hC' hstω hq',
        s.agree_claim_gap hat hN1 hK1 hℓr hm hru hδb hχ1 hfz haE hsrc hstω hbad⟩
    · exact s.agree_claim_match hat hN1 hK1 hKH hℓr hm hru hδb hχ1 hfz hsrc hω' hC' hstω hq'
  have h1 := agree_statePair_le_of_cover θ st hs s.agGood hG hnull _ S T Eset V hEm hVm cfun hcap hcover
  refine h1.trans ?_
  -- each rectangle: palette weight of the target times the source mass on the matching set
  have hcard : ∀ x : Fin (s.count 0) × ℤ, ∀ y, ((s.agTgtOffsets x.1 y).card : ℝ) ≤
      H ^ 4 * p.N k ^ (p.d * u) := by
    intro x y
    have h2 : (s.agTgtOffsets x.1 y).card ≤ (s.fineChoices 0 (s.parent 0 x.1) y).card :=
      Finset.card_image_le
    have h3 := s.fine_card 0 (s.parent 0 x.1) y
    have h4 : ((s.agTgtOffsets x.1 y).card : ℝ) ≤ (s.fineChoices 0 (s.parent 0 x.1) y).card := by
      exact_mod_cast h2
    simpa using h4.trans h3
  have hlam : 0 ≤ 4 * p.K k * p.N k ^ (-m) / p.blockWidth k r := by positivity
  have hrect : ∀ x ∈ S, ∀ y ∈ T x, θ (Eset x y) ≤ s.agSrcWeight δb x.1 * ENNReal.ofReal Lbr := by
    intro x hx y hy
    have hgap : E / 4 ≤ coeffGap (s.agSrcPoly δb x.1 x.2) (s.agTgtPoly δb x.1 x.2 y) :=
      (Finset.mem_filter.mp hy).2
    have hsub : Eset x y ⊆ s.agSrc δb x.1 x.2 ∩ p.uN k r (s.parent 0 x.1) ⁻¹'
        matchSet (s.agSrcPoly δb x.1 x.2) (s.agTgtPoly δb x.1 x.2 y) (s.agTgtOffsets x.1 y)
          (6 * H * a₁) (p.K k) := fun ω hω => ⟨hω.1.1, hω.2⟩
    have hmatch := agree_measure_inter_preimage_matchSet_le (p.μ k) (s.agSrc δb x.1 x.2)
      (p.uN k r (s.parent 0 x.1)) (s.agSrcWeight δb x.1) hlam
      (P := s.agSrcPoly δb x.1 x.2) (Q := s.agTgtPoly δb x.1 x.2 y) (O := s.agTgtOffsets x.1 y)
      (w := 6 * H * a₁) (L := p.K k) (e := E / 4) (θ := θ')
      (fun a b hab => s.agree_src_interval_cap hbase hat hN hK1 hKH hd0 hd1 hru hδb hδb1 hχ1 hrm1
        hrm2 hrm3 hcapk x.1 x.2 a b hab)
      hK0 (by positivity : (0 : ℝ) < E / 4) hgap hθ' (by linarith) (by positivity)
    calc θ (Eset x y) ≤ s.law (Eset x y) := hθ _
      _ ≤ p.μ k (Eset x y) := s.agree_law_le_mu hbase _
      _ ≤ p.μ k (s.agSrc δb x.1 x.2 ∩ p.uN k r (s.parent 0 x.1) ⁻¹'
          matchSet (s.agSrcPoly δb x.1 x.2) (s.agTgtPoly δb x.1 x.2 y) (s.agTgtOffsets x.1 y)
            (6 * H * a₁) (p.K k)) := measure_mono hsub
      _ ≤ _ := hmatch
      _ ≤ s.agSrcWeight δb x.1 * ENNReal.ofReal Lbr := by
          gcongr
          have hc := hcard x y
          have hθ'0 : 0 ≤ (6 * H * a₁) / θ' := by positivity
          have h8 : 8 * ((s.agTgtOffsets x.1 y).card : ℝ) * (6 * H * a₁) / θ' ≤
              8 * (H ^ 4 * p.N k ^ (p.d * u)) * (6 * H * a₁) / θ' := by
            apply div_le_div_of_nonneg_right _ hθ'.le
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith
          have h2 : (2 * ((s.agTgtOffsets x.1 y).card : ℝ) + 1) *
              (4 * p.K k * p.N k ^ (-m) / p.blockWidth k r) ≤
              (2 * (H ^ 4 * p.N k ^ (p.d * u)) + 1) *
                (4 * p.K k * p.N k ^ (-m) / p.blockWidth k r) := by
            gcongr
          rw [hLbr_def]
          linarith
  calc ∑ x ∈ S, ∑ y ∈ T x, cfun y * θ (Eset x y)
      ≤ ∑ x ∈ S, ∑ y ∈ T x, cfun y * (s.agSrcWeight δb x.1 * ENNReal.ofReal Lbr) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy =>
          mul_le_mul' le_rfl (hrect x hx y hy)
    _ = ∑ x ∈ S, (∑ y ∈ T x, cfun y) * (s.agSrcWeight δb x.1 * ENNReal.ofReal Lbr) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ S, (ENNReal.ofReal Cdom * ENNReal.ofReal (45 * H ^ 4)) *
          (s.agSrcWeight δb x.1 * ENNReal.ofReal Lbr) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul' _ le_rfl
        calc ∑ y ∈ T x, cfun y = ENNReal.ofReal Cdom *
              ∑ y ∈ T x, p.agPal3 k (p.N k ^ (-m)) ((s.layers 0).tag y 0) := by
              simp only [cfun]
              rw [Finset.mul_sum]
          _ ≤ ENNReal.ofReal Cdom *
              ∑ y ∈ s.agTgtList δb x.1 x.2, p.agPal3 k (p.N k ^ (-m)) ((s.layers 0).tag y 0) := by
              gcongr
              exact Finset.filter_subset _ _
          _ ≤ _ := by
              gcongr
              exact s.agree_sum_pal3_tgtList_le hπ hNpos δb x.1 x.2
    _ = ENNReal.ofReal Cdom * ENNReal.ofReal (45 * H ^ 4) * ENNReal.ofReal Lbr *
          ∑ x ∈ S, s.agSrcWeight δb x.1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ ≤ ENNReal.ofReal Cdom * ENNReal.ofReal (45 * H ^ 4) * ENNReal.ofReal Lbr *
          ENNReal.ofReal (4200 * p.K k ^ 2 * H * H) := by
        gcongr
        exact s.agree_sum_srcWeight_le hδb hδb1 hNpos hK1
    _ = _ := by ring

end ComparedSample

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
