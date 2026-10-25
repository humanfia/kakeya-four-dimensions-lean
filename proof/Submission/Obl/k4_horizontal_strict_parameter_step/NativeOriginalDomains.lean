/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at c4765076c45bb6cb7fbc53c5859035579f22a4b1, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeOriginalDomains.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMatching
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalDomainFloors

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

abbrev WitnessIndex := c.support.table.witnessMenu c.group

def witnessOfMark (r : Fin c.support.table.count) : c.WitnessIndex :=
  ⟨c.support.table.witnessKey c.group r, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩⟩

def witnessLabel (p : α × ℝ) : c.WitnessIndex := c.witnessOfMark (c.support.table.mark p)

theorem measurable_witnessLabel : Measurable c.witnessLabel :=
  (measurable_of_countable c.witnessOfMark).comp c.support.table.mark_measurable

/-- The full original fitted witness in the unchanged static/velocity cell.
Its mass is measured BEFORE any later current pair restriction. -/
def originalWitness (i : c.WitnessIndex) : Set (α × ℝ) :=
  {p | p.1 ∈ cfg.B k s i.val.1 ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i.val.1) ∧
    ⌊cfg.b k p.1 3 / cfg.N k ^ (-cfg.e₀)⌋ = i.val.2 0 ∧
    ⌊cfg.b k p.1 0 / c.D⌋ = i.val.2 1 ∧ ⌊cfg.b k p.1 1 / c.D⌋ = i.val.2 2}

def witnessWeight (i : c.WitnessIndex) : ℝ :=
  cfg.timeLength k s * c.D ^ 2 * c.a ^ cfg.d *
    binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (i.val.2 0)

theorem witnessWeight_nonneg (ha : 0 ≤ c.a) (i : c.WitnessIndex) : 0 ≤ c.witnessWeight i := by
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg hq.le (sq_nonneg _)) (Real.rpow_nonneg ha _))
    (binWeight_nonneg _ _ _)

theorem measurable_originalWitness (lev : cfg.AssignmentLevel k s) (i : c.WitnessIndex) :
    MeasurableSet (c.originalWitness i) := by
  have hb : Measurable (fun p : α × ℝ => cfg.b k p.1) := c.measurable_b.comp measurable_fst
  have hg (e : Fin 6) (a : ℝ) : Measurable (fun p : α × ℝ => ⌊cfg.b k p.1 e / a⌋) := by fun_prop
  have hB : MeasurableSet {p : α × ℝ | p.1 ∈ cfg.B k s i.val.1} :=
    (lev.fitted_measurable i.val.1).preimage measurable_fst
  have hI : MeasurableSet {p : α × ℝ | p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i.val.1)} :=
    measurableSet_Icc.preimage measurable_snd
  exact hB.inter (hI.inter (((hg 3 _) (measurableSet_singleton _)).inter
    (((hg 0 _) (measurableSet_singleton _)).inter ((hg 1 _) (measurableSet_singleton _)))))

theorem originalWitness_covers : ∀ᵐ p ∂σ, p ∈ c.originalWitness (c.witnessLabel p) := by
  filter_upwards [c.support.conull] with p hp
  have hn := c.support.table.decode_native p hp
  have hg := (c.layer.2.2.1 (c.support.table.old (c.support.table.mark p))).1 p.1
    (c.support.table.decode_old p hp).1
  exact ⟨hn.1, hn.2, hg.1, hg.2.1, hg.2.2⟩

def floorKeep (δ : ℝ) : Set (α × ℝ) :=
  originalDomainKeep (cfg.μ k) c.originalWitness c.witnessLabel c.witnessWeight δ

theorem measurable_floorKeep (δ : ℝ) : MeasurableSet (c.floorKeep δ) :=
  measurableSet_originalDomainKeep (cfg.μ k) c.originalWitness c.witnessLabel
    c.measurable_witnessLabel c.witnessWeight δ

/-- Light whole original witnesses lose at most their unchanged summed
reference weights, even though the original witnesses overlap. -/
theorem floor_loss (ha : 0 ≤ c.a) {δ : ℝ} (hδ : 0 ≤ δ) :
    σ (c.floorKeep δ)ᶜ ≤ ENNReal.ofReal (δ * ∑ i : c.WitnessIndex, c.witnessWeight i) :=
  original_domain_floor_loss (cfg.μ k) σ c.dominated c.originalWitness c.witnessLabel
    c.witnessWeight (c.witnessWeight_nonneg ha) hδ c.originalWitness_covers

/-- Only actual observed witness colours are charged by the original cutoff. -/
theorem witness_budget (lev : cfg.AssignmentLevel k s) (hbasic : cfg.Basic)
    (hℓ : cfg.ℓ = cfg.κ) (ha : c.a = cfg.N k ^ (-s))
    (hDq : c.D ≤ cfg.timeLength k s ^ 2)
    (hχq : cfg.N k ^ (-cfg.e₀) ≤ cfg.timeLength k s ^ 2) :
    (∑ i : c.WitnessIndex, c.witnessWeight i) ≤
      cfg.N k ^ c.ε * cfg.K k + 128 * cfg.K k ^ 5 := by
  have hH : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k c.ε σ c.D (cfg.N k ^ (-s))
      c.m c.AH c.group c.hH := by simpa only [ha] using c.layer
  have hfull := cfg.observed_reference_budget lev hbasic c.N_pos c.K_one hℓ c.D_pos
    hDq hχq σ c.dominated hH c.support.table c.support.contact
  rw [← ha, Fintype.sum_sum_type] at hfull
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have ha0 : 0 ≤ c.a := by rw [ha]; exact (Real.rpow_pos_of_pos c.N_pos _).le
  have hs : 0 ≤ ∑ i : c.support.table.sourceMenu (cfg.j k s),
      cfg.timeLength k s * c.D ^ 2 * c.a ^ cfg.d *
        binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
          ((c.support.table.colour c.group (cfg.j k s) (Sum.inl i)).1 0) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg
      (mul_nonneg (mul_nonneg hq.le (sq_nonneg _)) (Real.rpow_nonneg ha0 _)) (binWeight_nonneg _ _ _))
  change (∑ i : c.support.table.sourceMenu (cfg.j k s),
      cfg.timeLength k s * c.D ^ 2 * c.a ^ cfg.d *
        binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
          ((c.support.table.colour c.group (cfg.j k s) (Sum.inl i)).1 0)) +
      (∑ i : c.WitnessIndex, c.witnessWeight i) ≤ _ at hfull
  linarith

/-- The current good event preserves the original support, matching success,
and the full original witness floors pointwise. -/
def goodOriginal (M δ : ℝ) : Set (α × ℝ) :=
  c.support.event ∩ (c.badOriginal M)ᶜ ∩ c.floorKeep δ

theorem measurable_goodOriginal (M δ : ℝ) : MeasurableSet (c.goodOriginal M δ) :=
  (c.support.measurable.inter (c.measurable_badOriginal M).compl).inter (c.measurable_floorKeep δ)

def goodLaw (M δ : ℝ) : Measure (α × ℝ) := σ.restrict (c.goodOriginal M δ)

theorem goodLaw_le (M δ : ℝ) : c.goodLaw M δ ≤ σ := Measure.restrict_le_self

/-- Matching and original-domain cutoffs are paid additively in original
incidence units, before the one-native-entry-per-timeblock selection. -/
theorem goodLaw_mass (ha : 0 ≤ c.a) (M : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    σ univ ≤ c.goodLaw M δ univ + σ (c.badOriginal M) +
      ENNReal.ofReal (δ * ∑ i : c.WitnessIndex, c.witnessWeight i) := by
  have hbad : σ (c.goodOriginal M δ)ᶜ ≤ σ (c.badOriginal M) + σ (c.floorKeep δ)ᶜ := by
    apply (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [c.support.conull] with p hp hbad
    by_cases hm : p ∈ c.badOriginal M
    · exact Or.inl hm
    · exact Or.inr (fun hf => hbad ⟨⟨hp, hm⟩, hf⟩)
  calc
    σ univ = σ (c.goodOriginal M δ) + σ (c.goodOriginal M δ)ᶜ :=
      (measure_add_measure_compl (c.measurable_goodOriginal M δ)).symm
    _ ≤ σ (c.goodOriginal M δ) + (σ (c.badOriginal M) +
        ENNReal.ofReal (δ * ∑ i : c.WitnessIndex, c.witnessWeight i)) :=
      add_le_add le_rfl (hbad.trans (add_le_add le_rfl (c.floor_loss ha hδ)))
    _ = _ := by rw [goodLaw, Measure.restrict_apply_univ]; ac_rfl

/-- A velocity colour with zero original palette has zero current mass.
The conclusion is proved before choosing any successful pair. -/
theorem zero_palette_label_mass (i : c.WitnessIndex)
    (hz : binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (i.val.2 0) = 0) :
    σ {p | c.witnessLabel p = i} = 0 := by
  letI := c.finite_palette
  have hb := cfg.observed_whole_colour_cap c.support c.layer c.dominated c.caps
    c.re_lower c.re_upper c.velocity_lower c.velocity_upper (c.width_lower.trans c.width_upper)
    c.N_pos c.K_one c.D_pos c.D_one (Real.rpow_pos_of_pos c.N_pos _) c.velocity_width rfl
    c.mesh_time c.mesh_parameter (Sum.inr i)
  change σ {p | p ∈ c.support.event ∧
    c.support.table.colour c.group (cfg.j k s)
      (c.support.table.source c.group (cfg.j k s) (c.support.table.mark p)) =
        c.support.table.colour c.group (cfg.j k s) (Sum.inr i)} ≤
    ENNReal.ofReal (64800 * cfg.K k ^ 2 *
      binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (i.val.2 0) * cfg.timeLength k s * c.D ^ 2) at hb
  rw [hz, mul_zero, zero_mul, zero_mul, ENNReal.ofReal_zero] at hb
  apply le_antisymm ((measure_mono_ae ?_).trans hb) bot_le
  filter_upwards [c.support.conull] with p hp hi
  have hk := congrArg Subtype.val hi
  change (c.support.table.native (c.support.table.mark p),
    c.group (c.support.table.old (c.support.table.mark p))) = i.val at hk
  refine ⟨hp, ?_⟩
  change (c.group (c.support.table.old (c.support.table.mark p)),
    cfg.j k s (c.support.table.native (c.support.table.mark p))) = (i.val.2, cfg.j k s i.val.1)
  have hn : c.support.table.native (c.support.table.mark p) = i.val.1 := congrArg Prod.fst hk
  have hg : c.group (c.support.table.old (c.support.table.mark p)) = i.val.2 := congrArg Prod.snd hk
  rw [hn, hg]

/-- Zero-palette colours need no positive floor: they form a null event under
original caps. The retained candidate relation may thus require positivity. -/
theorem ae_positive_palette : ∀ᵐ p ∂σ,
    0 < binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) ((c.witnessLabel p).val.2 0) := by
  have hi (i : c.WitnessIndex) : ∀ᵐ p ∂σ, c.witnessLabel p = i →
      0 < binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (i.val.2 0) := by
    by_cases hpos : 0 < binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (i.val.2 0)
    · exact Filter.Eventually.of_forall (fun p hp => hpos)
    · have hz : binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (i.val.2 0) = 0 :=
        le_antisymm (le_of_not_gt hpos) (binWeight_nonneg _ _ _)
      have hne : ∀ᵐ p ∂σ, c.witnessLabel p ≠ i := by
        apply ae_iff.mpr
        simpa only [not_not] using c.zero_palette_label_mass i hz
      exact hne.mono (fun p hp hi => (hp hi).elim)
  filter_upwards [ae_all_iff.mpr hi] with p hp
  exact hp (c.witnessLabel p) rfl

/-- A candidate relation names actual successful observed marks with full
original floors. Its menu cardinality is the remaining whole-domain count. -/
def paired (M δ : ℝ) (h : Fin c.m) (i : Fin (cfg.n k s)) : Prop :=
  ∃ r : Fin c.support.table.count, c.support.table.old r = h ∧ c.support.table.native r = i ∧
    r ∉ c.badMarks M ∧
      0 < binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) ((c.witnessOfMark r).val.2 0) ∧
      ENNReal.ofReal (δ * c.witnessWeight (c.witnessOfMark r)) ≤
      cfg.μ k (c.originalWitness (c.witnessOfMark r))

/-- The retained current law already has the exact genuine incidence cover
required by the accepted native time-block selector. -/
theorem goodLaw_paired_cover (M δ : ℝ) : ∀ᵐ p ∂c.goodLaw M δ,
    ∃ h i, p.1 ∈ c.AH h ∧ p.1 ∈ cfg.B k s i ∧
      p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧ c.paired M δ h i := by
  filter_upwards [ae_restrict_mem (c.measurable_goodOriginal M δ),
    ae_restrict_of_ae c.ae_positive_palette] with p hp hpal
  let r := c.support.table.mark p
  have ho := (c.support.table.decode_old p hp.1.1).1
  have hn := c.support.table.decode_native p hp.1.1
  exact ⟨c.support.table.old r, c.support.table.native r, ho, hn.1, hn.2,
    r, rfl, rfl, hp.1.2, hpal, hp.2⟩

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
