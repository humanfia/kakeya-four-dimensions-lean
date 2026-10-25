/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldResidualLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ResidualColumnLists
import Submission.Obl.k4_scalar_graph_residual_discovery.PosteriorPointLists
import Submission.Obl.k4_scalar_graph_residual_discovery.GlobalPosteriorRecords
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalResidualChoice

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace Zoom

abbrev OriginalPosteriorRecord :=
  ((Fin 5 → ℤ) × (Fin 3 → ℤ)) × ((Fin 3 → ℤ) × ℤ)

theorem posteriorEntryRecord_fields {ρ : ℝ} (hρ : 0 < ρ) (b r : ℝ)
    {p : ScalarIncidence} {a : OriginalPosteriorRecord}
    (hp : posteriorEntryRecord ρ b r p = a) :
    cell ρ p.1.2 = a.1.1 ∧ cell r (position ρ a.1.1 p) = a.1.2 ∧
      cell b (scalarPosition p) = a.2.1 ∧ cell ρ p.1.2 1 = a.2.2 := by
  rw [posteriorEntryRecord_eq hρ] at hp
  have hq := congrArg (fun v : OriginalPosteriorRecord => v.1.1) hp
  change cell ρ p.1.2 = a.1.1 at hq
  refine ⟨hq, ?_, congrArg (fun v : OriginalPosteriorRecord => v.2.1) hp,
    congrArg (fun v : OriginalPosteriorRecord => v.2.2) hp⟩
  have hz := congrArg (fun v : OriginalPosteriorRecord => v.1.2) hp
  change cell r (position ρ (cell ρ p.1.2) p) = a.1.2 at hz
  rw [hq] at hz
  exact hz

noncomputable section

/-- Final original coefficient-entry and posterior-entry floors give an
ACTUAL pointwise list of canonical residuals in one world and zoom cell.
The posterior law is only `mu.restrict R`: every entry mass is the original
`mu (R intersect entry)`. All palette weights remain in the original units,
and the two nonnested boundary bins are paid by the existing `+2` term. -/
theorem canonical_residual_list_of_original_floors
    (μ : Measure ScalarIncidence) [IsFiniteMeasure μ]
    (θ : Measure ScalarLine) (π : Measure ℝ) [IsFiniteMeasure π]
    {R E : Set ScalarIncidence} (hR : MeasurableSet R) (hRE : R ⊆ E)
    {ρ β b r A H η C s ηp Cg Hrow L ζ δ ε Hc : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hb : 0 < b) (hr : 0 < r)
    (hscale : β ≤ ρ * r) (hA : 0 < A) (hH : 1 ≤ H)
    (hη : 0 < η) (hC : 0 ≤ C) (hs : 0 < s)
    (hηp : 0 < ηp) (hCg : 0 ≤ Cg) (hHrow : 0 ≤ Hrow) (hL : 0 ≤ L)
    (hζr : ζ ≤ r) (hprecision : δ + ε / ρ + 2 * Hc * b / ρ ≤ ζ)
    (q : Fin 5 → ℤ) (z : Fin 3 → ℤ)
    (hpalette : π (scalarVelocityBin ρ (q 1)) ≠ 0)
    (old : (Fin 3 → ℤ) → ℝ≥0∞)
    (hgraphcap : ∀ (W : Fin 3 → ℤ) (j : ℤ),
      μ {p | cell b (scalarPosition p) = W ∧ (⌊p.1.2 1 / β⌋ : ℤ) = j} ≤
        ENNReal.ofReal Cg * old W * π (scalarVelocityBin β j))
    (hposterior : ∀ a : OriginalPosteriorRecord,
      R ∩ (posteriorEntryRecord ρ b r ⁻¹' {a}) = ∅ ∨
        ENNReal.ofReal ηp * old a.2.1 * π (scalarVelocityBin ρ a.2.2) <
          μ (R ∩ (posteriorEntryRecord ρ b r ⁻¹' {a})))
    (hcoeff : ∀ p ∈ R, ∀ e, |p.1.2 e| ≤ H)
    (htime : ∀ p ∈ R, |p.2| ≤ 1)
    (hcoefFloor : ∀ B,
      R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q B) r z = ∅ ∨
        ENNReal.ofReal (r / A) * θ (parameterPiece ρ β q B) <
          μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q B) r z))
    (hcoefPrior : ∀ (j : ℤ) (B : Fin 5 → ℤ),
      μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q B) r z) ≠ 0 →
      B 1 = j → ENNReal.ofReal (η * s / H) * π (scalarVelocityBin β j) ≤
        θ (parameterPiece ρ β q B))
    (hcellcap : ∀ j : ℤ,
      μ {p | p ∈ E ∧ (⌊p.1.2 1 / β⌋ : ℤ) = j ∧ cell r (position ρ q p) = z} ≤
        ENNReal.ofReal (H ^ 2 * r * C * s) * π (scalarVelocityBin β j))
    (F : ℝ → ℝ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hcenter : |(center ρ q).2 4| ≤ Hc)
    (hrow : ∀ p ∈ R, cell ρ p.1.2 = q → |F p.2| ≤ Hrow)
    (hrowvar : ∀ p ∈ R, cell ρ p.1.2 = q → ∀ p' ∈ R, cell ρ p'.1.2 = q →
      |F p.2 - F p'.2| ≤ L * (|p.2 - p'.2| + ζ))
    (hrowclose : ∀ p ∈ R, cell ρ p.1.2 = q →
      |G (cell b (scalarPosition p)) 1 - F p.2| ≤ δ)
    (hgraph : ∀ p ∈ R,
      |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (cell b (scalarPosition p)) 0 -
        G (cell b (scalarPosition p)) 1 * p.1.2 1| ≤ ε) :
    ∃ Q : Finset ℤ,
      (Q.card : ℝ) ≤ (Cg / ηp + 2) *
        ((A * H ^ 3 * C / η) * (2 * (7 + Hrow + 2 * L) + 2)) ∧
      ∀ p ∈ R, cell ρ p.1.2 = q → cell r (position ρ q p) = z →
        ⌊stateResidual ρ b q G (cell b (scalarPosition p)) / r⌋ ∈ Q := by
  classical
  let record := posteriorEntryRecord ρ b r
  let entry (a : OriginalPosteriorRecord) := record ⁻¹' {a}
  let fine (p : ScalarIncidence) : ℤ := ⌊p.1.2 1 / β⌋
  let κ := μ.restrict R
  let Rq := R ∩ {p : ScalarIncidence | cell ρ p.1.2 = q}
  let Obs := {p : ScalarIncidence | p ∈ R ∧ cell ρ p.1.2 = q ∧ cell r (position ρ q p) = z}
  let S (p : ScalarIncidence) := stateResidual ρ b q G (cell b (scalarPosition p))
  let label (a : OriginalPosteriorRecord) : ℤ := ⌊stateResidual ρ b q G a.2.1 / r⌋
  let Kcol := (A * H ^ 3 * C / η) * (2 * (7 + Hrow + 2 * L) + 2)
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hKcol : 0 ≤ Kcol := by dsimp only [Kcol]; positivity
  have hmrecord : Measurable record := measurable_posteriorEntryRecord ρ b r
  have hmentry (a : OriginalPosteriorRecord) : MeasurableSet (entry a) :=
    hmrecord (measurableSet_singleton a)
  have hmfine : Measurable fine := by
    have hm : Measurable (fun p : ScalarIncidence => p.1.2 1) :=
      (measurable_pi_apply 1).comp (measurable_snd.comp measurable_fst)
    exact (hm.div_const β).floor
  have hmcell (a : OriginalPosteriorRecord) (j : ℤ) :
      MeasurableSet {p | p ∈ entry a ∧ fine p = j} := by
    convert (hmentry a).inter (hmfine (measurableSet_singleton j)) using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hentry_mass (a : OriginalPosteriorRecord) :
      κ (entry a) = μ (R ∩ (record ⁻¹' {a})) := by
    rw [Measure.restrict_apply (hmentry a), inter_comm]
  have hrecord_obs (p : ScalarIncidence) (hp : p ∈ Obs) :
      record p = ((q, z), (cell b (scalarPosition p), q 1)) := by
    dsimp only [record]
    rw [posteriorEntryRecord_eq hρ, hp.2.1, hp.2.2]
  have hobs_fields (a : OriginalPosteriorRecord) (ha : a ∈ record '' Obs) :
      a.1.1 = q ∧ a.1.2 = z ∧ a.2.2 = q 1 := by
    obtain ⟨p, hp, rfl⟩ := ha
    rw [hrecord_obs p hp]
    exact ⟨rfl, rfl, rfl⟩
  have hfinite : (record '' Obs).Finite := by
    have hW := finite_original_physical_records R hH hb hcoeff htime
    apply (hW.image (fun W => ((q, z), (W, q 1)))).subset
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨cell b (scalarPosition p), ⟨p, hp.1, rfl⟩, (hrecord_obs p hp).symm⟩
  have hpositive (a : OriginalPosteriorRecord) (ha : a ∈ record '' Obs) :
      κ (entry a) ≠ 0 := by
    obtain ⟨p, hp, hpa⟩ := ha
    rw [hentry_mass]
    rcases hposterior a with hempty | hpos
    · have hpentry : p ∈ R ∩ (record ⁻¹' {a}) := ⟨hp.1, hpa⟩
      have hpempty : p ∈ (∅ : Set ScalarIncidence) := hempty ▸ hpentry
      exact hpempty.elim
    · exact ne_of_gt (lt_of_le_of_lt zero_le hpos)
  have hfinal_floor (a : OriginalPosteriorRecord) :
      κ (record ⁻¹' {a}) = 0 ∨
        ENNReal.ofReal ηp * old a.2.1 * π (scalarVelocityBin ρ a.2.2) ≤ κ (record ⁻¹' {a}) := by
    change κ (entry a) = 0 ∨ _ ≤ κ (entry a)
    rw [hentry_mass]
    rcases hposterior a with hempty | hpos
    · exact Or.inl (by rw [hempty, measure_empty])
    · exact Or.inr hpos.le
  have hraw_cap (a : OriginalPosteriorRecord) (j : ℤ) :
      μ {p | record p = a ∧ fine p = j} ≤
        ENNReal.ofReal Cg * old a.2.1 * π (scalarVelocityBin β j) := by
    apply (measure_mono ?_).trans (hgraphcap a.2.1 j)
    intro p hp
    exact ⟨(posteriorEntryRecord_fields hρ b r hp.1).2.2.1, hp.2⟩
  have hposterior_cap (a : OriginalPosteriorRecord) (ha : a ∈ record '' Obs) (j : ℤ) :
      κ {p | p ∈ entry a ∧ fine p = j} ≤
        ((ENNReal.ofReal Cg * π (scalarVelocityBin β j)) /
          (ENNReal.ofReal ηp * π (scalarVelocityBin ρ (q 1)))) * κ (entry a) := by
    have hP : π (scalarVelocityBin ρ a.2.2) ≠ 0 := by
      simpa only [(hobs_fields a ha).2.2] using hpalette
    have hraw := posterior_palette_cap_of_final_floors μ κ Measure.restrict_le_self record fine
      (fun a => old a.2.1) (fun a => π (scalarVelocityBin ρ a.2.2))
      (fun j => π (scalarVelocityBin β j)) (ENNReal.ofReal Cg) (ENNReal.ofReal ηp)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hηp)) ENNReal.ofReal_ne_top
      hraw_cap hfinal_floor a hP (measure_ne_top π _) j
    simpa only [entry, Set.mem_preimage, Set.mem_singleton_iff, (hobs_fields a ha).2.2] using hraw
  have hRq : MeasurableSet Rq := hR.inter (measurable_fst (measurableSet_block ρ q))
  have hcoef_eq (B : Fin 5 → ℤ) :
      Rq ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q B) r z =
        R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q B) r z := by
    ext p
    constructor
    · rintro ⟨⟨hpR, _⟩, hp⟩
      exact ⟨hpR, hp⟩
    · rintro ⟨hpR, hp⟩
      exact ⟨⟨hpR, hp.1.1⟩, hp⟩
  have hnear (p : ScalarIncidence) (hp : p ∈ Rq) :
      |S p - residual ρ q F p.1 p.2| ≤ r := by
    have hh := (residual_near_original_state hρ hb q F G p _ hp.2 rfl hcenter
      (hrowclose p hp.1 hp.2) (hgraph p hp.1)).trans (hprecision.trans hζr)
    simpa only [S, abs_sub_comm] using hh
  have hcolumns (j : ℤ) : ∃ Q : Finset ℤ, (Q.card : ℝ) ≤ Kcol ∧
      ∀ a ∈ record '' Obs, κ {p | p ∈ entry a ∧ fine p = j} ≠ 0 → label a ∈ Q := by
    obtain ⟨Q, hQcard, hQmem⟩ := residual_column_list_of_final_parameter_floors μ θ hRq
      (fun _ hp => hRE hp.1) hρ hβ hr hscale hA hHpos hη hs hC hHrow hL hζr q z j
      (π (scalarVelocityBin β j)) (measure_ne_top π _)
      (fun p hp => hp.2) (fun p hp => hcoeff p hp.1) (fun p hp => htime p hp.1)
      (fun B => by simpa only [hcoef_eq] using hcoefFloor B)
      (fun B hcur hvel => hcoefPrior j B (by simpa only [hcoef_eq] using hcur) hvel)
      (hcellcap j) F S (fun p hp => hrow p hp.1 hp.2)
      (fun p hp p' hp' => hrowvar p hp.1 hp.2 p' hp'.1 hp'.2) hnear
    refine ⟨Q, hQcard, ?_⟩
    intro a ha hcur
    have hcur' : μ ({p | p ∈ entry a ∧ fine p = j} ∩ R) ≠ 0 := by
      simpa only [κ, Measure.restrict_apply (hmcell a j)] using hcur
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hcur'
    have hfields := posteriorEntryRecord_fields hρ b r hp.1.1
    have hpq : cell ρ p.1.2 = q := hfields.1.trans (hobs_fields a ha).1
    have hpz : cell r (position ρ q p) = z := by
      have hh := hfields.2.1
      rw [(hobs_fields a ha).1] at hh
      exact hh.trans (hobs_fields a ha).2.1
    have hmem := hQmem p ⟨hp.2, hpq⟩ hpz hp.1.2
    simpa only [label, S, hfields.2.2.1] using hmem
  obtain ⟨Q, hQcard, hQmem⟩ := pointwise_labels_of_original_posterior_entries κ π Obs record label
    hfinite entry hpositive hρ hβ (q 1) (fun p => p.1.2 1)
    (by
      intro a ha p hp
      exact (posteriorEntryRecord_fields hρ b r hp).2.2.2.trans (hobs_fields a ha).2.2)
    (ENNReal.ofReal Cg) (ENNReal.ofReal ηp) ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr hηp)) ENNReal.ofReal_ne_top hpalette hposterior_cap
    hKcol hcolumns
  refine ⟨Q, ?_, ?_⟩
  · simpa only [ENNReal.toReal_ofReal hCg, ENNReal.toReal_ofReal hηp.le, Kcol] using hQcard
  · intro p hp hpq hpz
    simpa only [label, record, posteriorEntryRecord] using hQmem p ⟨hp, hpq, hpz⟩

/-- The cellwise lists just constructed from original floors feed the
existing whole-state common choice at finitely many resolutions. Real
cardinality bounds are converted to the natural budgets only here. The
same original law, states and pointwise residuals are retained throughout. -/
theorem original_state_choice_of_cellwise_residual_lists
    (μ : Measure ScalarIncidence) (E : Set ScalarIncidence) (hE : μ Eᶜ = 0)
    {ρ b ζ H Hc δ ε : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hb : 0 < b)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hH : 0 ≤ H) (hHc : 1 ≤ Hc)
    (q : Fin 5 → ℤ) (F : ℝ → ℝ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hworld : ∀ p ∈ E, cell ρ p.1.2 = q)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hF : ∀ p ∈ E, |F p.2| ≤ H)
    (hcenter : ∀ e, |(center ρ q).2 e| ≤ Hc)
    (hrow : ∀ p ∈ E, |G (cell b (scalarPosition p)) 1 - F p.2| ≤ δ)
    (hgraph : ∀ p ∈ E,
      |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (cell b (scalarPosition p)) 0 -
        G (cell b (scalarPosition p)) 1 * p.1.2 1| ≤ ε)
    (hdiam : (1 + 3 * Hc) * b / ρ ≤ ζ)
    (herror : δ + ε / ρ + 2 * Hc * b / ρ ≤ ζ)
    (n : ℕ) (hn : 1 ≤ n) (s : ℕ → ℝ) (K : ℕ → ℕ)
    (A : ℝ) (hA : 1 ≤ A) (hs₀ : s 0 = 1) (hs : ∀ i, 0 < s i)
    (hratio : ∀ i, i + 1 < n → s i ≤ A * s (i + 1)) (hlast : s (n - 1) = ζ)
    (hactualLists : ∀ i < n, ∀ z : Fin 3 → ℤ, ∃ Q : Finset ℤ,
      (Q.card : ℝ) ≤ (K i : ℝ) ∧
      ∀ p ∈ E, cell (s i) (position ρ q p) = z →
        ⌊stateResidual ρ b q G (cell b (scalarPosition p)) / s i⌋ ∈ Q) :
    ∃ S : Set (Fin 3 → ℤ), MeasurableSet S ∧
      μ univ ≤ (∏ i ∈ Finset.range n, ((4 : ℝ≥0∞) ^ 3 * K i)) *
        μ {p | cell b (scalarPosition p) ∈ S} ∧
      ∀ p ∈ E, cell b (scalarPosition p) ∈ S →
        ∀ p' ∈ E, cell b (scalarPosition p') ∈ S →
          |residual ρ q F p.1 p.2 - residual ρ q F p'.1 p'.2| ≤
            6 * (A + H + 5) * (‖position ρ q p - position ρ q p'‖ + ζ) := by
  classical
  choose Q hQcard hQmem using fun i : Fin n => hactualLists i i.isLt
  let lists (i : ℕ) (z : Fin 3 → ℤ) : Finset ℤ :=
    if hi : i < n then Q ⟨i, hi⟩ z else ∅
  have hcard (i : ℕ) (hi : i < n) (z : Fin 3 → ℤ) : (lists i z).card ≤ K i := by
    have hh := hQcard ⟨i, hi⟩ z
    dsimp only [lists]
    rw [dif_pos hi]
    exact_mod_cast hh
  have hmem (i : ℕ) (hi : i < n) (p : ScalarIncidence) (hp : p ∈ E) :
      ⌊stateResidual ρ b q G (cell b (scalarPosition p)) / s i⌋ ∈
        lists i (cell (s i) (position ρ q p)) := by
    dsimp only [lists]
    rw [dif_pos hi]
    exact hQmem ⟨i, hi⟩ _ p hp rfl
  exact original_state_residual_common_choice μ E hE hρ hρ₁ hb hζ hζ₁ hH hHc q F G
    hworld htime hF hcenter hrow hgraph hdiam herror n hn s K A hA hs₀ hs hratio hlast
    lists hcard hmem

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
