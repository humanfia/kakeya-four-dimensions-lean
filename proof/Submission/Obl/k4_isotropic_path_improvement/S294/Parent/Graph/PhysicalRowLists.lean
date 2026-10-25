-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.PhysicalRowLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/PhysicalRowLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Coarse row lists at every tested mesh and the physical row
regularity of a `Qualification.PhysicalModel` (paper tex-06, coarse lists of
Prop. `a05:velocity-graph`, then `a05:common-local-choice`):

* `physical_row_list_of_broad`: at one mesh `s`, per coarse physical cell, the
  row `s`-cells of the fine states number at most `10¹⁰ A²⁷ (P³+1)` (the lib's
  `K4ThreeBaseRows.SupportedTriples.coarse_row_bins_card_le_normalized`), from
  per-state breadth of the lifted velocities, per-state domination of the
  velocity CODES at mesh `s` by one weight `π`, derivative lists per coarse
  cell and code, and the velocity graph;
* `physical_row_regularity`: these lists at all meshes `s i` fed to
  `PhysicalModel.original_physical_row_selection`.

The palette enters ONLY through `hdom` (per scale `i`: weights `π i` on the
velocity codes at mesh `s i`); breadth `hbroad` is per fine state and
scale-free; `hderiv` are the derivative lists (`a05:derivative-list`).
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.PhysicalRowSelection
import Submission.Lib.K4ThreeBaseRows
import Submission.Lib.K4XInterface

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
open Submission.Lib.K4ThreeBaseRows
open Submission.Lib.K4ThreeBaseRows.RowBinLists (rowEval vbin rowBin)
open Submission.Lib.K4CommonLocalChoice (cell)

noncomputable section

/-- The planar velocity `(c4, c6)` of a model line, as coordinates. -/
def planarVel (pm : PhysicalModel) (l : Ln) : Fin 2 → ℝ :=
  ![pm.scalarCoefficients l 4, pm.scalarCoefficients l 6]

theorem measurable_planarVel (pm : PhysicalModel) : Measurable (planarVel pm) := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · change Measurable (fun l => pm.scalarCoefficients l 4)
    exact (measurable_pi_apply 4).comp pm.measurable_scalarCoefficients
  · change Measurable (fun l => pm.scalarCoefficients l 6)
    exact (measurable_pi_apply 6).comp pm.measurable_scalarCoefficients

/-- The model's physical coordinates of an incidence. -/
abbrev physX (pm : PhysicalModel) (z : Ev) : Fin 4 → ℝ :=
  originalPhysicalCoordinates (pm.signal z.1) (pm.position z.1) (pm.velocity z.1) z.2

/-- The model's time derivative of the signal at an incidence. -/
def physRate (pm : PhysicalModel) (z : Ev) : ℝ :=
  pm.scalarCoefficients z.1 1 + 2 * pm.scalarCoefficients z.1 2 * z.2

/-- **Coarse row list of a physical model at one mesh.** The lib's
`SupportedTriples.coarse_row_bins_card_le_normalized`, on the fine states of a
`PhysicalModel` in one coarse physical cell: per-state breadth of the lifted
velocities, per-state domination of the velocity CODES at mesh `s` by one
weight `π`, derivative lists per coarse cell and velocity code, and the
velocity graph. Fine states are assumed nested in the coarse cells. -/
theorem physical_row_list_of_broad (pm : PhysicalModel) (hκ : 1 ≤ pm.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ] (E : Set Ev) (hE : MeasurableSet E) (hEp : E ⊆ pm.event)
    {b : ℝ} (hb : 0 < b) (G : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (hpos : ∀ z ∈ E, 0 < μ.real (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z}))
    {s : ℝ} (hs : 0 < s)
    (hnest : ∀ x ∈ E, ∀ z ∈ E, pm.physicalState b x = pm.physicalState b z →
      cell s (physX pm x) = cell s (physX pm z))
    (π : (Fin 2 → ℤ) → ℝ) (Bv : Finset (Fin 2 → ℤ)) (L : (Fin 4 → ℤ) → (Fin 2 → ℤ) → Finset ℤ)
    {K ε ρ c₀ D KL A P : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hc₀ : 0 < c₀) (hD : 0 < D)
    (hA : 1 ≤ A) (hKA : K ≤ A) (hKLA : KL ≤ A) (hDA : D ≤ A) (hcA : c₀⁻¹ ≤ A)
    (hρA : ρ⁻¹ ≤ A) (hεA : ε / s ≤ A) (hπ0 : ∀ β, 0 ≤ π β) (hP : ∑ β ∈ Bv, π β ≤ P)
    (hG : ∀ z ∈ E, ∀ k, |G (pm.physicalState b z) k| ≤ K)
    (hvel : ∀ z ∈ E, ∀ k, |planarVel pm z.1 k| ≤ K)
    (hgraph : ∀ z ∈ E, |physRate pm z - rowEval (G (pm.physicalState b z)) (planarVel pm z.1)| ≤ ε)
    (hderiv : ∀ z ∈ E, ⌊physRate pm z / s⌋ ∈ L (cell s (physX pm z)) (vbin s (planarVel pm z.1)))
    (hLcard : ∀ n β, ((L n β).card : ℝ) ≤ KL)
    (hBv : ∀ z ∈ E, vbin s (planarVel pm z.1) ∈ Bv)
    (hdom : ∀ z ∈ E, ∀ β, μ.real (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z} ∩
        {x | vbin s (planarVel pm x.1) = β}) ≤
      D * μ.real (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z}) * π β)
    (hbroad : ∀ z ∈ E, Broad (μ.restrict (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z}))
      (fun x => SupportedTriples.liftE (planarVel pm x.1)) ρ c₀)
    (n : Fin 4 → ℤ) :
    ∃ V : Finset (Fin 3 → ℤ), (V.card : ℝ) ≤ 10 ^ 10 * A ^ 27 * (P ^ 3 + 1) ∧
      ∀ z ∈ E, cell s (physX pm z) = n → cell s (G (pm.physicalState b z)) ∈ V := by
  classical
  set st := pm.physicalState b with hst
  have hstm : Measurable st := pm.measurable_physicalState b
  have hfin := pm.finite_physical_state_image hκ hEp hb
  let cells : Finset (Fin 4 → ℤ) :=
    hfin.toFinset.filter fun c => ∃ z ∈ E, st z = c ∧ cell s (physX pm z) = n
  let μc : (Fin 4 → ℤ) → Measure Ev := fun c => μ.restrict (E ∩ st ⁻¹' {c})
  have hμc (c : Fin 4 → ℤ) : IsFiniteMeasure (μc c) := inferInstance
  have hEc (c : Fin 4 → ℤ) : MeasurableSet (E ∩ st ⁻¹' {c}) :=
    hE.inter (hstm (measurableSet_singleton c))
  have hcellsE {c : Fin 4 → ℤ} (hc : c ∈ cells) : ∃ z ∈ E, st z = c ∧ cell s (physX pm z) = n :=
    (Finset.mem_filter.mp hc).2
  have hmain := SupportedTriples.coarse_row_bins_card_le_normalized cells μc
    (fun c => E ∩ st ⁻¹' {c}) G (fun x => planarVel pm x.1)
    ((measurable_planarVel pm).comp measurable_fst) (physRate pm) (L n) π Bv hs hρ hK hε hc₀ hD
    hA hKA hKLA hDA hcA hρA hεA
    (by
      intro c _
      change μ.restrict (E ∩ st ⁻¹' {c}) (E ∩ st ⁻¹' {c})ᶜ = 0
      rw [Measure.restrict_apply (hEc c).compl, compl_inter_self, measure_empty])
    (by
      intro c hc
      obtain ⟨z, hz, hzc, -⟩ := hcellsE hc
      change 0 < (μ.restrict (E ∩ st ⁻¹' {c})).real univ
      rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def, ← hzc]
      exact hpos z hz)
    (by
      intro c hc k
      obtain ⟨z, hz, hzc, -⟩ := hcellsE hc
      rw [← hzc]
      exact hG z hz k)
    (by
      intro c hc x hx
      obtain ⟨z, hz, hzc, hzn⟩ := hcellsE hc
      have hxc : st x = c := hx.2
      have hxn : cell s (physX pm x) = n := by
        rw [hnest x hx.1 z hz (hxc.trans hzc.symm), hzn]
      refine ⟨hvel x hx.1, ?_, ?_, hBv x hx.1⟩
      · rw [← hxc]
        exact hgraph x hx.1
      · have := hderiv x hx.1
        rwa [hxn] at this)
    (fun β => hLcard n β) hπ0 hP
    (by
      intro c hc β
      obtain ⟨z, hz, hzc, -⟩ := hcellsE hc
      change (μ.restrict (E ∩ st ⁻¹' {c})).real {x | vbin s (planarVel pm x.1) = β} ≤
        D * (μ.restrict (E ∩ st ⁻¹' {c})).real univ * π β
      have hmeas : MeasurableSet {x : Ev | vbin s (planarVel pm x.1) = β} :=
        (SupportedTriples.measurable_vbin ((measurable_planarVel pm).comp measurable_fst) s)
          (measurableSet_singleton β)
      rw [measureReal_def, measureReal_def, Measure.restrict_apply hmeas,
        Measure.restrict_apply_univ, ← measureReal_def, ← measureReal_def, inter_comm, ← hzc]
      exact hdom z hz β)
    (by
      intro c hc
      obtain ⟨z, hz, hzc, -⟩ := hcellsE hc
      rw [← hzc]
      exact hbroad z hz)
  refine ⟨cells.image fun c => rowBin s (G c), hmain, ?_⟩
  intro z hz hzn
  apply Finset.mem_image.mpr
  refine ⟨st z, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  exact ⟨hfin.mem_toFinset.mpr ⟨z, hz, rfl⟩, z, hz, rfl, hzn⟩

/-- Dyadic meshes nest: a fine state at mesh `b` determines its cell at mesh
`b 2^k`. -/
theorem cell_eq_of_physicalState_eq (pm : PhysicalModel) {b s : ℝ} (k : ℕ)
    (hs : s = b * (2 : ℝ) ^ k) {x z : Ev} (hxz : pm.physicalState b x = pm.physicalState b z) :
    cell s (physX pm x) = cell s (physX pm z) := by
  funext j
  have hj := congrFun hxz j
  simp only [Qualification.PhysicalModel.physicalState] at hj
  simp only [cell, hs]
  rw [← div_div, ← div_div, Submission.Lib.K4XInterface.floor_div_two_pow,
    Submission.Lib.K4XInterface.floor_div_two_pow, hj]

/-- **Physical row regularity of a model from per-scale palettes.** At each
tested mesh `s i` (`s 0 = 1`, ratios `≤ Ar`, `b ≤ s i`, `s (L-1) ≤ ρ`), the
coarse row lists of `physical_row_list_of_broad` (per-state code domination
`D` by `π i`, derivative lists `Lst i`, velocity box `Bv i`), fed to
`original_physical_row_selection`, select whole fine states carrying a
`∏ (4⁴ 7⁴ lists)⁻¹` fraction of the mass on which the rows are Lipschitz in
the physical coordinates. All palettes enter only through `hdom`. -/
theorem physical_row_regularity (pm : PhysicalModel) (hκ : 1 ≤ pm.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ] (E : Set Ev) (hE : MeasurableSet E) (hEp : E ⊆ pm.event)
    (hfull : ∀ᵐ z ∂μ, z ∈ E)
    {b ρ : ℝ} (hb : 0 < b) (hbρ : b ≤ ρ) (G : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (hpos : ∀ z ∈ E, 0 < μ.real (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z}))
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i)
    (hbgrid : ∀ i < L, b ≤ s i) {Ar : ℝ} (hAr : 1 ≤ Ar)
    (hratio : ∀ i, i + 1 < L → s i ≤ Ar * s (i + 1)) (hfloor : s (L - 1) ≤ ρ)
    (hnest : ∀ i < L, ∀ x ∈ E, ∀ z ∈ E, pm.physicalState b x = pm.physicalState b z →
      cell (s i) (physX pm x) = cell (s i) (physX pm z))
    (π : ℕ → (Fin 2 → ℤ) → ℝ) (Bv : ℕ → Finset (Fin 2 → ℤ))
    (Lst : ℕ → (Fin 4 → ℤ) → (Fin 2 → ℤ) → Finset ℤ)
    {K ε ρb c₀ D KL A P : ℝ} (hρb : 0 < ρb) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hc₀ : 0 < c₀) (hD : 0 < D)
    (hA : 1 ≤ A) (hKA : K ≤ A) (hKLA : KL ≤ A) (hDA : D ≤ A) (hcA : c₀⁻¹ ≤ A)
    (hρA : ρb⁻¹ ≤ A) (hεA : ∀ i < L, ε / s i ≤ A) (hπ0 : ∀ i β, 0 ≤ π i β)
    (hP : ∀ i < L, ∑ β ∈ Bv i, π i β ≤ P)
    (hG : ∀ z ∈ E, ∀ k, |G (pm.physicalState b z) k| ≤ K)
    (hvel : ∀ z ∈ E, ∀ k, |planarVel pm z.1 k| ≤ K)
    (hgraph : ∀ z ∈ E, |physRate pm z - rowEval (G (pm.physicalState b z)) (planarVel pm z.1)| ≤ ε)
    (hderiv : ∀ i < L, ∀ z ∈ E,
      ⌊physRate pm z / s i⌋ ∈ Lst i (cell (s i) (physX pm z)) (vbin (s i) (planarVel pm z.1)))
    (hLcard : ∀ i < L, ∀ n β, ((Lst i n β).card : ℝ) ≤ KL)
    (hBv : ∀ i < L, ∀ z ∈ E, vbin (s i) (planarVel pm z.1) ∈ Bv i)
    (hdom : ∀ i < L, ∀ z ∈ E, ∀ β, μ.real (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z} ∩
        {x | vbin (s i) (planarVel pm x.1) = β}) ≤
      D * μ.real (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z}) * π i β)
    (hbroad : ∀ z ∈ E, Broad (μ.restrict (E ∩ pm.physicalState b ⁻¹' {pm.physicalState b z}))
      (fun x => SupportedTriples.liftE (planarVel pm x.1)) ρb c₀) :
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      μ univ ≤ (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ 4 *
        ((7 : ℕ) ^ 4 * ⌊10 ^ 10 * A ^ 27 * (P ^ 3 + 1)⌋₊))) *
        μ ((pm.physicalState b) ⁻¹' U) ∧
      ∀ z ∈ E, pm.physicalState b z ∈ U → ∀ z' ∈ E, pm.physicalState b z' ∈ U →
        ‖G (pm.physicalState b z) - G (pm.physicalState b z')‖ ≤
          6 * (Ar + 3 * K) * (‖physX pm z - physX pm z'‖ + ρ) := by
  have hbound : ∀ z ∈ E, ‖G (pm.physicalState b z)‖ ≤ 3 * K := by
    intro z hz
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
    rw [Real.norm_eq_abs]
    linarith [hG z hz k]
  refine Qualification.PhysicalModel.original_physical_row_selection pm μ E hE hfull G b ρ (3 * K)
    hb hbρ (by positivity) hbound L hL s (fun _ => ⌊10 ^ 10 * A ^ 27 * (P ^ 3 + 1)⌋₊) Ar hAr hs0
    hspos hbgrid hratio hfloor ?_
  intro i hi n
  obtain ⟨V, hV, hmem⟩ := physical_row_list_of_broad pm hκ μ E hE hEp hb G hpos (hspos i)
    (hnest i hi) (π i) (Bv i) (Lst i) hρb hK hε hc₀ hD hA hKA hKLA hDA hcA hρA (hεA i hi)
    (hπ0 i) (hP i hi) hG hvel hgraph (hderiv i hi) (hLcard i hi) (hBv i hi) (hdom i hi) hbroad n
  exact ⟨V, Nat.le_floor hV, hmem⟩

/-- **Breadth under a small loss.** If a fiber loses at most a `lam ≤ c₀/2`
fraction of its mass, its breadth fraction is at least halved. -/
theorem broad_of_small_loss {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (e : Ω → EuclideanSpace ℝ (Fin 3)) (he : Measurable e) {ρ c₀ lam : ℝ} (hlam : 0 ≤ lam)
    (hlamc : lam ≤ c₀ / 2)
    (hbroad : Broad (μ.restrict B) e ρ c₀) (hloss : μ.real (B \ A) ≤ lam * μ.real B) :
    Broad (μ.restrict A) e ρ (c₀ / 2) := by
  intro V hV
  have hfar : MeasurableSet {x | ρ ≤ Metric.infDist (e x) (V : Set _)} :=
    measurableSet_le measurable_const ((Metric.continuous_infDist_pt _).measurable.comp he)
  have h := hbroad V hV
  simp only [measureReal_def, Measure.restrict_apply_univ, Measure.restrict_apply hfar] at h ⊢
  rw [← measureReal_def, ← measureReal_def] at h ⊢
  have h1 : μ.real ({x | ρ ≤ Metric.infDist (e x) (V : Set _)} ∩ B) ≤
      μ.real ({x | ρ ≤ Metric.infDist (e x) (V : Set _)} ∩ A) + μ.real (B \ A) := by
    calc μ.real ({x | ρ ≤ Metric.infDist (e x) (V : Set _)} ∩ B)
        ≤ μ.real (({x | ρ ≤ Metric.infDist (e x) (V : Set _)} ∩ A) ∪ (B \ A)) :=
          measureReal_mono (fun x ⟨hx1, hx2⟩ => by
            by_cases hxA : x ∈ A
            · exact Or.inl ⟨hx1, hxA⟩
            · exact Or.inr ⟨hx2, hxA⟩)
      _ ≤ _ := measureReal_union_le _ _
  have h2 : μ.real A ≤ μ.real B := measureReal_mono hAB
  have h3 : 0 ≤ μ.real A := measureReal_nonneg
  have hc₀ : 0 ≤ c₀ := by linarith
  nlinarith

/-- **State thinning at a loss threshold `lam`.** Deleting the states that lose
more than a `lam` fraction of their `B`-mass to `A` costs at most `1/lam` times
the loss; every surviving state keeps its whole `A`-fiber. -/
theorem state_thinning_frac {Ω σ : Type*} [MeasurableSpace Ω] [MeasurableSpace σ] [Countable σ]
    [MeasurableSingletonClass σ] (μ : Measure Ω) [IsFiniteMeasure μ] (st : Ω → σ)
    (hst : Measurable st) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) {lam : ℝ} (hlam : 0 < lam) :
    ∃ A' : Set Ω, MeasurableSet A' ∧ A' ⊆ A ∧
      μ.real (B \ A') ≤ (1 + lam⁻¹) * μ.real (B \ A) ∧
      ∀ D : σ, A' ∩ st ⁻¹' {D} = ∅ ∨
        (A' ∩ st ⁻¹' {D} = A ∩ st ⁻¹' {D} ∧
          μ.real ((B ∩ st ⁻¹' {D}) \ (A ∩ st ⁻¹' {D})) ≤ lam * μ.real (B ∩ st ⁻¹' {D})) := by
  classical
  let good : Set σ := {D | μ.real ((B ∩ st ⁻¹' {D}) \ (A ∩ st ⁻¹' {D})) ≤
    lam * μ.real (B ∩ st ⁻¹' {D})}
  have hgoodm : MeasurableSet (st ⁻¹' good) := hst (Set.to_countable good).measurableSet
  refine ⟨A ∩ st ⁻¹' good, hA.inter hgoodm, inter_subset_left, ?_, ?_⟩
  · -- the deleted states
    have hsplit : B \ (A ∩ st ⁻¹' good) ⊆ (B \ A) ∪ (B ∩ st ⁻¹' goodᶜ) := by
      intro x ⟨hxB, hxn⟩
      by_cases hxA : x ∈ A
      · exact Or.inr ⟨hxB, fun hg => hxn ⟨hxA, hg⟩⟩
      · exact Or.inl ⟨hxB, hxA⟩
    have hbad : μ.real (B ∩ st ⁻¹' goodᶜ) ≤ lam⁻¹ * μ.real (B \ A) := by
      have hs : (goodᶜ : Set σ).Countable := Set.to_countable _
      have hfib : ∀ D ∈ (goodᶜ : Set σ), MeasurableSet (st ⁻¹' {D}) :=
        fun D _ => hst (measurableSet_singleton D)
      have hE1 : μ (B ∩ st ⁻¹' goodᶜ) = ∑' D : (goodᶜ : Set σ), (μ.restrict B) (st ⁻¹' {(D : σ)}) := by
        rw [tsum_measure_preimage_singleton hs hfib, Measure.restrict_apply (hst hs.measurableSet),
          inter_comm]
      have hE2 : ∑' D : (goodᶜ : Set σ), (μ.restrict (B \ A)) (st ⁻¹' {(D : σ)}) ≤ μ (B \ A) := by
        rw [tsum_measure_preimage_singleton hs hfib]
        exact (measure_mono (subset_univ _)).trans (Measure.restrict_apply_univ _).le
      have hle : μ (B ∩ st ⁻¹' goodᶜ) ≤ ENNReal.ofReal lam⁻¹ * μ (B \ A) := by
        rw [hE1]
        calc ∑' D : (goodᶜ : Set σ), (μ.restrict B) (st ⁻¹' {(D : σ)})
            ≤ ∑' D : (goodᶜ : Set σ), ENNReal.ofReal lam⁻¹ *
                (μ.restrict (B \ A)) (st ⁻¹' {(D : σ)}) := by
              apply ENNReal.tsum_le_tsum
              rintro ⟨D, hD⟩
              have hDm := hst (measurableSet_singleton D)
              rw [Measure.restrict_apply hDm, Measure.restrict_apply hDm]
              have hD' : lam * μ.real (B ∩ st ⁻¹' {D}) <
                  μ.real ((B ∩ st ⁻¹' {D}) \ (A ∩ st ⁻¹' {D})) := not_le.mp hD
              have heq : (B ∩ st ⁻¹' {D}) \ (A ∩ st ⁻¹' {D}) = st ⁻¹' {D} ∩ (B \ A) := by
                ext x
                simp only [mem_sdiff, mem_inter_iff, mem_preimage, mem_singleton_iff]
                tauto
              rw [heq, inter_comm B] at hD'
              have hfin1 : μ (st ⁻¹' {D} ∩ B) ≠ ⊤ := measure_ne_top _ _
              have hfin2 : μ (st ⁻¹' {D} ∩ (B \ A)) ≠ ⊤ := measure_ne_top _ _
              rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hfin2,
                ← ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le)]
              apply ENNReal.ofReal_le_ofReal
              rw [← measureReal_def, ← measureReal_def]
              rw [le_inv_mul_iff₀ hlam]
              exact hD'.le
          _ = ENNReal.ofReal lam⁻¹ * ∑' D : (goodᶜ : Set σ),
                (μ.restrict (B \ A)) (st ⁻¹' {(D : σ)}) := ENNReal.tsum_mul_left
          _ ≤ ENNReal.ofReal lam⁻¹ * μ (B \ A) := mul_le_mul' le_rfl hE2
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top _ _)) hle
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hlam.le)] at h
      exact h
    calc μ.real (B \ (A ∩ st ⁻¹' good)) ≤ μ.real ((B \ A) ∪ (B ∩ st ⁻¹' goodᶜ)) :=
          measureReal_mono hsplit
      _ ≤ μ.real (B \ A) + μ.real (B ∩ st ⁻¹' goodᶜ) := measureReal_union_le _ _
      _ ≤ μ.real (B \ A) + lam⁻¹ * μ.real (B \ A) := add_le_add le_rfl hbad
      _ = (1 + lam⁻¹) * μ.real (B \ A) := by ring
  · intro D
    by_cases hD : D ∈ good
    · right
      have heq : A ∩ st ⁻¹' good ∩ st ⁻¹' {D} = A ∩ st ⁻¹' {D} := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨hxA, -⟩, hx⟩
          exact ⟨hxA, hx⟩
        · rintro ⟨hxA, hx⟩
          exact ⟨⟨hxA, hx ▸ hD⟩, hx⟩
      exact ⟨heq, hD⟩
    · left
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro h1 hx
      exact hD (hx ▸ h1.2)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
