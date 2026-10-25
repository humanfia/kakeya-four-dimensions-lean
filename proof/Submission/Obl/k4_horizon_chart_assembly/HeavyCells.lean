import Submission.Obl.k4_horizon_chart_assembly.CellDecoder
import Submission.Obl.k4_horizon_chart_assembly.Cells
import Submission.Obl.k4_horizon_chart_assembly.GroupGeometry
import Submission.Obl.k4_horizon_chart_assembly.TimeTransport

/-!
# Heavy observation cells and the kernel's code tables

The light-cell statement classifies an incidence by the original mass of its fine observation
cell `(⌊t/ρ₁⌋, ⌊y₁/ρ₂⌋, ⌊y₂/ρ₂⌋, ⌊B w/a⌋)`. Here, for one world, block `j` and native group
`Γ`, we build the kernel's good set `Gd` (normalized incidences whose cell is heavy) and its code
table `F` (the heavy cells visited by the group, shifted to normalized codes). With the mesh
`ρ₁ = q/D`, `ρ₂ = q/m`, `D = R m`, the normalized code of an incidence is exactly its cell
shifted by `(jD, σ m)`. Every heavy cell is visited by `O(K³)` groups (`CellDecoder`), so the
tables of all groups of a world have total size `O(K³) · #heavy cells`.
-/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

noncomputable section

/-! ## Fine observation cells -/

/-- The fine observation cell of an incidence: time bin, planar bins and hidden bin. -/
def worldCell (ρ₁ ρ₂ B a : ℝ) (p : Incidence) : (Fin 3 → ℤ) × ℤ :=
  (fun i => ⌊graphPoint p.1 p.2 i.castSucc / cellScale ρ₁ ρ₂ i⌋, ⌊B * graphPoint p.1 p.2 3 / a⌋)

theorem measurable_graphPoint_apply (k : Fin 4) :
    Measurable (fun p : Incidence => graphPoint p.1 p.2 k) := by
  fin_cases k <;> simp only [graphPoint] <;> fun_prop

theorem measurable_worldCell (ρ₁ ρ₂ B a : ℝ) : Measurable (worldCell ρ₁ ρ₂ B a) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    exact Int.measurable_floor.comp ((measurable_graphPoint_apply _).div_const _)
  · exact Int.measurable_floor.comp
      (((measurable_graphPoint_apply 3).const_mul B).div_const a)

theorem xl_eq_graphPoint (l : Trajectory) (t : ℝ) : xl l t = graphPoint l t := rfl

/-- The light-cell set of the frozen statement, written with `worldCell`. -/
theorem lightSet_eq_worldCell (ν : Measure Trajectory) (E : Set Incidence)
    (B a θ ρ₁ ρ₂ : ℝ) :
    {p | p ∈ E ∧ (ν.prod volume) {p' | p' ∈ E ∧ ⌊p'.2 / ρ₁⌋ = ⌊p.2 / ρ₁⌋ ∧
      ⌊(xl p'.1 p'.2) 1 / ρ₂⌋ = ⌊(xl p.1 p.2) 1 / ρ₂⌋ ∧
      ⌊(xl p'.1 p'.2) 2 / ρ₂⌋ = ⌊(xl p.1 p.2) 2 / ρ₂⌋ ∧
      (obsl B a p').2 = (obsl B a p).2} < ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)} =
    {p | p ∈ E ∧ (ν.prod volume) (E ∩ worldCell ρ₁ ρ₂ B a ⁻¹' {worldCell ρ₁ ρ₂ B a p}) <
      ENNReal.ofReal (θ * ρ₁ * ρ₂ ^ 2)} := by
  ext p
  simp only [mem_setOf_eq]
  apply and_congr_right
  intro _
  have hset : {p' : Incidence | p' ∈ E ∧ ⌊p'.2 / ρ₁⌋ = ⌊p.2 / ρ₁⌋ ∧
      ⌊(xl p'.1 p'.2) 1 / ρ₂⌋ = ⌊(xl p.1 p.2) 1 / ρ₂⌋ ∧
      ⌊(xl p'.1 p'.2) 2 / ρ₂⌋ = ⌊(xl p.1 p.2) 2 / ρ₂⌋ ∧
      (obsl B a p').2 = (obsl B a p).2} =
      E ∩ worldCell ρ₁ ρ₂ B a ⁻¹' {worldCell ρ₁ ρ₂ B a p} := by
    ext p'
    simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, worldCell,
      Prod.mk.injEq, funext_iff, Fin.forall_fin_succ, Fin.forall_fin_one]
    constructor
    · rintro ⟨hE, h0, h1, h2, h3⟩
      refine ⟨hE, ⟨?_, ?_, ?_, fun i => i.elim0⟩, ?_⟩
      · simpa [cellScale, graphPoint] using h0
      · simpa [cellScale, graphPoint, xl, Submission.Obl.k4_quadratic_atlas_normalization.x]
          using h1
      · simpa [cellScale, graphPoint, xl, Submission.Obl.k4_quadratic_atlas_normalization.x]
          using h2
      · simpa [obsl, Submission.Obl.k4_quadratic_atlas_normalization.obs, graphPoint,
          Submission.Obl.k4_quadratic_atlas_normalization.x] using h3
    · rintro ⟨hE, ⟨h0, h1, h2, -⟩, h3⟩
      refine ⟨hE, ?_, ?_, ?_, ?_⟩
      · simpa [cellScale, graphPoint] using h0
      · simpa [cellScale, graphPoint, xl, Submission.Obl.k4_quadratic_atlas_normalization.x]
          using h1
      · simpa [cellScale, graphPoint, xl, Submission.Obl.k4_quadratic_atlas_normalization.x]
          using h2
      · simpa [obsl, Submission.Obl.k4_quadratic_atlas_normalization.obs, graphPoint,
          Submission.Obl.k4_quadratic_atlas_normalization.x] using h3
  rw [hset]

/-! ## Heavy cells -/

/-- Cells of whole original incidence mass at least `θ`. -/
def heavySet (ν : Measure Trajectory) (E : Set Incidence)
    (code : Incidence → (Fin 3 → ℤ) × ℤ) (θ : ℝ) : Set ((Fin 3 → ℤ) × ℤ) :=
  {Z | ENNReal.ofReal θ ≤ (ν.prod volume) (E ∩ code ⁻¹' {Z})}

theorem incidence_restrict_finite (ν : Measure Trajectory) [IsFiniteMeasure ν]
    {E : Set Incidence} (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    IsFiniteMeasure ((ν.prod volume).restrict E) := by
  constructor
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  calc
    (ν.prod volume) E ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hunit
    _ = ν univ * volume (Icc (0 : ℝ) 1) := Measure.prod_prod _ _
    _ < ⊤ := by
      rw [Real.volume_Icc]
      exact ENNReal.mul_lt_top (measure_lt_top ν univ) ENNReal.ofReal_lt_top

theorem heavySet_eq (ν : Measure Trajectory) {E : Set Incidence}
    {code : Incidence → (Fin 3 → ℤ) × ℤ} (hcode : Measurable code) (θ : ℝ) :
    heavySet ν E code θ = {Z | ENNReal.ofReal θ ≤ ((ν.prod volume).restrict E) (code ⁻¹' {Z})} := by
  ext Z
  simp only [heavySet, mem_setOf_eq]
  rw [Measure.restrict_apply (hcode (measurableSet_singleton Z)), inter_comm]

theorem heavySet_finite (ν : Measure Trajectory) [IsFiniteMeasure ν]
    {E : Set Incidence} (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {code : Incidence → (Fin 3 → ℤ) × ℤ} (hcode : Measurable code) {θ : ℝ} (hθ : 0 < θ) :
    (heavySet ν E code θ).Finite := by
  haveI := incidence_restrict_finite ν hunit
  rw [heavySet_eq ν hcode θ]
  exact finite_heavy_codes _ code hcode hθ

/-- The number of heavy cells is at most the total mass over the floor. -/
theorem heavySet_card_le (ν : Measure Trajectory) [IsFiniteMeasure ν]
    {E : Set Incidence} (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {code : Incidence → (Fin 3 → ℤ) × ℤ} (hcode : Measurable code) {θ : ℝ} (hθ : 0 < θ) :
    ((heavySet_finite ν hunit hcode hθ).toFinset.card : ℝ) ≤ (ν.prod volume).real E / θ := by
  haveI := incidence_restrict_finite ν hunit
  have h := whole_cell_card_bound ((ν.prod volume).restrict E) code hcode
    (heavySet_finite ν hunit hcode hθ).toFinset hθ (by
      intro Z hZ
      have hZ' := (Set.Finite.mem_toFinset _).mp hZ
      rw [heavySet_eq ν hcode θ] at hZ'
      exact hZ')
  simpa only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter] using h

/-! ## The kernel's code table of one group -/

/-- The heavy cells visited by a family of incidences, shifted into normalized codes. -/
def kernelCodes (S : Set ((Fin 3 → ℤ) × ℤ)) (vis : (Fin 3 → ℤ) × ℤ → Prop)
    (shift : (Fin 3 → ℤ) × ℤ → ℤ × (Fin 2 → ℤ)) : Finset (ℤ × (Fin 2 → ℤ)) := by
  classical
  exact if h : S.Finite then (h.toFinset.filter vis).image shift else ∅

theorem mem_kernelCodes {S : Set ((Fin 3 → ℤ) × ℤ)} (hS : S.Finite)
    {vis : (Fin 3 → ℤ) × ℤ → Prop} {shift : (Fin 3 → ℤ) × ℤ → ℤ × (Fin 2 → ℤ)}
    {Z : (Fin 3 → ℤ) × ℤ} (hZ : Z ∈ S) (hv : vis Z) : shift Z ∈ kernelCodes S vis shift := by
  classical
  unfold kernelCodes
  rw [dif_pos hS]
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hZ, hv⟩)

/-- Total table size: a bounded number of visiting groups per heavy cell. -/
theorem sum_kernelCodes_card_le {I : Type*} [Fintype I] {S : Set ((Fin 3 → ℤ) × ℤ)}
    (hS : S.Finite) (vis : I → (Fin 3 → ℤ) × ℤ → Prop)
    (shift : I → (Fin 3 → ℤ) × ℤ → ℤ × (Fin 2 → ℤ)) {L : ℝ}
    (hL : ∀ Z ∈ S, ∀ (F : Finset I), (∀ i ∈ F, vis i Z) → (F.card : ℝ) ≤ L) :
    (∑ i : I, ((kernelCodes S (vis i) (shift i)).card : ℝ)) ≤ L * (hS.toFinset.card : ℝ) := by
  classical
  have h := normalized_table_card_bound hS.toFinset vis shift (L := L) (by
    intro Z hZ
    exact hL Z (hS.mem_toFinset.mp hZ) _ (fun i hi => (Finset.mem_filter.mp hi).2))
  convert h using 3 with i
  unfold kernelCodes
  rw [dif_pos hS]

/-- The normalized code of a group incidence: the shifted fine cell, when the mesh is aligned
with the block and with the group's position bins. -/
def shiftCode (D m j : ℕ) (σ : Fin 2 → ℤ) (Z : (Fin 3 → ℤ) × ℤ) : ℤ × (Fin 2 → ℤ) :=
  (Z.1 0 - (j : ℤ) * D, fun k => Z.1 k.succ - σ k * m)

theorem normalized_code_eq (P : MvPolynomial (Fin 4) ℝ) (B a : ℝ) {q R : ℝ} (hq : 0 < q)
    (hR : 0 < R) {D m : ℕ} (hm : 0 < m) (hDm : (D : ℝ) = R * m) (j : ℕ)
    (Γ : (Fin 2 → ℤ) × ℤ) (p : Incidence) :
    (⌊p.2 * (D : ℝ)⌋, fun k : Fin 2 => ⌊(D : ℝ) *
      (groupIntercept q a ((j : ℝ) * q) (R * q) Γ p.1 +
        p.2 • groupVelocity q (R * q) p.1) k⌋) =
      shiftCode D m j Γ.1 (worldCell (q / D) (q / m) B a (timeLift ((j : ℝ) * q) q p)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hD' : (0 : ℝ) < D := by rw [hDm]; positivity
  simp only [shiftCode, worldCell, timeLift, Prod.mk.injEq]
  constructor
  · have h : graphPoint p.1 ((j : ℝ) * q + q * p.2) (Fin.castSucc 0) / cellScale (q / D) (q / m) 0 =
        ((j * D : ℤ) : ℝ) + p.2 * D := by
      simp only [graphPoint, cellScale]
      push_cast
      field_simp
    rw [h, Int.floor_intCast_add]
    ring
  · funext k
    have hk : graphPoint p.1 ((j : ℝ) * q + q * p.2) k.succ.castSucc /
        cellScale (q / D) (q / m) k.succ =
        (D : ℝ) * (groupIntercept q a ((j : ℝ) * q) (R * q) Γ p.1 +
          p.2 • groupVelocity q (R * q) p.1) k + ((Γ.1 k * m : ℤ) : ℝ) := by
      fin_cases k <;>
      · simp [graphPoint, cellScale, groupIntercept, groupVelocity, normalizedBlockIntercept,
          normalizedBlockVelocity, midpointGroupCenter, planarPoint, planarVelocity, hDm]
        field_simp
        ring
    rw [hk, Int.floor_add_intCast]
    ring

end

end Submission.Obl.k4_horizon_chart_assembly

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

noncomputable section

/-! ## Native groups visiting one cell -/

/-- The incidences used by the assembly: those of eligible trajectories with the native
derivative floor. Both conditions hold almost everywhere. -/
def assemblyEvent (P : MvPolynomial (Fin 4) ℝ) (B K H : ℝ) (E : Set Incidence) :
    Set Incidence :=
  {p | p ∈ E ∧ nativeEligible P B K H p.1 ∧
    B / K ≤ |eval (graphPoint p.1 p.2) (pderiv (3 : Fin 4) P)|}

theorem assemblyEvent_subset (P : MvPolynomial (Fin 4) ℝ) (B K H : ℝ) (E : Set Incidence) :
    assemblyEvent P B K H E ⊆ E := fun _ hp => hp.1

/-- Group `Γ` of block `j` has an incidence of `E'` in the cell `Z`. -/
def groupVisits (P : MvPolynomial (Fin 4) ℝ) (B K H a q ρ₁ ρ₂ : ℝ) (E' : Set Incidence)
    (j : ℕ) (Γ : (Fin 2 → ℤ) × ℤ) (Z : (Fin 3 → ℤ) × ℤ) : Prop :=
  ∃ p ∈ E', p.1 ∈ nativeGroup P B K H ((j : ℝ) * q) q a Γ ∧
    p.2 ∈ Ico ((j : ℝ) * q) ((j : ℝ) * q + q) ∧ worldCell ρ₁ ρ₂ B a p = Z

/-- The number of native groups that may visit one fine cell. -/
def nativeMultiplicity (K : ℝ) : ℝ := (4 * K + 7) ^ 2 * (212 * K + 7)

/-- The time bin of a cell determines the block of every group visiting it. -/
theorem groupVisits_time_bin {P : MvPolynomial (Fin 4) ℝ} {B K H a q ρ₂ : ℝ}
    {E' : Set Incidence} (hq : 0 < q) {D : ℕ} (hD : 0 < D) {j : ℕ}
    {Γ : (Fin 2 → ℤ) × ℤ} {Z : (Fin 3 → ℤ) × ℤ}
    (h : groupVisits P B K H a q (q / D) ρ₂ E' j Γ Z) :
    (j : ℤ) * D ≤ Z.1 0 ∧ Z.1 0 < (j : ℤ) * D + D := by
  obtain ⟨p, -, -, ht, hZ⟩ := h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hz : Z.1 0 = ⌊p.2 / (q / D)⌋ := by
    rw [← hZ]
    rfl
  have hx : p.2 / (q / D) = p.2 * D / q := by field_simp
  rw [hz, hx]
  constructor
  · apply Int.le_floor.mpr
    push_cast
    rw [le_div_iff₀ hq]
    nlinarith [ht.1]
  · apply Int.floor_lt.mpr
    push_cast
    rw [div_lt_iff₀ hq]
    nlinarith [ht.2]

theorem groupVisits_block_eq {P : MvPolynomial (Fin 4) ℝ} {B K H a q ρ₂ : ℝ}
    {E' : Set Incidence} (hq : 0 < q) {D : ℕ} (hD : 0 < D) {j j' : ℕ}
    {Γ Γ' : (Fin 2 → ℤ) × ℤ} {Z : (Fin 3 → ℤ) × ℤ}
    (h : groupVisits P B K H a q (q / D) ρ₂ E' j Γ Z)
    (h' : groupVisits P B K H a q (q / D) ρ₂ E' j' Γ' Z) : j = j' := by
  obtain ⟨h1, h2⟩ := groupVisits_time_bin hq hD h
  obtain ⟨h1', h2'⟩ := groupVisits_time_bin hq hD h'
  have hD' : (0 : ℤ) < D := by exact_mod_cast hD
  have hlt : (j : ℤ) < j' + 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hlt' : (j' : ℤ) < j + 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  omega

/-- Every group visiting a cell lies in the cell's one native decoder. -/
theorem groupVisits_mem_decoder (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {B K H a q ρ₁ ρ₂ : ℝ} (hB : 0 < B) (hK : 0 ≤ K) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |P.coeff e| ≤ H) (hBinv : B⁻¹ ≤ H)
    (ha : 0 < a) (ha1 : a ≤ 1) (hq : 0 < q) (hqa : q ≤ a)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂) (hρ₂q : ρ₂ ≤ q)
    (hmesh : 4131 * H * (3 * H + 1) ^ 2 * ρ₂ ≤ a)
    {E E' : Set Incidence} (hE' : E' ⊆ E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {j : ℕ} (hj : (j : ℝ) * q ≤ 1) {Γ : (Fin 2 → ℤ) × ℤ} {Z : (Fin 3 → ℤ) × ℤ}
    (h : groupVisits P B K H a q ρ₁ ρ₂ E' j Γ Z) :
    Γ ∈ cellDecoder P B a q ρ₁ ρ₂ (2 * K) Z.1 Z.2 := by
  obtain ⟨p, hpE, hpU, hpt, hZ⟩ := h
  obtain ⟨l, t⟩ := p
  have ht01 : t ∈ Icc (0 : ℝ) 1 := (hunit (hE' hpE)).2
  have hs01 : (j : ℝ) * q ∈ Icc (0 : ℝ) 1 := ⟨by positivity, hj⟩
  have hdt : |(j : ℝ) * q - t| ≤ q := by
    rw [abs_le]
    constructor <;> linarith [hpt.1, hpt.2]
  have helig := hpU.1
  have hcode := hpU.2
  have hwhole := helig.2.2
  have hV : ‖planarVelocity l‖ ≤ 2 * K := nativeEligible_velocity_norm helig
  have hbound : ∀ u ∈ Icc (0 : ℝ) 1, |eval (graphPoint l u) P| ≤ 2 * K := by
    intro u hu
    have hh := (hwhole u hu).2.1
    change |eval (graphPoint l u) P| ≤ K * 1 at hh
    linarith
  have hfirst : |eval (graphPoint l t) (pderiv (3 : Fin 4) P)| ≤ 2 * K * B := by
    have hh := (hwhole t ht01).2.2.1
    change |eval (graphPoint l t) (pderiv (3 : Fin 4) P)| ≤ K * B at hh
    nlinarith
  have hsecond : |eval (graphPoint l t)
      (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ 2 * K * B ^ 2 := by
    have hh := (hwhole t ht01).2.2.2
    change |eval (graphPoint l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤
      K * B ^ 2 / 1 at hh
    rw [div_one] at hh
    nlinarith [sq_nonneg B]
  have hcoord := graphPoint_coord_bound hH l helig.2.1 ht01
  have hrep : ∀ i, |(Function.update (graphPoint l t) (3 : Fin 4)
      (a * (⌊B * graphPoint l t 3 / a⌋ : ℝ) / B)) i| ≤ 3 * H := by
    intro i
    have h := hidden_representative_coord_bound (graphPoint l t) hB ha ha1 hcoord i
    linarith
  have hmem := native_midpoint_cell_list P hP l (K := 2 * K) (by positivity) hB ha ha1 hq hqa
    hρ₁ hρ₁₂ hρ₂q (by linarith : (0 : ℝ) ≤ H) (by linarith : (1 : ℝ) ≤ 3 * H) hcoeff hrep
    hmesh hV hbound hs01 ht01 hdt hfirst hsecond
  rw [hcode] at hmem
  rw [← hZ]
  exact hmem

/-- At most `nativeMultiplicity K` (block, group) pairs visit one cell. -/
theorem groupVisits_card_le (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {B K H a q ρ₂ : ℝ} (hB : 0 < B) (hK : 0 ≤ K) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |P.coeff e| ≤ H) (hBinv : B⁻¹ ≤ H)
    (ha : 0 < a) (ha1 : a ≤ 1) (hq : 0 < q) (hqa : q ≤ a) {D : ℕ} (hD : 0 < D)
    (hρ₁₂ : q / D ≤ ρ₂) (hρ₂q : ρ₂ ≤ q)
    (hmesh : 4131 * H * (3 * H + 1) ^ 2 * ρ₂ ≤ a)
    {E E' : Set Incidence} (hE' : E' ⊆ E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (Z : (Fin 3 → ℤ) × ℤ) (F : Finset (ℕ × ((Fin 2 → ℤ) × ℤ)))
    (hFj : ∀ i ∈ F, (i.1 : ℝ) * q ≤ 1)
    (hF : ∀ i ∈ F, groupVisits P B K H a q (q / D) ρ₂ E' i.1 i.2 Z) :
    (F.card : ℝ) ≤ nativeMultiplicity K := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hcard : F.card ≤ (cellDecoder P B a q (q / D) ρ₂ (2 * K) Z.1 Z.2).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.2)
    · intro i hi
      exact groupVisits_mem_decoder P hP hB hK hH hcoeff hBinv ha ha1 hq hqa
        (by positivity) hρ₁₂ hρ₂q hmesh hE' hunit (hFj i hi) (hF i hi)
    · intro i hi i' hi' hii'
      have hj := groupVisits_block_eq hq hD (hF i hi) (hF i' hi')
      exact Prod.ext hj hii'
  calc
    (F.card : ℝ) ≤ (cellDecoder P B a q (q / D) ρ₂ (2 * K) Z.1 Z.2).card := by
      exact_mod_cast hcard
    _ ≤ (2 * (2 * K) + 7) ^ 2 * (106 * (2 * K) + 7) :=
      cellDecoder_card P B a q (q / D) ρ₂ (by positivity) Z.1 Z.2
    _ = nativeMultiplicity K := by unfold nativeMultiplicity; ring

end

end Submission.Obl.k4_horizon_chart_assembly
