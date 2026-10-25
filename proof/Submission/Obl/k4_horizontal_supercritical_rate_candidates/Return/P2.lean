import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.P1

/-!
# Second pruning: slices per crossing cell

Entries are (slice, crossing cell) inside the P1-kept set; the reference weight
`h² H a₁^d π(direction)` is put on the cells of the slice's strip grid. Kept points see a
dense slice in their cell, with a direction bin of positive palette mass.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace CoreData

variable (D : CoreData α)

/-- P2 entries. -/
def E2 (hc Hx K₁ : ℝ) (e : Fin D.Ly.n × (ℤ × ℤ × ℤ)) : Set (α × ℝ) :=
  D.G1 hc Hx K₁ ∩ (D.Ly.C e.1 ×ˢ univ) ∩ {p | xcell D.b hc Hx p = e.2}

/-- Crossing cells met by a slice. -/
def grid2 (hc Hx : ℝ) (i : Fin D.Ly.n) : Finset (ℤ × ℤ × ℤ) :=
  stripGrid hc Hx (2 * D.χ) (D.N ^ D.εL * D.Dw) ((D.Ly.qp i 1 : ℝ) * D.χ)
    ((D.Ly.qp i 2 : ℝ) * D.Dw) ((D.Ly.qp i 0 : ℝ) * D.χ) ((D.Ly.qp i 1 : ℝ) * D.χ)

/-- P2 reference weights. -/
def R2 (hc Hx : ℝ) (e : Fin D.Ly.n × (ℤ × ℤ × ℤ)) : ℝ≥0∞ := by
  classical
  exact if e.2 ∈ D.grid2 hc Hx e.1 then
    ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d) * D.π (D.dirBin e.1) else 0

/-- Points kept by P2. -/
def G2 (hc Hx K₁ : ℝ) : Set (α × ℝ) :=
  pruned D.ρs (D.G1 hc Hx K₁) (D.E2 hc Hx K₁) (D.R2 hc Hx) (ENNReal.ofReal K₁)

end CoreData

/-- Position of a slice's line at time `t`. -/
theorem slice_x1_bound (D : CoreData α) (H : CoreHyp D) {i : Fin D.Ly.n} {l : α}
    (hl : l ∈ D.Ly.C i) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |x1 D.b l t - ((D.Ly.qp i 1 : ℝ) * D.χ + t * ((D.Ly.qp i 0 : ℝ) * D.χ))| ≤ 2 * D.χ := by
  have hχ : 0 < D.χ := Real.rpow_pos_of_pos (by linarith [H.N2]) _
  obtain ⟨h3, h0, -, -⟩ := H.lygood.bins i l hl
  have a3 := (floor_div_eq_iff_mem_Ico hχ _).mp h3
  have a0 := (floor_div_eq_iff_mem_Ico hχ _).mp h0
  unfold x1
  have e : D.b l 0 + t * D.b l 3 - ((D.Ly.qp i 1 : ℝ) * D.χ + t * ((D.Ly.qp i 0 : ℝ) * D.χ)) =
      (D.b l 0 - (D.Ly.qp i 1 : ℝ) * D.χ) + t * (D.b l 3 - (D.Ly.qp i 0 : ℝ) * D.χ) := by ring
  rw [e, abs_le]
  have u1 : 0 ≤ t * (D.b l 3 - (D.Ly.qp i 0 : ℝ) * D.χ) :=
    mul_nonneg ht.1 (by linarith [a3.1])
  have u2 : t * (D.b l 3 - (D.Ly.qp i 0 : ℝ) * D.χ) ≤ D.χ := by
    have : D.b l 3 - (D.Ly.qp i 0 : ℝ) * D.χ ≤ D.χ := by linarith [a3.2]
    nlinarith [ht.1, ht.2]
  constructor <;> linarith [a0.1, a0.2]

theorem mem_grid2 (D : CoreData α) (H : CoreHyp D) {hc Hx : ℝ} (hhc : 0 < hc) (hHx : 0 < Hx)
    {p : α × ℝ} (hp : NativeOK D p) {i : Fin D.Ly.n} (hpi : p.1 ∈ D.Ly.C i) :
    xcell D.b hc Hx p ∈ D.grid2 hc Hx i := by
  unfold CoreData.grid2
  apply mem_stripGrid hhc hHx hp.1 (slice_x1_bound D H hpi hp.1)
  have := (H.lygood.fit i p.1 hpi p.2 hp.1).1
  have e : x2 D.b p.1 p.2 - ((D.Ly.qp i 2 : ℝ) * D.Dw - p.2 * ((D.Ly.qp i 1 : ℝ) * D.χ)) =
      x2 D.b p.1 p.2 - (D.Ly.qp i 2 : ℝ) * D.Dw + p.2 * ((D.Ly.qp i 1 : ℝ) * D.χ) := by ring
  rw [e]; exact this

theorem E2_uniq (D : CoreData α) (H : CoreHyp D) (hc Hx K₁ : ℝ) :
    ∀ x e e', x ∈ D.E2 hc Hx K₁ e → x ∈ D.E2 hc Hx K₁ e' → e = e' := by
  intro x e e' hx hx'
  have hi : e.1 = e'.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (H.lygood.disj _ _ hne) hx.1.2.1 hx'.1.2.1
  exact Prod.ext hi (hx.2.symm.trans hx'.2)

theorem E2_subset_G1 (D : CoreData α) (hc Hx K₁ : ℝ) (e : Fin D.Ly.n × (ℤ × ℤ × ℤ)) :
    D.E2 hc Hx K₁ e ⊆ D.G1 hc Hx K₁ := fun _ hx => hx.1.1

theorem measurableSet_E2 (D : CoreData α) (H : CoreHyp D) (hc Hx K₁ : ℝ)
    (e : Fin D.Ly.n × (ℤ × ℤ × ℤ)) : MeasurableSet (D.E2 hc Hx K₁ e) :=
  ((measurableSet_G1 D H hc Hx K₁).inter ((H.lygood.meas e.1).prod MeasurableSet.univ)).inter
    (measurableSet_xcell_eq H.bmeas hc Hx e.2)

theorem G2_subset (D : CoreData α) (hc Hx K₁ : ℝ) : D.G2 hc Hx K₁ ⊆ D.G1 hc Hx K₁ :=
  pruned_subset _ _ _ _ _

theorem measurableSet_G2 (D : CoreData α) (H : CoreHyp D) (hc Hx K₁ : ℝ) :
    MeasurableSet (D.G2 hc Hx K₁) :=
  measurableSet_pruned _ (measurableSet_G1 D H hc Hx K₁) _ _ _ (measurableSet_E2 D H hc Hx K₁)

theorem G2_loss (D : CoreData α) (hc Hx K₁ : ℝ) :
    D.ρs (D.G1 hc Hx K₁ \ D.G2 hc Hx K₁) ≤ (∑' e, D.R2 hc Hx e) / ENNReal.ofReal K₁ :=
  measure_diff_pruned_le _ _ _ _ _

/-- A slice whose direction bin has no palette mass carries no good mass. -/
theorem slice_null_of_pi_zero (D : CoreData α) (H : CoreHyp D) (i : Fin D.Ly.n)
    (hπ : D.π (D.dirBin i) = 0) : D.ρs {p | p ∈ D.G0 ∧ p.1 ∈ D.Ly.C i} = 0 := by
  have hχ : 0 < D.χ := Real.rpow_pos_of_pos (by linarith [H.N2]) _
  have hsub : {p | p ∈ D.G0 ∧ p.1 ∈ D.Ly.C i} ⊆ ⋃ j, {p | p.1 ∈ D.f₀.B j ∧ p.2 ∈ D.f₀.I j ∧
      ⌊D.b p.1 3 / D.χ⌋ = D.Ly.qp i 0} := by
    intro p hp
    obtain ⟨j, hB, hI⟩ := hp.1.2.2.2.2.1
    exact mem_iUnion.mpr ⟨j, hB, hI, (H.lygood.bins i p.1 hp.2).1⟩
  refine le_antisymm ?_ zero_le
  calc D.ρs {p | p ∈ D.G0 ∧ p.1 ∈ D.Ly.C i}
      ≤ D.μ (⋃ j, {p | p.1 ∈ D.f₀.B j ∧ p.2 ∈ D.f₀.I j ∧ ⌊D.b p.1 3 / D.χ⌋ = D.Ly.qp i 0}) :=
        ((H.ρsρ.trans H.ρμ) _).trans' (measure_mono hsub)
    _ ≤ ∑' j, D.μ {p | p.1 ∈ D.f₀.B j ∧ p.2 ∈ D.f₀.I j ∧ ⌊D.b p.1 3 / D.χ⌋ = D.Ly.qp i 0} :=
        measure_iUnion_le _
    _ = 0 := by
        refine ENNReal.tsum_eq_zero.mpr (fun j => le_antisymm ?_ zero_le)
        refine (H.f₀good.vdom j (D.Ly.qp i 0)).trans (le_of_eq ?_)
        rw [dirBin_eq D hχ i, hπ, mul_zero]

/-- Density of the slice of a kept point in its crossing cell. -/
theorem G2_dense (D : CoreData α) (H : CoreHyp D) {hc Hx K₁ : ℝ} (hhc : 0 < hc) (hHx : 0 < Hx)
    (hK₁ : 0 < K₁) :
    ∀ p ∈ D.G2 hc Hx K₁, ∃ i, p.1 ∈ D.Ly.C i ∧ D.π (D.dirBin i) ≠ 0 ∧
      ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d / K₁) * D.π (D.dirBin i) ≤
        D.ρs (D.G1 hc Hx K₁ ∩ (D.Ly.C i ×ˢ univ) ∩
          {q | xcell D.b hc Hx q = xcell D.b hc Hx p}) := by
  intro p hp
  have hp1 := G2_subset D hc Hx K₁ hp
  have hp0 := G1_subset D hc Hx K₁ hp1
  obtain ⟨i, hi⟩ := hp0.2.2.2.2.2.2.2
  have hpe : p ∈ D.E2 hc Hx K₁ (i, xcell D.b hc Hx p) := ⟨⟨hp1, hi, mem_univ _⟩, rfl⟩
  obtain ⟨hheavy, hnz⟩ := heavy_of_mem_pruned hp hpe
  refine ⟨i, hi, ?_, ?_⟩
  · intro hπ
    refine hnz (le_antisymm ?_ zero_le)
    rw [← slice_null_of_pi_zero D H i hπ]
    exact measure_mono (fun x hx => ⟨G1_subset D hc Hx K₁ hx.1.1, hx.1.2.1⟩)
  · have hR : D.R2 hc Hx (i, xcell D.b hc Hx p) =
        ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d) * D.π (D.dirBin i) := by
      unfold CoreData.R2
      rw [if_pos (mem_grid2 D H hhc hHx hp0.1 hi)]
    rw [hR] at hheavy
    have e : ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d / K₁) * D.π (D.dirBin i) =
        ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d) * D.π (D.dirBin i) / ENNReal.ofReal K₁ := by
      rw [ENNReal.ofReal_div_of_pos hK₁, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ring
    rw [e]
    exact hheavy

/-- Numerics of one strip grid. -/
theorem strip_count_bound {χ Dw E qa qb hc Hx : ℝ} (hχ : 0 < χ) (hDw : 0 < Dw) (hE : 1 ≤ E)
    (hhc : 0 < hc) (hHx : 0 < Hx) (hcχ : hc ≤ χ) (hcD : hc ≤ Dw) (hHxD : Hx ≤ Dw) (hc1 : hc ≤ 1)
    (hqa : |qa| ≤ E) (hqb : |qb| ≤ E) :
    (2 * (1 / 2) / hc + 5) * (2 * (2 * χ + |qa| * hc) / hc + 5) *
        (2 * (E * Dw + (|qb| + |(0 : ℝ)| * (1 + |qa|)) * hc) / Hx + 5) * (hc ^ 2 * Hx) ≤
      594 * E ^ 2 * χ * Dw := by
  have e1 : (2 * (1 / 2) / hc + 5) * hc = 1 + 5 * hc := by field_simp
  have e2 : (2 * (2 * χ + |qa| * hc) / hc + 5) * hc = 2 * (2 * χ + |qa| * hc) + 5 * hc := by
    field_simp
  have e3 : (2 * (E * Dw + (|qb| + |(0 : ℝ)| * (1 + |qa|)) * hc) / Hx + 5) * Hx =
      2 * (E * Dw + |qb| * hc) + 5 * Hx := by
    rw [abs_zero, zero_mul, add_zero]; field_simp
  have hA : 1 + 5 * hc ≤ 6 := by linarith
  have hB : 2 * (2 * χ + |qa| * hc) + 5 * hc ≤ 11 * E * χ := by
    have : |qa| * hc ≤ E * χ := mul_le_mul hqa hcχ hhc.le (by linarith)
    nlinarith
  have hC : 2 * (E * Dw + |qb| * hc) + 5 * Hx ≤ 9 * E * Dw := by
    have : |qb| * hc ≤ E * Dw := mul_le_mul hqb hcD hhc.le (by linarith)
    nlinarith
  calc (2 * (1 / 2) / hc + 5) * (2 * (2 * χ + |qa| * hc) / hc + 5) *
        (2 * (E * Dw + (|qb| + |(0 : ℝ)| * (1 + |qa|)) * hc) / Hx + 5) * (hc ^ 2 * Hx)
      = ((2 * (1 / 2) / hc + 5) * hc) * ((2 * (2 * χ + |qa| * hc) / hc + 5) * hc) *
        ((2 * (E * Dw + (|qb| + |(0 : ℝ)| * (1 + |qa|)) * hc) / Hx + 5) * Hx) := by ring
    _ = (1 + 5 * hc) * (2 * (2 * χ + |qa| * hc) + 5 * hc) * (2 * (E * Dw + |qb| * hc) + 5 * Hx) := by
        rw [e1, e2, e3]
    _ ≤ 6 * (11 * E * χ) * (9 * E * Dw) :=
        mul_le_mul (mul_le_mul hA hB (by positivity) (by norm_num)) hC (by positivity)
          (by positivity)
    _ = 594 * E ^ 2 * χ * Dw := by ring

/-- The P2 reference budget. -/
theorem R2_tsum_le (D : CoreData α) (H : CoreHyp D) {hc Hx : ℝ} (hhc : 0 < hc) (hHx : 0 < Hx)
    (hεL : 0 ≤ D.εL) (hcχ : hc ≤ D.χ) (hcD : hc ≤ D.Dw) (hHxD : Hx ≤ D.Dw) (hc1 : hc ≤ 1) :
    ∑' e, D.R2 hc Hx e ≤
      ENNReal.ofReal (594 * (D.N ^ D.εL) ^ 2) * ENNReal.ofReal (D.N ^ D.εL) := by
  classical
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hχ : 0 < D.χ := Real.rpow_pos_of_pos hN0 _
  have hDw : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hE : 1 ≤ D.N ^ D.εL := Real.one_le_rpow (by linarith [H.N2]) hεL
  have ha1 : 0 ≤ D.a₁ ^ D.d := Real.rpow_nonneg (Real.rpow_nonneg hN0.le _) _
  have hinner : ∀ i : Fin D.Ly.n, ∑' ω, D.R2 hc Hx (i, ω) =
      ((D.grid2 hc Hx i).card : ℝ≥0∞) *
        (ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d) * D.π (D.dirBin i)) := by
    intro i
    rw [tsum_eq_sum (s := D.grid2 hc Hx i)]
    · rw [Finset.sum_congr rfl (fun ω hω => (by unfold CoreData.R2; rw [if_pos hω] :
        D.R2 hc Hx (i, ω) = ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d) * D.π (D.dirBin i))),
        Finset.sum_const, nsmul_eq_mul]
    · intro ω hω; unfold CoreData.R2; rw [if_neg hω]
  have hper : ∀ i : Fin D.Ly.n, ((D.grid2 hc Hx i).card : ℝ≥0∞) *
      (ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d) * D.π (D.dirBin i)) ≤
        ENNReal.ofReal (594 * (D.N ^ D.εL) ^ 2) *
          (ENNReal.ofReal (D.χ * D.Dw * D.a₁ ^ D.d) * D.π (D.dirBin i)) := by
    intro i
    have hctr := H.lygood.ctr i
    have hqa : |(D.Ly.qp i 0 : ℝ) * D.χ| ≤ D.N ^ D.εL := by
      linarith [abs_nonneg ((D.Ly.qp i 1 : ℝ) * D.χ), abs_nonneg ((D.Ly.qp i 2 : ℝ) * D.Dw)]
    have hqb : |(D.Ly.qp i 1 : ℝ) * D.χ| ≤ D.N ^ D.εL := by
      linarith [abs_nonneg ((D.Ly.qp i 0 : ℝ) * D.χ), abs_nonneg ((D.Ly.qp i 2 : ℝ) * D.Dw)]
    have hcard := card_stripGrid (p := (D.Ly.qp i 1 : ℝ) * D.χ) (r := (D.Ly.qp i 2 : ℝ) * D.Dw)
      (v := (D.Ly.qp i 0 : ℝ) * D.χ) (w := (D.Ly.qp i 1 : ℝ) * D.χ) hhc hHx
      (by positivity : (0 : ℝ) ≤ 2 * D.χ) (by positivity : (0 : ℝ) ≤ D.N ^ D.εL * D.Dw)
    have hnum := strip_count_bound hχ hDw hE hhc hHx hcχ hcD hHxD hc1 hqa hqb
    have hreal : ((D.grid2 hc Hx i).card : ℝ) * (hc ^ 2 * Hx * D.a₁ ^ D.d) ≤
        594 * (D.N ^ D.εL) ^ 2 * (D.χ * D.Dw * D.a₁ ^ D.d) := by
      have h1 : ((D.grid2 hc Hx i).card : ℝ) * (hc ^ 2 * Hx) ≤
          594 * (D.N ^ D.εL) ^ 2 * D.χ * D.Dw := by
        unfold CoreData.grid2
        exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans hnum
      calc ((D.grid2 hc Hx i).card : ℝ) * (hc ^ 2 * Hx * D.a₁ ^ D.d)
          = ((D.grid2 hc Hx i).card : ℝ) * (hc ^ 2 * Hx) * D.a₁ ^ D.d := by ring
        _ ≤ 594 * (D.N ^ D.εL) ^ 2 * D.χ * D.Dw * D.a₁ ^ D.d :=
            mul_le_mul_of_nonneg_right h1 ha1
        _ = _ := by ring
    calc ((D.grid2 hc Hx i).card : ℝ≥0∞) *
        (ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d) * D.π (D.dirBin i))
        = ENNReal.ofReal (((D.grid2 hc Hx i).card : ℝ) * (hc ^ 2 * Hx * D.a₁ ^ D.d)) *
            D.π (D.dirBin i) := by
          rw [ENNReal.ofReal_mul (p := ((D.grid2 hc Hx i).card : ℝ)) (by positivity),
            ENNReal.ofReal_natCast]
          ring
      _ ≤ ENNReal.ofReal (594 * (D.N ^ D.εL) ^ 2 * (D.χ * D.Dw * D.a₁ ^ D.d)) *
            D.π (D.dirBin i) := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
  rw [ENNReal.tsum_prod', tsum_fintype]
  calc ∑ i, ∑' ω, D.R2 hc Hx (i, ω)
      = ∑ i, ((D.grid2 hc Hx i).card : ℝ≥0∞) *
          (ENNReal.ofReal (hc ^ 2 * Hx * D.a₁ ^ D.d) * D.π (D.dirBin i)) :=
        Finset.sum_congr rfl (fun i _ => hinner i)
    _ ≤ ∑ i, ENNReal.ofReal (594 * (D.N ^ D.εL) ^ 2) *
          (ENNReal.ofReal (D.χ * D.Dw * D.a₁ ^ D.d) * D.π (D.dirBin i)) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = ENNReal.ofReal (594 * (D.N ^ D.εL) ^ 2) *
          ∑ i, ENNReal.ofReal (D.χ * D.Dw * D.a₁ ^ D.d) * D.π (D.dirBin i) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact H.lygood.budget

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
