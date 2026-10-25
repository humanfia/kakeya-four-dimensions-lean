import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Prune2

/-!
# First pruning: coarse labels per crossing cell

Entries are (coarse label, crossing cell); the reference weight `h² H a₀^d` is put on the
cells of the label's plank grid. Kept points see a dense coarse label in their cell.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace CoreData

variable (D : CoreData α)

/-- P1 entries. -/
def E1 (hc Hx : ℝ) (e : Fin D.f₀.n × (ℤ × ℤ × ℤ)) : Set (α × ℝ) :=
  (D.f₀.B e.1 ×ˢ D.f₀.I e.1) ∩ D.G0 ∩ {p | xcell D.b hc Hx p = e.2}

/-- Crossing cells met by a coarse label. -/
def grid1 (hc Hx : ℝ) (j : Fin D.f₀.n) : Finset (ℤ × ℤ × ℤ) :=
  plankGrid hc Hx D.f₀.q D.K (D.N ^ (-D.κ * D.s₀))
    (((D.f₀.j j : ℕ) : ℝ) / 2 ^ D.f₀.T + D.f₀.q / 2) (D.f₀.c j)

/-- P1 reference weights. -/
def R1 (hc Hx : ℝ) (e : Fin D.f₀.n × (ℤ × ℤ × ℤ)) : ℝ≥0∞ := by
  classical
  exact if e.2 ∈ D.grid1 hc Hx e.1 then ENNReal.ofReal (hc ^ 2 * Hx * D.a₀ ^ D.d) else 0

/-- Points kept by P1. -/
def G1 (hc Hx K₁ : ℝ) : Set (α × ℝ) :=
  pruned D.ρs D.G0 (D.E1 hc Hx) (D.R1 hc Hx) (ENNReal.ofReal K₁)

end CoreData

theorem mem_blk_center {T : ℕ} {j : ℕ} {t : ℝ} (ht : t ∈ blk T j) :
    |t - ((j : ℝ) / 2 ^ T + ((2 : ℝ) ^ T)⁻¹ / 2)| ≤ ((2 : ℝ) ^ T)⁻¹ / 2 := by
  obtain ⟨h1, h2⟩ := ht
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  have e : ((j : ℝ) + 1) / 2 ^ T = (j : ℝ) / 2 ^ T + ((2 : ℝ) ^ T)⁻¹ := by
    rw [add_div, one_div]
  rw [e] at h2
  rw [abs_le]; constructor <;> linarith

theorem mem_grid1 (D : CoreData α) (H : CoreHyp D) {hc Hx : ℝ} (hhc : 0 < hc) (hHx : 0 < Hx)
    {p : α × ℝ} {j : Fin D.f₀.n} (hp : p.1 ∈ D.f₀.A j ∧ p.2 ∈ D.f₀.I j) :
    xcell D.b hc Hx p ∈ D.grid1 hc Hx j := by
  obtain ⟨g1, g2, -⟩ := H.f₀good.geom j p.1 hp.1 p.2 hp.2
  unfold CoreData.grid1
  exact mem_plankGrid hhc hHx (mem_blk_center hp.2) g1 g2

theorem E1_uniq (D : CoreData α) (H : CoreHyp D) (hc Hx : ℝ) :
    ∀ x e e', x ∈ D.E1 hc Hx e → x ∈ D.E1 hc Hx e' → e = e' := by
  intro x e e' hx hx'
  have hj : e.1 = e'.1 := D.f₀.label_unique H.f₀good.disj hx.1.2.2.1
    ⟨H.f₀good.BA _ hx.1.1.1, hx.1.1.2⟩ ⟨H.f₀good.BA _ hx'.1.1.1, hx'.1.1.2⟩
  have hω : e.2 = e'.2 := hx.2.symm.trans hx'.2
  exact Prod.ext hj hω

theorem E1_subset_G0 (D : CoreData α) (hc Hx : ℝ) (e : Fin D.f₀.n × (ℤ × ℤ × ℤ)) :
    D.E1 hc Hx e ⊆ D.G0 := fun _ hx => hx.1.2

theorem measurableSet_E1 (D : CoreData α) (H : CoreHyp D) (hc Hx : ℝ)
    (e : Fin D.f₀.n × (ℤ × ℤ × ℤ)) : MeasurableSet (D.E1 hc Hx e) := by
  have hI : MeasurableSet (D.f₀.I e.1) := by unfold Fam.I blk; exact measurableSet_Icc
  exact (((H.f₀good.measB e.1).prod hI).inter (measurableSet_G0 D H)).inter
    (measurableSet_xcell_eq H.bmeas hc Hx e.2)

theorem G1_subset (D : CoreData α) (hc Hx K₁ : ℝ) : D.G1 hc Hx K₁ ⊆ D.G0 :=
  pruned_subset _ _ _ _ _

theorem measurableSet_G1 (D : CoreData α) (H : CoreHyp D) (hc Hx K₁ : ℝ) :
    MeasurableSet (D.G1 hc Hx K₁) :=
  measurableSet_pruned _ (measurableSet_G0 D H) _ _ _ (measurableSet_E1 D H hc Hx)

theorem G1_loss (D : CoreData α) (hc Hx K₁ : ℝ) :
    D.ρs (D.G0 \ D.G1 hc Hx K₁) ≤ (∑' e, D.R1 hc Hx e) / ENNReal.ofReal K₁ :=
  measure_diff_pruned_le _ _ _ _ _

/-- Density of the coarse label of a kept point in its crossing cell. -/
theorem G1_dense (D : CoreData α) (H : CoreHyp D) {hc Hx K₁ : ℝ} (hhc : 0 < hc) (hHx : 0 < Hx)
    (hK₁ : 0 < K₁) :
    ∀ q ∈ D.G1 hc Hx K₁, ∃ j, q.1 ∈ D.f₀.B j ∧ q.2 ∈ D.f₀.I j ∧
      ENNReal.ofReal (hc ^ 2 * Hx * D.a₀ ^ D.d / K₁) ≤
        D.ρs ((D.f₀.B j ×ˢ D.f₀.I j) ∩ D.G1 hc Hx K₁ ∩
          {p | xcell D.b hc Hx p = xcell D.b hc Hx q}) := by
  intro q hq
  have hq0 := G1_subset D hc Hx K₁ hq
  obtain ⟨j, hBj, hIj⟩ := hq0.2.2.2.2.1
  refine ⟨j, hBj, hIj, ?_⟩
  have hqe : q ∈ D.E1 hc Hx (j, xcell D.b hc Hx q) := ⟨⟨⟨hBj, hIj⟩, hq0⟩, rfl⟩
  obtain ⟨hsub, hheavy⟩ := entry_subset_pruned (E1_uniq D H hc Hx) (E1_subset_G0 D hc Hx) hq hqe
  have hR : D.R1 hc Hx (j, xcell D.b hc Hx q) = ENNReal.ofReal (hc ^ 2 * Hx * D.a₀ ^ D.d) := by
    unfold CoreData.R1
    rw [if_pos (mem_grid1 D H hhc hHx ⟨H.f₀good.BA j hBj, hIj⟩)]
  rw [hR, ← ENNReal.ofReal_div_of_pos hK₁] at hheavy
  refine hheavy.trans (measure_mono ?_)
  intro x hx
  exact ⟨⟨hx.1.1, hsub hx⟩, hx.2⟩

/-- Numerics of one plank grid. -/
theorem plank_count_bound {K q g hc Hx : ℝ} (c : Fin 5 → ℝ) (hK : 1 ≤ K) (hq : 0 < q)
    (hg : 0 < g) (hg1 : g ≤ 1) (hhc : 0 < hc) (hHx : 0 < Hx) (hcq : hc ≤ q * g)
    (hHxq : Hx ≤ K * q * g) (hcb : ∀ e, |c e| ≤ K) :
    (2 * (q / 2) / hc + 5) * (2 * (K * q + |c 1| * hc) / hc + 5) *
        (2 * (K * q * g + (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * hc) / Hx + 5) *
        (hc ^ 2 * Hx) ≤ 810 * K ^ 3 * q ^ 3 * g := by
  have hK0 : 0 ≤ K := by linarith
  have hc1 := hcb 1; have hc3 := hcb 3; have hc4 := hcb 4
  have hqg : q * g ≤ q := mul_le_of_le_one_right hq.le hg1
  have hcq' : hc ≤ q := hcq.trans hqg
  have hm1 : |-(c 3 + c 4 * c 1)| ≤ K + K ^ 2 := by
    rw [abs_neg]
    calc |c 3 + c 4 * c 1| ≤ |c 3| + |c 4| * |c 1| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ K + K * K := add_le_add hc3 (mul_le_mul hc4 hc1 (abs_nonneg _) hK0)
      _ = K + K ^ 2 := by ring
  have hm2 : |c 4| * (1 + |c 1|) ≤ K * (1 + K) :=
    mul_le_mul hc4 (by linarith) (by positivity) hK0
  have e1 : (2 * (q / 2) / hc + 5) * hc = q + 5 * hc := by field_simp
  have e2 : (2 * (K * q + |c 1| * hc) / hc + 5) * hc = 2 * (K * q + |c 1| * hc) + 5 * hc := by
    field_simp
  have e3 : (2 * (K * q * g + (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * hc) / Hx + 5) * Hx =
      2 * (K * q * g + (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * hc) + 5 * Hx := by
    field_simp
  have hA : q + 5 * hc ≤ 6 * q := by linarith
  have hB : 2 * (K * q + |c 1| * hc) + 5 * hc ≤ 9 * K * q := by
    have : |c 1| * hc ≤ K * q := mul_le_mul hc1 hcq' hhc.le hK0
    nlinarith
  have hC : 2 * (K * q * g + (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * hc) + 5 * Hx ≤
      15 * K ^ 2 * (q * g) := by
    have h1 : (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * hc ≤ (2 * K + 2 * K ^ 2) * (q * g) :=
      mul_le_mul (by nlinarith) hcq hhc.le (by positivity)
    have h2 : K * q * g ≤ K ^ 2 * (q * g) := by
      have : K ≤ K ^ 2 := by nlinarith
      nlinarith [mul_pos hq hg]
    have h3 : 2 * K ≤ 2 * K ^ 2 := by nlinarith
    nlinarith [mul_pos hq hg]
  calc (2 * (q / 2) / hc + 5) * (2 * (K * q + |c 1| * hc) / hc + 5) *
        (2 * (K * q * g + (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * hc) / Hx + 5) *
        (hc ^ 2 * Hx)
      = ((2 * (q / 2) / hc + 5) * hc) * ((2 * (K * q + |c 1| * hc) / hc + 5) * hc) *
        ((2 * (K * q * g + (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * hc) / Hx + 5) * Hx) := by
          ring
    _ = (q + 5 * hc) * (2 * (K * q + |c 1| * hc) + 5 * hc) *
        (2 * (K * q * g + (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * hc) + 5 * Hx) := by
          rw [e1, e2, e3]
    _ ≤ (6 * q) * (9 * K * q) * (15 * K ^ 2 * (q * g)) := by
          apply mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hC
            (by positivity) (by positivity)
    _ = 810 * K ^ 3 * q ^ 3 * g := by ring

/-- The P1 reference budget. -/
theorem R1_tsum_le (D : CoreData α) (H : CoreHyp D) {hc Hx : ℝ} (hhc : 0 < hc) (hHx : 0 < Hx)
    (hcq : hc ≤ D.f₀.q * D.N ^ (-D.κ * D.s₀))
    (hHxq : Hx ≤ D.K * D.f₀.q * D.N ^ (-D.κ * D.s₀)) (hg1 : D.N ^ (-D.κ * D.s₀) ≤ 1) :
    ∑' e, D.R1 hc Hx e ≤ ENNReal.ofReal (810 * D.K ^ 4) := by
  classical
  haveI := H.νprob
  have hK : 1 ≤ D.K := H.K1
  have hK0 : 0 ≤ D.K := by linarith
  have hN0 : 0 < D.N := by linarith [H.N2]
  set g := D.N ^ (-D.κ * D.s₀) with hgdef
  have hg : 0 < g := Real.rpow_pos_of_pos hN0 _
  have hq := f₀_q_pos D
  have hinner : ∀ j : Fin D.f₀.n, ∑' ω, D.R1 hc Hx (j, ω) =
      ((D.grid1 hc Hx j).card : ℝ≥0∞) * ENNReal.ofReal (hc ^ 2 * Hx * D.a₀ ^ D.d) := by
    intro j
    rw [tsum_eq_sum (s := D.grid1 hc Hx j)]
    · rw [Finset.sum_congr rfl (fun ω hω => (by unfold CoreData.R1; rw [if_pos hω] :
        D.R1 hc Hx (j, ω) = ENNReal.ofReal (hc ^ 2 * Hx * D.a₀ ^ D.d))),
        Finset.sum_const, nsmul_eq_mul]
    · intro ω hω; unfold CoreData.R1; rw [if_neg hω]
  have hper : ∀ j : Fin D.f₀.n,
      ((D.grid1 hc Hx j).card : ℝ≥0∞) * ENNReal.ofReal (hc ^ 2 * Hx * D.a₀ ^ D.d) ≤
        ENNReal.ofReal (810 * D.K ^ 4) * (ENNReal.ofReal D.f₀.q * D.ν (D.f₀.A j)) := by
    intro j
    have hcard := card_plankGrid (c := D.f₀.c j) (tm := ((D.f₀.j j : ℕ) : ℝ) / 2 ^ D.f₀.T +
      D.f₀.q / 2) hhc hHx hq.le hK0 hg.le
    have hnum := plank_count_bound (D.f₀.c j) hK hq hg hg1 hhc hHx hcq hHxq (H.f₀good.cbd j)
    have hfloor := H.f₀good.floorA j
    have ha0 : 0 < D.a₀ ^ D.d := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN0 _) _
    -- real inequality
    have hreal : ((D.grid1 hc Hx j).card : ℝ) * (hc ^ 2 * Hx * D.a₀ ^ D.d) ≤
        810 * D.K ^ 4 * D.f₀.q * ((D.N ^ (-D.s₀)) ^ D.d * D.f₀.q ^ 2 * g / D.K) := by
      have h1 : ((D.grid1 hc Hx j).card : ℝ) * (hc ^ 2 * Hx) ≤ 810 * D.K ^ 3 * D.f₀.q ^ 3 * g :=
        (mul_le_mul_of_nonneg_right hcard (by positivity)).trans hnum
      have e : 810 * D.K ^ 4 * D.f₀.q * ((D.N ^ (-D.s₀)) ^ D.d * D.f₀.q ^ 2 * g / D.K) =
          810 * D.K ^ 3 * D.f₀.q ^ 3 * g * D.a₀ ^ D.d := by
        unfold CoreData.a₀; field_simp
      rw [e]
      calc ((D.grid1 hc Hx j).card : ℝ) * (hc ^ 2 * Hx * D.a₀ ^ D.d)
          = ((D.grid1 hc Hx j).card : ℝ) * (hc ^ 2 * Hx) * D.a₀ ^ D.d := by ring
        _ ≤ 810 * D.K ^ 3 * D.f₀.q ^ 3 * g * D.a₀ ^ D.d :=
            mul_le_mul_of_nonneg_right h1 ha0.le
    calc ((D.grid1 hc Hx j).card : ℝ≥0∞) * ENNReal.ofReal (hc ^ 2 * Hx * D.a₀ ^ D.d)
        = ENNReal.ofReal (((D.grid1 hc Hx j).card : ℝ) * (hc ^ 2 * Hx * D.a₀ ^ D.d)) := by
          rw [ENNReal.ofReal_mul (p := ((D.grid1 hc Hx j).card : ℝ)) (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (810 * D.K ^ 4 * D.f₀.q *
            ((D.N ^ (-D.s₀)) ^ D.d * D.f₀.q ^ 2 * g / D.K)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (810 * D.K ^ 4) * (ENNReal.ofReal D.f₀.q *
            ENNReal.ofReal ((D.N ^ (-D.s₀)) ^ D.d * D.f₀.q ^ 2 * g / D.K)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (810 * D.K ^ 4) * (ENNReal.ofReal D.f₀.q * D.ν (D.f₀.A j)) := by
          gcongr
  rw [ENNReal.tsum_prod', tsum_fintype]
  calc ∑ j, ∑' ω, D.R1 hc Hx (j, ω)
      = ∑ j, ((D.grid1 hc Hx j).card : ℝ≥0∞) * ENNReal.ofReal (hc ^ 2 * Hx * D.a₀ ^ D.d) :=
        Finset.sum_congr rfl (fun j _ => hinner j)
    _ ≤ ∑ j, ENNReal.ofReal (810 * D.K ^ 4) * (ENNReal.ofReal D.f₀.q * D.ν (D.f₀.A j)) :=
        Finset.sum_le_sum (fun j _ => hper j)
    _ = ENNReal.ofReal (810 * D.K ^ 4) * ∑ j, ENNReal.ofReal D.f₀.q * D.ν (D.f₀.A j) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (810 * D.K ^ 4) * 1 := by
        gcongr
        exact label_weights_le_one D.ν D.f₀ H.f₀good.measA H.f₀good.disj
    _ = _ := mul_one _

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
