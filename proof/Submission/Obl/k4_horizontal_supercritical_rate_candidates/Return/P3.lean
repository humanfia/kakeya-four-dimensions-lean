import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Flat

/-!
# Third pruning: slices per count cell and hidden cell

Entries are (slice, count cell, hidden cell of width `W`) inside the P2-kept set. A slice's
kept points in one count cell meet at most three hidden cells (flatness), so the reference
budget is three times the strip budget. Kept slices of one direction in one count cell and
hidden cell are few: `2 K K₁ (b₃/h₃ + 2) h₃ W^d / (b₃ a₁^d)`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace CoreData

variable (D : CoreData α)

/-- P3 entries. -/
def E3 (r Hx K₁ r₃ b₃ W : ℝ) (e : (Fin D.Ly.n × (ℤ × ℤ × ℤ)) × ℤ) : Set (α × ℝ) :=
  D.G2 (D.N ^ (-r)) Hx K₁ ∩ (D.Ly.C e.1.1 ×ˢ univ) ∩
    {p | xcell D.b (D.N ^ (-r₃)) b₃ p = e.1.2} ∩ {p | ⌊x3 D.b p.1 p.2 / W⌋ = e.2}

/-- P3 reference weights. -/
def R3 (r Hx K₁ r₃ b₃ W : ℝ) (e : (Fin D.Ly.n × (ℤ × ℤ × ℤ)) × ℤ) : ℝ≥0∞ := by
  classical
  exact if (D.E3 r Hx K₁ r₃ b₃ W e).Nonempty then
    ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d) * D.π (D.dirBin e.1.1) else 0

/-- Points kept by P3. -/
def G3 (r Hx K₁ r₃ b₃ W : ℝ) : Set (α × ℝ) :=
  pruned D.ρs (D.G2 (D.N ^ (-r)) Hx K₁) (D.E3 r Hx K₁ r₃ b₃ W) (D.R3 r Hx K₁ r₃ b₃ W)
    (ENNReal.ofReal K₁)

end CoreData

theorem E3_uniq (D : CoreData α) (H : CoreHyp D) (r Hx K₁ r₃ b₃ W : ℝ) : ∀ x e e', x ∈ D.E3 r Hx K₁ r₃ b₃ W e → x ∈ D.E3 r Hx K₁ r₃ b₃ W e' →
    e = e' := by
  intro x e e' hx hx'
  have hi : e.1.1 = e'.1.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (H.lygood.disj _ _ hne) hx.1.1.2.1 hx'.1.1.2.1
  have hω : e.1.2 = e'.1.2 := hx.1.2.symm.trans hx'.1.2
  have hk : e.2 = e'.2 := hx.2.symm.trans hx'.2
  exact Prod.ext (Prod.ext hi hω) hk

theorem E3_subset_G2 (D : CoreData α) (r Hx K₁ r₃ b₃ W : ℝ) (e : (Fin D.Ly.n × (ℤ × ℤ × ℤ)) × ℤ) :
    D.E3 r Hx K₁ r₃ b₃ W e ⊆ D.G2 (D.N ^ (-r)) Hx K₁ := fun _ hx => hx.1.1.1

theorem measurableSet_E3 (D : CoreData α) (H : CoreHyp D) (r Hx K₁ r₃ b₃ W : ℝ) (e : (Fin D.Ly.n × (ℤ × ℤ × ℤ)) × ℤ) :
    MeasurableSet (D.E3 r Hx K₁ r₃ b₃ W e) := by
  have hk : MeasurableSet {p : α × ℝ | ⌊x3 D.b p.1 p.2 / W⌋ = e.2} :=
    (Int.measurable_floor.comp ((measurable_x3 H.bmeas).div_const W)) (measurableSet_singleton _)
  exact (((measurableSet_G2 D H _ _ _).inter ((H.lygood.meas e.1.1).prod MeasurableSet.univ)).inter
    (measurableSet_xcell_eq H.bmeas _ b₃ e.1.2)).inter hk

theorem G3_subset (D : CoreData α) (r Hx K₁ r₃ b₃ W : ℝ) : D.G3 r Hx K₁ r₃ b₃ W ⊆ D.G2 (D.N ^ (-r)) Hx K₁ := pruned_subset _ _ _ _ _

theorem measurableSet_G3 (D : CoreData α) (H : CoreHyp D) (r Hx K₁ r₃ b₃ W : ℝ) : MeasurableSet (D.G3 r Hx K₁ r₃ b₃ W) :=
  measurableSet_pruned _ (measurableSet_G2 D H _ _ _) _ _ _ (measurableSet_E3 D H r Hx K₁ r₃ b₃ W)

theorem G3_loss (D : CoreData α) (r Hx K₁ r₃ b₃ W : ℝ) :
    D.ρs (D.G2 (D.N ^ (-r)) Hx K₁ \ D.G3 r Hx K₁ r₃ b₃ W) ≤
      (∑' e, D.R3 r Hx K₁ r₃ b₃ W e) / ENNReal.ofReal K₁ :=
  measure_diff_pruned_le _ _ _ _ _

theorem floor_close {a b W : ℝ} (hW : 0 < W) (h : |a - b| ≤ W) : |⌊a / W⌋ - ⌊b / W⌋| ≤ 1 := by
  have h' : |a / W - b / W| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hW, div_le_one hW]; exact h
  have h1 := Int.floor_le (a / W); have h2 := Int.lt_floor_add_one (a / W)
  have h3 := Int.floor_le (b / W); have h4 := Int.lt_floor_add_one (b / W)
  have hab := abs_le.mp h'
  have u1 : ⌊a / W⌋ < ⌊b / W⌋ + 2 := by
    have : (⌊a / W⌋ : ℝ) < ⌊b / W⌋ + 2 := by linarith [hab.2]
    exact_mod_cast this
  have u2 : ⌊b / W⌋ < ⌊a / W⌋ + 2 := by
    have : (⌊b / W⌋ : ℝ) < ⌊a / W⌋ + 2 := by linarith [hab.1]
    exact_mod_cast this
  rw [abs_le]; constructor <;> omega

/-- Hidden cells met by one slice in one count cell are within one of each other. -/
theorem E3_k_close (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B r₃ b₃ W : ℝ}
    (hok : CrossOK D r Hx K₁ B) (hb₃ : 0 < b₃) (hW : 0 < W) (h₃r : D.N ^ (-r₃) ≤ D.N ^ (-r))
    (hb₃Hx : b₃ ≤ Hx)
    (hWsl : 2 * (D.N ^ D.εL * D.a₁) + D.crossLip r Hx K₁ B * b₃ +
      9 * B * (2 * D.N ^ (-r₃)) * (1 + D.K + D.K ^ 2) ≤ W)
    {i : Fin D.Ly.n} {ω : ℤ × ℤ × ℤ} {k k₀ : ℤ}
    (hk₀ : (D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k₀)).Nonempty)
    (hk : (D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k)).Nonempty) : |k - k₀| ≤ 1 := by
  obtain ⟨p, hp⟩ := hk₀
  obtain ⟨q, hq⟩ := hk
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hh₃ : 0 < D.N ^ (-r₃) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨ht, -, hy⟩ := same_cell_bounds hh₃ hb₃ (hq.1.2.trans hp.1.2.symm)
  have hqn : NativeOK D q :=
    (G1_subset D _ _ _ (G2_subset D _ _ _ hq.1.1.1)).1
  have hw := slice_window D H hok hp.1.1.1 hp.1.1.2.1 hq.1.1.2.1 hqn (ht.le.trans h₃r)
    (hy.le.trans hb₃Hx)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hok.coef i 0)
  have hLip0 : 0 ≤ D.crossLip r Hx K₁ B := crossLip_nonneg D H hok
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hx3 : |x3 D.b q.1 q.2 - x3 D.b p.1 p.2| ≤ W := by
    refine hw.trans (le_trans ?_ hWsl)
    have e1 : D.crossLip r Hx K₁ B * |x2 D.b q.1 q.2 - x2 D.b p.1 p.2| ≤
        D.crossLip r Hx K₁ B * b₃ := mul_le_mul_of_nonneg_left hy.le hLip0
    have e2 : 9 * B * (2 * |q.2 - p.2|) * (1 + D.K + D.K ^ 2) ≤
        9 * B * (2 * D.N ^ (-r₃)) * (1 + D.K + D.K ^ 2) := by
      gcongr
    linarith
  have := floor_close hW hx3
  rw [hq.2, hp.2] at this
  exact this

/-- Points of a slice lie in its strip grid at any cell sizes. -/
theorem E3_cell_mem_grid (D : CoreData α) (H : CoreHyp D) {r Hx K₁ r₃ b₃ W : ℝ} (hb₃ : 0 < b₃)
    {i : Fin D.Ly.n} {ω : ℤ × ℤ × ℤ} {k : ℤ} (he : (D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k)).Nonempty) :
    ω ∈ D.grid2 (D.N ^ (-r₃)) b₃ i := by
  obtain ⟨p, hp⟩ := he
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hpn : NativeOK D p := (G1_subset D _ _ _ (G2_subset D _ _ _ hp.1.1.1)).1
  have hω : xcell D.b (D.N ^ (-r₃)) b₃ p = ω := hp.1.2
  rw [← hω]
  exact mem_grid2 D H (Real.rpow_pos_of_pos hN0 _) hb₃ hpn hp.1.1.2.1

/-- The P3 reference budget: three hidden cells per strip cell. -/
theorem R3_tsum_le (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B r₃ b₃ W : ℝ}
    (hok : CrossOK D r Hx K₁ B) (hb₃ : 0 < b₃) (hW : 0 < W) (h₃r : D.N ^ (-r₃) ≤ D.N ^ (-r))
    (hb₃Hx : b₃ ≤ Hx)
    (hWsl : 2 * (D.N ^ D.εL * D.a₁) + D.crossLip r Hx K₁ B * b₃ +
      9 * B * (2 * D.N ^ (-r₃)) * (1 + D.K + D.K ^ 2) ≤ W) :
    ∑' e, D.R3 r Hx K₁ r₃ b₃ W e ≤ 3 * ∑' e, D.R2 (D.N ^ (-r₃)) b₃ e := by
  classical
  rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun e => ?_)
  obtain ⟨i, ω⟩ := e
  by_cases hne : ∃ k₀, (D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k₀)).Nonempty
  · obtain ⟨k₀, hk₀⟩ := hne
    have hgrid : ω ∈ D.grid2 (D.N ^ (-r₃)) b₃ i := E3_cell_mem_grid D H hb₃ hk₀
    have hR2 : D.R2 (D.N ^ (-r₃)) b₃ (i, ω) =
        ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d) * D.π (D.dirBin i) := by
      unfold CoreData.R2; rw [if_pos hgrid]
    rw [hR2]
    rw [tsum_eq_sum (s := {k₀ - 1, k₀, k₀ + 1})]
    · calc ∑ k ∈ ({k₀ - 1, k₀, k₀ + 1} : Finset ℤ), D.R3 r Hx K₁ r₃ b₃ W ((i, ω), k)
          ≤ ∑ _k ∈ ({k₀ - 1, k₀, k₀ + 1} : Finset ℤ),
              ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d) * D.π (D.dirBin i) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            unfold CoreData.R3
            split_ifs
            · exact le_rfl
            · exact zero_le
        _ = (({k₀ - 1, k₀, k₀ + 1} : Finset ℤ).card : ℝ≥0∞) *
              (ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d) * D.π (D.dirBin i)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * (ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d) * D.π (D.dirBin i)) := by
            gcongr
            exact_mod_cast Finset.card_le_three
    · intro k hk
      unfold CoreData.R3
      rw [if_neg]
      intro hkne
      have := E3_k_close D H hok hb₃ hW h₃r hb₃Hx hWsl hk₀ hkne
      apply hk
      have h3 := abs_le.mp this
      have : k = k₀ - 1 ∨ k = k₀ ∨ k = k₀ + 1 := by omega
      rcases this with h | h | h <;> simp [h]
  · push Not at hne
    have h0 : ∀ k, D.R3 r Hx K₁ r₃ b₃ W ((i, ω), k) = 0 := by
      intro k; unfold CoreData.R3
      rw [if_neg (by rw [Set.not_nonempty_iff_eq_empty]; exact hne k)]
    simp only [h0, tsum_zero, zero_le]

/-- Density of the slice entry of a kept point. -/
theorem G3_dense (D : CoreData α) {r Hx K₁ r₃ b₃ W : ℝ} (hK₁ : 0 < K₁)
    {q : α × ℝ} (hq : q ∈ D.G3 r Hx K₁ r₃ b₃ W) {i : Fin D.Ly.n} (hqi : q.1 ∈ D.Ly.C i) :
    ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d / K₁) * D.π (D.dirBin i) ≤
        D.ρs (D.E3 r Hx K₁ r₃ b₃ W ((i, xcell D.b (D.N ^ (-r₃)) b₃ q),
          ⌊x3 D.b q.1 q.2 / W⌋)) ∧
      D.ρs (D.E3 r Hx K₁ r₃ b₃ W ((i, xcell D.b (D.N ^ (-r₃)) b₃ q),
          ⌊x3 D.b q.1 q.2 / W⌋)) ≠ 0 := by
  classical
  have hqe : q ∈ D.E3 r Hx K₁ r₃ b₃ W ((i, xcell D.b (D.N ^ (-r₃)) b₃ q), ⌊x3 D.b q.1 q.2 / W⌋) :=
    ⟨⟨⟨G3_subset D r Hx K₁ r₃ b₃ W hq, hqi, mem_univ _⟩, rfl⟩, rfl⟩
  obtain ⟨hheavy, hnz⟩ := heavy_of_mem_pruned hq hqe
  refine ⟨?_, hnz⟩
  have hR : D.R3 r Hx K₁ r₃ b₃ W ((i, xcell D.b (D.N ^ (-r₃)) b₃ q), ⌊x3 D.b q.1 q.2 / W⌋) =
      ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d) * D.π (D.dirBin i) := by
    unfold CoreData.R3; rw [if_pos ⟨q, hqe⟩]
  rw [hR] at hheavy
  have e : ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d / K₁) * D.π (D.dirBin i) =
      ENNReal.ofReal ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d) * D.π (D.dirBin i) /
        ENNReal.ofReal K₁ := by
    rw [ENNReal.ofReal_div_of_pos hK₁, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ring
  rw [e]; exact hheavy

/-- Few kept slices of one direction in one count cell and one hidden cell. -/
theorem count3 (D : CoreData α) (H : CoreHyp D) {r Hx K₁ r₃ b₃ W : ℝ} (hK₁ : 0 < K₁)
    (hb₃ : 0 < b₃) (hW : 0 < W) (hW1 : W ≤ 1) (hWs : -Real.logb D.N W ≤ D.Rcap)
    (hr₃1 : D.Rcap⁻¹ ≤ r₃) (hr₃2 : r₃ ≤ D.Rcap) (hM1 : D.Rcap⁻¹ ≤ D.M) (hM2 : D.M ≤ D.Rcap)
    (ω : ℤ × ℤ × ℤ) (k v : ℤ) (S : Finset (Fin D.Ly.n))
    (hS : ∀ i ∈ S, D.Ly.qp i 0 = v ∧ ∃ q ∈ D.G3 r Hx K₁ r₃ b₃ W, q.1 ∈ D.Ly.C i ∧
      xcell D.b (D.N ^ (-r₃)) b₃ q = ω ∧ ⌊x3 D.b q.1 q.2 / W⌋ = k) :
    (S.card : ℝ) * ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d / K₁) ≤
      (b₃ / D.N ^ (-r₃) + 2) * (2 * (D.K * ((D.N ^ (-r₃)) ^ 3 * W ^ D.d))) := by
  classical
  haveI := H.πprob
  have hN : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hχ : 0 < D.χ := Real.rpow_pos_of_pos hN0 _
  have hh₃ : 0 < D.N ^ (-r₃) := Real.rpow_pos_of_pos hN0 _
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  set h₃ := D.N ^ (-r₃) with hh₃def
  set πv := D.π (Ico ((v : ℝ) * D.χ) (((v : ℝ) + 1) * D.χ)) with hπv
  have hbin : ∀ i ∈ S, D.dirBin i = Ico ((v : ℝ) * D.χ) (((v : ℝ) + 1) * D.χ) := by
    intro i hi; unfold CoreData.dirBin; rw [(hS i hi).1]
  -- each entry is heavy
  have hent : ∀ i ∈ S, ENNReal.ofReal (h₃ ^ 2 * b₃ * D.a₁ ^ D.d / K₁) * πv ≤
      D.ρs (D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k)) ∧ D.ρs (D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k)) ≠ 0 := by
    intro i hi
    obtain ⟨-, q, hq, hqi, hqω, hqk⟩ := hS i hi
    have := G3_dense D hK₁ hq hqi
    rw [hqω, hqk, hbin i hi] at this
    exact this
  -- the union lies in a capped set
  set σ := -Real.logb D.N W with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ, neg_nonneg]; exact Real.logb_nonpos hN hW.le hW1
  have hNσ : D.N ^ (-σ) = W := by rw [hσ, neg_neg, Real.rpow_logb hN0 hN.ne' hW]
  have hunion : (⋃ i ∈ S, D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k)) ⊆
      ⋃ Q ∈ columnCubes h₃ b₃ ω, ({p | cube D.b (D.N ^ (-r₃)) p = Q} ∩
        {p | x3 D.b p.1 p.2 ∈ Icc ((k : ℝ) * W) ((k : ℝ) * W + D.N ^ (-σ))} ∩
        {p | ⌊D.b p.1 3 / D.N ^ (-D.M)⌋ = v}) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
    refine mem_iUnion₂.mpr ⟨cube D.b h₃ p, mem_columnCubes hh₃ hb₃ hpi.1.2, ?_⟩
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · have hk' := (floor_div_eq_iff_mem_Ico hW k).mp hpi.2
      show x3 D.b p.1 p.2 ∈ Icc ((k : ℝ) * W) ((k : ℝ) * W + D.N ^ (-σ))
      rw [hNσ]; exact ⟨hk'.1, by linarith [hk'.2]⟩
    · show ⌊D.b p.1 3 / D.N ^ (-D.M)⌋ = v
      rw [← (hS i hi).1]; exact (H.lygood.bins i p.1 hpi.1.1.2.1).1
  have hm : D.ρs ≤ D.μ := H.ρsρ.trans H.ρμ
  have hcube : ∀ Q, D.ρs ({p | cube D.b (D.N ^ (-r₃)) p = Q} ∩
        {p | x3 D.b p.1 p.2 ∈ Icc ((k : ℝ) * W) ((k : ℝ) * W + D.N ^ (-σ))} ∩
        {p | ⌊D.b p.1 3 / D.N ^ (-D.M)⌋ = v}) ≤
      2 * ENNReal.ofReal (D.K * (h₃ ^ 3 * W ^ D.d)) * πv := by
    intro Q
    have hc := cube_dir_cap H.caps hN hr₃1 hr₃2 hσ0 hWs hM1 hM2 Q ((k : ℝ) * W) v D.ρs hm
    refine hc.trans (le_of_eq ?_)
    have hpow : D.N ^ (-3 * r₃ - D.d * σ) = h₃ ^ 3 * W ^ D.d := by
      rw [show -3 * r₃ - D.d * σ = (-r₃) * ((3 : ℕ) : ℝ) + (-σ) * D.d by push_cast; ring,
        Real.rpow_add hN0, Real.rpow_mul hN0.le, Real.rpow_mul hN0.le, Real.rpow_natCast, hNσ]
    have hb' : {u : ℝ | ⌊u / D.N ^ (-D.M)⌋ = v} = Ico ((v : ℝ) * D.χ) (((v : ℝ) + 1) * D.χ) := by
      ext u; simp only [mem_ofPred_eq]; exact floor_div_eq_iff_mem_Ico hχ _
    rw [hpow, hb']
  have hsum : (S.card : ℝ≥0∞) * (ENNReal.ofReal (h₃ ^ 2 * b₃ * D.a₁ ^ D.d / K₁) * πv) ≤
      ENNReal.ofReal ((b₃ / h₃ + 2) * (2 * (D.K * (h₃ ^ 3 * W ^ D.d)))) * πv := by
    calc (S.card : ℝ≥0∞) * (ENNReal.ofReal (h₃ ^ 2 * b₃ * D.a₁ ^ D.d / K₁) * πv)
        = ∑ _i ∈ S, ENNReal.ofReal (h₃ ^ 2 * b₃ * D.a₁ ^ D.d / K₁) * πv := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, D.ρs (D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k)) :=
          Finset.sum_le_sum (fun i hi => (hent i hi).1)
      _ = D.ρs (⋃ i ∈ S, D.E3 r Hx K₁ r₃ b₃ W ((i, ω), k)) := by
          rw [measure_biUnion_finset]
          · intro i _ i' _ hii'
            refine Set.disjoint_left.mpr (fun x hx hx' => hii' ?_)
            have := E3_uniq D H r Hx K₁ r₃ b₃ W x _ _ hx hx'
            exact congrArg (fun e => e.1.1) this
          · intro i _; exact measurableSet_E3 D H r Hx K₁ r₃ b₃ W _
      _ ≤ ∑ Q ∈ columnCubes h₃ b₃ ω, D.ρs ({p | cube D.b (D.N ^ (-r₃)) p = Q} ∩
            {p | x3 D.b p.1 p.2 ∈ Icc ((k : ℝ) * W) ((k : ℝ) * W + D.N ^ (-σ))} ∩
            {p | ⌊D.b p.1 3 / D.N ^ (-D.M)⌋ = v}) :=
          (measure_mono hunion).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _Q ∈ columnCubes h₃ b₃ ω, 2 * ENNReal.ofReal (D.K * (h₃ ^ 3 * W ^ D.d)) * πv :=
          Finset.sum_le_sum (fun Q _ => hcube Q)
      _ = ((columnCubes h₃ b₃ ω).card : ℝ≥0∞) *
            (2 * ENNReal.ofReal (D.K * (h₃ ^ 3 * W ^ D.d)) * πv) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (b₃ / h₃ + 2) * (2 * ENNReal.ofReal (D.K * (h₃ ^ 3 * W ^ D.d)) * πv) := by
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (card_columnCubes hh₃ hb₃ ω)
      _ = ENNReal.ofReal ((b₃ / h₃ + 2) * (2 * (D.K * (h₃ ^ 3 * W ^ D.d)))) * πv := by
          rw [ENNReal.ofReal_mul (p := b₃ / h₃ + 2) (by positivity),
            ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
          ring
  have hRHS0 : 0 ≤ (b₃ / h₃ + 2) * (2 * (D.K * (h₃ ^ 3 * W ^ D.d))) := by positivity
  by_cases hπ0 : πv = 0
  · -- no kept slice in a palette-null direction
    have hSe : S = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      refine (hent i hi).2 (le_antisymm ?_ zero_le)
      have hnull := slice_null_of_pi_zero D H i (by rw [hbin i hi]; exact hπ0)
      rw [← hnull]
      refine measure_mono (fun x hx => ⟨?_, hx.1.1.2.1⟩)
      exact G1_subset D _ _ _ (G2_subset D _ _ _ hx.1.1.1)
    rw [hSe, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact hRHS0
  · have hπtop : πv ≠ ⊤ := measure_ne_top _ _
    rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hπ0 hπtop] at hsum
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at hsum
    exact (ENNReal.ofReal_le_ofReal_iff hRHS0).mp hsum

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
