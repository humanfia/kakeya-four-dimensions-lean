import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.P4
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.PaletteCount

/-!
# The Scalar support count on a candidate label

On the block of a candidate label `Q`, the kept points occupy few (Scalar cell, terminal bin)
states: per Scalar cell, the conditional palette bound reduces the count to one direction; in one
direction, few slices are kept (third pruning) and each slice meets few terminal bins (flatness).
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace CoreData

variable (D : CoreData α)

/-- Second-position spread of a candidate label in one Scalar cell. -/
def cellδ2 (σ : ℝ) : ℝ :=
  D.K * (σ * D.fc.q) + D.K * (σ * D.fc.q) + 2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc))

/-- Hidden spread of a candidate label in one Scalar cell. -/
def cellW0 (σ : ℝ) : ℝ :=
  2 * (D.K * D.N ^ (-D.sc)) + D.K * (1 + D.N ^ (-D.sc) / D.fc.q) * (σ * D.fc.q + σ * D.fc.q) +
    D.K * (1 + D.N ^ (-D.sc) / D.fc.q ^ 2) *
      (5 / 2 * D.K * D.fc.q * (σ * D.fc.q) + 3 / 2 * D.K * D.fc.q * (σ * D.fc.q) +
        2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc)))

/-- Ancestor slope bound. -/
def Λa : ℝ := 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2)

/-- Scalar value spread of one slice in one Scalar cell. -/
def binSpread (r Hx K₁ B σ : ℝ) : ℝ :=
  (2 * (D.N ^ D.εL * D.a₁) + D.crossLip r Hx K₁ B * D.cellδ2 σ +
      9 * B * (2 * (σ * D.fc.q)) * (1 + D.K + D.K ^ 2) +
      D.Λa * (σ * D.fc.q + σ * D.fc.q + D.cellδ2 σ)) / D.a₀

end CoreData

theorem mu_univ_le (D : CoreData α) (H : CoreHyp D) : D.μ univ ≤ ENNReal.ofReal D.K := by
  haveI := H.νprob
  have h1 : D.μ univ = D.μ (univ ×ˢ Icc (0 : ℝ) 1) := by
    rw [← measure_add_measure_compl (s := univ ×ˢ Icc (0 : ℝ) 1)
      (MeasurableSet.univ.prod measurableSet_Icc), H.μsupp, add_zero]
  rw [h1]
  refine (H.μdom _).trans (le_of_eq ?_)
  rw [Measure.smul_apply, Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, smul_eq_mul, mul_one]

theorem rhos_ne_top (D : CoreData α) (H : CoreHyp D) (E : Set (α × ℝ)) : D.ρs E ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (((H.ρsρ.trans H.ρμ) E).trans ((measure_mono (subset_univ E)).trans (mu_univ_le D H)))

/-- Two points of a candidate label in one Scalar cell are close. -/
theorem scalar_cell_close (D : CoreData α) (H : CoreHyp D) {σ : ℝ} (hσ : 0 < σ)
    {Q : Fin D.fc.n} {p p' : α × ℝ} (hp : p.1 ∈ D.fc.B Q ∧ p.2 ∈ D.fc.I Q)
    (hp' : p'.1 ∈ D.fc.B Q ∧ p'.2 ∈ D.fc.I Q) (hz : D.zc σ Q p = D.zc σ Q p') :
    |p.2 - p'.2| ≤ σ * D.fc.q ∧ |x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2| ≤ σ * D.fc.q ∧
      |x2 D.b p.1 p.2 - x2 D.b p'.1 p'.2| ≤ D.cellδ2 σ ∧
      |x3 D.b p.1 p.2 - x3 D.b p'.1 p'.2| ≤ D.cellW0 σ := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  obtain ⟨a0, a1⟩ := zc_apply D σ Q p
  obtain ⟨b0, b1⟩ := zc_apply D σ Q p'
  have key : ∀ {u v : ℝ}, ⌊u / σ⌋ = ⌊v / σ⌋ → |u - v| ≤ σ := by
    intro u v huv
    have h1 := Int.floor_le (u / σ); have h2 := Int.lt_floor_add_one (u / σ)
    have h3 := Int.floor_le (v / σ); have h4 := Int.lt_floor_add_one (v / σ)
    rw [huv] at h1 h2
    rw [le_div_iff₀ hσ] at h1 h3; rw [div_lt_iff₀ hσ] at h2 h4
    rw [abs_le]; constructor <;> nlinarith
  have ht : |p.2 - p'.2| ≤ σ * D.fc.q := by
    have h := key (show ⌊(p.2 - D.tQ Q) / D.fc.q / σ⌋ = ⌊(p'.2 - D.tQ Q) / D.fc.q / σ⌋ by
      rw [← a0, ← b0, hz])
    rw [← sub_div, abs_div, abs_of_pos hqc, div_le_iff₀ hqc] at h
    have e : p.2 - D.tQ Q - (p'.2 - D.tQ Q) = p.2 - p'.2 := by ring
    rw [e] at h; linarith
  have h1 : |x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2| ≤ σ * D.fc.q := by
    have h := key (show ⌊(x1 D.b p.1 p.2 - D.ZQ Q) / D.fc.q / σ⌋ =
        ⌊(x1 D.b p'.1 p'.2 - D.ZQ Q) / D.fc.q / σ⌋ by rw [← a1, ← b1, hz])
    rw [← sub_div, abs_div, abs_of_pos hqc, div_le_iff₀ hqc] at h
    have e : x1 D.b p.1 p.2 - D.ZQ Q - (x1 D.b p'.1 p'.2 - D.ZQ Q) =
        x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2 := by ring
    rw [e] at h; linarith
  obtain ⟨h2, h3⟩ := label_spread H.fcgood H.K1 hN0 hp hp' ht h1
  exact ⟨ht, h1, h2, h3⟩

theorem floor_diff_le {a b c : ℝ} (hc : 0 ≤ c) (h : |a - b| ≤ c) :
    |⌊a⌋ - ⌊b⌋| ≤ (⌊c⌋₊ : ℤ) + 1 := by
  have h1 := Int.floor_le a; have h2 := Int.lt_floor_add_one a
  have h3 := Int.floor_le b; have h4 := Int.lt_floor_add_one b
  have hcf : c < (⌊c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one c
  have hab := abs_le.mp h
  have u1 : ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) < (⌊c⌋₊ : ℝ) + 2 := by push_cast; linarith
  have u2 : ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) < (⌊c⌋₊ : ℝ) + 2 := by push_cast; linarith
  have v1 : ⌊a⌋ - ⌊b⌋ < (⌊c⌋₊ : ℤ) + 2 := by exact_mod_cast u1
  have v2 : ⌊b⌋ - ⌊a⌋ < (⌊c⌋₊ : ℤ) + 2 := by exact_mod_cast u2
  rw [abs_le]; constructor <;> omega

theorem card_le_of_subset_Icc {T : Finset ℤ} {j₀ : ℤ} {M : ℕ}
    (h : ∀ j ∈ T, |j - j₀| ≤ (M : ℤ)) : T.card ≤ 2 * M + 1 := by
  have hsub : T ⊆ Finset.Icc (j₀ - M) (j₀ + M) := by
    intro j hj
    have := abs_le.mp (h j hj)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Int.card_Icc]
  omega

/-- One slice meets few terminal bins in one Scalar cell. -/
theorem slice_bins_card (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B σ at' : ℝ}
    (hok : CrossOK D r Hx K₁ B) (hσ : 0 < σ) (hat : 0 < at')
    (hσr : σ * D.fc.q ≤ D.N ^ (-r)) (hδH : D.cellδ2 σ ≤ Hx)
    (Q : Fin D.fc.n) (z : Fin 2 → ℤ) (i : Fin D.Ly.n) (T : Finset ℤ)
    (hT : ∀ j ∈ T, ∃ p ∈ D.G2 (D.N ^ (-r)) Hx K₁, p.1 ∈ D.fc.B Q ∧ p.2 ∈ D.fc.I Q ∧
      D.zc σ Q p = z ∧ p.1 ∈ D.Ly.C i ∧ ⌊D.xv Q p / at'⌋ = j) :
    T.card ≤ 2 * (⌊D.binSpread r Hx K₁ B σ / at'⌋₊ + 1) + 1 := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨j₀, hj₀⟩
  · rw [hTe]; simp
  obtain ⟨p₀, hp₀, hp₀B, hp₀I, hp₀z, hp₀i, hp₀j⟩ := hT j₀ hj₀
  have hN0 : 0 < D.N := by linarith [H.N2]
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hspread0 : 0 ≤ D.binSpread r Hx K₁ B σ / at' := by
    have hLip := crossLip_nonneg D H hok
    have hB0 := hok.B0
    have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
    have hK0 : 0 ≤ D.K := by linarith [H.K1]
    have hδ : 0 ≤ D.cellδ2 σ := by unfold CoreData.cellδ2; positivity
    have hΛ : 0 ≤ D.Λa := by unfold CoreData.Λa; have := f₀_q_pos D; positivity
    have ha1 : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
    unfold CoreData.binSpread; positivity
  refine card_le_of_subset_Icc (j₀ := j₀) (fun j hj => ?_)
  obtain ⟨p, hp, hpB, hpI, hpz, hpi, hpj⟩ := hT j hj
  rw [← hpj, ← hp₀j]
  apply floor_diff_le hspread0
  rw [← sub_div, abs_div, abs_of_pos hat]
  apply div_le_div_of_nonneg_right _ hat.le
  have hp0 : p ∈ D.G0 := G1_subset D _ _ _ (G2_subset D _ _ _ hp)
  obtain ⟨ct, c1, c2, -⟩ := scalar_cell_close D H hσ ⟨hpB, hpI⟩ ⟨hp₀B, hp₀I⟩ (hpz.trans hp₀z.symm)
  have hw := slice_window D H hok hp₀ hp₀i hpi hp0.1 (ct.trans hσr) (c2.trans hδH)
  have hxv := xv_sub_le D H (p' := p₀) hp0 ⟨hpB, hpI⟩
  refine hxv.trans ?_
  unfold CoreData.binSpread
  apply div_le_div_of_nonneg_right _ ha0.le
  have hLip := crossLip_nonneg D H hok
  have hB0 := hok.B0
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hΛ : 0 ≤ D.Λa := by unfold CoreData.Λa; have := f₀_q_pos D; positivity
  have e1 : D.crossLip r Hx K₁ B * |x2 D.b p.1 p.2 - x2 D.b p₀.1 p₀.2| ≤
      D.crossLip r Hx K₁ B * D.cellδ2 σ := mul_le_mul_of_nonneg_left c2 hLip
  have e2 : 9 * B * (2 * |p.2 - p₀.2|) * (1 + D.K + D.K ^ 2) ≤
      9 * B * (2 * (σ * D.fc.q)) * (1 + D.K + D.K ^ 2) := by gcongr
  have e3 : 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (|p.2 - p₀.2| +
      |x1 D.b p.1 p.2 - x1 D.b p₀.1 p₀.2| + |x2 D.b p.1 p.2 - x2 D.b p₀.1 p₀.2|) ≤
      D.Λa * (σ * D.fc.q + σ * D.fc.q + D.cellδ2 σ) := by
    unfold CoreData.Λa
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add ct c1) c2) hΛ
  linarith

/-- The number of (count cell, hidden cell) pairs in one Scalar cell. -/
def pairBox (ω₀ : ℤ × ℤ × ℤ) (k₀ : ℤ) : Finset ((ℤ × ℤ × ℤ) × ℤ) :=
  ((Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1) ×ˢ (Finset.Icc (-1 : ℤ) 1 ×ˢ
    Finset.Icc (-1 : ℤ) 1)).image
    (fun abcd => ((ω₀.1 + abcd.1.1, ω₀.2.1 + abcd.1.2, ω₀.2.2 + abcd.2.1), k₀ + abcd.2.2))

theorem card_pairBox (ω₀ : ℤ × ℤ × ℤ) (k₀ : ℤ) : (pairBox ω₀ k₀).card ≤ 81 := by
  unfold pairBox
  refine Finset.card_image_le.trans ?_
  simp

theorem mem_pairBox {ω₀ ω : ℤ × ℤ × ℤ} {k₀ k : ℤ} (h1 : |ω.1 - ω₀.1| ≤ 1)
    (h2 : |ω.2.1 - ω₀.2.1| ≤ 1) (h3 : |ω.2.2 - ω₀.2.2| ≤ 1) (h4 : |k - k₀| ≤ 1) :
    (ω, k) ∈ pairBox ω₀ k₀ := by
  unfold pairBox
  refine Finset.mem_image.mpr ⟨((ω.1 - ω₀.1, ω.2.1 - ω₀.2.1), (ω.2.2 - ω₀.2.2, k - k₀)), ?_, ?_⟩
  · have a1 := abs_le.mp h1; have a2 := abs_le.mp h2; have a3 := abs_le.mp h3
    have a4 := abs_le.mp h4
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  · simp only [add_sub_cancel]

/-- A kept point in a Scalar cell has count cell and hidden cell next to those of another. -/
theorem cell_pair_close (D : CoreData α) (H : CoreHyp D) {r₃ b₃ W σ : ℝ}
    (hb₃ : 0 < b₃) (hW : 0 < W) (hσ : 0 < σ) (hσ3 : σ * D.fc.q ≤ D.N ^ (-r₃))
    (hδb : D.cellδ2 σ ≤ b₃) (hW0 : D.cellW0 σ ≤ W) {Q : Fin D.fc.n} {p p₀ : α × ℝ}
    (hp : p.1 ∈ D.fc.B Q ∧ p.2 ∈ D.fc.I Q) (hp₀ : p₀.1 ∈ D.fc.B Q ∧ p₀.2 ∈ D.fc.I Q)
    (hz : D.zc σ Q p = D.zc σ Q p₀) :
    (xcell D.b (D.N ^ (-r₃)) b₃ p, ⌊x3 D.b p.1 p.2 / W⌋) ∈
      pairBox (xcell D.b (D.N ^ (-r₃)) b₃ p₀) ⌊x3 D.b p₀.1 p₀.2 / W⌋ := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hh₃ : 0 < D.N ^ (-r₃) := Real.rpow_pos_of_pos hN0 _
  have hcl := scalar_cell_close D H hσ hp hp₀ hz
  exact mem_pairBox (floor_close hh₃ (hcl.1.trans hσ3)) (floor_close hh₃ (hcl.2.1.trans hσ3))
    (floor_close hb₃ (hcl.2.2.1.trans hδb)) (floor_close hW (hcl.2.2.2.trans hW0))

/-- The count bound of the third pruning. -/
def CoreData.cb3 (D : CoreData α) (r₃ b₃ W K₁ : ℝ) : ℝ :=
  (b₃ / D.N ^ (-r₃) + 2) * (2 * (D.K * ((D.N ^ (-r₃)) ^ 3 * W ^ D.d))) /
    ((D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d / K₁)

/-- Few kept slices of one direction in one Scalar cell. -/
theorem slices_card (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B r₃ b₃ W σ : ℝ}
    (hok : CrossOK D r Hx K₁ B) (hK₁ : 0 < K₁) (hb₃ : 0 < b₃) (hW : 0 < W) (hW1 : W ≤ 1)
    (hWs : -Real.logb D.N W ≤ D.Rcap) (hr₃1 : D.Rcap⁻¹ ≤ r₃) (hr₃2 : r₃ ≤ D.Rcap)
    (hσ : 0 < σ) (hσ3 : σ * D.fc.q ≤ D.N ^ (-r₃)) (hδb : D.cellδ2 σ ≤ b₃)
    (hW0 : D.cellW0 σ ≤ W) (Q : Fin D.fc.n) (z : Fin 2 → ℤ) (v : ℤ) (SL : Finset (Fin D.Ly.n))
    (hSL : ∀ i ∈ SL, D.Ly.qp i 0 = v ∧ ∃ p ∈ D.G3 r Hx K₁ r₃ b₃ W, p.1 ∈ D.fc.B Q ∧
      p.2 ∈ D.fc.I Q ∧ D.zc σ Q p = z ∧ p.1 ∈ D.Ly.C i) :
    SL.card ≤ 81 * ⌊D.cb3 r₃ b₃ W K₁⌋₊ := by
  classical
  rcases SL.eq_empty_or_nonempty with hSe | ⟨i₀, hi₀⟩
  · rw [hSe]; simp
  obtain ⟨-, p₀, hp₀, hp₀B, hp₀I, hp₀z, -⟩ := hSL i₀ hi₀
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hh₃ : 0 < D.N ^ (-r₃) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, ω₀ = xcell D.b (D.N ^ (-r₃)) b₃ p₀ := ⟨_, rfl⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ = ⌊x3 D.b p₀.1 p₀.2 / W⌋ := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : (ℤ × ℤ × ℤ) × ℤ → Finset (Fin D.Ly.n), S = fun ωk => SL.filter (fun i =>
    ∃ q ∈ D.G3 r Hx K₁ r₃ b₃ W, q.1 ∈ D.Ly.C i ∧ xcell D.b (D.N ^ (-r₃)) b₃ q = ωk.1 ∧
      ⌊x3 D.b q.1 q.2 / W⌋ = ωk.2) := ⟨_, rfl⟩
  have hcount : ∀ ωk, (S ωk).card ≤ ⌊D.cb3 r₃ b₃ W K₁⌋₊ := by
    intro ωk
    apply Nat.le_floor
    have h := count3 D H hK₁ hb₃ hW hW1 hWs hr₃1 hr₃2 hok.M1 hok.M2 ωk.1 ωk.2 v (S ωk)
      (fun i hi => by
        rw [hS] at hi
        exact ⟨(hSL i (Finset.mem_filter.mp hi).1).1, (Finset.mem_filter.mp hi).2⟩)
    unfold CoreData.cb3
    have hθ : 0 < (D.N ^ (-r₃)) ^ 2 * b₃ * D.a₁ ^ D.d / K₁ := by
      have : 0 < D.a₁ ^ D.d := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN0 _) _
      positivity
    rw [le_div_iff₀ hθ]; exact h
  have hmemS : ∀ i ∈ SL, ∀ p ∈ D.G3 r Hx K₁ r₃ b₃ W, p.1 ∈ D.Ly.C i →
      i ∈ S (xcell D.b (D.N ^ (-r₃)) b₃ p, ⌊x3 D.b p.1 p.2 / W⌋) := by
    intro i hi p hp hpi
    rw [hS]
    exact Finset.mem_filter.mpr ⟨hi, p, hp, hpi, rfl, rfl⟩
  obtain ⟨PB, hPB⟩ : ∃ PB, PB = pairBox ω₀ k₀ := ⟨_, rfl⟩
  have hsub : SL ⊆ PB.biUnion S := by
    intro i hi
    have hw := (hSL i hi).2
    obtain ⟨p, hpall⟩ := hw
    refine Finset.mem_biUnion.mpr ⟨(xcell D.b (D.N ^ (-r₃)) b₃ p, ⌊x3 D.b p.1 p.2 / W⌋), ?_,
      hmemS i hi p hpall.1 hpall.2.2.2.2⟩
    rw [hPB, hω₀, hk₀]
    exact cell_pair_close D H hb₃ hW hσ hσ3 hδb hW0 ⟨hpall.2.1, hpall.2.2.1⟩ ⟨hp₀B, hp₀I⟩
      (hpall.2.2.2.1.trans hp₀z.symm)
  have hPBc : PB.card ≤ 81 := by rw [hPB]; exact card_pairBox ω₀ k₀
  calc SL.card ≤ (PB.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ ωk ∈ PB, (S ωk).card := Finset.card_biUnion_le
    _ ≤ ∑ _ωk ∈ PB, ⌊D.cb3 r₃ b₃ W K₁⌋₊ := Finset.sum_le_sum (fun ωk _ => hcount ωk)
    _ = PB.card * ⌊D.cb3 r₃ b₃ W K₁⌋₊ := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 81 * ⌊D.cb3 r₃ b₃ W K₁⌋₊ := Nat.mul_le_mul_right _ hPBc

/-- The number of terminal bins of one direction, per Scalar cell. -/
def CoreData.nmax (D : CoreData α) (r Hx K₁ B r₃ b₃ W σ at' : ℝ) : ℕ :=
  81 * ⌊D.cb3 r₃ b₃ W K₁⌋₊ * (2 * (⌊D.binSpread r Hx K₁ B σ / at'⌋₊ + 1) + 1)

open Classical in
/-- Few kept states in one Scalar cell. -/
theorem states_card (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B r₃ b₃ W σ at' : ℝ}
    (hok : CrossOK D r Hx K₁ B) (hK₁ : 0 < K₁) (hb₃ : 0 < b₃) (hW : 0 < W) (hW1 : W ≤ 1)
    (hWs : -Real.logb D.N W ≤ D.Rcap) (hr₃1 : D.Rcap⁻¹ ≤ r₃) (hr₃2 : r₃ ≤ D.Rcap)
    (hσ : 0 < σ) (hat : 0 < at') (hσ3 : σ * D.fc.q ≤ D.N ^ (-r₃)) (hσr : σ * D.fc.q ≤ D.N ^ (-r))
    (hδb : D.cellδ2 σ ≤ b₃) (hδH : D.cellδ2 σ ≤ Hx) (hW0 : D.cellW0 σ ≤ W)
    (Q : Fin D.fc.n) (z : Fin 2 → ℤ) (Jbox : Finset ℤ) :
    ((Jbox.filter (fun j => (D.E4 (D.G3 r Hx K₁ r₃ b₃ W) σ at' ((Q, z), j) ∩
        D.G4 (D.G3 r Hx K₁ r₃ b₃ W) σ at' K₁).Nonempty)).card : ℝ) ≤
      D.K * K₁ * (D.nmax r Hx K₁ B r₃ b₃ W σ at' : ℝ) := by
  classical
  haveI := H.πprob
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hχ : 0 < D.χ := Real.rpow_pos_of_pos hN0 _
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  obtain ⟨G3, hG3⟩ : ∃ G3, G3 = D.G3 r Hx K₁ r₃ b₃ W := ⟨_, rfl⟩
  have hG3G0 : G3 ⊆ D.G0 := by
    rw [hG3]; exact fun x hx => G1_subset D _ _ _ (G2_subset D _ _ _ (G3_subset D _ _ _ _ _ _ hx))
  have hG3m : MeasurableSet G3 := by rw [hG3]; exact measurableSet_G3 D H _ _ _ _ _ _
  rw [← hG3]
  set J := Jbox.filter (fun j => (D.E4 G3 σ at' ((Q, z), j) ∩ D.G4 G3 σ at' K₁).Nonempty) with hJ
  have hdir : Measurable (fun p : α × ℝ => D.b p.1 3) :=
    (measurable_pi_apply 3).comp (H.bmeas.comp measurable_fst)
  have hwit : ∀ j ∈ J, ∃ p ∈ D.G4 G3 σ at' K₁, p ∈ D.E4 G3 σ at' ((Q, z), j) := by
    intro j hj
    obtain ⟨p, hp1, hp2⟩ := (Finset.mem_filter.mp hj).2
    exact ⟨p, hp2, hp1⟩
  have hNmax : ∀ v : ℤ, (J.filter (fun j => D.ρs (D.E4 G3 σ at' ((Q, z), j) ∩
      {x | ⌊D.b x.1 3 / D.χ⌋ = v}) ≠ 0)).card ≤ D.nmax r Hx K₁ B r₃ b₃ W σ at' := by
    intro v
    obtain ⟨SL, hSL⟩ : ∃ SL : Finset (Fin D.Ly.n), SL = Finset.univ.filter (fun i =>
        D.Ly.qp i 0 = v ∧ ∃ p ∈ G3, p.1 ∈ D.fc.B Q ∧ p.2 ∈ D.fc.I Q ∧ D.zc σ Q p = z ∧
          p.1 ∈ D.Ly.C i) := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : Fin D.Ly.n → Finset ℤ, T = fun i => Jbox.filter (fun j =>
        ∃ p ∈ D.G2 (D.N ^ (-r)) Hx K₁, p.1 ∈ D.fc.B Q ∧ p.2 ∈ D.fc.I Q ∧ D.zc σ Q p = z ∧
          p.1 ∈ D.Ly.C i ∧ ⌊D.xv Q p / at'⌋ = j) := ⟨_, rfl⟩
    have hsub : J.filter (fun j => D.ρs (D.E4 G3 σ at' ((Q, z), j) ∩
        {x | ⌊D.b x.1 3 / D.χ⌋ = v}) ≠ 0) ⊆ SL.biUnion T := by
      intro j hj
      obtain ⟨hjJ, hjm⟩ := Finset.mem_filter.mp hj
      obtain ⟨x, hxE, hxv⟩ := nonempty_of_measure_ne_zero hjm
      have hx3 : x ∈ G3 := hxE.1.1.1
      have hx0 : x ∈ D.G0 := hG3G0 hx3
      obtain ⟨i, hi⟩ := hx0.2.2.2.2.2.2.2
      have hqv : D.Ly.qp i 0 = v := by
        rw [← (H.lygood.bins i x.1 hi).1]; exact hxv
      refine Finset.mem_biUnion.mpr ⟨i, ?_, ?_⟩
      · rw [hSL]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqv, x, hx3, hxE.1.1.2.1, hxE.1.1.2.2,
          hxE.1.2, hi⟩
      · rw [hT]
        have hx2 : x ∈ D.G2 (D.N ^ (-r)) Hx K₁ := by
          rw [hG3] at hx3; exact G3_subset D _ _ _ _ _ _ hx3
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjJ).1, x, hx2, hxE.1.1.2.1,
          hxE.1.1.2.2, hxE.1.2, hi, hxE.2⟩
    have hSLc : SL.card ≤ 81 * ⌊D.cb3 r₃ b₃ W K₁⌋₊ := by
      refine slices_card D H hok hK₁ hb₃ hW hW1 hWs hr₃1 hr₃2 hσ hσ3 hδb hW0 Q z v SL ?_
      intro i hi
      rw [hSL] at hi
      obtain ⟨-, hqv, p, hp, hrest⟩ := Finset.mem_filter.mp hi
      exact ⟨hqv, p, hG3 ▸ hp, hrest⟩
    have hTc : ∀ i, (T i).card ≤ 2 * (⌊D.binSpread r Hx K₁ B σ / at'⌋₊ + 1) + 1 := by
      intro i
      refine slice_bins_card D H hok hσ hat hσr hδH Q z i (T i) ?_
      intro j hj
      rw [hT] at hj
      exact (Finset.mem_filter.mp hj).2
    calc _ ≤ (SL.biUnion T).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ SL, (T i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ SL, (2 * (⌊D.binSpread r Hx K₁ B σ / at'⌋₊ + 1) + 1) :=
          Finset.sum_le_sum (fun i _ => hTc i)
      _ = SL.card * (2 * (⌊D.binSpread r Hx K₁ B σ / at'⌋₊ + 1) + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 81 * ⌊D.cb3 r₃ b₃ W K₁⌋₊ * (2 * (⌊D.binSpread r Hx K₁ B σ / at'⌋₊ + 1) + 1) :=
          Nat.mul_le_mul_right _ hSLc
      _ = D.nmax r Hx K₁ B r₃ b₃ W σ at' := rfl
  have hpc := palette_count D.ρs D.π hχ (fun p => D.b p.1 3) hdir J
    (fun j => D.E4 G3 σ at' ((Q, z), j)) (fun j _ => measurableSet_E4 D H hG3m σ at' _)
    (fun j hj => by
      obtain ⟨p, hp, hpe⟩ := hwit j hj
      exact (heavy_of_mem_pruned hp hpe).2)
    (fun j _ => rhos_ne_top D H _) (ENNReal.ofReal (D.K * K₁))
    (fun j hj v => by
      obtain ⟨p, hp, hpe⟩ := hwit j hj
      exact (G4_palette D H hG3G0 hK₁ hp hpe).2 v)
    (D.nmax r Hx K₁ B r₃ b₃ W σ at') hNmax
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (D.nmax r Hx K₁ B r₃ b₃ W σ at'),
    ← ENNReal.ofReal_mul (by positivity)] at hpc
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hpc

theorem abs_floor_le_of_abs_le {u c : ℝ} (hc : 0 ≤ c) (h : |u| ≤ c) : |⌊u⌋| ≤ (⌊c⌋₊ : ℤ) + 1 := by
  have := floor_diff_le hc (show |u - 0| ≤ c by rwa [sub_zero])
  rwa [Int.floor_zero, sub_zero] at this

/-- The Scalar support on a candidate label. -/
theorem support_count (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B r₃ b₃ W σ at' : ℝ}
    (hok : CrossOK D r Hx K₁ B) (hK₁ : 0 < K₁) (hb₃ : 0 < b₃) (hW : 0 < W) (hW1 : W ≤ 1)
    (hWs : -Real.logb D.N W ≤ D.Rcap) (hr₃1 : D.Rcap⁻¹ ≤ r₃) (hr₃2 : r₃ ≤ D.Rcap)
    (hσ : 0 < σ) (hat : 0 < at') (hσ3 : σ * D.fc.q ≤ D.N ^ (-r₃)) (hσr : σ * D.fc.q ≤ D.N ^ (-r))
    (hδb : D.cellδ2 σ ≤ b₃) (hδH : D.cellδ2 σ ≤ Hx) (hW0 : D.cellW0 σ ≤ W) (Q : Fin D.fc.n) :
    ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) ≤ (2 * ((⌊(2 * D.K + 1) / σ⌋₊ : ℝ) + 1) + 1) ^ 2 *
        (D.K * K₁ * (D.nmax r Hx K₁ B r₃ b₃ W σ at' : ℝ)) ∧
      ∀ p ∈ D.G4 (D.G3 r Hx K₁ r₃ b₃ W) σ at' K₁, p.1 ∈ D.fc.B Q → p.2 ∈ D.fc.I Q →
        (D.zc σ Q p, ⌊D.xv Q p / at'⌋) ∈ F := by
  classical
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK1 := H.K1
  have hK0 : 0 ≤ D.K := by linarith
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  set Lz : ℕ := ⌊(2 * D.K + 1) / σ⌋₊ + 1 with hLz
  set Lj : ℕ := ⌊D.K / at'⌋₊ + 1 with hLj
  obtain ⟨boxZ, hboxZ⟩ : ∃ boxZ : Finset (Fin 2 → ℤ),
      boxZ = Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(Lz : ℤ)) Lz) := ⟨_, rfl⟩
  obtain ⟨boxJ, hboxJ⟩ : ∃ boxJ : Finset ℤ, boxJ = Finset.Icc (-(Lj : ℤ)) Lj := ⟨_, rfl⟩
  set G4 := D.G4 (D.G3 r Hx K₁ r₃ b₃ W) σ at' K₁ with hG4
  refine ⟨(boxZ ×ˢ boxJ).filter (fun zj => (D.E4 (D.G3 r Hx K₁ r₃ b₃ W) σ at'
    ((Q, zj.1), zj.2) ∩ G4).Nonempty), ?_, ?_⟩
  · have hcardZ : (boxZ.card : ℝ) = (2 * ((⌊(2 * D.K + 1) / σ⌋₊ : ℝ) + 1) + 1) ^ 2 := by
      rw [hboxZ, Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have : ((Lz : ℤ) + 1 - -(Lz : ℤ)).toNat = 2 * Lz + 1 := by omega
      rw [this]; push_cast [hLz]; ring
    rw [Finset.card_filter, Finset.sum_product, ← hcardZ]
    have hz : ∀ z ∈ boxZ, ((∑ j ∈ boxJ, if (D.E4 (D.G3 r Hx K₁ r₃ b₃ W) σ at' ((Q, z), j) ∩
        G4).Nonempty then 1 else 0 : ℕ) : ℝ) ≤ D.K * K₁ * (D.nmax r Hx K₁ B r₃ b₃ W σ at' : ℝ) := by
      intro z _
      rw [← Finset.card_filter]
      exact states_card D H hok hK₁ hb₃ hW hW1 hWs hr₃1 hr₃2 hσ hat hσ3 hσr hδb hδH hW0 Q z boxJ
    rw [Nat.cast_sum]
    calc ∑ z ∈ boxZ, ((∑ j ∈ boxJ, if (D.E4 (D.G3 r Hx K₁ r₃ b₃ W) σ at' ((Q, z), j) ∩
          G4).Nonempty then 1 else 0 : ℕ) : ℝ)
        ≤ ∑ _z ∈ boxZ, D.K * K₁ * (D.nmax r Hx K₁ B r₃ b₃ W σ at' : ℝ) := Finset.sum_le_sum hz
      _ = (boxZ.card : ℝ) * (D.K * K₁ * (D.nmax r Hx K₁ B r₃ b₃ W σ at' : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  · intro p hp hpB hpI
    have hp3 : p ∈ D.G3 r Hx K₁ r₃ b₃ W := G4_subset D _ _ _ _ hp
    have hp0 : p ∈ D.G0 :=
      G1_subset D _ _ _ (G2_subset D _ _ _ (G3_subset D _ _ _ _ _ _ hp3))
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, p, ⟨⟨⟨hp3, hpB, hpI⟩, rfl⟩, rfl⟩, hp⟩
    · -- the Scalar cell lies in the box
      rw [hboxZ, Fintype.mem_piFinset]
      obtain ⟨a0, a1⟩ := zc_apply D σ Q p
      have hc0 : 0 ≤ (2 * D.K + 1) / σ := by positivity
      have hτ : |(p.2 - D.tQ Q) / D.fc.q / σ| ≤ (2 * D.K + 1) / σ := by
        rw [abs_div, abs_of_pos hσ]
        apply div_le_div_of_nonneg_right _ hσ.le
        have hI := hpI
        unfold Fam.I blk at hI
        unfold CoreData.tQ
        have hq : D.fc.q = ((2 : ℝ) ^ D.fc.T)⁻¹ := rfl
        have e : (((D.fc.j Q : ℕ) : ℝ) + 1) / 2 ^ D.fc.T = ((D.fc.j Q : ℕ) : ℝ) / 2 ^ D.fc.T + D.fc.q := by
          rw [hq, add_div, one_div]
        rw [e] at hI
        rw [abs_div, abs_of_pos hqc, div_le_iff₀ hqc, abs_le]
        constructor <;> nlinarith [hI.1, hI.2]
      have hy : |(x1 D.b p.1 p.2 - D.ZQ Q) / D.fc.q / σ| ≤ (2 * D.K + 1) / σ := by
        rw [abs_div, abs_of_pos hσ]
        apply div_le_div_of_nonneg_right _ hσ.le
        rw [abs_div, abs_of_pos hqc, div_le_iff₀ hqc]
        have g1 := (H.fcgood.geom Q p.1 (H.fcgood.BA Q hpB) p.2 hpI).1
        have hc1 := H.fcgood.cbd Q 1
        have htq : |p.2 - D.tQ Q| ≤ D.fc.q := by
          have hI := hpI
          unfold Fam.I blk at hI
          unfold CoreData.tQ
          have hq : D.fc.q = ((2 : ℝ) ^ D.fc.T)⁻¹ := rfl
          have e : (((D.fc.j Q : ℕ) : ℝ) + 1) / 2 ^ D.fc.T =
              ((D.fc.j Q : ℕ) : ℝ) / 2 ^ D.fc.T + D.fc.q := by rw [hq, add_div, one_div]
          rw [e] at hI
          rw [abs_le]; constructor <;> linarith [hI.1, hI.2]
        have e : x1 D.b p.1 p.2 - D.ZQ Q = (x1 D.b p.1 p.2 - D.fc.c Q 0 - p.2 * D.fc.c Q 1) +
            (p.2 - D.tQ Q) * D.fc.c Q 1 := by unfold CoreData.ZQ; ring
        rw [e]
        have h2 : |(p.2 - D.tQ Q) * D.fc.c Q 1| ≤ D.fc.q * D.K := by
          rw [abs_mul]; exact mul_le_mul htq hc1 (abs_nonneg _) hqc.le
        calc _ ≤ |x1 D.b p.1 p.2 - D.fc.c Q 0 - p.2 * D.fc.c Q 1| + |(p.2 - D.tQ Q) * D.fc.c Q 1| :=
              abs_add_le _ _
          _ ≤ D.K * D.fc.q + D.fc.q * D.K := add_le_add g1 h2
          _ ≤ (2 * D.K + 1) * D.fc.q := by nlinarith
      intro k
      fin_cases k
      · have := abs_floor_le_of_abs_le hc0 hτ
        rw [← a0] at this
        have := abs_le.mp this
        exact Finset.mem_Icc.mpr ⟨by push_cast [hLz]; omega, by push_cast [hLz]; omega⟩
      · have := abs_floor_le_of_abs_le hc0 hy
        rw [← a1] at this
        have := abs_le.mp this
        exact Finset.mem_Icc.mpr ⟨by push_cast [hLz]; omega, by push_cast [hLz]; omega⟩
    · -- the terminal bin lies in the box
      rw [hboxJ]
      obtain ⟨j₀, hBj, hIj⟩ := hp0.2.2.2.2.1
      have hfit := H.f₀good.fit j₀ p.1 hBj p.2 hIj
      have hxv : |D.xv Q p| ≤ D.K := by
        unfold CoreData.xv
        rw [D.blockVal_eq Q p hqc.ne', Lanc_eq D H hp0 ⟨hpB, hpI⟩ ⟨hBj, hIj⟩]
        have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
        rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
        exact hfit
      have hc0 : 0 ≤ D.K / at' := by positivity
      have := abs_floor_le_of_abs_le hc0
        (show |D.xv Q p / at'| ≤ D.K / at' by
          rw [abs_div, abs_of_pos hat]; exact div_le_div_of_nonneg_right hxv hat.le)
      have := abs_le.mp this
      exact Finset.mem_Icc.mpr ⟨by push_cast [hLj]; omega, by push_cast [hLj]; omega⟩

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
