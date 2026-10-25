import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Support

/-!
# Scalar caps on a candidate label

A Scalar cell of a candidate label lies in few cubes of side `σ q_c`; on each cube the ancestor
fit moves by at most `3 Λa σ q_c`, so a Scalar value bin of width `w` is a hidden window of width
`2 a₀ w`. The model caps then bound the mass of a (cell, value bin), with or without a
direction bin.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- One cube and a hidden window of one bin width. -/
theorem cube_window_cap {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    {N K d S rlo rhi shi vlo vhi : ℝ} (hcaps : Caps μ π b N K d S rlo rhi shi vlo vhi)
    (hN : 1 < N) {r σ : ℝ} (hr1 : rlo ≤ r) (hr2 : r ≤ rhi) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ shi)
    (q : Fin 3 → ℤ) (w : ℝ) (m : Measure (α × ℝ)) (hm : m ≤ μ) :
    m ({p | cube b (N ^ (-r)) p = q} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + N ^ (-σ))}) ≤
      2 * ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) := by
  set W := N ^ (-σ) with hWdef
  have hW : 0 < W := Real.rpow_pos_of_pos (by linarith) _
  have hsub : {p | cube b (N ^ (-r)) p = q} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + W)} ⊆
      {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋} ∪
      {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋ + 1} := by
    intro p hp
    obtain ⟨hq, hw1, hw2⟩ := hp
    have hlo : ⌊w / W⌋ ≤ ⌊x3 b p.1 p.2 / W⌋ := Int.floor_mono (div_le_div_of_nonneg_right hw1 hW.le)
    have hhi : ⌊x3 b p.1 p.2 / W⌋ ≤ ⌊w / W⌋ + 1 := by
      have : x3 b p.1 p.2 / W ≤ w / W + 1 := by
        rw [div_add_one hW.ne', div_le_div_iff_of_pos_right hW]; exact hw2
      exact (Int.floor_mono this).trans (by rw [Int.floor_add_one])
    rcases lt_or_eq_of_le hlo with hlt | heq
    · exact Or.inr ⟨hq, by omega⟩
    · exact Or.inl ⟨hq, heq.symm⟩
  calc m ({p | cube b (N ^ (-r)) p = q} ∩ {p | x3 b p.1 p.2 ∈ Icc w (w + W)})
      ≤ μ ({p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋} ∪
          {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋ + 1}) :=
        (hm _).trans' (measure_mono hsub)
    _ ≤ μ {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋} +
          μ {p | cube b (N ^ (-r)) p = q ∧ ⌊x3 b p.1 p.2 / W⌋ = ⌊w / W⌋ + 1} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) + ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) :=
        add_le_add (hcaps.cap r σ hr1 hr2 hσ0 hσ1 q _) (hcaps.cap r σ hr1 hr2 hσ0 hσ1 q _)
    _ = 2 * ENNReal.ofReal (K * N ^ (-3 * r - d * σ)) := by rw [two_mul]

namespace CoreData

variable (D : CoreData α)

/-- Cubes of side `σ q_c` met by one Scalar cell of a candidate label. -/
def cellCubes (σ : ℝ) (Q : Fin D.fc.n) (z : Fin 2 → ℤ) : Finset (Fin 3 → ℤ) :=
  (aniGrid (σ * D.fc.q) (σ * D.fc.q) (σ * D.fc.q / 2) (σ * D.fc.q / 2)
    (D.K * D.fc.q * D.N ^ (-D.κ * D.sc)) (D.tQ Q + D.fc.q * (((z 0 : ℤ) : ℝ) + 1 / 2) * σ)
    (D.ZQ Q + D.fc.q * (((z 1 : ℤ) : ℝ) + 1 / 2) * σ)
    (D.fc.c Q 2 + D.fc.c Q 4 * (D.ZQ Q + D.fc.q * (((z 1 : ℤ) : ℝ) + 1 / 2) * σ)) 0
    (-(D.fc.c Q 3)) (D.fc.c Q 4)).image (fun abc => ![abc.1, abc.2.1, abc.2.2])

end CoreData

theorem floor_center {u σ : ℝ} (hσ : 0 < σ) {k : ℤ} (h : ⌊u / σ⌋ = k) :
    |u - ((k : ℝ) + 1 / 2) * σ| ≤ σ / 2 := by
  have h1 := Int.floor_le (u / σ); have h2 := Int.lt_floor_add_one (u / σ)
  rw [h, le_div_iff₀ hσ] at h1; rw [h, div_lt_iff₀ hσ] at h2
  rw [abs_le]; constructor <;> nlinarith

theorem mem_cellCubes (D : CoreData α) (H : CoreHyp D) {σ : ℝ} (hσ : 0 < σ) {Q : Fin D.fc.n}
    {p : α × ℝ} (hpQ : p.1 ∈ D.fc.B Q ∧ p.2 ∈ D.fc.I Q) {z : Fin 2 → ℤ} (hz : D.zc σ Q p = z) :
    cube D.b (σ * D.fc.q) p ∈ D.cellCubes σ Q z := by
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hh : 0 < σ * D.fc.q := mul_pos hσ hqc
  obtain ⟨a0, a1⟩ := zc_apply D σ Q p
  have hz0 : ⌊(p.2 - D.tQ Q) / D.fc.q / σ⌋ = z 0 := by rw [← a0, hz]
  have hz1 : ⌊(x1 D.b p.1 p.2 - D.ZQ Q) / D.fc.q / σ⌋ = z 1 := by rw [← a1, hz]
  have c0 := floor_center hσ hz0
  have c1 := floor_center hσ hz1
  have ht : |p.2 - (D.tQ Q + D.fc.q * (((z 0 : ℤ) : ℝ) + 1 / 2) * σ)| ≤ σ * D.fc.q / 2 := by
    have e : p.2 - (D.tQ Q + D.fc.q * (((z 0 : ℤ) : ℝ) + 1 / 2) * σ) =
        D.fc.q * ((p.2 - D.tQ Q) / D.fc.q - (((z 0 : ℤ) : ℝ) + 1 / 2) * σ) := by
      field_simp; ring
    rw [e, abs_mul, abs_of_pos hqc]
    calc D.fc.q * |(p.2 - D.tQ Q) / D.fc.q - (((z 0 : ℤ) : ℝ) + 1 / 2) * σ|
        ≤ D.fc.q * (σ / 2) := mul_le_mul_of_nonneg_left c0 hqc.le
      _ = σ * D.fc.q / 2 := by ring
  have hx : |x1 D.b p.1 p.2 - (D.ZQ Q + D.fc.q * (((z 1 : ℤ) : ℝ) + 1 / 2) * σ + p.2 * 0)| ≤
      σ * D.fc.q / 2 := by
    have e : x1 D.b p.1 p.2 - (D.ZQ Q + D.fc.q * (((z 1 : ℤ) : ℝ) + 1 / 2) * σ + p.2 * 0) =
        D.fc.q * ((x1 D.b p.1 p.2 - D.ZQ Q) / D.fc.q - (((z 1 : ℤ) : ℝ) + 1 / 2) * σ) := by
      field_simp; ring
    rw [e, abs_mul, abs_of_pos hqc]
    calc D.fc.q * |(x1 D.b p.1 p.2 - D.ZQ Q) / D.fc.q - (((z 1 : ℤ) : ℝ) + 1 / 2) * σ|
        ≤ D.fc.q * (σ / 2) := mul_le_mul_of_nonneg_left c1 hqc.le
      _ = σ * D.fc.q / 2 := by ring
  obtain ⟨-, g2, -⟩ := H.fcgood.geom Q p.1 (H.fcgood.BA Q hpQ.1) p.2 hpQ.2
  have hy : |x2 D.b p.1 p.2 - ((D.fc.c Q 2 + D.fc.c Q 4 * (D.ZQ Q + D.fc.q * (((z 1 : ℤ) : ℝ) +
      1 / 2) * σ)) - p.2 * -(D.fc.c Q 3)) - D.fc.c Q 4 * (x1 D.b p.1 p.2 -
      (D.ZQ Q + D.fc.q * (((z 1 : ℤ) : ℝ) + 1 / 2) * σ + p.2 * 0))| ≤
      D.K * D.fc.q * D.N ^ (-D.κ * D.sc) := by
    have e : x2 D.b p.1 p.2 - ((D.fc.c Q 2 + D.fc.c Q 4 * (D.ZQ Q + D.fc.q * (((z 1 : ℤ) : ℝ) +
        1 / 2) * σ)) - p.2 * -(D.fc.c Q 3)) - D.fc.c Q 4 * (x1 D.b p.1 p.2 -
        (D.ZQ Q + D.fc.q * (((z 1 : ℤ) : ℝ) + 1 / 2) * σ + p.2 * 0)) =
        x2 D.b p.1 p.2 - D.fc.c Q 2 - p.2 * D.fc.c Q 3 - D.fc.c Q 4 * x1 D.b p.1 p.2 := by ring
    rw [e]; exact g2
  have hmem := mem_aniGrid hh hh ht hx hy
  unfold CoreData.cellCubes
  rw [cube_eq_of_floors]
  exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩

theorem card_cellCubes (D : CoreData α) (H : CoreHyp D) {σ : ℝ} (hσ : 0 < σ) (Q : Fin D.fc.n)
    (z : Fin 2 → ℤ) :
    ((D.cellCubes σ Q z).card : ℝ) ≤
      36 * (2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc) + 2 * D.K * (σ * D.fc.q)) / (σ * D.fc.q) + 5) := by
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hh : 0 < σ * D.fc.q := mul_pos hσ hqc
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hC : 0 ≤ D.K * D.fc.q * D.N ^ (-D.κ * D.sc) := by positivity
  unfold CoreData.cellCubes
  refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
  refine (card_aniGrid hh hh (by positivity) (by positivity) hC _ _ _ _ _ _).trans ?_
  have hc3 := H.fcgood.cbd Q 3
  have hc4 := H.fcgood.cbd Q 4
  have e1 : 2 * (σ * D.fc.q / 2) / (σ * D.fc.q) + 5 = 6 := by field_simp; ring
  have e2 : 2 * (σ * D.fc.q / 2 + |(0 : ℝ)| * (σ * D.fc.q)) / (σ * D.fc.q) + 5 = 6 := by
    rw [abs_zero, zero_mul, add_zero]; field_simp; ring
  rw [e1, e2]
  have h3 : (|-(D.fc.c Q 3)| + |D.fc.c Q 4| * (1 + |(0 : ℝ)|)) * (σ * D.fc.q) ≤
      2 * D.K * (σ * D.fc.q) := by
    rw [abs_neg, abs_zero, add_zero, mul_one]
    exact mul_le_mul_of_nonneg_right (by linarith) hh.le
  have h4 : 2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc) + (|-(D.fc.c Q 3)| + |D.fc.c Q 4| *
      (1 + |(0 : ℝ)|)) * (σ * D.fc.q)) / (σ * D.fc.q) + 5 ≤
      2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc) + 2 * D.K * (σ * D.fc.q)) / (σ * D.fc.q) + 5 := by
    gcongr
  nlinarith

/-- A Scalar (cell, value bin) set lies in cube windows. -/
theorem scalar_cell_subset (D : CoreData α) (H : CoreHyp D) {σ w : ℝ} (hσ : 0 < σ) (hw : 0 < w)
    (hΛ : 6 * D.Λa * (σ * D.fc.q) ≤ D.a₀ * w) {Q : Fin D.fc.n} {G : Set (α × ℝ)}
    (hG : G ⊆ D.G0) (z : Fin 2 → ℤ) (jj : ℤ) :
    G ∩ (D.fc.B Q ×ˢ D.fc.I Q) ∩ {p | D.zc σ Q p = z ∧ ⌊D.xv Q p / w⌋ = jj} ⊆
      ⋃ c ∈ D.cellCubes σ Q z, ({p | cube D.b (σ * D.fc.q) p = c} ∩
        {p | x3 D.b p.1 p.2 ∈ Icc (D.Lanc Q 0 + D.Lanc Q 1 * ((c 0 : ℝ) * (σ * D.fc.q)) +
          D.Lanc Q 2 * ((c 1 : ℝ) * (σ * D.fc.q)) + D.Lanc Q 3 * ((c 2 : ℝ) * (σ * D.fc.q)) +
          D.a₀ * ((jj : ℝ) * w) - 3 * D.Λa * (σ * D.fc.q))
          (D.Lanc Q 0 + D.Lanc Q 1 * ((c 0 : ℝ) * (σ * D.fc.q)) +
          D.Lanc Q 2 * ((c 1 : ℝ) * (σ * D.fc.q)) + D.Lanc Q 3 * ((c 2 : ℝ) * (σ * D.fc.q)) +
          D.a₀ * ((jj : ℝ) * w) - 3 * D.Λa * (σ * D.fc.q) + 2 * (D.a₀ * w))}) := by
  intro p hp
  obtain ⟨⟨hpG, hpQ⟩, hpz, hpj⟩ := hp
  have hp0 := hG hpG
  have hN0 : 0 < D.N := by linarith [H.N2]
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hh : 0 < σ * D.fc.q := mul_pos hσ hqc
  refine mem_iUnion₂.mpr ⟨cube D.b (σ * D.fc.q) p, mem_cellCubes D H hσ hpQ hpz, rfl, ?_⟩
  obtain ⟨c1, c2, c3⟩ := Lanc_coeff D H hp0 hpQ
  set h := σ * D.fc.q
  set L := D.Lanc Q
  have hxv : D.xv Q p = (x3 D.b p.1 p.2 - (L 0 + L 1 * p.2 + L 2 * x1 D.b p.1 p.2 +
      L 3 * x2 D.b p.1 p.2)) / D.a₀ := D.blockVal_eq Q p hqc.ne'
  have hj := (floor_div_eq_iff_mem_Ico hw jj).mp hpj
  rw [hxv] at hj
  have hj1 := hj.1; have hj2 := hj.2
  rw [le_div_iff₀ ha0] at hj1; rw [div_lt_iff₀ ha0] at hj2
  have ft := floor_cell_abs (x := p.2) hh
  have f1 := floor_cell_abs (x := x1 D.b p.1 p.2) hh
  have f2 := floor_cell_abs (x := x2 D.b p.1 p.2) hh
  have hcube : cube D.b h p = ![⌊p.2 / h⌋, ⌊x1 D.b p.1 p.2 / h⌋, ⌊x2 D.b p.1 p.2 / h⌋] :=
    cube_eq_of_floors _ _ _
  rw [hcube]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  set T0 := (⌊p.2 / h⌋ : ℝ) * h
  set T1 := (⌊x1 D.b p.1 p.2 / h⌋ : ℝ) * h
  set T2 := (⌊x2 D.b p.1 p.2 / h⌋ : ℝ) * h
  have hΛ0 : 0 ≤ D.Λa := (abs_nonneg _).trans c1
  have hdiff : |(L 1 * p.2 + L 2 * x1 D.b p.1 p.2 + L 3 * x2 D.b p.1 p.2) -
      (L 1 * T0 + L 2 * T1 + L 3 * T2)| ≤ 3 * D.Λa * h := by
    have e : (L 1 * p.2 + L 2 * x1 D.b p.1 p.2 + L 3 * x2 D.b p.1 p.2) -
        (L 1 * T0 + L 2 * T1 + L 3 * T2) =
        L 1 * (p.2 - T0) + L 2 * (x1 D.b p.1 p.2 - T1) + L 3 * (x2 D.b p.1 p.2 - T2) := by ring
    rw [e]
    calc _ ≤ |L 1 * (p.2 - T0)| + |L 2 * (x1 D.b p.1 p.2 - T1)| + |L 3 * (x2 D.b p.1 p.2 - T2)| :=
          abs_add_three _ _ _
      _ ≤ D.Λa * h + D.Λa * h + D.Λa * h := by
          gcongr
          · rw [abs_mul]; exact mul_le_mul c1 ft (abs_nonneg _) hΛ0
          · rw [abs_mul]; exact mul_le_mul c2 f1 (abs_nonneg _) hΛ0
          · rw [abs_mul]; exact mul_le_mul c3 f2 (abs_nonneg _) hΛ0
      _ = 3 * D.Λa * h := by ring
  have hd := abs_le.mp hdiff
  constructor
  · show L 0 + L 1 * T0 + L 2 * T1 + L 3 * T2 + D.a₀ * ((jj : ℝ) * w) - 3 * D.Λa * h ≤
      x3 D.b p.1 p.2
    nlinarith
  · show x3 D.b p.1 p.2 ≤ L 0 + L 1 * T0 + L 2 * T1 + L 3 * T2 + D.a₀ * ((jj : ℝ) * w) -
      3 * D.Λa * h + 2 * (D.a₀ * w)
    nlinarith

/-- Mass of one Scalar (cell, value bin) of a candidate label. -/
theorem scalar_value_cap (D : CoreData α) (H : CoreHyp D) {σ w rh σ' : ℝ} (hσ : 0 < σ)
    (hw : 0 < w) (hΛ : 6 * D.Λa * (σ * D.fc.q) ≤ D.a₀ * w) (hrh : D.N ^ (-rh) = σ * D.fc.q)
    (hrh1 : D.Rcap⁻¹ ≤ rh) (hrh2 : rh ≤ D.Rcap) (hσ' : D.N ^ (-σ') = 2 * (D.a₀ * w))
    (hσ'0 : 0 ≤ σ') (hσ'1 : σ' ≤ D.Rcap) {Q : Fin D.fc.n} {G : Set (α × ℝ)}
    (hG : G ⊆ D.G0) (z : Fin 2 → ℤ) (jj : ℤ) :
    D.ρs (G ∩ (D.fc.B Q ×ˢ D.fc.I Q) ∩ {p | D.zc σ Q p = z ∧ ⌊D.xv Q p / w⌋ = jj}) ≤
      ((D.cellCubes σ Q z).card : ℝ≥0∞) *
        (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d))) := by
  have hN : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hm : D.ρs ≤ D.μ := H.ρsρ.trans H.ρμ
  have hpow : D.N ^ (-3 * rh - D.d * σ') = (σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d := by
    rw [show -3 * rh - D.d * σ' = (-rh) * ((3 : ℕ) : ℝ) + (-σ') * D.d by push_cast; ring,
      Real.rpow_add hN0, Real.rpow_mul hN0.le, Real.rpow_mul hN0.le, Real.rpow_natCast, hrh, hσ']
  refine (measure_mono (scalar_cell_subset D H hσ hw hΛ hG z jj)).trans
    ((measure_biUnion_finset_le _ _).trans ?_)
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun c _ => ?_)
  have hc := cube_window_cap H.caps hN hrh1 hrh2 hσ'0 hσ'1 c (D.Lanc Q 0 + D.Lanc Q 1 * ((c 0 : ℝ) * (σ * D.fc.q)) + D.Lanc Q 2 * ((c 1 : ℝ) * (σ * D.fc.q)) + D.Lanc Q 3 * ((c 2 : ℝ) * (σ * D.fc.q)) + D.a₀ * ((jj : ℝ) * w) - 3 * D.Λa * (σ * D.fc.q)) D.ρs hm
  rw [hrh, hσ', hpow] at hc
  exact hc

/-- Mass of one Scalar (cell, value bin) of a candidate label in one direction bin. -/
theorem scalar_angle_cap (D : CoreData α) (H : CoreHyp D) {σ w rh σ' v : ℝ} (hσ : 0 < σ)
    (hw : 0 < w) (hΛ : 6 * D.Λa * (σ * D.fc.q) ≤ D.a₀ * w) (hrh : D.N ^ (-rh) = σ * D.fc.q)
    (hrh1 : D.Rcap⁻¹ ≤ rh) (hrh2 : rh ≤ D.Rcap) (hσ' : D.N ^ (-σ') = 2 * (D.a₀ * w))
    (hσ'0 : 0 ≤ σ') (hσ'1 : σ' ≤ D.Rcap) (hv1 : D.Rcap⁻¹ ≤ v) (hv2 : v ≤ D.Rcap)
    {Q : Fin D.fc.n} {G : Set (α × ℝ)} (hG : G ⊆ D.G0) (z : Fin 2 → ℤ) (jj kk : ℤ) :
    D.ρs (G ∩ (D.fc.B Q ×ˢ D.fc.I Q) ∩ {p | D.zc σ Q p = z ∧ ⌊D.xv Q p / w⌋ = jj} ∩
        {p | ⌊D.b p.1 3 / D.N ^ (-v)⌋ = kk}) ≤
      ((D.cellCubes σ Q z).card : ℝ≥0∞) *
        (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d)) *
          D.π {u : ℝ | ⌊u / D.N ^ (-v)⌋ = kk}) := by
  have hN : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hm : D.ρs ≤ D.μ := H.ρsρ.trans H.ρμ
  have hpow : D.N ^ (-3 * rh - D.d * σ') = (σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d := by
    rw [show -3 * rh - D.d * σ' = (-rh) * ((3 : ℕ) : ℝ) + (-σ') * D.d by push_cast; ring,
      Real.rpow_add hN0, Real.rpow_mul hN0.le, Real.rpow_mul hN0.le, Real.rpow_natCast, hrh, hσ']
  have hsub := scalar_cell_subset D H hσ hw hΛ hG (Q := Q) z jj
  have hsub' : G ∩ (D.fc.B Q ×ˢ D.fc.I Q) ∩ {p | D.zc σ Q p = z ∧ ⌊D.xv Q p / w⌋ = jj} ∩
      {p | ⌊D.b p.1 3 / D.N ^ (-v)⌋ = kk} ⊆
      ⋃ c ∈ D.cellCubes σ Q z, ({p | cube D.b (σ * D.fc.q) p = c} ∩
        {p | x3 D.b p.1 p.2 ∈ Icc (D.Lanc Q 0 + D.Lanc Q 1 * ((c 0 : ℝ) * (σ * D.fc.q)) +
          D.Lanc Q 2 * ((c 1 : ℝ) * (σ * D.fc.q)) + D.Lanc Q 3 * ((c 2 : ℝ) * (σ * D.fc.q)) +
          D.a₀ * ((jj : ℝ) * w) - 3 * D.Λa * (σ * D.fc.q))
          (D.Lanc Q 0 + D.Lanc Q 1 * ((c 0 : ℝ) * (σ * D.fc.q)) +
          D.Lanc Q 2 * ((c 1 : ℝ) * (σ * D.fc.q)) + D.Lanc Q 3 * ((c 2 : ℝ) * (σ * D.fc.q)) +
          D.a₀ * ((jj : ℝ) * w) - 3 * D.Λa * (σ * D.fc.q) + 2 * (D.a₀ * w))} ∩
        {p | ⌊D.b p.1 3 / D.N ^ (-v)⌋ = kk}) := by
    intro p hp
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp (hsub hp.1)
    exact mem_iUnion₂.mpr ⟨c, hc, hpc, hp.2⟩
  refine (measure_mono hsub').trans ((measure_biUnion_finset_le _ _).trans ?_)
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun c _ => ?_)
  have hc := cube_dir_cap H.caps hN hrh1 hrh2 hσ'0 hσ'1 hv1 hv2 c (D.Lanc Q 0 + D.Lanc Q 1 * ((c 0 : ℝ) * (σ * D.fc.q)) + D.Lanc Q 2 * ((c 1 : ℝ) * (σ * D.fc.q)) + D.Lanc Q 3 * ((c 2 : ℝ) * (σ * D.fc.q)) + D.a₀ * ((jj : ℝ) * w) - 3 * D.Λa * (σ * D.fc.q)) kk D.ρs hm
  rw [hrh, hσ', hpow] at hc
  exact hc

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
