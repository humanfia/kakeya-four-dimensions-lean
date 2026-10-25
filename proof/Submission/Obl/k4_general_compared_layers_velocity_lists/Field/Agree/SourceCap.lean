-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.SourceCap; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900, on
   `Parent.native_band_box_cap` of this checkout (`NativeBandCaps.lean`). -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.PointClaims
import Submission.Obl.k4_general_compared_layers_velocity_lists.NativeBandCaps

/-!
# Source densities in the transverse coordinate

A source (a color-0 event `e` and a time cell `c` of its parent block) has, in the normalized
transverse coordinate `U`, interval masses `μ(agSrc ∩ {U ∈ [a, b]}) ≤ W (b - a + λ)` with
`W = 2100 K² H a₁^d q δb χ w π(tag bin)` and `λ = 4 K χ / w` (`agree_src_interval_cap`): integrate the
original native joint caps over the moving box (time cell, intercept tube of the coarse tags,
transverse window), with the fine-layer fit of precision `H a₁`. Summing over sources costs the
color-0 reference budget (`agree_sum_srcWeight_le`).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

namespace ComparedSample

variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

/-- The source weight of a color-0 event at base mesh `δb`. -/
def agSrcWeight (δb : ℝ) (e : Fin (s.count 0)) : ℝ≥0∞ :=
  ENNReal.ofReal (2100 * p.K k ^ 2 * H * (p.N k ^ (-(r + u))) ^ p.d * p.blockLen k r * δb *
      p.N k ^ (-m) * p.blockWidth k r) *
    p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (s.layers 0).tag (s.coarse 0 e) 0}

/-- The time of a source lies in its cell: `0 ≤ t - t_s ≤ q δb`. -/
theorem agree_src_time_sharp {δb : ℝ} (hδb : 0 < δb) {e : Fin (s.count 0)} {c : ℤ} {ω : α × ℝ}
    (hω : ω ∈ s.agSrc δb e c) :
    0 ≤ ω.2 - s.agSrcTime δb e c ∧ ω.2 - s.agSrcTime δb e c ≤ p.blockLen k r * δb := by
  have hc : ⌊p.tauN k r (s.parent 0 e) ω / δb⌋ = c := hω.2
  have hq := agree_blockLen_pos (p := p) k r
  have hlo := (le_div_iff₀ hδb).mp (hc ▸ Int.floor_le (p.tauN k r (s.parent 0 e) ω / δb))
  have hhi := (div_lt_iff₀ hδb).mp (hc ▸ Int.lt_floor_add_one (p.tauN k r (s.parent 0 e) ω / δb))
  have hdiff : ω.2 - s.agSrcTime δb e c =
      p.blockLen k r * (p.tauN k r (s.parent 0 e) ω - (c : ℝ) * δb) := by
    have h := agree_tauN_mul_add (s.parent 0 e) ω
    unfold agSrcTime
    linear_combination h
  rw [hdiff]
  constructor
  · exact mul_nonneg hq.le (by linarith)
  · exact mul_le_mul_of_nonneg_left (by linarith) hq.le

/-- **Source interval cap.** -/
theorem agree_src_interval_cap (hbase : p.Basic) {R : ℝ} (hat : p.AtDepth k r R) (hN : 1 < p.N k)
    (hK1 : 1 ≤ p.K k) (hKH : p.K k ≤ H) (hd0 : 0 ≤ p.d) (hd1 : p.d ≤ 1) (hru : 0 ≤ r + u)
    {δb rm : ℝ} (hδb : 0 < δb) (hδb1 : δb ≤ 1) (hχ1 : p.N k ^ (-m) ≤ 1)
    (hrm1 : p.N k ^ (-rm) ≤ p.blockLen k r * δb / 2)
    (hrm2 : 3 * p.K k ^ 2 * p.N k ^ (-rm) ≤ p.N k ^ (-m))
    (hrm3 : 54 * p.N k ^ (m / 1000) * (p.K k + 1) ^ 4 * p.N k ^ (-rm) ≤ p.N k ^ (-(r + u)))
    (hcapk : ∀ s' : ℝ, 0 ≤ s' → s' ≤ r + u → ∀ (q : Fin 3 → ℤ) (a v' : ℤ),
      p.μ k {ω | p.z k (p.N k) rm ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s'))⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v'} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * rm - p.d * s')) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v'})
    (e : Fin (s.count 0)) (c : ℤ) (a b : ℝ) (hab : a ≤ b) :
    p.μ k (s.agSrc δb e c ∩ p.uN k r (s.parent 0 e) ⁻¹' Icc a b) ≤
      s.agSrcWeight δb e *
        ENNReal.ofReal (b - a + 4 * p.K k * p.N k ^ (-m) / p.blockWidth k r) := by
  classical
  set Ev := s.agSrc δb e c ∩ p.uN k r (s.parent 0 e) ⁻¹' Icc a b with hEv
  by_cases hne : Ev.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact zero_le
  obtain ⟨ω₀, hω₀⟩ := hne
  have hNpos : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := hN.le
  have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hNpos _
  have ha : 0 < p.N k ^ (-(r + u)) := Real.rpow_pos_of_pos hNpos _
  have hH1 : 1 ≤ H := by linarith [s.loss_one]
  have hq := agree_blockLen_pos (p := p) k r
  have hw := agree_blockWidth_pos (p := p) r hNpos
  set χ := p.N k ^ (-m) with hχ_def
  set K := p.K k with hK_def
  set Qb := s.parent 0 e with hQb
  set i := s.coarse 0 e with hi
  set j := s.fine 0 e with hj
  set tag0 := (s.layers 0).tag i 0 with htag0_def
  set tag1 := (s.layers 0).tag i 1 with htag1_def
  set q := p.blockLen k r with hq_def
  set wQ := p.blockWidth k r with hwQ_def
  have hK0 : 0 ≤ K := by linarith
  -- the velocity of the coarse tag line is bounded, by any incidence of the event
  have hvel0 : |(tag0 : ℝ) * χ| ≤ K + 1 := by
    obtain ⟨hgood, -, -, hC, -⟩ := s.agree_event_data0 hω₀.1.1
    have hb3 : |p.b k ω₀.1 3| ≤ K := by
      have := hgood.2
      have h0 := abs_nonneg (p.b k ω₀.1 0)
      have h1 := abs_nonneg (p.b k ω₀.1 1)
      have h4 := abs_nonneg (p.b k ω₀.1 4)
      linarith
    have hv := agree_abs_sub_bin_le hχ (s.agree_coarse_tags hC).1
    have := abs_sub_abs_le_abs_sub ((tag0 : ℝ) * χ) (p.b k ω₀.1 3)
    rw [abs_sub_comm] at this
    linarith
  have hc3 := hat.agree_coeff_le Qb 3
  have hc4 := hat.agree_coeff_le Qb 4
  have hc2 := hat.agree_coeff_le Qb 2
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hL : 0 ≤ 3 * K ^ 2 := by positivity
  let time : ℝ := s.agSrcTime δb e c + q * δb / 2
  let center : Fin 2 → ℝ :=
    ![(tag1 : ℝ) * χ, p.c k r Qb 2 + p.c k r Qb 4 * ((tag1 : ℝ) * χ) + wQ * ((a + b) / 2)]
  let velocity : Fin 2 → ℝ := ![(tag0 : ℝ) * χ, p.c k r Qb 3 + p.c k r Qb 4 * ((tag0 : ℝ) * χ)]
  let width : Fin 2 → ℝ := ![2 * χ, wQ * ((b - a) / 2) + 2 * K * χ]
  have hv : ∀ i, |velocity i| ≤ 3 * K ^ 2 := by
    intro i
    fin_cases i
    · simp only [velocity, Fin.zero_eta, Matrix.cons_val_zero]
      linarith
    · simp only [velocity, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_zero]
      calc _ ≤ |p.c k r Qb 3| + |p.c k r Qb 4 * ((tag0 : ℝ) * χ)| := abs_add_le _ _
        _ = |p.c k r Qb 3| + |p.c k r Qb 4| * |(tag0 : ℝ) * χ| := by rw [abs_mul]
        _ ≤ K + K * (K + 1) := by gcongr
        _ ≤ 3 * K ^ 2 := by nlinarith
  have hrmpos : 0 < p.N k ^ (-rm) := Real.rpow_pos_of_pos hNpos _
  have hrmle : p.N k ^ (-rm) ≤ 3 * K ^ 2 * p.N k ^ (-rm) := by
    have : 1 ≤ 3 * K ^ 2 := by nlinarith
    nlinarith
  have hwidth1 : 2 * K * χ ≤ wQ * ((b - a) / 2) + 2 * K * χ := by
    have : 0 ≤ wQ * ((b - a) / 2) := mul_nonneg hw.le (by linarith)
    linarith
  have hKχ : χ ≤ 2 * K * χ := by nlinarith
  have hdw : ∀ i, p.N k ^ (-rm) ≤ width i := by
    intro i
    fin_cases i
    · simp only [width, Fin.zero_eta, Matrix.cons_val_zero]
      linarith
    · simp only [width, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_zero]
      linarith
  have hmove : ∀ i, 3 * K ^ 2 * p.N k ^ (-rm) ≤ width i := by
    intro i
    fin_cases i
    · simp only [width, Fin.zero_eta, Matrix.cons_val_zero]
      linarith
    · simp only [width, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_zero]
      linarith
  have hfine := s.layer_valid (0 : Fin 2).succ
  have hGdeg : ((s.layers (0 : Fin 2).succ).G j).totalDegree ≤ 2 :=
    (hfine.2.2.2.2.2.1 j).2.1
  have hbox : ∀ ω ∈ Ev, (![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) ∈
      Submission.Lib.K4MovingMeshBoxes.movingBox time (q * δb / 2) center velocity width := by
    intro ω hω
    obtain ⟨⟨hωe, hωc⟩, hωU⟩ := hω
    obtain ⟨hgood, hB, ht, hC, hF⟩ := s.agree_event_data0 hωe
    have hunit := agree_block_subset_unit k r _ ht
    obtain ⟨htag0', htag1'⟩ := s.agree_coarse_tags hC
    have htube := intercept_velocity_bin_tube hχ htag1' htag0' hunit
    obtain ⟨hts0, hts1⟩ := s.agree_src_time_sharp hδb ⟨hωe, hωc⟩
    refine ⟨?_, ?_⟩
    · show |ω.2 - time| ≤ q * δb / 2
      simp only [time]
      rw [abs_le]
      constructor <;> linarith
    · intro i
      fin_cases i
      · show |p.x k ω.1 ω.2 1 - (center 0 + ω.2 * velocity 0)| ≤ width 0
        simp only [center, velocity, width, Matrix.cons_val_zero]
        exact htube
      · show |p.x k ω.1 ω.2 2 - (center 1 + ω.2 * velocity 1)| ≤ width 1
        simp only [center, velocity, width, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_zero]
        have hY := agree_x_two_eq_tilt (p := p) hNpos Qb ω
        have hU := hωU
        simp only [mem_preimage, mem_Icc] at hU
        have hx1 : p.x k ω.1 ω.2 1 = p.b k ω.1 0 + ω.2 * p.b k ω.1 3 := rfl
        have heq : p.x k ω.1 ω.2 2 -
            (p.c k r Qb 2 + p.c k r Qb 4 * ((tag1 : ℝ) * χ) + wQ * ((a + b) / 2) +
              ω.2 * (p.c k r Qb 3 + p.c k r Qb 4 * ((tag0 : ℝ) * χ))) =
            p.c k r Qb 4 * (p.b k ω.1 0 + ω.2 * p.b k ω.1 3 -
              ((tag1 : ℝ) * χ + ω.2 * ((tag0 : ℝ) * χ))) +
              wQ * (p.uN k r Qb ω - (a + b) / 2) := by
          rw [hY, ← hx1]
          unfold tiltY
          ring
        rw [heq]
        have hUc : |p.uN k r Qb ω - (a + b) / 2| ≤ (b - a) / 2 := by
          rw [abs_le]
          constructor <;> linarith [hU.1, hU.2]
        calc _ ≤ |p.c k r Qb 4 * (p.b k ω.1 0 + ω.2 * p.b k ω.1 3 -
                ((tag1 : ℝ) * χ + ω.2 * ((tag0 : ℝ) * χ)))| +
              |wQ * (p.uN k r Qb ω - (a + b) / 2)| := abs_add_le _ _
          _ = |p.c k r Qb 4| * |p.b k ω.1 0 + ω.2 * p.b k ω.1 3 -
                ((tag1 : ℝ) * χ + ω.2 * ((tag0 : ℝ) * χ))| +
              wQ * |p.uN k r Qb ω - (a + b) / 2| := by
              rw [abs_mul, abs_mul, abs_of_pos hw]
          _ ≤ K * (2 * χ) + wQ * ((b - a) / 2) := by
              gcongr
          _ = wQ * ((b - a) / 2) + 2 * K * χ := by ring
  have hvelEv : ∀ ω ∈ Ev, ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = tag0 := by
    intro ω hω
    exact (s.agree_coarse_tags (s.agree_event_data0 hω.1.1).2.2.2.1).1
  have hfitEv : ∀ ω ∈ Ev, |eval (p.x k ω.1 ω.2) (p.P k) -
      (fun x : Fin 3 → ℝ => eval ![x 0, x 2] ((s.layers (0 : Fin 2).succ).G j))
        ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2]| ≤ H * p.N k ^ (-(r + u)) := by
    intro ω hω
    obtain ⟨hgood, hB, ht, hC, hF⟩ := s.agree_event_data0 hω.1.1
    have hunit := agree_block_subset_unit k r _ ht
    exact s.agree_fine_fit hF hunit
  have hvarEv : ∀ ω ∈ Ev, ∀ y : Fin 3 → ℝ,
      (∀ i, |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i - y i| ≤
        p.N k ^ (-rm)) →
      |(fun x : Fin 3 → ℝ => eval ![x 0, x 2] ((s.layers (0 : Fin 2).succ).G j))
          ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] -
        (fun x : Fin 3 → ℝ => eval ![x 0, x 2] ((s.layers (0 : Fin 2).succ).G j)) y| ≤
        p.N k ^ (-(r + u)) := by
    intro ω hω y hy
    obtain ⟨hgood, -, -, -, -⟩ := s.agree_event_data0 hω.1.1
    have hbd := baseGood_base_bound p hK1 hgood
    have hx : ∀ i, |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i| ≤ K := by
      intro i
      fin_cases i
      · exact hbd 0
      · exact hbd 1
      · exact hbd 2
    have hrm1' : p.N k ^ (-rm) ≤ 1 := by
      have : q * δb / 2 ≤ 1 := by
        have hq1 := agree_blockLen_le_one (p := p) k r
        nlinarith
      linarith
    have h := projected_predictor_variation ((s.layers (0 : Fin 2).succ).G j) hGdeg
      (Real.rpow_nonneg hNpos.le (m / 1000)) hK1 hrmpos.le hrm1'
      (fun b => s.coefficient_bound (0 : Fin 2).succ j b) _ y hx hy
    exact h.trans hrm3
  have hΔ : 0 < H * p.N k ^ (-(r + u)) := by positivity
  have hmin : p.N k ^ (-(r + u)) ≤ H * p.N k ^ (-(r + u)) := le_mul_of_one_le_left ha.le hH1
  have hc := native_band_box_cap p hbase hN hK1 hd0 hru hΔ hmin hrm1 hL time center velocity
    width hv hdw hmove tag0
    (fun x : Fin 3 → ℝ => eval ![x 0, x 2] ((s.layers (0 : Fin 2).succ).G j))
    (p.μ k) le_rfl Ev hbox hvelEv hfitEv hvarEv hcapk
  refine hc.trans ?_
  -- compare the weights
  unfold agSrcWeight
  rw [mul_comm (ENNReal.ofReal _ * _) (ENNReal.ofReal _), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  simp only [width, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hpow : (H * p.N k ^ (-(r + u))) ^ p.d ≤ H * (p.N k ^ (-(r + u))) ^ p.d := by
    rw [Real.mul_rpow (by linarith) ha.le]
    gcongr
    calc H ^ p.d ≤ H ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hH1 hd1
      _ = H := Real.rpow_one H
  have hapos : 0 ≤ (p.N k ^ (-(r + u))) ^ p.d := Real.rpow_nonneg ha.le _
  have hlam : b - a + 4 * K * χ / wQ = (wQ * ((b - a) / 2) + 2 * K * χ) * 2 / wQ := by
    field_simp
    ring
  rw [hlam]
  have hfac : 0 ≤ 4200 * K ^ 2 * (q * δb / 2) * (2 * χ) * (wQ * ((b - a) / 2) + 2 * K * χ) := by
    have : 0 ≤ wQ * ((b - a) / 2) + 2 * K * χ := by
      have : 0 ≤ wQ * ((b - a) / 2) := mul_nonneg hw.le (by linarith)
      positivity
    positivity
  calc 4200 * K ^ 2 * (H * p.N k ^ (-(r + u))) ^ p.d * (q * δb / 2) * (2 * χ) *
        (wQ * ((b - a) / 2) + 2 * K * χ)
      = (H * p.N k ^ (-(r + u))) ^ p.d *
          (4200 * K ^ 2 * (q * δb / 2) * (2 * χ) * (wQ * ((b - a) / 2) + 2 * K * χ)) := by ring
    _ ≤ (H * (p.N k ^ (-(r + u))) ^ p.d) *
          (4200 * K ^ 2 * (q * δb / 2) * (2 * χ) * (wQ * ((b - a) / 2) + 2 * K * χ)) :=
        mul_le_mul_of_nonneg_right hpow hfac
    _ = _ := by
        simp only [hq_def, hwQ_def, hK_def, hχ_def]
        have hw' : p.blockWidth k r ≠ 0 := ne_of_gt (agree_blockWidth_pos (p := p) r hNpos)
        field_simp
        ring

/-- **Sum of source weights**, through the color-0 reference budget. -/
theorem agree_sum_srcWeight_le {δb : ℝ} (hδb : 0 < δb) (hδb1 : δb ≤ 1) (hN : 0 < p.N k)
    (hK1 : 1 ≤ p.K k) :
    ∑ x ∈ (Finset.univ : Finset (Fin (s.count 0))) ×ˢ Finset.Icc (0 : ℤ) ⌊1 / δb⌋,
        s.agSrcWeight δb x.1 ≤ ENNReal.ofReal (4200 * p.K k ^ 2 * H * H) := by
  rw [Finset.sum_product]
  simp only [Finset.sum_const, nsmul_eq_mul]
  set card := (Finset.Icc (0 : ℤ) ⌊1 / δb⌋).card with hcard_def
  have hcard : (card : ℝ) * δb ≤ 2 := by
    rw [hcard_def, Int.card_Icc]
    have hfl : (0 : ℤ) ≤ ⌊1 / δb⌋ + 1 - 0 := by
      have : (0 : ℤ) ≤ ⌊1 / δb⌋ := Int.floor_nonneg.mpr (by positivity)
      omega
    have hcast : (((⌊1 / δb⌋ + 1 - 0).toNat : ℕ) : ℝ) = ((⌊1 / δb⌋ : ℤ) : ℝ) + 1 := by
      have h := Int.toNat_of_nonneg hfl
      have h' : ((((⌊1 / δb⌋ + 1 - 0).toNat : ℕ) : ℤ) : ℝ) = (((⌊1 / δb⌋ + 1 - 0 : ℤ)) : ℝ) := by
        rw [h]
      rw [Int.cast_natCast] at h'
      rw [h']
      push_cast
      ring
    rw [hcast]
    have h1 := Int.floor_le (1 / δb)
    have h2 : ((⌊1 / δb⌋ : ℤ) : ℝ) * δb ≤ 1 := by
      calc ((⌊1 / δb⌋ : ℤ) : ℝ) * δb ≤ 1 / δb * δb := mul_le_mul_of_nonneg_right h1 hδb.le
        _ = 1 := by field_simp
    nlinarith
  have hH0 : 0 ≤ H := by linarith [s.loss_one]
  have hq := agree_blockLen_pos (p := p) k r
  have hw := agree_blockWidth_pos (p := p) r hN
  have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have ha : 0 ≤ (p.N k ^ (-(r + u))) ^ p.d := Real.rpow_nonneg (Real.rpow_pos_of_pos hN _).le _
  have hK0 : 0 ≤ p.K k := by linarith
  have hstep : ∀ e : Fin (s.count 0), (card : ℝ≥0∞) * s.agSrcWeight δb e ≤
      ENNReal.ofReal (4200 * p.K k ^ 2 * H) *
        (ENNReal.ofReal (p.blockLen k r * p.N k ^ (-m) * p.blockWidth k r *
          (p.N k ^ (-(r + u))) ^ p.d) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (s.layers 0).tag (s.coarse 0 e) 0}) := by
    intro e
    unfold agSrcWeight
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hX : 0 ≤ 2100 * p.K k ^ 2 * H * (p.N k ^ (-(r + u))) ^ p.d * p.blockLen k r *
        p.N k ^ (-m) * p.blockWidth k r := by positivity
    calc (card : ℝ) * (2100 * p.K k ^ 2 * H * (p.N k ^ (-(r + u))) ^ p.d * p.blockLen k r * δb *
          p.N k ^ (-m) * p.blockWidth k r)
        = ((card : ℝ) * δb) * (2100 * p.K k ^ 2 * H * (p.N k ^ (-(r + u))) ^ p.d *
            p.blockLen k r * p.N k ^ (-m) * p.blockWidth k r) := by ring
      _ ≤ 2 * (2100 * p.K k ^ 2 * H * (p.N k ^ (-(r + u))) ^ p.d *
            p.blockLen k r * p.N k ^ (-m) * p.blockWidth k r) :=
          mul_le_mul_of_nonneg_right hcard hX
      _ = _ := by ring
  have hbudget := s.reference_budget 0
  have hsum : (∑ e : Fin (s.count 0),
      ENNReal.ofReal (p.blockLen k r * p.N k ^ (-m) * p.blockWidth k r *
        (p.N k ^ (-(r + u))) ^ p.d) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (s.layers 0).tag (s.coarse 0 e) 0}) ≤
      ENNReal.ofReal H := by
    convert hbudget using 4 with e
    rw [agree_blockLen_eq_zpow]
    simp only [Matrix.cons_val_zero, blockWidth, agree_blockLen_eq_zpow]
    congr 2
    ring
  calc _ ≤ ∑ e : Fin (s.count 0), ENNReal.ofReal (4200 * p.K k ^ 2 * H) *
        (ENNReal.ofReal (p.blockLen k r * p.N k ^ (-m) * p.blockWidth k r *
          (p.N k ^ (-(r + u))) ^ p.d) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (s.layers 0).tag (s.coarse 0 e) 0}) :=
        Finset.sum_le_sum fun e _ => hstep e
    _ = ENNReal.ofReal (4200 * p.K k ^ 2 * H) * ∑ e : Fin (s.count 0),
        (ENNReal.ofReal (p.blockLen k r * p.N k ^ (-m) * p.blockWidth k r *
          (p.N k ^ (-(r + u))) ^ p.d) *
          p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (s.layers 0).tag (s.coarse 0 e) 0}) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (4200 * p.K k ^ 2 * H) * ENNReal.ofReal H := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end ComparedSample

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
