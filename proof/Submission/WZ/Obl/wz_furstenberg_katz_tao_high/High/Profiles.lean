-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.Profiles.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/Profiles.lean (95ffa93).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.AtScale

/-!
# Cell profiles from counts

For a finite pin set `Q`, `cellCount Q ρ` is the number of occupied `ρ`-grid squares.
* `cellCount_mono_ratio`: for `ρ' ≤ ρ`, `cellCount Q ρ' ≤ (ρ / ρ' + 2) ^ 2 cellCount Q ρ`
  (a `ρ`-square meets at most `(ρ/ρ' + 2)^2` squares of side `ρ'`).
* `cellCount_le_box`: pins of norm `≤ 4` occupy at most `(8 / ρ + 2) ^ 2` squares.
* `cellCount_ge_of_frostman`: if every closed ball of radius `2 ρ` holds at most `A` pins, then
  `#Q ≤ A · cellCount Q ρ`.
These are the inputs of x0672's `halving_select` for the profile `G i = log_B cellCount Q (B ^ -i)`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high

attribute [local instance] Classical.propDecidable

/-- The number of occupied `ρ`-grid squares. -/
noncomputable def cellCount (Q : Finset E2) (ρ : ℝ) : ℕ := (Q.image (cellOf ρ)).card

/-- Integer points of an interval of length `L` (in units of `ρ'`). -/
theorem floor_range_card {a ρ ρ' : ℝ} (hρ' : 0 < ρ') (hρ : 0 < ρ) :
    ((Finset.Icc ⌊a / ρ'⌋ ⌊(a + ρ) / ρ'⌋).card : ℝ) ≤ ρ / ρ' + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le (a / ρ')
  have h2 := Int.lt_floor_add_one (a / ρ')
  have h3 := Int.floor_le ((a + ρ) / ρ')
  have h4 := Int.lt_floor_add_one ((a + ρ) / ρ')
  have hdiv : (a + ρ) / ρ' = a / ρ' + ρ / ρ' := by rw [add_div]
  have hcast : ((⌊(a + ρ) / ρ'⌋ + 1 - ⌊a / ρ'⌋).toNat : ℝ) ≤
      ((⌊(a + ρ) / ρ'⌋ + 1 - ⌊a / ρ'⌋ : ℤ) : ℝ) + 0 := by
    rw [add_zero]
    have hnn : (0 : ℤ) ≤ ⌊(a + ρ) / ρ'⌋ + 1 - ⌊a / ρ'⌋ := by
      have : ⌊a / ρ'⌋ ≤ ⌊(a + ρ) / ρ'⌋ := Int.floor_le_floor (by
        rw [hdiv]; have : 0 < ρ / ρ' := div_pos hρ hρ'; linarith)
      omega
    exact_mod_cast (Int.toNat_of_nonneg hnn).le
  calc ((⌊(a + ρ) / ρ'⌋ + 1 - ⌊a / ρ'⌋).toNat : ℝ)
      ≤ ((⌊(a + ρ) / ρ'⌋ + 1 - ⌊a / ρ'⌋ : ℤ) : ℝ) := by linarith
    _ = (⌊(a + ρ) / ρ'⌋ : ℝ) + 1 - ⌊a / ρ'⌋ := by push_cast; ring
    _ ≤ ρ / ρ' + 2 := by
        have h3' : (⌊(a + ρ) / ρ'⌋ : ℝ) ≤ a / ρ' + ρ / ρ' := by rw [← hdiv]; exact Int.floor_le _
        linarith

/-- A `ρ`-square meets at most `(ρ/ρ' + 2)^2` squares of side `ρ'`. -/
theorem cellCount_mono_ratio (Q : Finset E2) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ') :
    (cellCount Q ρ' : ℝ) ≤ (ρ / ρ' + 2) ^ 2 * cellCount Q ρ := by
  classical
  unfold cellCount
  -- fibers of the coarse cell map on the fine cells
  set Cf := Q.image (cellOf ρ') with hCf
  set Cc := Q.image (cellOf ρ) with hCc
  -- each fine cell is witnessed by a point; map it to the coarse cell of that point
  have hwit : ∀ c ∈ Cf, ∃ x ∈ Q, cellOf ρ' x = c := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨x, hx, rfl⟩
  choose! wit hwitQ hwitc using hwit
  have hmaps : ∀ c ∈ Cf, cellOf ρ (wit c) ∈ Cc := fun c hc =>
    Finset.mem_image.mpr ⟨wit c, hwitQ c hc, rfl⟩
  have hsum : (Cf.card : ℝ) = ∑ d ∈ Cc, ((Cf.filter (fun c => cellOf ρ (wit c) = d)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun c => cellOf ρ (wit c)) (s := Cf) (t := Cc)
      hmaps
    rw [this]; push_cast; rfl
  rw [hsum]
  have hfib : ∀ d ∈ Cc, ((Cf.filter (fun c => cellOf ρ (wit c) = d)).card : ℝ) ≤ (ρ / ρ' + 2) ^ 2 := by
    intro d hd
    -- fine cells whose witness lies in the coarse square `d`
    have hsub : Cf.filter (fun c => cellOf ρ (wit c) = d) ⊆
        Finset.Icc ⌊((d.1 : ℝ) * ρ) / ρ'⌋ ⌊((d.1 : ℝ) * ρ + ρ) / ρ'⌋ ×ˢ
          Finset.Icc ⌊((d.2 : ℝ) * ρ) / ρ'⌋ ⌊((d.2 : ℝ) * ρ + ρ) / ρ'⌋ := by
      intro c hc
      obtain ⟨hcf, hcd⟩ := Finset.mem_filter.mp hc
      have hwc := hwitc c hcf
      set x := wit c
      have hd1 : ⌊x 0 / ρ⌋ = d.1 := by rw [← hcd]; rfl
      have hd2 : ⌊x 1 / ρ⌋ = d.2 := by rw [← hcd]; rfl
      have hc1 : ⌊x 0 / ρ'⌋ = c.1 := by rw [← hwc]; rfl
      have hc2 : ⌊x 1 / ρ'⌋ = c.2 := by rw [← hwc]; rfl
      have bounds : ∀ (t : ℝ) (k : ℤ), ⌊t / ρ⌋ = k →
          ⌊((k : ℝ) * ρ) / ρ'⌋ ≤ ⌊t / ρ'⌋ ∧ ⌊t / ρ'⌋ ≤ ⌊((k : ℝ) * ρ + ρ) / ρ'⌋ := by
        intro t k hk
        have h1 := Int.floor_le (t / ρ)
        have h2 := Int.lt_floor_add_one (t / ρ)
        rw [hk] at h1 h2
        have ht1 : (k : ℝ) * ρ ≤ t := by rw [le_div_iff₀ hρ] at h1; linarith
        have ht2 : t ≤ (k : ℝ) * ρ + ρ := by
          rw [div_lt_iff₀ hρ] at h2; linarith
        exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right ht1 hρ'.le),
          Int.floor_le_floor (div_le_div_of_nonneg_right ht2 hρ'.le)⟩
      obtain ⟨b1, b2⟩ := bounds (x 0) d.1 hd1
      obtain ⟨b3, b4⟩ := bounds (x 1) d.2 hd2
      rw [hc1] at b1 b2
      rw [hc2] at b3 b4
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨b1, b2⟩, Finset.mem_Icc.mpr ⟨b3, b4⟩⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_product] at h1
    have h2 := floor_range_card (a := (d.1 : ℝ) * ρ) hρ' hρ
    have h3 := floor_range_card (a := (d.2 : ℝ) * ρ) hρ' hρ
    calc ((Cf.filter (fun c => cellOf ρ (wit c) = d)).card : ℝ)
        ≤ ((Finset.Icc ⌊((d.1 : ℝ) * ρ) / ρ'⌋ ⌊((d.1 : ℝ) * ρ + ρ) / ρ'⌋).card : ℝ) *
          ((Finset.Icc ⌊((d.2 : ℝ) * ρ) / ρ'⌋ ⌊((d.2 : ℝ) * ρ + ρ) / ρ'⌋).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ (ρ / ρ' + 2) * (ρ / ρ' + 2) :=
          mul_le_mul h2 h3 (Nat.cast_nonneg _) (by positivity)
      _ = (ρ / ρ' + 2) ^ 2 := by ring
  calc ∑ d ∈ Cc, ((Cf.filter (fun c => cellOf ρ (wit c) = d)).card : ℝ)
      ≤ ∑ _d ∈ Cc, (ρ / ρ' + 2) ^ 2 := Finset.sum_le_sum hfib
    _ = (ρ / ρ' + 2) ^ 2 * Cc.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Pins of norm at most `4` occupy at most `(8 / ρ + 2) ^ 2` squares of side `ρ`. -/
theorem cellCount_le_box (Q : Finset E2) {ρ : ℝ} (hρ : 0 < ρ) (hQ4 : ∀ x ∈ Q, ‖x‖ ≤ 4) :
    (cellCount Q ρ : ℝ) ≤ (8 / ρ + 2) ^ 2 := by
  classical
  unfold cellCount
  have hsub : Q.image (cellOf ρ) ⊆ Finset.Icc ⌊(-4 : ℝ) / ρ⌋ ⌊((-4 : ℝ) + 8) / ρ⌋ ×ˢ
      Finset.Icc ⌊(-4 : ℝ) / ρ⌋ ⌊((-4 : ℝ) + 8) / ρ⌋ := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    have hn := hQ4 x hx
    have hc0 : |x 0| ≤ 4 := by
      have := PiLp.norm_apply_le x 0
      rw [Real.norm_eq_abs] at this
      exact this.trans hn
    have hc1 : |x 1| ≤ 4 := by
      have := PiLp.norm_apply_le x 1
      rw [Real.norm_eq_abs] at this
      exact this.trans hn
    have hb : ∀ t : ℝ, |t| ≤ 4 → ⌊(-4 : ℝ) / ρ⌋ ≤ ⌊t / ρ⌋ ∧ ⌊t / ρ⌋ ≤ ⌊((-4 : ℝ) + 8) / ρ⌋ := by
      intro t ht
      rw [abs_le] at ht
      exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right ht.1 hρ.le),
        Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hρ.le)⟩
    obtain ⟨a1, a2⟩ := hb _ hc0
    obtain ⟨a3, a4⟩ := hb _ hc1
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨a1, a2⟩, Finset.mem_Icc.mpr ⟨a3, a4⟩⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_product] at h1
  have h2 := floor_range_card (a := (-4 : ℝ)) hρ (show (0 : ℝ) < 8 by norm_num)
  calc ((Q.image (cellOf ρ)).card : ℝ)
      ≤ ((Finset.Icc ⌊(-4 : ℝ) / ρ⌋ ⌊((-4 : ℝ) + 8) / ρ⌋).card : ℝ) *
        ((Finset.Icc ⌊(-4 : ℝ) / ρ⌋ ⌊((-4 : ℝ) + 8) / ρ⌋).card : ℝ) := by exact_mod_cast h1
    _ ≤ (8 / ρ + 2) * (8 / ρ + 2) := mul_le_mul h2 h2 (Nat.cast_nonneg _) (by positivity)
    _ = (8 / ρ + 2) ^ 2 := by ring

/-- If every closed ball of radius `2 ρ` holds at most `A` pins, `#Q ≤ A · cellCount Q ρ`. -/
theorem card_le_cellCount_mul (Q : Finset E2) {ρ A : ℝ} (hρ : 0 < ρ)
    (hA : ∀ x ∈ Q, ((Q.filter (fun z => dist z x ≤ 2 * ρ)).card : ℝ) ≤ A) :
    (Q.card : ℝ) ≤ A * cellCount Q ρ := by
  classical
  unfold cellCount
  have hsum : (Q.card : ℝ) = ∑ c ∈ Q.image (cellOf ρ), ((Q.filter (fun z => cellOf ρ z = c)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := cellOf ρ) (s := Q) (t := Q.image (cellOf ρ))
      (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    rw [this]; push_cast; rfl
  rw [hsum]
  calc ∑ c ∈ Q.image (cellOf ρ), ((Q.filter (fun z => cellOf ρ z = c)).card : ℝ)
      ≤ ∑ _c ∈ Q.image (cellOf ρ), A := by
        apply Finset.sum_le_sum
        intro c hc
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
        refine le_trans ?_ (hA x hx)
        have hsub : Q.filter (fun z => cellOf ρ z = cellOf ρ x) ⊆ Q.filter (fun z => dist z x ≤ 2 * ρ) := by
          intro z hz
          obtain ⟨hzQ, hzc⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzQ, dist_le_of_cellOf_eq hρ hzc⟩
        exact_mod_cast Finset.card_le_card hsub
    _ = A * (Q.image (cellOf ρ)).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- `log_B` comparison: `X ≤ c B ^ k Y` gives `log_B X ≤ log_B Y + k + log_B c`. -/
theorem logb_le_of_le_mul_rpow {B X Y c k : ℝ} (hB : 1 < B) (hX : 0 < X) (hY : 0 < Y) (hc : 0 < c)
    (h : X ≤ c * B ^ k * Y) : Real.logb B X ≤ Real.logb B Y + k + Real.logb B c := by
  have hB0 : 0 < B := by linarith
  have hBk : 0 < B ^ k := Real.rpow_pos_of_pos hB0 k
  have h1 : Real.logb B X ≤ Real.logb B (c * B ^ k * Y) :=
    Real.logb_le_logb_of_le hB hX h
  rw [Real.logb_mul (by positivity) hY.ne', Real.logb_mul hc.ne' hBk.ne',
    Real.logb_rpow hB0 (by linarith)] at h1
  linarith

/-- The cell profile at the palette scales `B ^ (-i)`. -/
noncomputable def cellProfile (Q : Finset E2) (B : ℝ) (i : ℕ) : ℝ :=
  Real.logb B (cellCount Q (B ^ (-(i : ℝ))))

theorem cellCount_pos {Q : Finset E2} (hQ : Q.Nonempty) (ρ : ℝ) : 0 < cellCount Q ρ := by
  unfold cellCount
  exact Finset.card_pos.mpr (hQ.image _)

/-- `halving_select`'s Lipschitz hypothesis: `G j - G i ≤ 2 (j - i) + log_B 9`. -/
theorem cellProfile_lip {Q : Finset E2} (hQ : Q.Nonempty) {B : ℝ} (hB : 1 < B) {i j : ℕ}
    (hij : i ≤ j) :
    cellProfile Q B j - cellProfile Q B i ≤ 2 * ((j : ℝ) - i) + Real.logb B 9 := by
  have hB0 : 0 < B := by linarith
  have hρi : 0 < B ^ (-(i : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hρj : 0 < B ^ (-(j : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hmono := cellCount_mono_ratio Q hρi hρj
  have hratio : B ^ (-(i : ℝ)) / B ^ (-(j : ℝ)) = B ^ ((j : ℝ) - i) := by
    rw [← Real.rpow_sub hB0]; ring_nf
  rw [hratio] at hmono
  have hge1 : 1 ≤ B ^ ((j : ℝ) - i) := Real.one_le_rpow hB.le (by
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith)
  have h9 : (B ^ ((j : ℝ) - i) + 2) ^ 2 ≤ 9 * B ^ (2 * ((j : ℝ) - i)) := by
    have hsq : B ^ (2 * ((j : ℝ) - i)) = (B ^ ((j : ℝ) - i)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]; ring_nf
    rw [hsq]
    nlinarith
  have hpos_i : (0 : ℝ) < cellCount Q (B ^ (-(i : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  have hpos_j : (0 : ℝ) < cellCount Q (B ^ (-(j : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  have hle : (cellCount Q (B ^ (-(j : ℝ))) : ℝ) ≤ 9 * B ^ (2 * ((j : ℝ) - i)) *
      cellCount Q (B ^ (-(i : ℝ))) :=
    hmono.trans (mul_le_mul_of_nonneg_right h9 hpos_i.le)
  have := logb_le_of_le_mul_rpow hB hpos_j hpos_i (by norm_num) hle
  unfold cellProfile
  linarith

/-- `halving_select`'s bottom hypothesis: `G i ≤ 2 i + log_B 100` for pins of norm `≤ 4`. -/
theorem cellProfile_le {Q : Finset E2} (hQ : Q.Nonempty) (hQ4 : ∀ x ∈ Q, ‖x‖ ≤ 4) {B : ℝ}
    (hB : 1 < B) (i : ℕ) :
    cellProfile Q B i ≤ 2 * (i : ℝ) + Real.logb B 100 := by
  have hB0 : 0 < B := by linarith
  have hρ : 0 < B ^ (-(i : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hbox := cellCount_le_box Q hρ hQ4
  have hinv : 8 / B ^ (-(i : ℝ)) = 8 * B ^ (i : ℝ) := by
    rw [Real.rpow_neg hB0.le, div_inv_eq_mul]
  rw [hinv] at hbox
  have hge1 : 1 ≤ B ^ (i : ℝ) := Real.one_le_rpow hB.le (Nat.cast_nonneg _)
  have h100 : (8 * B ^ (i : ℝ) + 2) ^ 2 ≤ 100 * B ^ (2 * (i : ℝ)) * 1 := by
    have hsq : B ^ (2 * (i : ℝ)) = (B ^ (i : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]; ring_nf
    rw [hsq]
    nlinarith
  have hpos : (0 : ℝ) < cellCount Q (B ^ (-(i : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  have := logb_le_of_le_mul_rpow hB hpos (by norm_num) (by norm_num) (hbox.trans h100)
  unfold cellProfile
  rw [Real.logb_one] at this
  linarith

/-- Lower bound from normalized Frostman: if every ball of radius `2 B ^ (-i)` around a pin holds
at most `C · 2 B ^ (-i) · #Q` pins, then `G i ≥ i - log_B (2 C)`. -/
theorem cellProfile_ge {Q : Finset E2} (hQ : Q.Nonempty) {B C : ℝ} (hB : 1 < B) (hC : 0 < C)
    (i : ℕ)
    (hfr : ∀ x ∈ Q, ((Q.filter (fun z => dist z x ≤ 2 * B ^ (-(i : ℝ)))).card : ℝ) ≤
      C * (2 * B ^ (-(i : ℝ))) * Q.card) :
    (i : ℝ) - Real.logb B (2 * C) ≤ cellProfile Q B i := by
  have hB0 : 0 < B := by linarith
  have hρ : 0 < B ^ (-(i : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hQpos : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hcnt := card_le_cellCount_mul Q hρ hfr
  have hpos : (0 : ℝ) < cellCount Q (B ^ (-(i : ℝ))) := by exact_mod_cast cellCount_pos hQ _
  -- #Q ≤ C 2 B^-i #Q cellCount, so 1 ≤ 2 C B^-i cellCount, i.e. B^i ≤ 2C cellCount
  have h1 : (1 : ℝ) ≤ 2 * C * B ^ (-(i : ℝ)) * cellCount Q (B ^ (-(i : ℝ))) := by
    have : (Q.card : ℝ) * 1 ≤ Q.card * (2 * C * B ^ (-(i : ℝ)) * cellCount Q (B ^ (-(i : ℝ)))) := by
      calc (Q.card : ℝ) * 1 = Q.card := by ring
        _ ≤ C * (2 * B ^ (-(i : ℝ))) * Q.card * cellCount Q (B ^ (-(i : ℝ))) := hcnt
        _ = Q.card * (2 * C * B ^ (-(i : ℝ)) * cellCount Q (B ^ (-(i : ℝ)))) := by ring
    exact le_of_mul_le_mul_left this hQpos
  have h2 : B ^ (i : ℝ) ≤ 2 * C * cellCount Q (B ^ (-(i : ℝ))) := by
    have hBi : B ^ (i : ℝ) * B ^ (-(i : ℝ)) = 1 := by
      rw [← Real.rpow_add hB0]; simp
    have hBi0 : 0 < B ^ (i : ℝ) := Real.rpow_pos_of_pos hB0 _
    calc B ^ (i : ℝ) = B ^ (i : ℝ) * 1 := by ring
      _ ≤ B ^ (i : ℝ) * (2 * C * B ^ (-(i : ℝ)) * cellCount Q (B ^ (-(i : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 hBi0.le
      _ = (B ^ (i : ℝ) * B ^ (-(i : ℝ))) * (2 * C * cellCount Q (B ^ (-(i : ℝ)))) := by ring
      _ = 2 * C * cellCount Q (B ^ (-(i : ℝ))) := by rw [hBi, one_mul]
  have h3 : Real.logb B (B ^ (i : ℝ)) ≤ Real.logb B (2 * C * cellCount Q (B ^ (-(i : ℝ)))) :=
    Real.logb_le_logb_of_le hB (Real.rpow_pos_of_pos hB0 _) h2
  rw [Real.logb_rpow hB0 (by linarith), Real.logb_mul (by positivity) hpos.ne'] at h3
  unfold cellProfile
  linarith

/-- Coarse cells are at most four times the fine ones (`ρ' ≤ ρ`): the points of one fine
square lie in at most `2 × 2` coarse squares. -/
theorem cellCount_coarse_le (Q : Finset E2) {ρ ρ' : ℝ} (hρ' : 0 < ρ') (hρρ : ρ' ≤ ρ) :
    (cellCount Q ρ : ℝ) ≤ 4 * cellCount Q ρ' := by
  classical
  have hρ : 0 < ρ := hρ'.trans_le hρρ
  unfold cellCount
  set Cf := Q.image (cellOf ρ') with hCf
  set Cc := Q.image (cellOf ρ) with hCc
  -- every coarse cell contains a point whose fine cell is in Cf; count coarse cells per fine cell
  have hmaps : ∀ c ∈ Cc, ∃ x ∈ Q, cellOf ρ x = c := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨x, hx, rfl⟩
  choose! wit hwitQ hwitc using hmaps
  have hmapsto : ∀ c ∈ Cc, cellOf ρ' (wit c) ∈ Cf := fun c hc =>
    Finset.mem_image.mpr ⟨wit c, hwitQ c hc, rfl⟩
  have hsum : (Cc.card : ℝ) = ∑ d ∈ Cf, ((Cc.filter (fun c => cellOf ρ' (wit c) = d)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun c => cellOf ρ' (wit c)) (s := Cc) (t := Cf)
      hmapsto
    rw [this]; push_cast; rfl
  rw [hsum]
  have hfib : ∀ d ∈ Cf, ((Cc.filter (fun c => cellOf ρ' (wit c) = d)).card : ℝ) ≤ 4 := by
    intro d hd
    -- coarse cells whose witness lies in the fine square `d`
    have hsub : Cc.filter (fun c => cellOf ρ' (wit c) = d) ⊆
        Finset.Icc ⌊((d.1 : ℝ) * ρ') / ρ⌋ (⌊((d.1 : ℝ) * ρ') / ρ⌋ + 1) ×ˢ
          Finset.Icc ⌊((d.2 : ℝ) * ρ') / ρ⌋ (⌊((d.2 : ℝ) * ρ') / ρ⌋ + 1) := by
      intro c hc
      obtain ⟨hcC, hcd⟩ := Finset.mem_filter.mp hc
      have hwc := hwitc c hcC
      set x := wit c
      have hd1 : ⌊x 0 / ρ'⌋ = d.1 := by rw [← hcd]; rfl
      have hd2 : ⌊x 1 / ρ'⌋ = d.2 := by rw [← hcd]; rfl
      have hc1 : ⌊x 0 / ρ⌋ = c.1 := by rw [← hwc]; rfl
      have hc2 : ⌊x 1 / ρ⌋ = c.2 := by rw [← hwc]; rfl
      have bounds : ∀ (t : ℝ) (k : ℤ), ⌊t / ρ'⌋ = k →
          ⌊((k : ℝ) * ρ') / ρ⌋ ≤ ⌊t / ρ⌋ ∧ ⌊t / ρ⌋ ≤ ⌊((k : ℝ) * ρ') / ρ⌋ + 1 := by
        intro t k hk
        have h1 := Int.floor_le (t / ρ')
        have h2 := Int.lt_floor_add_one (t / ρ')
        rw [hk] at h1 h2
        have ht1 : (k : ℝ) * ρ' ≤ t := by rw [le_div_iff₀ hρ'] at h1; linarith
        have ht2 : t < (k : ℝ) * ρ' + ρ' := by rw [div_lt_iff₀ hρ'] at h2; linarith
        refine ⟨Int.floor_le_floor (div_le_div_of_nonneg_right ht1 hρ.le), ?_⟩
        -- t / ρ < k ρ' / ρ + 1
        have h3 : t / ρ < (k : ℝ) * ρ' / ρ + 1 := by
          rw [div_lt_iff₀ hρ]
          have : (k : ℝ) * ρ' / ρ * ρ = (k : ℝ) * ρ' := by field_simp
          nlinarith
        have h4 := Int.floor_le ((k : ℝ) * ρ' / ρ)
        have h5 : ⌊t / ρ⌋ < ⌊((k : ℝ) * ρ') / ρ⌋ + 2 := by
          have := Int.floor_le (t / ρ)
          have h6 := Int.lt_floor_add_one ((k : ℝ) * ρ' / ρ)
          have : (⌊t / ρ⌋ : ℝ) < (⌊((k : ℝ) * ρ') / ρ⌋ : ℝ) + 2 := by linarith
          exact_mod_cast this
        omega
      obtain ⟨b1, b2⟩ := bounds (x 0) d.1 hd1
      obtain ⟨b3, b4⟩ := bounds (x 1) d.2 hd2
      rw [hc1] at b1 b2
      rw [hc2] at b3 b4
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨b1, b2⟩, Finset.mem_Icc.mpr ⟨b3, b4⟩⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc] at h1
    have h2 : (⌊((d.1 : ℝ) * ρ') / ρ⌋ + 1 + 1 - ⌊((d.1 : ℝ) * ρ') / ρ⌋).toNat = 2 := by omega
    have h3 : (⌊((d.2 : ℝ) * ρ') / ρ⌋ + 1 + 1 - ⌊((d.2 : ℝ) * ρ') / ρ⌋).toNat = 2 := by omega
    rw [h2, h3] at h1
    exact_mod_cast h1
  calc ∑ d ∈ Cf, ((Cc.filter (fun c => cellOf ρ' (wit c) = d)).card : ℝ)
      ≤ ∑ _d ∈ Cf, (4 : ℝ) := Finset.sum_le_sum hfib
    _ = 4 * Cf.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
