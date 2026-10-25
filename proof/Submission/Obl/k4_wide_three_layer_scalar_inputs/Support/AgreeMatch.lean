import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeDefs
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Caps

set_option linter.unusedVariables false

/-!
# The matching step of the coefficient agreement
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H R : ℝ}

namespace ComparedBlock

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable (CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams)

/-- A good incidence lies near the chart line of its own class at the reference time. -/
theorem good_refZ (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hL : HorizontalForm (cfg.F k s CB.i) CB.L) (hχ : 0 < χ) (hδt : 0 < P.δt)
    {p : α × ℝ} (hp : CB.Good p) :
    |CB.frame.zt p.2 - refX P (CB.cell P p)| ≤ P.δt / 2 ∧
    |CB.frame.zZ (cfg.b k p.1) p.2 - CB.refZ P (CB.cls p) (CB.cell P p)| ≤
      χ / CB.frame.q + P.δt * (2 * cfg.K k + χ) / 2 := by
  have hq : 0 < CB.frame.q := by simp only [frame, blockFrame]; positivity
  obtain ⟨hzt, -, -, -, hb3⟩ := CB.good_bounds hB hN hK hL hp
  have hx : |CB.frame.zt p.2 - refX P (CB.cell P p)| ≤ P.δt / 2 := by
    have := abs_sub_center_of_floor hδt (rfl : ⌊CB.frame.zt p.2 / P.δt⌋ = CB.cell P p)
    rw [show refX P (CB.cell P p) = P.δt * ((CB.cell P p : ℝ) + 1 / 2) by simp [refX, mul_comm]]
    exact this
  refine ⟨hx, ?_⟩
  have hch := hp.chart
  simp only [chart] at hch
  set n := (CB.chartOf (CB.cls p)).1
  set m := (CB.chartOf (CB.cls p)).2
  have hn : ⌊cfg.b k p.1 3 / χ⌋ = n := by
    simp only [n, cls]; rw [← hch]
  have hm : ⌊cfg.b k p.1 0 / χ⌋ = m := by
    simp only [m, cls]; rw [← hch]
  have hb3c := abs_sub_center_of_floor hχ hn
  have hb0c := abs_sub_center_of_floor hχ hm
  have ht := I_subset_unit hp.I
  set T := CB.refT P (CB.cell P p)
  have hT : |p.2 - T| ≤ CB.frame.q * P.δt / 2 := by
    have e : p.2 - T = CB.frame.q * (CB.frame.zt p.2 - refX P (CB.cell P p)) := by
      simp only [T, refT, frame, Frame.zt, blockFrame]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hq]
    calc CB.frame.q * |CB.frame.zt p.2 - refX P (CB.cell P p)| ≤ CB.frame.q * (P.δt / 2) := by
          gcongr
      _ = _ := by ring
  have hnc : |((n : ℝ) + 1 / 2) * χ - CB.frame.c 1| ≤ 2 * cfg.K k + χ := by
    have e : ((n : ℝ) + 1 / 2) * χ - CB.frame.c 1 =
        (cfg.b k p.1 3 - CB.frame.c 1) - (cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)) := by ring
    rw [e]
    calc _ ≤ |cfg.b k p.1 3 - CB.frame.c 1| + |cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)| :=
          abs_sub _ _
      _ ≤ 2 * cfg.K k + χ / 2 := add_le_add hb3 hb3c
      _ ≤ 2 * cfg.K k + χ := by linarith
  have hid : CB.frame.zZ (cfg.b k p.1) p.2 - CB.refZ P (CB.cls p) (CB.cell P p) =
      ((cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)) + p.2 * (cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)) +
        (p.2 - T) * (((n : ℝ) + 1 / 2) * χ - CB.frame.c 1)) / CB.frame.q := by
    simp only [Frame.zZ, refZ, x1ref, T, n, m]
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hq, div_le_iff₀ hq]
  have ht1 : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  calc _ ≤ |cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)| +
        |p.2| * |cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)| +
        |p.2 - T| * |((n : ℝ) + 1 / 2) * χ - CB.frame.c 1| := by
        refine (abs_add_three _ _ _).trans ?_; simp only [abs_mul, le_refl]
    _ ≤ χ / 2 + 1 * (χ / 2) + CB.frame.q * P.δt / 2 * (2 * cfg.K k + χ) := by
        gcongr
    _ = (χ / CB.frame.q + P.δt * (2 * cfg.K k + χ) / 2) * CB.frame.q := by
        field_simp; ring

/-- The two incidences of a disagreeing pair cross: the target chart passes near the source
cell. -/
theorem good_cross (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hL : HorizontalForm (cfg.F k s CB.i) CB.L) (hχ : 0 < χ) (hδt : 0 < P.δt)
    (hδz : 0 < P.δz) (hδU : 0 < P.δU) (hδX : 0 < P.δX)
    {p p' : α × ℝ} (hp : CB.Good p) (hp' : CB.Good p') (hσ : CB.sig P p = CB.sig P p') :
    |(((CB.chartOf (CB.cls p')).2 : ℝ) + 1 / 2) * χ -
      (CB.x1ref P (CB.cls p) (CB.cell P p) - CB.refT P (CB.cell P p) *
        (((CB.chartOf (CB.cls p')).1 : ℝ) + 1 / 2) * χ)| ≤
      2 * χ + (CB.frame.q * P.δt + CB.frame.q * P.δz) * (3 * cfg.K k + χ) +
        (cfg.K k + 1) * (CB.frame.q * P.δz) := by
  have hq : 0 < CB.frame.q := by simp only [frame, blockFrame]; positivity
  obtain ⟨hzt, -, -, -, hb3⟩ := CB.good_bounds hB hN hK hL hp
  obtain ⟨hzt', -, -, -, hb3'⟩ := CB.good_bounds hB hN hK hL hp'
  obtain ⟨hx, -⟩ := CB.good_refZ P hB hN hK hL hχ hδt hp
  obtain ⟨c0, c1, -, -⟩ := CB.sig_close P hδz hδU hδX hσ
  have hch := hp.chart
  have hch' := hp'.chart
  simp only [chart] at hch hch'
  set n := (CB.chartOf (CB.cls p)).1
  set m := (CB.chartOf (CB.cls p)).2
  set n' := (CB.chartOf (CB.cls p')).1
  set m' := (CB.chartOf (CB.cls p')).2
  have hn : ⌊cfg.b k p.1 3 / χ⌋ = n := by simp only [n, cls]; rw [← hch]
  have hm : ⌊cfg.b k p.1 0 / χ⌋ = m := by simp only [m, cls]; rw [← hch]
  have hn' : ⌊cfg.b k p'.1 3 / χ⌋ = n' := by simp only [n', cls]; rw [← hch']
  have hm' : ⌊cfg.b k p'.1 0 / χ⌋ = m' := by simp only [m', cls]; rw [← hch']
  have e1 := abs_sub_center_of_floor hχ hn
  have e2 := abs_sub_center_of_floor hχ hm
  have e3 := abs_sub_center_of_floor hχ hn'
  have e4 := abs_sub_center_of_floor hχ hm'
  have ht := I_subset_unit hp.I
  have ht' := I_subset_unit hp'.I
  set t := p.2
  set t' := p'.2
  set T := CB.refT P (CB.cell P p)
  have hc1 : |CB.frame.c 1| ≤ cfg.K k := hB.c_bd CB.i 1
  -- times
  have hTt : |t - T| ≤ CB.frame.q * P.δt / 2 := by
    have e : t - T = CB.frame.q * (CB.frame.zt t - refX P (CB.cell P p)) := by
      simp only [T, refT, frame, Frame.zt, blockFrame]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hq]
    calc CB.frame.q * |CB.frame.zt t - refX P (CB.cell P p)| ≤ CB.frame.q * (P.δt / 2) := by
          gcongr
      _ = _ := by ring
  have htt' : |t - t'| ≤ CB.frame.q * P.δz := by
    have e : t - t' = CB.frame.q * (CB.frame.zt t - CB.frame.zt t') := by
      simp only [frame, Frame.zt, blockFrame]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hq]; gcongr
  -- positions
  have hxx' : |(cfg.b k p'.1 0 + t' * cfg.b k p'.1 3) - (cfg.b k p.1 0 + t * cfg.b k p.1 3)| ≤
      (cfg.K k + 1) * (CB.frame.q * P.δz) := by
    have e : (cfg.b k p'.1 0 + t' * cfg.b k p'.1 3) - (cfg.b k p.1 0 + t * cfg.b k p.1 3) =
        CB.frame.q * (CB.frame.zZ (cfg.b k p'.1) t' - CB.frame.zZ (cfg.b k p.1) t) +
          (t' - t) * CB.frame.c 1 := by
      simp only [frame, Frame.zZ, blockFrame]; field_simp; ring
    rw [e]
    calc _ ≤ CB.frame.q * |CB.frame.zZ (cfg.b k p'.1) t' - CB.frame.zZ (cfg.b k p.1) t| +
          |t' - t| * |CB.frame.c 1| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul, abs_of_pos hq]
      _ ≤ CB.frame.q * P.δz + CB.frame.q * P.δz * cfg.K k := by
          gcongr
          · rw [abs_sub_comm]; exact c1.le
          · rw [abs_sub_comm]; exact htt'
      _ = _ := by ring
  have hb3abs : |cfg.b k p.1 3| ≤ 3 * cfg.K k := by
    calc |cfg.b k p.1 3| = |(cfg.b k p.1 3 - CB.frame.c 1) + CB.frame.c 1| := by ring_nf
      _ ≤ |cfg.b k p.1 3 - CB.frame.c 1| + |CB.frame.c 1| := abs_add_le _ _
      _ ≤ 2 * cfg.K k + cfg.K k := add_le_add hb3 hc1
      _ = 3 * cfg.K k := by ring
  have hb3abs' : |cfg.b k p'.1 3| ≤ 3 * cfg.K k := by
    calc |cfg.b k p'.1 3| = |(cfg.b k p'.1 3 - CB.frame.c 1) + CB.frame.c 1| := by ring_nf
      _ ≤ |cfg.b k p'.1 3 - CB.frame.c 1| + |CB.frame.c 1| := abs_add_le _ _
      _ ≤ 2 * cfg.K k + cfg.K k := add_le_add hb3' hc1
      _ = 3 * cfg.K k := by ring
  have hnc : |((n : ℝ) + 1 / 2) * χ| ≤ 3 * cfg.K k + χ := by
    calc |((n : ℝ) + 1 / 2) * χ| = |cfg.b k p.1 3 - (cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2))| := by
          ring_nf
      _ ≤ |cfg.b k p.1 3| + |cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)| := abs_sub _ _
      _ ≤ 3 * cfg.K k + χ / 2 := add_le_add hb3abs e1
      _ ≤ 3 * cfg.K k + χ := by linarith
  have hnc' : |((n' : ℝ) + 1 / 2) * χ| ≤ 3 * cfg.K k + χ := by
    calc |((n' : ℝ) + 1 / 2) * χ| = |cfg.b k p'.1 3 - (cfg.b k p'.1 3 - χ * ((n' : ℝ) + 1 / 2))| := by
          ring_nf
      _ ≤ |cfg.b k p'.1 3| + |cfg.b k p'.1 3 - χ * ((n' : ℝ) + 1 / 2)| := abs_sub _ _
      _ ≤ 3 * cfg.K k + χ / 2 := add_le_add hb3abs' e3
      _ ≤ 3 * cfg.K k + χ := by linarith
  have habs1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have habs1' : |t'| ≤ 1 := abs_le.mpr ⟨by linarith [ht'.1], ht'.2⟩
  have hid : (((m' : ℝ) + 1 / 2) * χ - (CB.x1ref P (CB.cls p) (CB.cell P p) - T * ((n' : ℝ) + 1 / 2) * χ)) =
      ((χ * ((m' : ℝ) + 1 / 2) - cfg.b k p'.1 0) + t' * (χ * ((n' : ℝ) + 1 / 2) - cfg.b k p'.1 3)) +
      (T - t') * (((n' : ℝ) + 1 / 2) * χ) +
      ((cfg.b k p'.1 0 + t' * cfg.b k p'.1 3) - (cfg.b k p.1 0 + t * cfg.b k p.1 3)) +
      ((cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)) + t * (cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)) +
        (t - T) * (((n : ℝ) + 1 / 2) * χ)) := by
    simp only [x1ref, n, m, n', m']; ring
  rw [hid]
  have hA : |(χ * ((m' : ℝ) + 1 / 2) - cfg.b k p'.1 0) + t' * (χ * ((n' : ℝ) + 1 / 2) - cfg.b k p'.1 3)| ≤ χ := by
    calc _ ≤ |χ * ((m' : ℝ) + 1 / 2) - cfg.b k p'.1 0| + |t'| * |χ * ((n' : ℝ) + 1 / 2) - cfg.b k p'.1 3| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul]
      _ ≤ χ / 2 + 1 * (χ / 2) := by
          gcongr
          · rw [abs_sub_comm]; exact e4
          · rw [abs_sub_comm]; exact e3
      _ = χ := by ring
  have hB' : |(T - t') * (((n' : ℝ) + 1 / 2) * χ)| ≤ (CB.frame.q * P.δt / 2 + CB.frame.q * P.δz) *
      (3 * cfg.K k + χ) := by
    rw [abs_mul]
    gcongr
    calc |T - t'| = |(T - t) + (t - t')| := by ring_nf
      _ ≤ |T - t| + |t - t'| := abs_add_le _ _
      _ ≤ CB.frame.q * P.δt / 2 + CB.frame.q * P.δz := by
          gcongr; rw [abs_sub_comm]; exact hTt
  have hC : |(cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)) + t * (cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)) +
        (t - T) * (((n : ℝ) + 1 / 2) * χ)| ≤ χ + CB.frame.q * P.δt / 2 * (3 * cfg.K k + χ) := by
    calc _ ≤ |cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)| + |t| * |cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)| +
          |t - T| * |((n : ℝ) + 1 / 2) * χ| := by
          refine (abs_add_three _ _ _).trans ?_; simp only [abs_mul, le_refl]
      _ ≤ χ / 2 + 1 * (χ / 2) + CB.frame.q * P.δt / 2 * (3 * cfg.K k + χ) := by gcongr
      _ = _ := by ring
  have hKχ : 0 ≤ 3 * cfg.K k + χ := by linarith
  calc _ ≤ χ + (CB.frame.q * P.δt / 2 + CB.frame.q * P.δz) * (3 * cfg.K k + χ) +
        (cfg.K k + 1) * (CB.frame.q * P.δz) + (χ + CB.frame.q * P.δt / 2 * (3 * cfg.K k + χ)) := by
        have h4 : ∀ a b c d : ℝ, |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
          intro a b c d
          have := abs_add_le (a + b + c) d
          have := abs_add_le (a + b) c
          have := abs_add_le a b
          linarith
        refine (h4 _ _ _ _).trans ?_
        gcongr
    _ = _ := by ring

/-- **The matching step.**  For almost every incidence `p` of `lam1 ≤ CB.lam` and every
coefficient class occurring at the fine state of `p` and disagreeing with the class of `p`, the
target chart crosses the source cell and the transverse coordinate of `p` lies in the matching
set. -/
theorem match_step (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hL : HorizontalForm (cfg.F k s CB.i) CB.L) (hχ : 0 < χ) (hH : 1 ≤ H)
    (hδt : 0 < P.δt) (hδt2 : P.δt ≤ 2) (hδz : 0 < P.δz) (hδU : 0 < P.δU) (hδX : 0 < P.δX)
    (lam1 : Measure (α × ℝ)) (hlam1 : lam1 ≤ CB.lam) {ρ2 ρN w : ℝ}
    (hρ2 : χ / CB.frame.q + P.δt * (2 * cfg.K k + χ) / 2 ≤ ρ2)
    (hρN : 2 * χ + (CB.frame.q * P.δt + CB.frame.q * P.δz) * (3 * cfg.K k + χ) +
        (cfg.K k + 1) * (CB.frame.q * P.δz) ≤ ρN)
    (hgap : P.e + 2 * H * (P.δz + P.δt / 2 + ρ2) ≤ P.eR)
    (hw : (2 * H + 2) * cfg.N k ^ (-u) + P.δX + H * ((1 + 2 * 2 + (cfg.K k + ρ2) + cfg.K k) *
        (2 * (P.δt / 2) + P.δz) + (1 + 2 + 2 * (cfg.K k + ρ2) + cfg.K k) * (2 * ρ2 + P.δz) +
        (1 + 2 + (cfg.K k + ρ2) + 2 * cfg.K k) * P.δU) ≤ w) :
    ∀ᵐ p ∂lam1, ∀ γ' : CB.Γ, lam1 {x | CB.sig P x = CB.sig P p ∧ CB.cls x = γ'} ≠ 0 →
      ¬ CB.Rg P (CB.sig P p) γ' (CB.cls p) →
      CB.Near P ρN (CB.src p) (CB.cell P p) γ' ∧
        CB.frame.tr (cfg.b k p.1) p.2 ∈ CB.Mset P w (cfg.K k) (CB.src p) (CB.cell P p) γ' := by
  have hac : lam1 ≪ CB.lam := Measure.absolutelyContinuous_of_le hlam1
  have hgood : ∀ᵐ p ∂lam1, CB.Good p := hac.ae_le CB.ae_good
  have hgoodc : lam1 {p | ¬ CB.Good p} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]; filter_upwards [hgood] with p hp; simpa using hp
  filter_upwards [hgood] with p hp γ' hocc hR
  -- a good witness of the target at the same fine state
  obtain ⟨p', ⟨hσ', hcls'⟩, hp'⟩ : ∃ p', (CB.sig P p' = CB.sig P p ∧ CB.cls p' = γ') ∧ CB.Good p' := by
    by_contra hcon
    push Not at hcon
    apply hocc
    apply measure_mono_null _ hgoodc
    intro x hx
    exact hcon x hx
  have hq : 0 < CB.frame.q := by simp only [frame, blockFrame]; positivity
  obtain ⟨hzt, hzZ, htr, hres, -⟩ := CB.good_bounds hB hN hK hL hp
  obtain ⟨hzt', hzZ', htr', hres', -⟩ := CB.good_bounds hB hN hK hL hp'
  obtain ⟨hx, hy⟩ := CB.good_refZ P hB hN hK hL hχ hδt hp
  obtain ⟨c0, c1, c2, c3⟩ := CB.sig_close P hδz hδU hδX hσ'.symm
  have hcross := CB.good_cross P hB hN hK hL hχ hδt hδz hδU hδX hp hp' hσ'.symm
  rw [hcls'] at hcross
  -- the chart of the target and its lists
  have hcls'' : CB.crs (CB.lab p'.1) = γ' := hcls'
  have hch' := hp'.chart
  rw [hcls''] at hch'
  have hγ'G : γ' ∈ CB.G (CB.chartOf γ') := by
    have := hp'.coarse; rw [hch', hcls''] at this; exact this
  have hd' : ⌊CB.D1 (CB.lab p'.1) / cfg.N k ^ (-u)⌋ ∈ CB.F1 (CB.chartOf γ') γ' := by
    have := hp'.off1; rw [hch', hcls''] at this; exact this
  refine ⟨⟨hcross.trans hρN, hγ'G⟩, ?_⟩
  -- the gap at the reference point
  set c := CB.cell P p
  set xr := refX P c
  set yr := CB.refZ P (CB.cls p) c
  have hRg : P.eR ≤ CB.gapAt (CB.cls p) γ' (zcx P (CB.sig P p)) (zcy P (CB.sig P p)) := by
    have := not_lt.mp hR
    rwa [gapAt_comm] at this
  have hxc : |zcx P (CB.sig P p) - CB.frame.zt p.2| ≤ P.δz / 2 := by
    have := abs_sub_center_of_floor hδz (rfl : ⌊CB.frame.zt p.2 / P.δz⌋ = CB.sig P p 0)
    rw [abs_sub_comm]
    simpa [zcx, mul_comm, sig, sigmaState, coords] using this
  have hyc : |zcy P (CB.sig P p) - CB.frame.zZ (cfg.b k p.1) p.2| ≤ P.δz / 2 := by
    have := abs_sub_center_of_floor hδz
      (rfl : ⌊CB.frame.zZ (cfg.b k p.1) p.2 / P.δz⌋ = CB.sig P p 1)
    rw [abs_sub_comm]
    simpa [zcy, mul_comm, sig, sigmaState, coords] using this
  have htc : ∀ γ e, |CB.tc γ e| ≤ H := CB.tc_bd
  have hmove := gap_move (htc (CB.cls p)) (htc γ') (zcx P (CB.sig P p)) (zcy P (CB.sig P p)) xr yr
  have hdist : |zcx P (CB.sig P p) - xr| + |zcy P (CB.sig P p) - yr| ≤ P.δz + P.δt / 2 + ρ2 := by
    have h1 : |zcx P (CB.sig P p) - xr| ≤ P.δz / 2 + P.δt / 2 := by
      calc _ = |(zcx P (CB.sig P p) - CB.frame.zt p.2) + (CB.frame.zt p.2 - xr)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add hxc hx
    have h2 : |zcy P (CB.sig P p) - yr| ≤ P.δz / 2 + ρ2 := by
      calc _ = |(zcy P (CB.sig P p) - CB.frame.zZ (cfg.b k p.1) p.2) +
            (CB.frame.zZ (cfg.b k p.1) p.2 - yr)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add hyc (hy.trans hρ2)
    linarith
  have hgapref : P.e ≤ |CB.cδ₁ P (CB.src p) c γ'| + |CB.cδ₂ (CB.src p) γ'| := by
    have hH0 : 0 ≤ H := by linarith
    have : CB.gapAt (CB.cls p) γ' (zcx P (CB.sig P p)) (zcy P (CB.sig P p)) ≤
        |CB.cδ₁ P (CB.src p) c γ'| + |CB.cδ₂ (CB.src p) γ'| +
          2 * H * (P.δz + P.δt / 2 + ρ2) := by
      refine hmove.trans ?_
      simp only [cδ₁, cδ₂, src]
      gcongr
    linarith
  simp only [Mset, hgapref, ite_true]
  -- membership in the matching set
  refine ⟨abs_le.mp htr, (⌊CB.D1 (CB.lab p'.1) / cfg.N k ^ (-u)⌋ : ℝ) * cfg.N k ^ (-u),
    Finset.mem_image_of_mem _ hd', ?_⟩
  have hη : 0 < cfg.N k ^ (-u) := Real.rpow_pos_of_pos hN _
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hρ20 : 0 ≤ ρ2 := le_trans (by positivity) hρ2
  have hm := point_match (CB.pc_bd (CB.cls p)) (htc (CB.cls p)) (CB.pc_bd γ') (htc γ') hη
    hp.fit1 (by rw [← hcls'']; exact hp'.fit1) c0.le c1.le c2.le c3.le hx (hy.trans hρ2)
    (X := 2) (Y := cfg.K k + ρ2) (Ub := cfg.K k)
    (by rw [abs_le]; constructor <;> linarith [hzt.1, hzt.2])
    (by rw [abs_le]; constructor <;> linarith [hzt'.1, hzt'.2])
    (by
      have h1 : |xr| ≤ |CB.frame.zt p.2| + P.δt / 2 := by
        calc |xr| = |CB.frame.zt p.2 - (CB.frame.zt p.2 - xr)| := by ring_nf
          _ ≤ |CB.frame.zt p.2| + |CB.frame.zt p.2 - xr| := abs_sub _ _
          _ ≤ _ := by gcongr
      have h2 : |CB.frame.zt p.2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hzt.1, hzt.2]
      linarith)
    (by linarith)
    (by linarith)
    (by
      have h1 : |yr| ≤ |CB.frame.zZ (cfg.b k p.1) p.2| + ρ2 := by
        calc |yr| = |CB.frame.zZ (cfg.b k p.1) p.2 - (CB.frame.zZ (cfg.b k p.1) p.2 - yr)| := by
              ring_nf
          _ ≤ |CB.frame.zZ (cfg.b k p.1) p.2| + |CB.frame.zZ (cfg.b k p.1) p.2 - yr| := abs_sub _ _
          _ ≤ _ := by gcongr; exact hy.trans hρ2
      linarith)
    htr htr'
  refine le_trans (le_of_eq ?_) (hm.trans hw)
  simp only [cδ₀, cδ₁, cδ₂, src, cls]
  rfl

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
