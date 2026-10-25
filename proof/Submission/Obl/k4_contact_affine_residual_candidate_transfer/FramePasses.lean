import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameCellCaps
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameAtlas

/-!
# Calibration passes on residual labels

Given the residual caps of a frame, the incidence law of a residual label has
capped base cubes as soon as its hidden values are confined in every cube.
Two confinements are used:

* crude: the parent fit puts every hidden value in `[-H, H]`; the label's own
  affine part is then at most `2 H` on its incidences;
* fine: the parent label's affine part, whose coefficients the crude pass
  bounds, confines the hidden values of a child label to width about the
  parent width; the difference of the child's and the parent's affine parts is
  then at most twice the parent fit width.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4MovingMeshBoxes
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- The residual pure caps of a frame, on base cubes of side `N ^ (-r)` and
hidden bins of width `N ^ (-s)`. -/
def Frame.CapsAt (f : Frame D k s₀ U') (Cr R : ℝ) : Prop :=
  ∀ r s : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → ∀ (c : Fin 3 → ℤ) (j : ℤ),
    f.resμ {p | baseMesh (D.N k ^ (-r)) (f.resBase p) = c ∧
      ⌊f.resW p / D.N k ^ (-s)⌋ = j} ≤ ENNReal.ofReal (Cr * D.N k ^ (-3 * r - D.d * s))

/-- Cube caps of a label's incidence law from confined hidden values. -/
theorem FrameGood.nodeLaw_cap (hg : FrameGood f Rk θ K₂ e₀') {Cr R : ℝ}
    (hcaps : f.CapsAt Cr R) {h : ℕ} (hh : h ≤ f.m) (i : Fin (f.retained h).card)
    {r s ρ : ℝ} (hρ : 0 ≤ ρ) (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hs1 : 0 ≤ s) (hs2 : s ≤ R)
    (y : (Fin 3 → ℤ) → ℝ)
    (hconf : ∀ p ∈ f.labelSet h i,
      |f.resW p - y (baseMesh (D.N k ^ (-r)) (f.resBase p))| ≤ ρ)
    (c : Fin 3 → ℤ) :
    f.nodeLaw h i {p | baseMesh (D.N k ^ (-r)) (f.resBase p) = c} ≤
      ENNReal.ofReal (Cr * (4 * ρ / D.N k ^ (-s) + 2) * (D.N k ^ (-s)) ^ D.d *
        (D.N k ^ (-r)) ^ 3) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hb := cell_cap_of_confined f.resμ (f.labelSet h i) (hg.measurableSet_labelSet hh i)
    f.resBase f.resW (Real.rpow_pos_of_pos hN (-s)) hρ c (y c)
    (fun p hp hc => by rw [← hc]; exact hconf p hp) (hcaps r s hr1 hr2 hs1 hs2 c)
  refine hb.trans (le_of_eq ?_)
  congr 1
  have e1 : D.N k ^ (-3 * r - D.d * s) = (D.N k ^ (-r)) ^ 3 * (D.N k ^ (-s)) ^ D.d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le,
      ← Real.rpow_add hN]
    congr 1
    push_cast
    ring
  rw [e1]
  ring

/-- The residual block length is at most `K ^ 2` times the transverse width. -/
theorem FrameGood.resq_le_g (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    f.resq h ≤ D.K k ^ 2 * D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hK : 0 < D.K k := by linarith [hg.K_ge]
  have hc := (hg.res_count hh).1
  have hp : 0 < D.N k ^ (D.κ * ((h : ℝ) * (U' / f.m))) / D.K k ^ 2 := by positivity
  have hinv := inv_anti₀ hp hc
  rw [inv_div] at hinv
  rw [Frame.resq, zpow_neg, zpow_natCast]
  refine hinv.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, neg_mul, Real.rpow_neg hN.le]

/-- One calibration pass on a residual label: confined hidden values and a
bounded affine function give box-adapted slope bounds. -/
theorem FrameGood.node_pass (hg : FrameGood f Rk θ K₂ e₀') {A₀ : ℝ}
    (hA : BoxCalibration A₀) {Cr R : ℝ} (hCr : 0 < Cr) (hcaps : f.CapsAt Cr R)
    {h : ℕ} (hh : h ≤ f.m) (i : Fin (f.retained h).card) (L : Fin 4 → ℝ)
    {E r s ρ Φ A : ℝ} (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R)
    (hs1 : 0 ≤ s) (hs2 : s ≤ R) (y : (Fin 3 → ℤ) → ℝ)
    (hconf : ∀ p ∈ f.labelSet h i,
      |f.resW p - y (baseMesh (D.N k ^ (-r)) (f.resBase p))| ≤ ρ)
    (hval : ∀ p ∈ f.labelSet h i, |affineAt L (f.resBase p)| ≤ E)
    (hΦ : 4 * ρ / D.N k ^ (-s) + 2 ≤ Φ)
    (hAge : A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
      (1 + 16 * (8 * boxK (D.K k) K₂ + 4) * Cr * Φ * D.K k ^ 5 / θ ^ 2 *
        D.N k ^ (D.d * ((h : ℝ) * (U' / f.m) - s))) ^ (6 : ℕ) ≤ A)
    (habs : A * (D.N k ^ (-r) / f.resq h ^ 2) ≤ 1 / 2) :
    f.resq h * |L 1 - f.boxZ h i * L 3| ≤ A * E ∧
      f.resq h * |L 2 + f.resMid h i * L 3| ≤ A * E ∧
      f.resq h ^ 2 * |L 3| ≤ A * E := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hK : 0 < D.K k := by linarith [hg.K_ge]
  have hθ := hg.θ_pos
  have hq := f.resq_pos h
  have hqg := hg.resq_le_g hh
  set q := f.resq h with hq_def
  set x := (h : ℝ) * (U' / f.m) with hx_def
  set a := D.N k ^ (-s) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have hΦ0 : 0 < Φ := by
    have : 0 ≤ 4 * ρ / a := by positivity
    linarith
  set C := Cr * Φ * a ^ D.d with hC_def
  have hC : 0 < C := by positivity
  set m := θ ^ 2 / D.K k ^ 5 * q ^ 4 * (D.N k ^ (-x)) ^ D.d with hm_def
  have hm : 0 < m := by positivity
  set δh := D.N k ^ (-r) / q ^ 2 with hδh_def
  have hδh : 0 < δh := by positivity
  have hside : q ^ 2 * δh = D.N k ^ (-r) := by rw [hδh_def]; field_simp
  have hβ : boxBeta (boxK (D.K k) K₂) C q / m = 16 * (8 * boxK (D.K k) K₂ + 4) * Cr *
      Φ * D.K k ^ 5 / θ ^ 2 * D.N k ^ (D.d * (x - s)) := by
    have e : D.N k ^ (D.d * (x - s)) = a ^ D.d / (D.N k ^ (-x)) ^ D.d := by
      rw [ha_def, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_sub hN]
      congr 1
      ring
    have hax : 0 < (D.N k ^ (-x)) ^ D.d := by positivity
    rw [e, boxBeta, hC_def, hm_def]
    field_simp
  have hAexact : A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
      (1 + boxBeta (boxK (D.K k) K₂) C q / m) ^ (6 : ℕ) ≤ A := by rw [hβ]; exact hAge
  have habs' : A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
      (1 + boxBeta (boxK (D.K k) K₂) C q / m) ^ (6 : ℕ) * δh ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hAexact hδh.le).trans habs
  have hmass : ENNReal.ofReal m ≤ f.nodeLaw h i univ := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hg.nodeLaw_mass hh i)
    have hq' : q / D.K k ^ 2 ≤ D.N k ^ (-D.κ * x) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc m = θ ^ 2 / D.K k ^ 3 * q * ((D.N k ^ (-x)) ^ D.d * q ^ 2 * (q / D.K k ^ 2)) := by
          rw [hm_def]
          field_simp
      _ ≤ θ ^ 2 / D.K k ^ 3 * q * ((D.N k ^ (-x)) ^ D.d * q ^ 2 *
            D.N k ^ (-D.κ * x)) := by gcongr
  have hcap : ∀ c : Fin 3 → ℤ, f.nodeLaw h i {p | baseMesh (q ^ 2 * δh) (f.resBase p) = c} ≤
      ENNReal.ofReal (C * (q ^ 2 * δh) ^ 3) := by
    intro c
    rw [hside]
    refine (hg.nodeLaw_cap hcaps hh i hρ hr1 hr2 hs1 hs2 y hconf c).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hC_def]
    gcongr
  have hval' : ∀ l ∈ (f.level h).B i, ∀ τ ∈ Data.I (f.level h).T ((f.level h).j i),
      |L 0 + L 1 * τ + L 2 * point (f.coeff l) τ 1 + L 3 * point (f.coeff l) τ 2| ≤ E :=
    fun l hl τ hτ => hval (l, τ) ⟨hl, hτ⟩
  obtain ⟨h1, h2, h3⟩ := hg.node_slopes hA hh i L hE hC hm hδh habs' hmass hcap hval'
  have hAE := mul_le_mul_of_nonneg_right hAexact hE
  exact ⟨h1.trans hAE, h2.trans hAE, h3.trans hAE⟩

/-- The fit of a label's own palette entry, in residual coordinates. -/
theorem FrameGood.resW_fit (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) {p : α × ℝ} (hp : p ∈ f.labelSet h i) :
    |f.resW p - affineAt (f.labelL h i) (f.resBase p)| ≤
      f.H * D.N k ^ (-((h : ℝ) * (U' / f.m))) := by
  have hfit := (hg.res_fit hh i p.1 hp.1 p.2 hp.2).1
  refine le_of_eq_of_le ?_ hfit
  congr 1
  simp only [Frame.level, Frame.labelL, affineAt, Frame.resW, Frame.resBase, affineBase,
    eval_sub, eval_X, eval_add, eval_mul, eval_C, point]
  simp

/-- The crude pass: a label's own affine part is at most `2 H` on its
incidences, whose hidden values lie in `[-H, H]`. -/
theorem FrameGood.crude_pass (hg : FrameGood f Rk θ K₂ e₀') {A₀ : ℝ}
    (hA : BoxCalibration A₀) {Cr R : ℝ} (hCr : 0 < Cr) (hcaps : f.CapsAt Cr R)
    {h : ℕ} (hh : h ≤ f.m) (i : Fin (f.retained h).card) {r A : ℝ}
    (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hR : 0 ≤ R)
    (hAge : A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
      (1 + 16 * (8 * boxK (D.K k) K₂ + 4) * Cr * (4 * f.H + 2) * D.K k ^ 5 / θ ^ 2 *
        D.N k ^ (D.d * ((h : ℝ) * (U' / f.m)))) ^ (6 : ℕ) ≤ A)
    (habs : A * (D.N k ^ (-r) / f.resq h ^ 2) ≤ 1 / 2) :
    f.resq h * |f.labelL h i 1 - f.boxZ h i * f.labelL h i 3| ≤ A * (2 * f.H) ∧
      f.resq h * |f.labelL h i 2 + f.resMid h i * f.labelL h i 3| ≤ A * (2 * f.H) ∧
      f.resq h ^ 2 * |f.labelL h i 3| ≤ A * (2 * f.H) := by
  have hN1 : 1 ≤ D.N k := by linarith [hg.N_ge]
  have hH := hg.H_ge
  have hx : 0 ≤ (h : ℝ) * (U' / f.m) := by
    have := hg.U'_pos
    have : (0 : ℝ) < f.m := by exact_mod_cast hg.m_pos
    positivity
  have hah : D.N k ^ (-((h : ℝ) * (U' / f.m))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have e1 : D.N k ^ (-(0 : ℝ)) = 1 := by simp
  refine hg.node_pass hA hCr hcaps hh i (f.labelL h i) (E := 2 * f.H) (s := 0)
    (by linarith) (by linarith : (0 : ℝ) ≤ f.H) hr1 hr2 le_rfl hR (fun _ => 0) ?_ ?_
    (le_of_eq (by rw [e1, div_one])) (by rw [sub_zero]; exact hAge) habs
  · intro p hp
    simpa using hg.resW_le hh i hp
  · intro p hp
    have h1 := hg.resW_le hh i hp
    have h2 := hg.resW_fit hh i hp
    have h3 := abs_sub_abs_le_abs_sub (affineAt (f.labelL h i) (f.resBase p)) (f.resW p)
    have h4 := abs_sub_comm (affineAt (f.labelL h i) (f.resBase p)) (f.resW p)
    have h5 : f.H * D.N k ^ (-((h : ℝ) * (U' / f.m))) ≤ f.H := by
      calc _ ≤ f.H * 1 := by gcongr
        _ = f.H := mul_one _
    linarith

/-- A real number is within one mesh step of its mesh corner. -/
theorem abs_sub_floor_mul_le {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    |u - (⌊u / σ⌋ : ℝ) * σ| ≤ σ := by
  have h1 : (⌊u / σ⌋ : ℝ) * σ ≤ u := (le_div_iff₀ hσ).mp (Int.floor_le (u / σ))
  have h2 : u < ((⌊u / σ⌋ : ℝ) + 1) * σ := (div_lt_iff₀ hσ).mp (Int.lt_floor_add_one (u / σ))
  rw [abs_le]
  constructor <;> nlinarith

/-- The corner of a base cube. -/
def cubeCorner (σ : ℝ) (c : Fin 3 → ℤ) : Fin 3 → ℝ := fun e => (c e : ℝ) * σ

/-- An affine function varies by at most its slopes times the side on a base cube. -/
theorem affineAt_sub_corner (L : Fin 4 → ℝ) {σ : ℝ} (hσ : 0 < σ) (z : Fin 3 → ℝ) :
    |affineAt L z - affineAt L (cubeCorner σ (baseMesh σ z))| ≤
      (|L 1| + |L 2| + |L 3|) * σ := by
  have e0 := abs_sub_floor_mul_le hσ (z 0)
  have e1 := abs_sub_floor_mul_le hσ (z 1)
  have e2 := abs_sub_floor_mul_le hσ (z 2)
  have hsub : affineAt L z - affineAt L (cubeCorner σ (baseMesh σ z)) =
      L 1 * (z 0 - (⌊z 0 / σ⌋ : ℝ) * σ) + L 2 * (z 1 - (⌊z 1 / σ⌋ : ℝ) * σ) +
        L 3 * (z 2 - (⌊z 2 / σ⌋ : ℝ) * σ) := by
    simp only [affineAt, cubeCorner, baseMesh]
    ring
  rw [hsub]
  calc _ ≤ |L 1 * (z 0 - (⌊z 0 / σ⌋ : ℝ) * σ)| + |L 2 * (z 1 - (⌊z 1 / σ⌋ : ℝ) * σ)| +
        |L 3 * (z 2 - (⌊z 2 / σ⌋ : ℝ) * σ)| := abs_add_three _ _ _
    _ ≤ |L 1| * σ + |L 2| * σ + |L 3| * σ := by
      rw [abs_mul, abs_mul, abs_mul]
      gcongr
    _ = _ := by ring

theorem affineAt_sub (L L' : Fin 4 → ℝ) (z : Fin 3 → ℝ) :
    affineAt (L - L') z = affineAt L z - affineAt L' z := by
  simp only [affineAt, Pi.sub_apply]
  ring

/-- The fine pass: the parent label's affine part confines the hidden values of
a child label to about the parent width, and the difference of the child's and
the parent's affine parts is at most twice the parent fit width. -/
theorem FrameGood.fine_pass (hg : FrameGood f Rk θ K₂ e₀') {A₀ : ℝ}
    (hA : BoxCalibration A₀) {Cr R : ℝ} (hCr : 0 < Cr) (hcaps : f.CapsAt Cr R)
    {h : ℕ} (hh : h < f.m) (i : Fin (f.retained (h + 1)).card) {r Λ A : ℝ}
    (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hsR : (h : ℝ) * (U' / f.m) ≤ R)
    (hΛ : |f.labelL h (f.upLabel hg hh i) 1| + |f.labelL h (f.upLabel hg hh i) 2| +
      |f.labelL h (f.upLabel hg hh i) 3| ≤ Λ)
    (hΛr : Λ * D.N k ^ (-r) ≤ D.N k ^ (-((h : ℝ) * (U' / f.m))))
    (hAge : A₀ * (1 + boxK (D.K k) K₂) ^ A₀ *
      (1 + 16 * (8 * boxK (D.K k) K₂ + 4) * Cr * (4 * f.H + 6) * D.K k ^ 5 / θ ^ 2 *
        D.N k ^ (D.d * (U' / f.m))) ^ (6 : ℕ) ≤ A)
    (habs : A * (D.N k ^ (-r) / f.resq (h + 1) ^ 2) ≤ 1 / 2) :
    f.resq (h + 1) * |(f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 1 -
        f.boxZ (h + 1) i * (f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 3| ≤
        A * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m)))) ∧
      f.resq (h + 1) * |(f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 2 +
        f.resMid (h + 1) i * (f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 3| ≤
        A * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m)))) ∧
      f.resq (h + 1) ^ 2 * |(f.labelL (h + 1) i - f.labelL h (f.upLabel hg hh i)) 3| ≤
        A * (2 * f.H * D.N k ^ (-((h : ℝ) * (U' / f.m)))) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hN1 : 1 ≤ D.N k := by linarith [hg.N_ge]
  have hH := hg.H_ge
  have hm0 : (0 : ℝ) < f.m := by exact_mod_cast hg.m_pos
  have hη : 0 ≤ U' / f.m := by have := hg.U'_pos; positivity
  have hx : 0 ≤ (h : ℝ) * (U' / f.m) := by positivity
  set Lu := f.labelL h (f.upLabel hg hh i) with hLu
  set ah := D.N k ^ (-((h : ℝ) * (U' / f.m))) with hah_def
  have hah : 0 < ah := Real.rpow_pos_of_pos hN _
  set σ := D.N k ^ (-r) with hσ_def
  have hσ : 0 < σ := Real.rpow_pos_of_pos hN _
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hΛ
  have hah1 : D.N k ^ (-(((h + 1 : ℕ) : ℝ) * (U' / f.m))) ≤ ah := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    push_cast
    nlinarith
  have e2 : ((h + 1 : ℕ) : ℝ) * (U' / f.m) - (h : ℝ) * (U' / f.m) = U' / f.m := by
    push_cast
    ring
  refine hg.node_pass (h := h + 1) hA hCr hcaps hh i (f.labelL (h + 1) i - Lu)
    (E := 2 * f.H * ah) (s := (h : ℝ) * (U' / f.m)) (ρ := f.H * ah + Λ * σ)
    (Φ := 4 * f.H + 6) (by positivity) (by positivity) hr1 hr2 hx hsR
    (fun c => affineAt Lu (cubeCorner σ c)) ?_ ?_ ?_ (by rw [e2]; exact hAge) habs
  · intro p hp
    have h1 := hg.resW_sub_up hh i hp
    have h2 := affineAt_sub_corner Lu hσ (f.resBase p)
    have h3 := abs_sub_le (f.resW p) (affineAt Lu (f.resBase p))
      (affineAt Lu (cubeCorner σ (baseMesh σ (f.resBase p))))
    have h4 : (|Lu 1| + |Lu 2| + |Lu 3|) * σ ≤ Λ * σ :=
      mul_le_mul_of_nonneg_right hΛ hσ.le
    linarith
  · intro p hp
    have h1 := hg.resW_sub_up hh i hp
    have h2 := hg.resW_fit (h := h + 1) hh i hp
    rw [affineAt_sub]
    have h3 := abs_sub_le (affineAt (f.labelL (h + 1) i) (f.resBase p)) (f.resW p)
      (affineAt Lu (f.resBase p))
    have h4 := abs_sub_comm (affineAt (f.labelL (h + 1) i) (f.resBase p)) (f.resW p)
    have h5 : f.H * D.N k ^ (-(((h + 1 : ℕ) : ℝ) * (U' / f.m))) ≤ f.H * ah := by gcongr
    linarith
  · have h1 : 4 * (f.H * ah + Λ * σ) / ah ≤ 4 * f.H + 4 := by
      rw [div_le_iff₀ hah]
      nlinarith
    linarith

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
