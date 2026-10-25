import Submission.Obl.k4_horizontal_wide_interval_return.ParentCaps
import Submission.Obl.k4_horizontal_wide_interval_return.ScalarCaps
import Submission.Obl.k4_horizontal_wide_interval_return.ScalarCoefficients
import Submission.Obl.k4_horizontal_wide_interval_return.FineMesh
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set Filter
open Submission.Lib.K4MovingMeshBoxes

namespace Data

variable {α : Type} [MeasurableSpace α]

/-- The geometric output needed from the wide interval comparison. All cap
transfer, native coefficient budgets and scalar normalization are handled by
`uniform_extraction_of_geometry`. The retained prior is the original one. -/
def GeometricExtractionAt (cfg : Data α) (k : ℕ) (θ s v m J : ℝ) : Prop :=
  ∃ (i : Fin (cfg.n k s)) (lam : Measure (α × ℝ)) (Bs : Set α) (F : CellFrame),
    MeasurableSet Bs ∧ Bs ⊆ cfg.B k s i ∧ lam ≤ cfg.ρ k ∧
    (∀ᵐ p ∂lam, p.1 ∈ Bs ∧ p.2 ∈ Icc F.t₀ (F.t₀ + F.q)) ∧
    ENNReal.ofReal (cfg.N k ^ (-θ)) * (ENNReal.ofReal F.q * cfg.ν k (cfg.A k s i)) ≤
      lam univ ∧
    F.a = cfg.N k ^ (-s) ∧ F.q = ((2 : ℝ) ^ cfg.T k s)⁻¹ ∧
    F.g = cfg.N k ^ (-cfg.κ * s) ∧
    F.t₀ = (cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s ∧ F.c = cfg.c k s i ∧
    (∀ e, |F.L e| ≤ cfg.N k ^ J) ∧ (∀ e, |F.C e| ≤ cfg.N k ^ θ) ∧
    (∀ l ∈ Bs, ∀ t ∈ Icc F.t₀ (F.t₀ + F.q),
      |F.zZ t (lineZ (cfg.b k l) t)| ≤ cfg.N k ^ θ ∧
      |F.U t (lineZ (cfg.b k l) t) (lineY (cfg.b k l) t)| ≤ cfg.N k ^ θ ∧
      |F.resid t (lineZ (cfg.b k l) t) (lineY (cfg.b k l) t)
        (lineX (cfg.b k l) t)| ≤ cfg.N k ^ θ) ∧
    ∃ Fs : Finset ((Fin 2 → ℤ) × ℤ),
      (Fs.card : ℝ) * (cfg.N k ^ (-m)) ^ 2 ≤
        cfg.N k ^ θ * (cfg.N k ^ (-v)) ^ (-cfg.d) ∧
      ∀ᵐ p ∂lam, (F.cellCode (cfg.N k ^ (-m)) (cfg.b k p.1) p.2,
        ⌊F.cellSig (cfg.b k p.1) p.2 / cfg.N k ^ (-v)⌋) ∈ Fs

/-- The analytic geometry and finite residual support suffice for the precise
scalar input. Native caps and every fixed coefficient budget follow from the
frozen parent hypotheses. -/
theorem uniform_extraction_of_geometry (cfg : Data α) (hc : cfg.Valid)
    {s v m U' J : ℝ} (hs : 0 < s) (hv : 0 < v) (hvm : v < m)
    (hκm : cfg.κ * s ≤ m) (hU' : 0 < U') (hU'm : U' < m)
    (hsU : s + v ≤ cfg.U) (hJ : 17 ≤ J)
    (hgeometry : ∀ θ : ℝ, 0 < θ → ∀ᶠ k in atTop,
      cfg.GeometricExtractionAt k θ s v m J) :
    UniformCellExtraction cfg.N cfg.d cfg.U cfg.ν cfg.ρ cfg.b
      cfg.T cfg.n cfg.j cfg.A cfg.B := by
  have hκs : 0 < cfg.κ * s := mul_pos hc.rate_pos hs
  have hm : 0 < m := hv.trans hvm
  have hJ0 : 0 ≤ J := by linarith
  have hR0 : 0 ≤ 3 * J + 4 * cfg.κ * s + 8 := by nlinarith
  refine ⟨s, v, m, cfg.S, U', 3 * J + 4 * cfg.κ * s + 8,
    hs, hv, hvm, hc.palette_pos, hU', hU'm, hsU, hR0, ?_⟩
  intro η hη
  let θ : ℝ := min (η / 100) (1 / 4)
  have hθ : 0 < θ := lt_min (by linarith) (by norm_num)
  have hθη : θ ≤ η / 100 := min_le_left _ _
  have hθ1 : θ ≤ 1 / 4 := min_le_right _ _
  have hθleη : θ ≤ η := by linarith
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [hc.resolution_lower k]
  have hnum := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hc.resolution_tendsto hc.loss_lower hc.loss_subpower
  have hcoeff := hnum 3 (show 3 * θ < η by linarith) (show (0 : ℝ) ≤ 40 by norm_num)
  have hord := hnum 3 (show θ < η / 2 by linarith) (show (0 : ℝ) ≤ 3000 by norm_num)
  have hang := hnum 4 (show θ < η / 2 by linarith) (show (0 : ℝ) ≤ 6000 by norm_num)
  have hHnum := hnum 1 (show θ < 1 by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  let Q : ℝ := 1 + 2 * cfg.κ * s
  let Bdepth : ℝ := J + s + Q + m + v + 20
  have hQ : 0 ≤ Q := by dsimp [Q]; nlinarith
  have hBdepth : 0 < Bdepth := by dsimp [Bdepth]; linarith
  let rmin : ℝ := η / (4 * cfg.S)
  have hrmin : 0 < rmin := div_pos hη (mul_pos (by norm_num) hc.palette_pos)
  have hrminη : cfg.S * rmin ≤ η / 2 := by
    dsimp [rmin]
    have hS : cfg.S ≠ 0 := hc.palette_pos.ne'
    field_simp
    nlinarith
  let R : ℝ := 2 + s + s⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hs]
  have hRlo : R⁻¹ ≤ s := by
    have h : s⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hs) h
  filter_upwards [hgeometry θ hθ, hc.prepared R hR,
    cfg.eventually_native_scalar_caps hc hBdepth hs hv.le hU' hrmin,
    hc.loss_subpower η hη, hc.loss_subpower 1 (by norm_num),
    hcoeff, hord, hang, hHnum] with k hk hp hnative hKη hKN hcoeffk hordk hangk hHk
  obtain ⟨i, lam, Bs, F, hBsmeas, hBs, hlam, hsupp, hmass, ha, hq, hg,
    hstart, hcframe, hL, hC, hgeom, Fs, hFscard, hFssupp⟩ := hk
  have hNk : 2 ≤ cfg.N k := hc.resolution_lower k
  have hNpos : 0 < cfg.N k := by linarith
  have hK : 1 ≤ cfg.K k := hc.loss_lower k
  have hKpos : 0 < cfg.K k := by linarith
  have hnpθ : 1 ≤ cfg.N k ^ θ := Real.one_le_rpow (hN1 k) hθ.le
  let H : ℝ := cfg.K k * cfg.N k ^ θ
  have hH : 1 ≤ H := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ cfg.K k * cfg.N k ^ θ := mul_le_mul hK hnpθ (by norm_num) (by linarith)
  have hHN : H ≤ cfg.N k := by simpa only [one_mul, pow_one, Real.rpow_one] using hHk.le
  simp only [Real.rpow_one] at hKN
  have hθH : cfg.N k ^ θ ≤ H := le_mul_of_one_le_left (by positivity) hK
  have hKH : cfg.K k ≤ H := le_mul_of_one_le_right (by positivity) hnpθ
  have hqpos : 0 < F.q := by rw [hq]; positivity
  have hgpos : 0 < F.g := by rw [hg]; exact Real.rpow_pos_of_pos hNpos _
  have hg1 : F.g ≤ 1 := by
    rw [hg]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by nlinarith)
  have hapos : 0 < F.a := by rw [ha]; exact Real.rpow_pos_of_pos hNpos _
  have hσpos : 0 < cfg.N k ^ (-m) := Real.rpow_pos_of_pos hNpos _
  have hσg : cfg.N k ^ (-m) ≤ F.g := by
    rw [hg]
    exact Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
  have hδpos : 0 < cfg.N k ^ (-Bdepth) := Real.rpow_pos_of_pos hNpos _
  have hp' := hp s hRlo (by linarith : s ≤ cfg.U)
  simp only [zpow_neg, zpow_natCast] at hp'
  have hpi := hp'.2.2.2.2.1 i
  have hsets := hp'.2.2.1 i
  have hfloor : ENNReal.ofReal (F.a ^ cfg.d * F.q ^ 2 * F.g / cfg.K k) ≤
      cfg.ν k (cfg.A k s i) := by
    simpa only [ha, hq, hg, hc.horizontal_rate] using hpi.1
  have hAne : cfg.ν k (cfg.A k s i) ≠ 0 := by
    have hf : 0 < ENNReal.ofReal (F.a ^ cfg.d * F.q ^ 2 * F.g / cfg.K k) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact ne_of_gt (hf.trans_le hfloor)
  have hcH : ∀ e, |F.c e| ≤ H := by
    intro e
    rw [hcframe]
    exact (hpi.2.2.2.1 e).trans hKH
  have hCH : ∀ e, |F.C e| ≤ H := fun e => (hC e).trans hθH
  have hgeomH : ∀ l ∈ Bs, ∀ t ∈ Icc F.t₀ (F.t₀ + F.q),
      |F.zZ t (lineZ (cfg.b k l) t)| ≤ H ∧
      |F.U t (lineZ (cfg.b k l) t) (lineY (cfg.b k l) t)| ≤ H ∧
      |F.resid t (lineZ (cfg.b k l) t) (lineY (cfg.b k l) t) (lineX (cfg.b k l) t)| ≤ H :=
    fun l hl t ht => ⟨((hgeom l hl t ht).1).trans hθH,
      ((hgeom l hl t ht).2.1).trans hθH, ((hgeom l hl t ht).2.2).trans hθH⟩
  have hinv := cell_inverse_power_bound hNpos hKN hp'.2.1 hq hg
  have hmesh := fine_mesh_of_power_bounds hNk (zero_le_one.trans hH) hHN hJ0 hQ
    hs.le hm.le hv.le hqpos hgpos hg1 ha hinv
  change 4 * H ^ 2 * cfg.N k ^ (-Bdepth) ≤ F.q * cfg.N k ^ (-m) ∧
    4 * H ^ 2 * cfg.N k ^ (-Bdepth) ≤ F.q * F.g ∧
    (3 * cfg.N k ^ J * (F.q * F.g) + 40 * F.a * H ^ 3) * cfg.N k ^ (-Bdepth) ≤
      F.a * cfg.N k ^ (-v) * (F.q * F.g) at hmesh
  have hordinaryBudget : 3000 * cfg.K k * H * cfg.K k ≤ cfg.N k ^ (η / 2) := by
    calc _ = 3000 * cfg.K k ^ 3 * cfg.N k ^ θ := by dsimp [H]; ring
      _ ≤ _ := hordk.le
  have hangularBudget : 6000 * cfg.K k * H * cfg.K k * cfg.K k ≤ cfg.N k ^ (η / 2) := by
    calc _ = 6000 * cfg.K k ^ 4 * cfg.N k ^ θ := by dsimp [H]; ring
      _ ≤ _ := hangk.le
  have hcoeffBudget : 40 * H ^ 3 ≤ cfg.N k ^ η := by
    calc _ = 40 * cfg.K k ^ 3 * cfg.N k ^ (3 * θ) := by
          dsimp [H]
          rw [mul_pow, ← Real.rpow_mul_natCast hNpos.le]
          simp only [Nat.cast_ofNat, mul_comm θ, mul_assoc]
      _ ≤ _ := hcoeffk.le
  have hbasic := hc.basic k
  have hlamμ : lam ≤ cfg.μ k := hlam.trans hbasic.2.2.2.2.1
  obtain ⟨hnative, hpalette, hjoint⟩ := hnative lam hlamμ
  have hcaps := CellFrame.scalar_caps_from_original (F := F) lam (cfg.b k) hbasic.1
    (cfg.ν k (cfg.A k s i)) (Bs ×ˢ Icc F.t₀ (F.t₀ + F.q))
    (fun r ℓ => cfg.π k {w | ⌊w / cfg.N k ^ (-r)⌋ = ℓ})
    hNk hη hc.palette_pos hv.le hrminη hH (Real.rpow_nonneg hNpos.le _)
    hqpos hgpos hg1 hapos hσpos hσg hδpos hmesh.1 hmesh.2.1 hmesh.2.2
    hcH hCH hL hKpos.le hKpos hKpos.le hfloor hordinaryBudget hangularBudget hsupp
    (fun p hp => ⟨hp.2, (hgeomH p.1 hp.1 p.2 hp.2).1, (hgeomH p.1 hp.1 p.2 hp.2).2.1⟩)
    (by simpa only [ha] using hnative) hpalette (by simpa only [ha] using hjoint)
  have hinput : CellInput (cfg.N k) η cfg.d v m cfg.S U' (cfg.ν k) lam (cfg.b k)
      (cfg.A k s i) Bs F := by
    refine ⟨hbasic.1, hsets.1, hBsmeas, hBs.trans hsets.2.2, hbasic.2.1,
      hAne, hqpos, hgpos, hapos, ?_, hsupp, ?_, ?_, hcaps.1, ?_, hcaps.2⟩
    · refine hlamμ.trans (hbasic.2.2.2.1.trans ?_)
      intro E
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hKη) le_rfl
    · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_le (hN1 k) (neg_le_neg hθleη))) le_rfl).trans hmass
    · intro l hl e
      apply (CellFrame.lineCoeffs_bound_of_geometry F (cfg.b k l) hH hqpos.ne'
        hgpos.ne' hapos.ne' hCH ?_ e).trans hcoeffBudget
      intro z hz
      apply hgeomH l hl
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg hqpos.le hz.1)
      · simpa only [mul_one, add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left hz.2 hqpos.le) F.t₀
    · refine ⟨Fs, hFscard.trans ?_, hFssupp⟩
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (hN1 k) hθleη) (by positivity)
  have hNtoJ : cfg.N k ≤ cfg.N k ^ J := by
    calc cfg.N k = cfg.N k ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
  exact extractionAt_of_power_bounds i Bs F hNk hKN hs hc.rate_pos hJ hp'.2.1
    hinput hlam hBs (fun e => (hcH e).trans (hHN.trans hNtoJ)) hL
    (fun e => (hCH e).trans (hHN.trans hNtoJ)) ha hq hg hstart

end Data

/-- A geometric target for the analytic three-layer argument. All depths and
the native coefficient exponent are fixed before the loss. -/
def GeometricPreparation : Prop :=
  Row → Submission.Lib.K4QuadSheetMatching.TwoColorStatement →
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Valid → cfg.Projected →
    ∃ s v m U' J : ℝ, 0 < s ∧ 0 < v ∧ v < m ∧ cfg.κ * s ≤ m ∧
      0 < U' ∧ U' < m ∧ s + v ≤ cfg.U ∧ 17 ≤ J ∧
      ∀ θ : ℝ, 0 < θ → ∀ᶠ k in atTop, cfg.GeometricExtractionAt k θ s v m J

theorem modelPreparation_of_geometry (h : GeometricPreparation) : ModelPreparation := by
  intro hRow hMatching α _ cfg hc hp
  obtain ⟨s, v, m, U', J, hs, hv, hvm, hκm, hU', hU'm, hsU, hJ, hgeom⟩ :=
    h hRow hMatching α cfg hc hp
  exact cfg.uniform_extraction_of_geometry hc hs hv hvm hκm hU' hU'm hsU hJ hgeom

end Submission.Obl.k4_horizontal_wide_interval_return
