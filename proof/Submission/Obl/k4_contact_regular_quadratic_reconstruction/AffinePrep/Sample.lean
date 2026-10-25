import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.LineFacts
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.ChartBounds
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.FineCells
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.CoreApply
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.VelocityCellCore

/-!
# The second affine preparation at one late sample

All the asymptotic facts are frozen at one sample `k`, one coarse label `(s, i)` and one
improvement `v`: the original atlas rows, the centering of the label, the original native caps
transported to residual bins of the fine width in the normalized chart (`hres`), and the
original velocity palette (`hpal`). Under explicit numerical conditions, a shifted regular
quadratic candidate yields a fine affine source (`affine_candidate_at`).
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open MeasureTheory Set MvPolynomial Filter
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4QuadraticSheetCore
open Submission.Lib.K4AffineMeshCaps (baseMesh)
open Submission.Obl.k4_critical_switching_state_preparation.Data

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem shiftedPt_of_residual (D : ChartData) (b : Fin 6 → ℝ) (t : ℝ) :
    ![basePt b t 0, basePt b t 1, basePt b t 2,
      (point b t 3 - eval (point b t) (affineBase D.L')) + D.γ] = shiftedPt D.L b t := by
  funext m
  fin_cases m <;> simp [basePt, shiftedPt, point, affineBase, ChartData.L'] <;> ring

/-- The normalized observed point with the unscaled residual of the shifted predictor. -/
def obsPoint (D : ChartData) (cfg : Model α) (k : ℕ) (p : α × ℝ) : Fin 4 → ℝ :=
  ![D.normBase (basePt (cfg.b k p.1) p.2) 0, D.normBase (basePt (cfg.b k p.1) p.2) 1,
    D.normBase (basePt (cfg.b k p.1) p.2) 2,
    cfg.x k p.1 p.2 3 - eval (cfg.x k p.1 p.2) (affineBase D.L')]

theorem eval_tildeTest_obsPoint (D : ChartData) (cfg : Model α) (k : ℕ) (hq : D.q ≠ 0)
    (hB : D.B ≠ 0) (Q : MvPolynomial (Fin 4) ℝ) (p : α × ℝ) :
    eval (obsPoint D cfg k p) (D.tildeTest Q) = eval (shiftedPt D.L (cfg.b k p.1) p.2) Q := by
  rw [obsPoint, D.eval_tildeTest hq hB, ← shiftedPt_of_residual]
  rfl

set_option maxHeartbeats 8000000 in
/-- **The second affine preparation at one sample.** -/
theorem affine_candidate_at {cfg : Model α} (h : cfg.Valid) {k : ℕ} {s v η ε R : ℝ}
    {i : Fin (cfg.n k s)}
    -- the mesh, velocity bins, core scale and constants
    {hm rv Λ Cs J B₀ A₀ : ℝ} (hhm : 0 < hm) (hhm8 : hm ≤ 1 / 8) (hrv : 0 < rv)
    (hΛ : 1 ≤ Λ) (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs) (hJ : 0 ≤ J)
    (hN : 2 ≤ cfg.N k) (hK : 1 ≤ cfg.K k) (hη : 0 ≤ η)
    -- the coarse label
    (hBm : MeasurableSet (cfg.B k s i)) (hBA : cfg.B k s i ⊆ cfg.A k s i)
    (hcl : ∀ e, |cfg.c k s i e| ≤ cfg.K k)
    (hgq : cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹)
    (hqg : ((2 : ℝ) ^ cfg.T k s)⁻¹ ≤ cfg.K k * cfg.N k ^ (-cfg.ℓ * s))
    (hνA : ENNReal.ofReal ((cfg.N k ^ (-s)) ^ cfg.d * (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 *
      cfg.N k ^ (-cfg.ℓ * s) / cfg.K k) ≤ cfg.ν k (cfg.A k s i))
    (hrows : ∀ l ∈ cfg.A k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤
          cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ ∧
        |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤
          cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.N k ^ (-cfg.ℓ * s) ∧
        |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤
          cfg.K k * cfg.N k ^ (-cfg.ℓ * s))
    (hcenter : |cfg.c k s i 3 + (cfg.c k s i 0 + ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s *
        cfg.c k s i 1)| ≤ J * ((2 : ℝ) ^ cfg.T k s)⁻¹)
    (hpivot : |cfg.c k s i 4 - ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s| ≤
      J * ((2 : ℝ) ^ cfg.T k s)⁻¹)
    -- the transported original caps at this sample
    (hres : ∀ τ : Measure (α × ℝ), τ ≤ cfg.μ k → ENNReal.ofReal (cfg.N k ^ (-B₀)) ≤ τ univ →
      ∀ L' : Fin 4 → ℝ,
      (∀ᵐ x ∂τ, |eval (cfg.x k x.1 x.2) (affineBase L') - (cfg.x k x.1 x.2) 3| ≤ 1 / 4) →
      ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ), M.det ≠ 0 →
      (∀ r, ∑ m, |M r m| ≤ cfg.N k ^ A₀) →
      (∀ (q : Fin 3 → ℤ) (j : ℤ), τ {x | baseMesh hm
          (Submission.Lib.K4AffineMeshCaps.affineBase M b (cfg.x k x.1 x.2 ∘ Fin.castSucc)) = q ∧
          ⌊((cfg.x k x.1 x.2) 3 - eval (cfg.x k x.1 x.2) (affineBase L')) /
            cfg.N k ^ (-s - v)⌋ = j} ≤
        ENNReal.ofReal (27 * (6 * cfg.K k + 5) * cfg.K k * |M.det|⁻¹ *
          (hm ^ 3 * (cfg.N k ^ (-s - v)) ^ cfg.d))) ∧
      (∀ (q : Fin 3 → ℤ) (j v₀ : ℤ), τ {x | baseMesh hm
          (Submission.Lib.K4AffineMeshCaps.affineBase M b (cfg.x k x.1 x.2 ∘ Fin.castSucc)) = q ∧
          ⌊((cfg.x k x.1 x.2) 3 - eval (cfg.x k x.1 x.2) (affineBase L')) /
            cfg.N k ^ (-s - v)⌋ = j ∧ ⌊cfg.b k x.1 3 / rv⌋ = v₀} ≤
        ENNReal.ofReal (27 * (6 * cfg.K k + 5) * cfg.K k * |M.det|⁻¹ *
          (hm ^ 3 * (cfg.N k ^ (-s - v)) ^ cfg.d)) * cfg.π k {w : ℝ | ⌊w / rv⌋ = v₀}))
    (hpal : ∀ a : ℤ, cfg.π k {w : ℝ | ⌊w / rv⌋ = a} ≤ ENNReal.ofReal (cfg.K k * rv ^ cfg.S))
    -- numerical conditions (all subpower or fixed-power absorptions)
    (nmass : cfg.N k ^ (-B₀) ≤ cfg.N k ^ (-cfg.d * v - η) * ((2 : ℝ) ^ cfg.T k s)⁻¹ *
      ((cfg.N k ^ (-s)) ^ cfg.d * (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 *
        cfg.N k ^ (-cfg.ℓ * s) / cfg.K k) / 18)
    (nrows : (1 + |((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s| + |cfg.c k s i 0 +
      ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s * cfg.c k s i 1|) *
        (((2 : ℝ) ^ cfg.T k s)⁻¹⁻¹ + ((((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2)⁻¹) ≤ cfg.N k ^ A₀)
    (nlip : 2 * (81 * cfg.N k ^ R * (7 + 4 * (cfg.K k + cfg.K k) +
        (cfg.K k + cfg.K k + cfg.K k * (cfg.K k + cfg.K k)) +
        34 * (2 * cfg.K k + 2 * cfg.K k ^ 2 + 2 * J * cfg.K k + J)) ^ 2) * (3 * hm) ≤
      cfg.N k ^ η * cfg.N k ^ (-s - v))
    (nlip' : 2 * (2 * (81 * cfg.N k ^ R * (7 + 4 * (cfg.K k + cfg.K k) +
        (cfg.K k + cfg.K k + cfg.K k * (cfg.K k + cfg.K k)) +
        34 * (2 * cfg.K k + 2 * cfg.K k ^ 2 + 2 * J * cfg.K k + J)) ^ 2)) * (3 * hm) ≤
      (cfg.N k ^ η)⁻¹ / 2)
    (nvel : 2 * (2 * (8 * (1 + 4 * (cfg.N k ^ η) ^ 2) * (27 * (6 * cfg.K k + 5) * cfg.K k *
        ((8 * (2 * cfg.K k + 2 * cfg.K k ^ 2 + 2 * J * cfg.K k + J)) ^ 2 *
          (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 4) * (hm ^ 3 * (cfg.N k ^ (-s - v)) ^ cfg.d)) *
        (cfg.K k * rv ^ cfg.S))) <
      cfg.N k ^ (-cfg.d * v - η) * ((2 : ℝ) ^ cfg.T k s)⁻¹ *
        ((cfg.N k ^ (-s)) ^ cfg.d * (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 *
          cfg.N k ^ (-cfg.ℓ * s) / cfg.K k) * hm ^ 3 / (18 * 16))
    (nvol : Λ⁻¹ ≤ cfg.N k ^ (-cfg.d * v - η) * ((2 : ℝ) ^ cfg.T k s)⁻¹ *
        ((cfg.N k ^ (-s)) ^ cfg.d * (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 *
          cfg.N k ^ (-cfg.ℓ * s) / cfg.K k) / 36 * hm ^ 3 /
        (8 * (1 + 4 * (cfg.N k ^ η) ^ 2) * (27 * (6 * cfg.K k + 5) * cfg.K k *
          ((8 * (2 * cfg.K k + 2 * cfg.K k ^ 2 + 2 * J * cfg.K k + J)) ^ 2 *
            (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 4) * (hm ^ 3 * (cfg.N k ^ (-s - v)) ^ cfg.d))))
    (nsep : Λ⁻¹ ≤ rv / 2 / (8 * (2 * cfg.K k + 2 * cfg.K k ^ 2 + 2 * J * cfg.K k + J)))
    (nH : cfg.N k ^ η ≤ Λ)
    (ncon : cfg.N k ^ (-cfg.e₀) / ((2 : ℝ) ^ cfg.T k s)⁻¹ /
      (8 * (2 * cfg.K k + 2 * cfg.K k ^ 2 + 2 * J * cfg.K k + J)) ≤ 1)
    (ns1 : 4 * Cs * remezC 4 Λ * (3 * hm) ≤ 1)
    (ns2 : 8 * discBudget Cs Λ * (3 * hm) * Λ ^ 2 ≤ 1)
    (ns3 : 192 * Cs * sffKappa Cs Λ * (cfg.N k ^ (-cfg.e₀) / ((2 : ℝ) ^ cfg.T k s)⁻¹ /
      (8 * (2 * cfg.K k + 2 * cfg.K k ^ 2 + 2 * J * cfg.K k + J)) + 3 * hm) * Λ ^ 2 ≤ 1)
    (ntrim : 2 * cfg.K k * (2 * hm) ≤ cfg.N k ^ (-cfg.d * v - η))
    (nfin : cfg.N k ^ (-s - v) * coreLoss Cs Λ ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v))
    (nfinm : 36 * cfg.N k ^ (-cfg.d * v - ε) ≤ cfg.N k ^ (-cfg.d * v - η))
    (hshift : cfg.ShiftedCandidate k s v η R i) :
    cfg.AffineCandidate k s v ε i := by
  classical
  obtain ⟨L, G, hGdeg, hGcoeff, hmassW⟩ := (shiftedCandidate_iff cfg k s v η R i).mp hshift
  -- abbreviations
  set N := cfg.N k with hNdef
  set K := cfg.K k with hKdef
  set q : ℝ := ((2 : ℝ) ^ cfg.T k s)⁻¹ with hqdef
  set t₀ : ℝ := ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s with ht₀def
  set c : ℝ := N ^ (-s - v) with hcdef
  set H : ℝ := N ^ η with hHdef
  set Bz : ℝ := 2 * K + 2 * K ^ 2 + 2 * J * K + J with hBzdef
  set W := shiftedWitness cfg k s v η i L G with hWdef
  set νlow : ℝ := (N ^ (-s)) ^ cfg.d * q ^ 2 * N ^ (-cfg.ℓ * s) / K with hνlow
  set m₀ : ℝ := N ^ (-cfg.d * v - η) * q * νlow with hm₀def
  have hN0 : 0 < N := by linarith only [hN]
  have hK0 : 0 < K := by linarith only [hK]
  have hq : 0 < q := by positivity
  have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hc : 0 < c := by positivity
  have hH1 : 1 ≤ H := Real.one_le_rpow (by linarith) hη
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hBz : 0 < Bz := by positivity
  have h2KBz : 2 * K ≤ Bz := by
    have h2 : 0 ≤ 2 * K ^ 2 + 2 * J * K + J := by positivity
    rw [hBzdef]; linarith only [h2]
  have hBz8 : 1 ≤ 8 * Bz := by linarith only [h2KBz, hK]
  have hνlow0 : 0 ≤ νlow := by positivity
  have hm₀0 : 0 ≤ m₀ := by positivity
  have ht₀0 : 0 ≤ t₀ := by positivity
  have ht₀1 : t₀ ≤ 1 := by
    rw [ht₀def, div_le_one (by positivity)]
    exact_mod_cast (cfg.j k s i).isLt.le
  obtain ⟨hb, hν, hπ, hdom, hρμ, hsupp, -⟩ := h.basic k
  haveI : IsProbabilityMeasure (cfg.ν k) := hν
  haveI : IsFiniteMeasure (cfg.μ k) := Transfer.basic_incidence_finite cfg h.basic k
  haveI : IsFiniteMeasure (cfg.ρ k) := isFiniteMeasure_of_le (cfg.μ k) hρμ
  -- the witness mass in real and relative forms
  have hmassW' : ENNReal.ofReal (N ^ (-cfg.d * v - η) * q) * cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k W := by
    simpa only [div_eq_mul_inv, hqdef] using hmassW
  have hmassReal : ENNReal.ofReal m₀ ≤ cfg.ρ k W := by
    refine le_trans ?_ hmassW'
    rw [hm₀def, ENNReal.ofReal_mul (by positivity)]
    gcongr
  -- Step 1: the quarter-band source
  have htrim : ENNReal.ofReal K * (cfg.ν k (cfg.B k s i) * ENNReal.ofReal (2 * (q * hm))) ≤
      cfg.ρ k W / 2 := by
    have hνBA : cfg.ν k (cfg.B k s i) ≤ cfg.ν k (cfg.A k s i) := measure_mono hBA
    calc ENNReal.ofReal K * (cfg.ν k (cfg.B k s i) * ENNReal.ofReal (2 * (q * hm))) ≤
        ENNReal.ofReal K * (cfg.ν k (cfg.A k s i) * ENNReal.ofReal (2 * (q * hm))) := by gcongr
      _ = ENNReal.ofReal (K * (2 * (q * hm))) * cfg.ν k (cfg.A k s i) := by
        rw [ENNReal.ofReal_mul hK0.le]; ring
      _ ≤ ENNReal.ofReal (N ^ (-cfg.d * v - η) * q / 2) * cfg.ν k (cfg.A k s i) := by
        gcongr
        have h1 := mul_le_mul_of_nonneg_right ntrim (by positivity : (0 : ℝ) ≤ q / 2)
        calc K * (2 * (q * hm)) = 2 * K * (2 * hm) * (q / 2) := by ring
          _ ≤ N ^ (-cfg.d * v - η) * (q / 2) := h1
          _ = N ^ (-cfg.d * v - η) * q / 2 := by ring
      _ = ENNReal.ofReal (N ^ (-cfg.d * v - η) * q) * cfg.ν k (cfg.A k s i) / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat,
          ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
      _ ≤ cfg.ρ k W / 2 := ENNReal.div_le_div_right hmassW' 2
  obtain ⟨γ, E, hγ, hEm, hEW, hEgood, hEtrim, hEmass, hEband⟩ := quarter_source h hBm hhm.le htrim
  -- Step 2: the normalized chart
  set Z₀ : ℝ := cfg.c k s i 0 + t₀ * cfg.c k s i 1 with hZ₀def
  set Y₀ : ℝ := cfg.c k s i 2 + t₀ * cfg.c k s i 3 + cfg.c k s i 4 * Z₀ with hY₀def
  set D : ChartData := ⟨t₀, q, Z₀, Y₀, Bz, c, L, γ⟩ with hDdef
  have hDq : D.q ≠ 0 := hq.ne'
  have hDB : D.B ≠ 0 := hBz.ne'
  have hDc : D.c ≠ 0 := hc.ne'
  set εc : ℝ := N ^ (-cfg.e₀) / q / (8 * Bz) with hεc
  -- Step 3: the normalized witness lines
  have hLF : ∀ p ∈ E, LineFacts D G H (K / (8 * Bz)) εc hm (cfg.b k p.1) ((p.2 - t₀) / q) := by
    intro p hp
    exact lineFacts_of_witness hGdeg hJ hhm hhm8 hgq hrows hBA hK D rfl rfl rfl rfl rfl rfl rfl
      rfl hcenter hpivot p (hEW hp) (hEgood hp) (hEtrim hp) (hEband p hp) hN0
  -- the normalized observed points
  set zo : α × ℝ → Fin 3 → ℝ := fun p => D.normBase (basePt (cfg.b k p.1) p.2) with hzo
  set code : α × ℝ → Fin 3 → ℤ := fun p => cellCode hm (zo p) with hcode
  have hzoP : ∀ p ∈ E, lineP (D.normLine (cfg.b k p.1)) ((p.2 - t₀) / q) = zo p := by
    intro p hp
    rw [D.normLine_lineP hDq hDB]
    congr 2
    change t₀ + q * ((p.2 - t₀) / q) = p.2
    field_simp
    ring
  have hzo_in : ∀ p ∈ E, ∀ m, hm ≤ zo p m ∧ zo p m ≤ 1 - hm := by
    intro p hp m
    rw [← hzoP p hp]
    exact (hLF p hp).inner m
  have hzo_cube : ∀ p ∈ E, zo p ∈ Icc (0 : Fin 3 → ℝ) 1 := by
    intro p hp
    constructor
    · intro m; have := (hzo_in p hp m).1; simp only [Pi.zero_apply]; linarith only [this, hhm]
    · intro m; have := (hzo_in p hp m).2; simp only [Pi.one_apply]; linarith only [this, hhm]
  have hcode_eq : ∀ p, code p = baseMesh hm (Submission.Lib.K4AffineMeshCaps.affineBase
      D.normMat D.normOff (cfg.x k p.1 p.2 ∘ Fin.castSucc)) := by
    intro p
    rw [x_castSucc, ← D.normBase_eq_affine]
    rfl
  have hcode_meas : Measurable code := by
    have hZm : Measurable fun p : α × ℝ => cfg.x k p.1 p.2 ∘ Fin.castSucc := by
      have hbp : Measurable fun p : α × ℝ => cfg.b k p.1 := hb.comp measurable_fst
      unfold x
      fun_prop
    have h1 := (Submission.Lib.K4AffineMeshCaps.measurable_baseMesh hm).comp
      ((Submission.Lib.K4AffineMeshCaps.measurable_affineBase D.normMat D.normOff).comp hZm)
    have e : code = baseMesh hm ∘ (Submission.Lib.K4AffineMeshCaps.affineBase D.normMat D.normOff ∘
        fun p : α × ℝ => cfg.x k p.1 p.2 ∘ Fin.castSucc) := by
      funext p; exact hcode_eq p
    rw [e]
    exact h1
  -- Step 4: the transported original caps on the source
  set τ : Measure (α × ℝ) := (cfg.ρ k).restrict E with hτdef
  have hτμ : τ ≤ cfg.μ k := Measure.restrict_le_self.trans hρμ
  have hτmass : ENNReal.ofReal (N ^ (-B₀)) ≤ τ univ := by
    rw [hτdef, Measure.restrict_apply_univ]
    refine le_trans ?_ hEmass
    calc ENNReal.ofReal (N ^ (-B₀)) ≤ ENNReal.ofReal (m₀ / 18) := ENNReal.ofReal_le_ofReal nmass
      _ = ENNReal.ofReal m₀ / 18 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 18), ENNReal.ofReal_ofNat]
      _ ≤ cfg.ρ k W / 18 := ENNReal.div_le_div_right hmassReal 18
  have hquarter : ∀ᵐ x ∂τ, |eval (cfg.x k x.1 x.2) (affineBase D.L') - (cfg.x k x.1 x.2) 3| ≤
      1 / 4 := by
    refine ae_restrict_of_forall_mem hEm fun p hp => ?_
    have hb8 := hEband p hp
    have e : eval (cfg.x k p.1 p.2) (affineBase D.L') - (cfg.x k p.1 p.2) 3 =
        -(cfg.shiftedPoint k L p.1 p.2 3 - γ) := by
      simp [affineBase, ChartData.L', Model.shiftedPoint, x, hDdef]
      ring
    rw [e, abs_neg]
    linarith
  have hdet : D.normMat.det ≠ 0 := by
    rw [D.det_normMat]; positivity
  have hdetinv : |D.normMat.det|⁻¹ = (8 * Bz) ^ 2 * q ^ 4 := by
    rw [D.det_normMat, abs_of_pos (by positivity)]
    simp [hDdef, mul_inv, inv_inv]
    ring
  have hrowsum : ∀ r, ∑ m, |D.normMat r m| ≤ N ^ A₀ :=
    fun r => (D.normMat_rowSum_le hq hBz8 r).trans nrows
  obtain ⟨hcapP, hcapA⟩ := hres τ hτμ hτmass D.L' hquarter D.normMat D.normOff hdet hrowsum
  set C₀ : ℝ := 27 * (6 * K + 5) * K * ((8 * Bz) ^ 2 * q ^ 4) * (hm ^ 3 * c ^ cfg.d) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hcapC : 27 * (6 * K + 5) * K * |D.normMat.det|⁻¹ * (hm ^ 3 * c ^ cfg.d) = C₀ := by
    rw [hdetinv]
  -- Step 5: fine cells of the regular quadratic fibers
  set SB : ℝ := 7 + 4 * (K + K) + (K + K + K * (K + K)) + 34 * Bz with hSB
  set MG : ℝ := 81 * N ^ R * SB ^ 2 with hMG
  have hMGc : Submission.Lib.K4ChartLifting.coeffL1 (D.tildeTest G) ≤ MG := by
    have h1 := D.coeffL1_tildeTest_le G hGdeg
    have h2 : Submission.Lib.K4ChartLifting.coeffL1 G ≤ 81 * N ^ R := by
      have := Submission.Lib.K4ChartLifting.coeffL1_le_of_coeff_le (n := 4) (D := 2) G hGdeg
        (N ^ R) hGcoeff
      norm_num at this
      exact this
    have hZ : |D.Z₀| ≤ K + K := by
      change |cfg.c k s i 0 + t₀ * cfg.c k s i 1| ≤ K + K
      have := hcl 0; have := hcl 1
      calc _ ≤ |cfg.c k s i 0| + |t₀ * cfg.c k s i 1| := abs_add_le _ _
        _ ≤ K + 1 * K := by
          rw [abs_mul, abs_of_nonneg ht₀0]; gcongr
        _ = K + K := by ring
    have hY : |D.Y₀| ≤ K + K + K * (K + K) := by
      change |cfg.c k s i 2 + t₀ * cfg.c k s i 3 + cfg.c k s i 4 * Z₀| ≤ _
      have := hcl 2; have := hcl 3; have := hcl 4
      calc _ ≤ |cfg.c k s i 2| + |t₀ * cfg.c k s i 3| + |cfg.c k s i 4 * Z₀| :=
            abs_add_three _ _ _
        _ ≤ K + 1 * K + K * (K + K) := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht₀0]
          gcongr
        _ = _ := by ring
    have h3 := D.substBudget_one_le (by rw [abs_of_nonneg ht₀0]; exact ht₀1) hq.le hq1 hγ hBz.le
    have h4 : D.substBudget 1 ≤ SB := by
      refine h3.trans ?_
      change 7 + 4 * |D.Z₀| + |D.Y₀| + 34 * Bz ≤ SB
      rw [hSB]; linarith
    have h5 : 0 ≤ D.substBudget 1 := (zero_le_one).trans (D.one_le_substBudget 1)
    calc _ ≤ Submission.Lib.K4ChartLifting.coeffL1 G * D.substBudget 1 ^ 2 := h1
      _ ≤ 81 * N ^ R * SB ^ 2 := by
        have := Submission.Lib.K4ChartLifting.coeffL1_nonneg G
        gcongr
  have hfine : ∀ (qq : Fin 3 → ℤ) (S : Set (α × ℝ)) (capS : ENNReal),
      (∀ a : ℤ, τ {p | (code p = qq ∧ p ∈ S) ∧ ⌊obsPoint D cfg k p 3 / c⌋ = a} ≤ capS) →
      cfg.ρ k {p | p ∈ E ∧ code p = qq ∧ p ∈ S} ≤ ENNReal.ofReal (8 * (1 + 4 * H ^ 2)) * capS := by
    intro qq S capS hcapS
    set Es := {p | p ∈ E ∧ code p = qq ∧ p ∈ S} with hEs
    have hEsE : Es ⊆ E := fun p hp => hp.1
    have hτEs : τ Es = cfg.ρ k Es := by
      rw [hτdef, Measure.restrict_apply' hEm, Set.inter_eq_left.mpr hEsE]
    rw [← hτEs]
    by_cases hne : Es.Nonempty
    · obtain ⟨p₀, hp₀⟩ := hne
      set z : Fin 4 → ℝ := ![(qq 0 : ℝ) * hm, (qq 1 : ℝ) * hm, (qq 2 : ℝ) * hm, 0] with hz
      have hcellbd : ∀ p, code p = qq → ∀ m : Fin 3, (qq m : ℝ) * hm ≤ zo p m ∧
          zo p m < ((qq m : ℝ) + 1) * hm := by
        intro p hpq m
        have hm' : ⌊zo p m / hm⌋ = qq m := by rw [← hpq]; rfl
        have h1 := Int.floor_le (zo p m / hm)
        have h2 := Int.lt_floor_add_one (zo p m / hm)
        rw [hm'] at h1 h2
        constructor
        · rwa [le_div_iff₀ hhm] at h1
        · rwa [div_lt_iff₀ hhm] at h2
      have hz012 : ∀ m : Fin 3, |(qq m : ℝ) * hm| ≤ 1 := by
        intro m
        obtain ⟨h1, h2⟩ := hcellbd p₀ hp₀.2.1 m
        obtain ⟨h3, h4⟩ := hzo_in p₀ hp₀.1 m
        rw [add_mul, one_mul] at h2
        rw [abs_le]
        constructor <;> linarith only [h1, h2, h3, h4, hhm]
      have hzbd : ∀ m, |z m| ≤ 1 := by
        intro m
        fin_cases m
        · exact hz012 0
        · exact hz012 1
        · exact hz012 2
        · simp [hz]
      have hband : ∀ p ∈ E, |obsPoint D cfg k p 3| ≤ 1 / 8 := by
        intro p hp
        have hb8 := hEband p hp
        have e : obsPoint D cfg k p 3 = cfg.shiftedPoint k L p.1 p.2 3 - γ := by
          simp [obsPoint, affineBase, ChartData.L', Model.shiftedPoint, x, hDdef]
          ring
        rw [e]; exact hb8
      have hx : ∀ p ∈ Es, (∀ m, |obsPoint D cfg k p m| ≤ 1) ∧
          (∀ m : Fin 3, |obsPoint D cfg k p m.castSucc - z m.castSucc| ≤ hm) ∧
          |eval (obsPoint D cfg k p) (D.tildeTest G)| ≤ H * c ∧
          H⁻¹ ≤ |eval (obsPoint D cfg k p) (pderiv 3 (D.tildeTest G))| := by
        intro p hp
        have hpE := hp.1
        have hfit := (hEW hpE).2.2.1 p.2 (hEW hpE).2.1
        have hfl := (hEW hpE).2.2.2
        have hsh : shiftedPt D.L (cfg.b k p.1) p.2 = cfg.shiftedPoint k L p.1 p.2 := by
          rw [shiftedPoint_eq]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro m
          fin_cases m
          · have := hzo_in p hpE 0
            change |zo p 0| ≤ 1
            rw [abs_le]; constructor <;> linarith only [this.1, this.2, hhm]
          · have := hzo_in p hpE 1
            change |zo p 1| ≤ 1
            rw [abs_le]; constructor <;> linarith only [this.1, this.2, hhm]
          · have := hzo_in p hpE 2
            change |zo p 2| ≤ 1
            rw [abs_le]; constructor <;> linarith only [this.1, this.2, hhm]
          · have := hband p hpE
            change |obsPoint D cfg k p 3| ≤ 1
            linarith only [this]
        · intro m
          fin_cases m
          · obtain ⟨h1, h2⟩ := hcellbd p hp.2.1 0
            rw [add_mul, one_mul] at h2
            change |zo p 0 - (qq 0 : ℝ) * hm| ≤ hm
            rw [abs_le]; constructor <;> linarith only [h1, h2]
          · obtain ⟨h1, h2⟩ := hcellbd p hp.2.1 1
            rw [add_mul, one_mul] at h2
            change |zo p 1 - (qq 1 : ℝ) * hm| ≤ hm
            rw [abs_le]; constructor <;> linarith only [h1, h2]
          · obtain ⟨h1, h2⟩ := hcellbd p hp.2.1 2
            rw [add_mul, one_mul] at h2
            change |zo p 2 - (qq 2 : ℝ) * hm| ≤ hm
            rw [abs_le]; constructor <;> linarith only [h1, h2]
        · rw [eval_tildeTest_obsPoint D cfg k hDq hDB, hsh]
          exact hfit.2.1
        · rw [D.pderiv_tildeTest, eval_tildeTest_obsPoint D cfg k hDq hDB, hsh, hHdef,
            ← Real.rpow_neg hN0.le]
          exact hfl
      have hET : Es ⊆ {p | code p = qq ∧ p ∈ S} := fun p hp => hp.2
      exact fine_cell_cap τ Es {p | code p = qq ∧ p ∈ S} hET (obsPoint D cfg k) (D.tildeTest G)
        ((D.tildeTest_degree G).trans hGdeg) z hH1 hc hMGc hzbd hx nlip nlip' capS hcapS
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty]
      exact zero_le
  -- the two kinds of fine caps
  have hobs3 : ∀ p, obsPoint D cfg k p 3 =
      (cfg.x k p.1 p.2) 3 - eval (cfg.x k p.1 p.2) (affineBase D.L') := fun p => rfl
  have hfineA : ∀ (qq : Fin 3 → ℤ) (v₀ : ℤ),
      cfg.ρ k {p | p ∈ E ∧ code p = qq ∧ p ∈ {p : α × ℝ | ⌊cfg.b k p.1 3 / rv⌋ = v₀}} ≤
        ENNReal.ofReal (8 * (1 + 4 * H ^ 2) * C₀ * (K * rv ^ cfg.S)) := by
    intro qq v₀
    have h1 := hfine qq {p : α × ℝ | ⌊cfg.b k p.1 3 / rv⌋ = v₀}
      (ENNReal.ofReal C₀ * cfg.π k {w : ℝ | ⌊w / rv⌋ = v₀}) (by
        intro a
        refine le_trans (measure_mono ?_) ((hcapA qq a v₀).trans_eq (by rw [hcapC]))
        intro p hp
        obtain ⟨⟨hpq, hpv⟩, hpa⟩ := hp
        refine ⟨?_, ?_, hpv⟩
        · rw [← hcode_eq]; exact hpq
        · rw [← hobs3]; exact hpa)
    refine h1.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (8 * (1 + 4 * H ^ 2) * C₀) * cfg.π k {w : ℝ | ⌊w / rv⌋ = v₀} ≤
        ENNReal.ofReal (8 * (1 + 4 * H ^ 2) * C₀) * ENNReal.ofReal (K * rv ^ cfg.S) := by
          gcongr; exact hpal v₀
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hfineP : ∀ (qq : Fin 3 → ℤ),
      cfg.ρ k {p | p ∈ E ∧ code p = qq} ≤ ENNReal.ofReal (8 * (1 + 4 * H ^ 2) * C₀) := by
    intro qq
    have h1 := hfine qq univ (ENNReal.ofReal C₀) (by
        intro a
        refine le_trans (measure_mono ?_) ((hcapP qq a).trans_eq (by rw [hcapC]))
        intro p hp
        obtain ⟨⟨hpq, -⟩, hpa⟩ := hp
        refine ⟨?_, ?_⟩
        · rw [← hcode_eq]; exact hpq
        · rw [← hobs3]; exact hpa)
    have e : {p | p ∈ E ∧ code p = qq} = {p | p ∈ E ∧ code p = qq ∧ p ∈ (univ : Set (α × ℝ))} := by
      ext p; simp
    rw [e]
    refine h1.trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  -- Step 6: delete light cells; three separated velocities in every remaining cell
  set θ : ℝ := m₀ * hm ^ 3 / (18 * 16) with hθdef
  set bb : ℝ := 2 * (8 * (1 + 4 * H ^ 2) * C₀ * (K * rv ^ cfg.S)) with hbbdef
  have hθ0 : 0 < θ := by
    have : 0 < m₀ := by
      rw [hm₀def, hνlow]
      positivity
    positivity
  have hbb0 : 0 ≤ bb := by positivity
  have hsmallV : 2 * bb < θ := nvel
  have hcover : ∀ p ∈ E, code p ∈ cubeCodes hm := fun p hp =>
    cellCode_mem_cubeCodes hhm (hzo_cube p hp)
  have hvcap : ∀ qq ∈ cubeCodes hm, ∀ c' : ℝ,
      cfg.ρ k {p | p ∈ E ∧ code p = qq ∧ |cfg.b k p.1 3 - c'| ≤ rv / 2} ≤ ENNReal.ofReal bb := by
    intro qq _ c'
    set v₁ : ℤ := ⌊(c' - rv / 2) / rv⌋
    have hsub : {p | p ∈ E ∧ code p = qq ∧ |cfg.b k p.1 3 - c'| ≤ rv / 2} ⊆
        {p | p ∈ E ∧ code p = qq ∧ p ∈ {p : α × ℝ | ⌊cfg.b k p.1 3 / rv⌋ = v₁}} ∪
          {p | p ∈ E ∧ code p = qq ∧ p ∈ {p : α × ℝ | ⌊cfg.b k p.1 3 / rv⌋ = v₁ + 1}} := by
      intro p ⟨hpE, hpq, hpv⟩
      rcases floor_mem_pair hrv hpv with h1 | h1
      · exact Or.inl ⟨hpE, hpq, h1⟩
      · exact Or.inr ⟨hpE, hpq, h1⟩
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    calc _ ≤ ENNReal.ofReal (8 * (1 + 4 * H ^ 2) * C₀ * (K * rv ^ cfg.S)) +
          ENNReal.ofReal (8 * (1 + 4 * H ^ 2) * C₀ * (K * rv ^ cfg.S)) :=
          add_le_add (hfineA qq v₁) (hfineA qq (v₁ + 1))
      _ = ENNReal.ofReal bb := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), hbbdef]
        ring_nf
  obtain ⟨G', hG'm, hG'E, hG'mass, hheavy⟩ := Transfer.finite_velocity_cell_core (cfg.ρ k) code
    hcode_meas E hEm (cubeCodes hm) hcover (fun p => cfg.b k p.1 3) hθ0 hbb0 hsmallV hvcap
  -- Step 7: the filled set of the remaining cells
  set Hs : Finset (Fin 3 → ℤ) := (cubeCodes hm).filter (fun qq => ∃ p ∈ G', code p = qq)
    with hHs
  set Ecore : Set (Fin 3 → ℝ) := ⋃ qq ∈ Hs, cellBox hm qq with hEcore
  have hG'cells : ∀ p ∈ G', code p ∈ Hs := fun p hp =>
    Finset.mem_filter.mpr ⟨hcover p (hG'E hp), p, hp, rfl⟩
  have hG'le : cfg.ρ k G' ≤ Hs.card * ENNReal.ofReal (8 * (1 + 4 * H ^ 2) * C₀) := by
    refine measure_le_card_mul_of_codes (cfg.ρ k) G' code Hs hG'cells _ (fun qq _ => ?_)
    have hsub : {p | p ∈ G' ∧ code p = qq} ⊆ {p | p ∈ E ∧ code p = qq} :=
      fun p hp => ⟨hG'E hp.1, hp.2⟩
    exact (measure_mono hsub).trans (hfineP qq)
  have hEmass' : ENNReal.ofReal (m₀ / 18) ≤ cfg.ρ k E := by
    calc ENNReal.ofReal (m₀ / 18) = ENNReal.ofReal m₀ / 18 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 18), ENNReal.ofReal_ofNat]
      _ ≤ cfg.ρ k W / 18 := ENNReal.div_le_div_right hmassReal 18
      _ ≤ cfg.ρ k E := hEmass
  have hEreal : m₀ / 18 ≤ (cfg.ρ k).real E := by
    have := ENNReal.toReal_mono (measure_ne_top (cfg.ρ k) E) hEmass'
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hFcard : ((cubeCodes hm).card : ℝ) * θ ≤ m₀ / 36 := by
    have hc1 := card_cubeCodes hhm
    have hpow : (1 / hm + 1) ^ 3 * hm ^ 3 = (1 + hm) ^ 3 := by
      field_simp
    have h98 : (1 + hm) ^ 3 ≤ 2 := by
      have : 1 + hm ≤ 9 / 8 := by linarith
      calc (1 + hm) ^ 3 ≤ (9 / 8) ^ 3 := by gcongr
        _ ≤ 2 := by norm_num
    calc ((cubeCodes hm).card : ℝ) * θ ≤ (1 / hm + 1) ^ 3 * θ := by
          gcongr
      _ = (1 / hm + 1) ^ 3 * hm ^ 3 * (m₀ / (18 * 16)) := by rw [hθdef]; ring
      _ ≤ 2 * (m₀ / (18 * 16)) := by
          rw [hpow]; gcongr
      _ ≤ m₀ / 36 := by linarith only [hm₀0]
  have hG'real : m₀ / 36 ≤ (cfg.ρ k).real G' := by linarith only [hEreal, hG'mass, hFcard]
  have hcm0 : 0 < 8 * (1 + 4 * H ^ 2) * C₀ := by
    rw [hC₀]
    have : 0 < c ^ cfg.d := Real.rpow_pos_of_pos hc _
    positivity
  have hHs_card : m₀ / 36 ≤ (Hs.card : ℝ) * (8 * (1 + 4 * H ^ 2) * C₀) := by
    refine hG'real.trans ?_
    have h1 := ENNReal.toReal_mono (by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_ne_top) hG'le
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at h1
    exact h1
  have hvolE : ENNReal.ofReal Λ⁻¹ ≤ volume Ecore := by
    rw [hEcore, volume_biUnion_cellBox hhm Hs, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    refine nvol.trans ?_
    rw [div_le_iff₀ hcm0]
    have := mul_le_mul_of_nonneg_right hHs_card (by positivity : (0 : ℝ) ≤ hm ^ 3)
    calc m₀ / 36 * hm ^ 3 ≤ (Hs.card : ℝ) * (8 * (1 + 4 * H ^ 2) * C₀) * hm ^ 3 := this
      _ = (Hs.card : ℝ) * hm ^ 3 * (8 * (1 + 4 * H ^ 2) * C₀) := by ring
  -- Step 8: the affine-sheet core in the normalized cube
  have hhat : (D.hatTest G).totalDegree ≤ 2 := (D.hatTest_degree G).trans hGdeg
  set S : Set (Fin 6 → ℝ) := {bl | ∃ p ∈ E, bl = D.normLine (cfg.b k p.1)} with hSdef
  have hEne : E.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, measure_empty] at hEmass'
    have : 0 < m₀ / 18 := by
      have : 0 < m₀ := by rw [hm₀def, hνlow]; positivity
      positivity
    exact absurd hEmass' (not_le.mpr (ENNReal.ofReal_pos.mpr this))
  obtain ⟨pE, hpE⟩ := hEne
  have hKv : K / (8 * Bz) ≤ Λ := by
    have : K / (8 * Bz) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [h2KBz, hK]
    linarith only [this, hΛ]
  have hHinv : Λ⁻¹ ≤ H⁻¹ := inv_anti₀ hH0 nH
  have hT : ∀ bl ∈ S, (∀ σ ∈ Icc (0 : ℝ) 1, |testVal (testAlpha (D.hatTest G))
        (testBeta (D.hatTest G)) (testGamma (D.hatTest G)) bl σ| ≤ Λ ∧
        |testDer (testAlpha (D.hatTest G)) (testBeta (D.hatTest G)) bl σ| ≤ Λ) ∧
      (∀ σ ∈ Icc (0 : ℝ) 1, lineP bl σ ∈ Icc (0 : Fin 3 → ℝ) 1) ∧
      ∃ σe ∈ Icc (0 : ℝ) 1, Λ⁻¹ ≤ |testDer (testAlpha (D.hatTest G)) (testBeta (D.hatTest G)) bl σe| := by
    rintro bl ⟨p, hp, rfl⟩
    have hlf := hLF p hp
    refine ⟨fun σ hσ => ⟨(hlf.fit σ hσ).1.trans nH, (hlf.fit σ hσ).2.trans nH⟩, hlf.cube,
      _, hlf.obs, hHinv.trans hlf.event⟩
  have hEc : Ecore ⊆ Icc (0 : Fin 3 → ℝ) 1 := by
    intro z hz
    rw [hEcore] at hz
    obtain ⟨qq, hqq, hzq⟩ := mem_iUnion₂.mp hz
    obtain ⟨-, p, hp, hpq⟩ := Finset.mem_filter.mp hqq
    have hzp : zo p ∈ cellBox hm qq := by rw [← hpq]; exact mem_cellBox_cellCode hm (zo p)
    exact cellBox_subset_cube hhm hzp (fun m => (hzo_in p (hG'E hp) m).1)
      (fun m => (hzo_in p (hG'E hp) m).2) hzq
  have hwit : ∀ z ∈ Ecore, ∃ b₁ ∈ S, ∃ b₂ ∈ S, ∃ b₃ ∈ S,
      ∃ σ₁ ∈ Icc (0 : ℝ) 1, ∃ σ₂ ∈ Icc (0 : ℝ) 1, ∃ σ₃ ∈ Icc (0 : ℝ) 1,
        l1dist (lineP b₁ σ₁) z ≤ 3 * hm ∧ l1dist (lineP b₂ σ₂) z ≤ 3 * hm ∧
        l1dist (lineP b₃ σ₃) z ≤ 3 * hm ∧
        Λ⁻¹ ≤ |b₁ 3 - b₂ 3| ∧ Λ⁻¹ ≤ |b₁ 3 - b₃ 3| ∧ Λ⁻¹ ≤ |b₂ 3 - b₃ 3| ∧
        Λ⁻¹ ≤ |testDer (testAlpha (D.hatTest G)) (testBeta (D.hatTest G)) b₁ σ₁| := by
    intro z hz
    rw [hEcore] at hz
    obtain ⟨qq, hqq, hzq⟩ := mem_iUnion₂.mp hz
    obtain ⟨-, p, hp, hpq⟩ := Finset.mem_filter.mp hqq
    obtain ⟨-, p₀, hp₀, p₁, hp₁, p₂, hp₂, hc₀, hc₁, hc₂, hs01, hs02, hs12⟩ :=
      hheavy qq ⟨p, hp, hpq⟩
    have hin : ∀ p' ∈ G', code p' = qq →
        l1dist (lineP (D.normLine (cfg.b k p'.1)) ((p'.2 - t₀) / q)) z ≤ 3 * hm := by
      intro p' hp' hc'
      rw [hzoP p' (hG'E hp')]
      have hzp : zo p' ∈ cellBox hm qq := by rw [← hc']; exact mem_cellBox_cellCode hm (zo p')
      exact l1dist_le_of_mem_cellBox hhm hzp hzq
    have hsep : ∀ p' p'' : α × ℝ, rv / 2 < |cfg.b k p'.1 3 - cfg.b k p''.1 3| →
        Λ⁻¹ ≤ |D.normLine (cfg.b k p'.1) 3 - D.normLine (cfg.b k p''.1) 3| := by
      intro p' p'' hpp
      rw [D.normLine_velocity, D.normLine_velocity, ← sub_div, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < 8 * D.B)]
      refine nsep.trans ?_
      apply div_le_div_of_nonneg_right hpp.le (by positivity)
    refine ⟨_, ⟨p₀, hG'E hp₀, rfl⟩, _, ⟨p₁, hG'E hp₁, rfl⟩, _, ⟨p₂, hG'E hp₂, rfl⟩,
      _, (hLF p₀ (hG'E hp₀)).obs, _, (hLF p₁ (hG'E hp₁)).obs, _, (hLF p₂ (hG'E hp₂)).obs,
      hin p₀ hp₀ hc₀, hin p₁ hp₁ hc₁, hin p₂ hp₂ hc₂, hsep p₀ p₁ hs01, hsep p₀ p₂ hs02,
      hsep p₁ p₂ hs12, hHinv.trans (hLF p₀ (hG'E hp₀)).event⟩
  obtain ⟨a₁, a₂, v₁, v₂, hbr⟩ := core_two_branches Cs hCs hCs0 (testAlpha (D.hatTest G))
    (testBeta (D.hatTest G)) (testGamma (D.hatTest G)) (testBeta_degree _ hhat)
    (testGamma_degree _ hhat) Λ εc (3 * hm) S S Ecore hΛ
    (((hLF pE hpE).alpha).trans nH)
    (fun bl hbl => (hT bl hbl).1) (fun bl hbl => (hT bl hbl).2.1)
    (by rintro bl ⟨p, hp, rfl⟩; exact (hLF p hp).con)
    (by rintro bl ⟨p, hp, rfl⟩; exact (hLF p hp).vel.trans hKv)
    hEc hvolE hwit ncon (by positivity) ns1 ns2 ns3 hT
  -- Step 9: the heavier branch, pulled back to an original affine predictor
  set branch : ℝ → (Fin 3 → ℝ) → Set (α × ℝ) := fun a vv => {p | p ∈ E ∧
    ∀ σ ∈ Icc (0 : ℝ) 1, |lineW (D.normLine (cfg.b k p.1)) σ -
      affineFn a vv (lineP (D.normLine (cfg.b k p.1)) σ)| ≤ coreLoss Cs Λ} with hbranch
  have hcover12 : E ⊆ branch a₁ v₁ ∪ branch a₂ v₂ := by
    intro p hp
    rcases hbr _ ⟨p, hp, rfl⟩ with h1 | h2
    · exact Or.inl ⟨hp, h1⟩
    · exact Or.inr ⟨hp, h2⟩
  have hfinE : cfg.ρ k E ≠ ⊤ := measure_ne_top _ _
  have hpick : ∃ (a : ℝ) (vv : Fin 3 → ℝ), cfg.ρ k E / 2 ≤ cfg.ρ k (branch a vv) := by
    by_cases h1 : cfg.ρ k E / 2 ≤ cfg.ρ k (branch a₁ v₁)
    · exact ⟨a₁, v₁, h1⟩
    · refine ⟨a₂, v₂, ?_⟩
      have h1' : cfg.ρ k (branch a₁ v₁) < cfg.ρ k E / 2 := lt_of_not_ge h1
      have h2 : cfg.ρ k E ≤ cfg.ρ k (branch a₁ v₁) + cfg.ρ k (branch a₂ v₂) :=
        (measure_mono hcover12).trans (measure_union_le _ _)
      by_contra h3
      have h3' : cfg.ρ k (branch a₂ v₂) < cfg.ρ k E / 2 := lt_of_not_ge h3
      have := h2.trans_lt (ENNReal.add_lt_add h1' h3')
      rw [ENNReal.add_halves] at this
      exact lt_irrefl _ this
  obtain ⟨a, vv, hav⟩ := hpick
  set Lf : Fin 4 → ℝ := D.pullAffine a vv with hLf
  set closeSet : Set (α × ℝ) := {p | ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
    |eval (cfg.x k p.1 t) (affineBase Lf) - cfg.x k p.1 t 3| ≤ c * coreLoss Cs Λ} with hclose
  have hIeq : I (cfg.T k s) (cfg.j k s i) = Icc t₀ (t₀ + q) := I_eq_Icc _ _
  have hbranch_close : branch a vv ⊆ closeSet := by
    intro p ⟨hpE, hpb⟩ t ht
    rw [hIeq] at ht
    set σ := (t - t₀) / q with hσ
    have hσ01 : σ ∈ Icc (0 : ℝ) 1 := by
      rw [hσ]
      constructor
      · exact div_nonneg (by linarith only [ht.1]) hq.le
      · rw [div_le_one hq]; linarith only [ht.2]
    have htσ : D.t₀ + D.q * σ = t := by
      change t₀ + q * ((t - t₀) / q) = t
      field_simp; ring
    have h1 := hpb σ hσ01
    rw [D.normLine_lineW hDq, D.normLine_lineP hDq hDB, htσ] at h1
    rw [D.eval_pullAffine]
    have hx3 : (fun m : Fin 3 => cfg.x k p.1 t m.castSucc) = basePt (cfg.b k p.1) t := by
      rw [← x_castSucc]; rfl
    have hbp : (![cfg.x k p.1 t 0, cfg.x k p.1 t 1, cfg.x k p.1 t 2] : Fin 3 → ℝ) =
        basePt (cfg.b k p.1) t := by
      funext m; fin_cases m <;> rfl
    rw [hbp]
    have hpt : point (cfg.b k p.1) t = cfg.x k p.1 t := rfl
    rw [hpt] at h1
    have e : eval (cfg.x k p.1 t) (affineBase D.L') + D.c * affineFn a vv
        (D.normBase (basePt (cfg.b k p.1) t)) - cfg.x k p.1 t 3 =
        -(D.c * ((cfg.x k p.1 t 3 - eval (cfg.x k p.1 t) (affineBase D.L')) / D.c -
          affineFn a vv (D.normBase (basePt (cfg.b k p.1) t)))) := by
      field_simp
      ring
    rw [e, abs_neg, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left h1 hc.le
  have hclose_meas : MeasurableSet closeSet := by
    have hbp : Measurable fun p : α × ℝ => cfg.b k p.1 := hb.comp measurable_fst
    have hcl : IsClosed {β : Fin 6 → ℝ | ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |eval (point β t) (affineBase Lf) - point β t 3| ≤ c * coreLoss Cs Λ} := by
      have e : {β : Fin 6 → ℝ | ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
          |eval (point β t) (affineBase Lf) - point β t 3| ≤ c * coreLoss Cs Λ} =
          ⋂ t ∈ I (cfg.T k s) (cfg.j k s i), {β : Fin 6 → ℝ |
            |eval (point β t) (affineBase Lf) - point β t 3| ≤ c * coreLoss Cs Λ} := by
        ext β; simp only [mem_setOf_eq, mem_iInter]
      rw [e]
      refine isClosed_biInter fun t _ => ?_
      have hpc : Continuous fun β : Fin 6 → ℝ => point β t := by unfold point; fun_prop
      have h3 : Continuous fun β : Fin 6 → ℝ => point β t 3 := (continuous_apply 3).comp hpc
      have he : Continuous fun β : Fin 6 → ℝ => eval (point β t) (affineBase Lf) :=
        (MvPolynomial.continuous_eval _).comp hpc
      exact isClosed_le (continuous_abs.comp (he.sub h3)) continuous_const
    have := hbp hcl.measurableSet
    exact this
  set W' : Set (α × ℝ) := E ∩ closeSet with hW'
  have hW'm : MeasurableSet W' := hEm.inter hclose_meas
  have hbranchW' : branch a vv ⊆ W' := fun p hp => ⟨hp.1, hbranch_close hp⟩
  refine ⟨(cfg.ρ k).restrict W', Lf, Measure.restrict_le_self, ?_, ?_⟩
  · rw [Measure.restrict_apply_univ]
    refine le_trans ?_ (hav.trans (measure_mono hbranchW'))
    calc ENNReal.ofReal (N ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i)
        = ENNReal.ofReal (N ^ (-cfg.d * v - ε) * q) * cfg.ν k (cfg.A k s i) := by
          rw [div_eq_mul_inv]
      _ ≤ ENNReal.ofReal (N ^ (-cfg.d * v - η) * q / 36) * cfg.ν k (cfg.A k s i) := by
          gcongr
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 36)]
          have h1 := mul_le_mul_of_nonneg_right nfinm hq.le
          calc N ^ (-cfg.d * v - ε) * q * 36 = 36 * N ^ (-cfg.d * v - ε) * q := by ring
            _ ≤ N ^ (-cfg.d * v - η) * q := h1
      _ = ENNReal.ofReal (N ^ (-cfg.d * v - η) * q) * cfg.ν k (cfg.A k s i) / 18 / 2 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 36), ENNReal.ofReal_ofNat,
            ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
            ← mul_assoc, ← mul_assoc, ← ENNReal.mul_inv (by norm_num) (by norm_num)]
          norm_num
      _ ≤ cfg.ρ k W / 18 / 2 := ENNReal.div_le_div_right (ENNReal.div_le_div_right hmassW' 18) 2
      _ ≤ cfg.ρ k E / 2 := ENNReal.div_le_div_right hEmass 2
  · refine ae_restrict_of_forall_mem hW'm fun p hp => ?_
    have hpW := hEW hp.1
    exact ⟨hpW.1, hpW.2.1, fun t ht => (hp.2 t ht).trans nfin⟩

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
