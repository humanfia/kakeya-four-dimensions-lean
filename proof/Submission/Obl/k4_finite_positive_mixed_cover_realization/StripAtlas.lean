import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripBins
import Submission.Obl.k4_finite_positive_mixed_cover_realization.ActualPairCharge

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface Submission.Lib.K4VelocityStrips
open Submission.Obl.k4_finite_forest_width_selection
open Submission.Obl.k4_native_finite_terminal_atlas_lift
open scoped RealInnerProductSpace

noncomputable def planePerp (n : Plane) : Plane := WithLp.toLp 2 ![-n 1, n 0]

lemma planePerp_norm (n : Plane) : ‖planePerp n‖ = ‖n‖ := by
  have hsq : ‖planePerp n‖ ^ 2 = ‖n‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, planePerp, Fin.sum_univ_two, add_comm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma planePerp_inner (n : Plane) : inner ℝ (planePerp n) n = 0 := by
  simp [planePerp, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The output incidences are defined by original finite-format chart sets and
a constant alignment table. Analytical witness masks do not enter this set. -/
def CoverData.pieceIncidence {W : ℕ} {p : PathData W} (c : CoverData p)
    (width gap : ℝ) (j : ℕ) (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    (a : Fin c.n) (z : ℤ) : Set Incidence :=
  {v | (v ∈ p.counted (c.old a) ∧ v.1 ∈ c.stripPiece width a z) ∧
    ∃ d : Fin p.C, (p.lev d = j ∧ p.world d = p.world (c.old a) ∧
      forestAncestor p.lev p.par d c.level = c.old a ∧ c.Aligned normal bias gap a d) ∧
      v ∈ p.counted d}

noncomputable def CoverData.stripNewCenter {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) (key : Fin p.C × UnitStripCode) : Plane :=
  let q := ((2 : ℝ) ^ p.T c.level)⁻¹
  let repr := c.stripRepresentative width key.1 key.2.1
  compositeCenter ((p.bin key.1 : ℝ) / (2 : ℝ) ^ p.T c.level) q
    (p.center key.1) (stripCenter repr.1 ((key.2.2 : ℝ) * width) repr.2)
    (p.velocity key.1) (stripVelocity repr.1 repr.2) (p.frame key.1)

noncomputable def CoverData.stripNewVelocity {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) (key : Fin p.C × UnitStripCode) : Plane :=
  let repr := c.stripRepresentative width key.1 key.2.1
  compositeVelocity (((2 : ℝ) ^ p.T c.level)⁻¹) (p.velocity key.1)
    (stripVelocity repr.1 repr.2) (p.frame key.1)

noncomputable def CoverData.stripNewFrame {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) (key : Fin p.C × UnitStripCode) : Frame :=
  let repr := c.stripRepresentative width key.1 key.2.1
  p.frame key.1 * stripLocalFrame p.κ (4 + 6 * p.κ) width (planePerp repr.1) repr.1

section
variable {W m Mp Dp Mg Dg : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε width gap : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (j : ℕ) (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)

include hc hp

lemma CoverData.Valid.pieceIncidence_format (a : Fin c.n) (z : ℤ) (q : ℕ) :
    gfmt 7 (Nk ^ Mp + (Nk ^ Mg + 2) + p.C * Nk ^ Mp)
      (max (max Dp (max Dg 1)) Dp)
      {x : Fin 7 → ℝ | ((q, fun e : Fin 6 => x e.castSucc), x 6) ∈
        c.pieceIncidence width gap j normal bias a z} := by
  exact strip_aligned_incidence_format p.counted
    (fun q => ((hp.chart (c.old a)).2.2.2.2.2.2.2.2.1 q).2)
    (hc.stripPiece_format a z)
    (fun d q => ((hp.chart d).2.2.2.2.2.2.2.2.1 q).2) _ q

lemma CoverData.Valid.pieceIncidence_measurable (a : Fin c.n) (z : ℤ) :
    MeasurableSet (c.pieceIncidence width gap j normal bias a z) := by
  have hOld : MeasurableSet (p.counted (c.old a)) := (hp.chart (c.old a)).2.2.2.2.2.2.2.1
  have hDeep : MeasurableSet {v : Incidence | ∃ d : Fin p.C,
      (p.lev d = j ∧ p.world d = p.world (c.old a) ∧
        forestAncestor p.lev p.par d c.level = c.old a ∧ c.Aligned normal bias gap a d) ∧
          v ∈ p.counted d} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro d
    by_cases hd : p.lev d = j ∧ p.world d = p.world (c.old a) ∧
        forestAncestor p.lev p.par d c.level = c.old a ∧ c.Aligned normal bias gap a d
    · have heq : {v : Incidence | (p.lev d = j ∧ p.world d = p.world (c.old a) ∧
          forestAncestor p.lev p.par d c.level = c.old a ∧ c.Aligned normal bias gap a d) ∧
            v ∈ p.counted d} = p.counted d := by ext v; exact ⟨And.right, fun hv => ⟨hd, hv⟩⟩
      rw [heq]
      exact (hp.chart d).2.2.2.2.2.2.2.1
    · have heq : {v : Incidence | (p.lev d = j ∧ p.world d = p.world (c.old a) ∧
          forestAncestor p.lev p.par d c.level = c.old a ∧ c.Aligned normal bias gap a d) ∧
            v ∈ p.counted d} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun v hv => hd hv.1
      rw [heq]
      exact MeasurableSet.empty
  exact (hOld.inter ((hc.stripPiece_measurable a z).preimage measurable_fst)).inter hDeep

end

/-- The finite sign-format cost is polynomial before any requested slack is
chosen. No candidate count enters the geometric chart slack. -/
lemma strip_format_budget {Nk : ℝ} {Mp Mg Mold Mr C : ℕ}
    (hNk : 2 ≤ Nk) (hMp : Mp ≤ Mold) (hMg : Mg ≤ Mold) (hC : (C : ℝ) ≤ Nk ^ Mp) :
    Nk ^ Mp + (Nk ^ Mg + 2) + C * Nk ^ Mp ≤ Nk ^ (2 * Mold + Mr + 8) := by
  have hN1 : 1 ≤ Nk := by linarith
  have hX : 1 ≤ Nk ^ (2 * Mold) := one_le_pow₀ hN1
  have hM : Nk ^ Mp ≤ Nk ^ Mold := pow_le_pow_right₀ hN1 hMp
  have h2Mp : Nk ^ Mp ≤ Nk ^ (2 * Mold) := pow_le_pow_right₀ hN1 (by omega)
  have h2Mg : Nk ^ Mg ≤ Nk ^ (2 * Mold) := pow_le_pow_right₀ hN1 (by omega)
  have hprod : (C : ℝ) * Nk ^ Mp ≤ Nk ^ (2 * Mold) := by
    apply (mul_le_mul (hC.trans hM) hM (by positivity) (by positivity)).trans_eq
    rw [two_mul, pow_add]
  have h8 : 5 ≤ Nk ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hNk 3
    norm_num at h
    linarith
  calc
    _ ≤ 5 * Nk ^ (2 * Mold) := by linarith
    _ ≤ Nk ^ 3 * Nk ^ (2 * Mold) := mul_le_mul_of_nonneg_right h8 (by positivity)
    _ = Nk ^ (2 * Mold + 3) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)

/-- One nonempty midpoint piece gives a true narrowed chart, retaining the old
quadratic test and time block. The geometric slack is only 32 times the square
of the incoming path slack. -/
theorem CoverData.Valid.stripPiece_chart
    {W m Mp Dp Mg Dg Mold Mr : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε width gap : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 2 ≤ Nk) (hMp : Mp ≤ Mold) (hMg : Mg ≤ Mold)
    (hκ : p.κ ≤ Nk) (hT : (2 : ℝ) ^ p.T c.level ≤ Nk ^ Mold)
    (hB : ∀ w, 0 ≤ B w) (hwidth : 0 < width) (hwidth1 : width ≤ 1)
    (hinv : width⁻¹ ≤ Nk ^ Mr)
    (hfit : Nk ^ (4 * ρ * c.gain * L + 4 * ε) * Nk ^ (-c.gain * L) ≤ width)
    (j : ℕ) (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    (a : Fin c.n) (z : ℤ) (hne : (c.stripPiece width a z).Nonempty) :
    gchart Nk (2 * Mold + Mr + 8) (max Dp (max Dg 1)) (32 * p.κ ^ 2)
      (p.T c.level) (p.bin (c.old a) : ℝ) (p.r c.level)
      (B (p.world (c.old a))) (E (p.world (c.old a)))
      (c.stripNewCenter width (c.old a, (c.stripRow width a, z)))
      (c.stripNewVelocity width (c.old a, (c.stripRow width a, z)))
      (c.stripNewFrame width (c.old a, (c.stripRow width a, z)))
      (p.test (c.old a)) (c.stripPiece width a z)
      (c.pieceIncidence width gap j normal bias a z) True := by
  have hN1 : 1 ≤ Nk := by linarith
  have hκ0 : 0 < p.κ := by linarith [hp.one_le_slack]
  have hold0 := hp.chart (c.old a)
  rw [hc.old_level a] at hold0
  have hold : gchart Nk Mold Dp p.κ (p.T c.level) (p.bin (c.old a) : ℝ) (p.r c.level)
      (B (p.world (c.old a))) (E (p.world (c.old a))) (p.center (c.old a))
      (p.velocity (c.old a)) (p.frame (c.old a)) (p.test (c.old a))
      (p.assigned (c.old a)) (p.counted (c.old a)) True :=
    gchart_mono hold0 hN1 hMp le_rfl hκ0 le_rfl (hB _) id
  have hbin := hp.label_bin (c.old a)
  rw [hc.old_level a] at hbin
  have hbinR : (p.bin (c.old a) : ℝ) ≤ (2 : ℝ) ^ p.T c.level := by exact_mod_cast hbin.le
  have hn := hc.representative_unit ht (width := width) (c.old a) (c.stripRow width a)
  have hformat := strip_format_budget (Mr := Mr) hNk hMp hMg hp.count_le
  have hformatA : Nk ^ Mg + 2 ≤ Nk ^ (2 * Mold + Mr + 8) := by
    apply le_trans _ hformat
    have h0 : 0 ≤ Nk ^ Mp + (p.C : ℝ) * Nk ^ Mp := by positivity
    linarith
  have hchart := gchart_strip_path_slack
    (A' := c.stripPiece width a z) (F' := c.pieceIncidence width gap j normal bias a z)
    hold hNk hp.one_le_slack hκ
    (show Dp ≤ max Dp (max Dg 1) from le_max_left _ _) (hB _)
    (show 0 ≤ (p.bin (c.old a) : ℝ) by positivity) hbinR hT
    hwidth hwidth1 hinv ((planePerp_norm _).trans hn) hn (planePerp_inner _)
    (hc.stripPiece_center ht hp hwidth a z hne)
    (hc.representative_bias ht hp (hfit.trans hwidth1) (c.old a) (c.stripRow width a))
    (fun l hl => hc.representative_fit ht hp hwidth hfit a l hl.1)
    (fun l hl => stripMidpointBin_error hwidth hl.2)
    (fun l hl => hc.assigned_subset a hl.1)
    (fun v hv => hv.1.1) (fun v hv => hv.1.2)
    (hc.stripPiece_measurable a z) (hc.pieceIncidence_measurable hp j normal bias a z)
    (fun q => ⟨gfmt_mono hformatA (le_max_right _ _) (hc.stripPiece_format a z q),
      gfmt_mono hformat (by omega) (hc.pieceIncidence_format hp j normal bias a z q)⟩) trivial
  simpa only [CoverData.stripNewCenter, CoverData.stripNewVelocity, CoverData.stripNewFrame]
    using hchart

end Submission.Obl.k4_finite_positive_mixed_cover_realization
