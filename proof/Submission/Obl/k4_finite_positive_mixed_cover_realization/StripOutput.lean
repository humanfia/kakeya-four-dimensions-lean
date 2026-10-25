import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripLists
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripMass
import Submission.Obl.k4_finite_positive_mixed_cover_realization.CodedFamilies

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

open Classical in
/-- A substantial aligned original witness gives the complete frozen width
output. The output labels are parent/parameter/midpoint codes, and every
remaining complexity, frame and list bound is displayed explicitly. -/
theorem CoverData.Valid.strip_output
    {W m Mp Dp Mg Dg Mold Mr j : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε width gap Δ τ saving : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 2 ≤ Nk) (hMp : Mp ≤ Mold) (hMg : Mg ≤ Mold)
    (hκ : p.κ ≤ Nk) (hT : (2 : ℝ) ^ p.T c.level ≤ Nk ^ Mold)
    (hB : ∀ w, 0 ≤ B w) (hwidth : 0 < width) (hwidth1 : width ≤ 1)
    (hinv : width⁻¹ ≤ Nk ^ Mr)
    (hfit : Nk ^ (4 * ρ * c.gain * L + 4 * ε) * Nk ^ (-c.gain * L) ≤ width)
    (hgap : gap ≤ width) (hrj : 0 ≤ p.r j) (hrjL : p.r j ≤ L)
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    (hdepth : p.r c.level + Δ * L ≤ L)
    (hfactor : p.κ * (5 + 6 * p.κ) * width ≤ Nk ^ (-saving))
    (hsaving : δ₀ * L + Δ * L ≤ saving)
    (hslack : 1242 * p.κ ^ 2 ≤ Nk ^ τ)
    (hmass : ENNReal.ofReal (Nk ^ (-τ)) ≤ ∑ a : Fin c.n,
      ENNReal.ofReal (ω (p.world (c.old a))) * ((ν (p.world (c.old a))).prod volume)
        (c.alignedWitness normal bias gap j a)) :
    Output Nk L W ω ν E B κ₁ Δ m p.r p.T p.nw
      ((2 * Mold + Mr + 8) + (Mg + Mr + 4)) (max Dp (max Dg 1)) τ := by
  classical
  let I := c.UsedStripPiece width
  let J := c.usedStripKeys width
  let code : I → J := fun q => ⟨c.stripKey width q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩
  have hcode : Function.Surjective code := by
    intro key
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp key.property
    exact ⟨q, Subtype.ext hq⟩
  have hlevel (key : J) : p.lev key.val.1 = c.level := by
    obtain ⟨q, hq⟩ := hcode key
    rw [← hq]
    exact hc.old_level q.val.1
  let outBin : J → Fin (2 ^ p.T c.level) := fun key => ⟨p.bin key.val.1, by
    have hk := hp.label_bin key.val.1
    rwa [hlevel key] at hk⟩
  let e := Fintype.equivFin I
  let codeF : Fin (Fintype.card I) → J := code ∘ e.symm
  have hcodeF : Function.Surjective codeF := hcode.comp e.symm.surjective
  have hN1 : 1 ≤ Nk := by linarith
  have hκ0 : 0 < p.κ := by linarith [hp.one_le_slack]
  have hchartSlack : 32 * p.κ ^ 2 ≤ Nk ^ τ :=
    (show 32 * p.κ ^ 2 ≤ 1242 * p.κ ^ 2 by nlinarith [sq_nonneg p.κ]).trans hslack
  have hcharts (q : I) :
      gchart Nk (2 * Mold + Mr + 8) (max Dp (max Dg 1)) (Nk ^ τ)
        (p.T c.level) ((outBin (code q) : ℕ) : ℝ) (p.r c.level)
        (B (p.world (code q).val.1)) (E (p.world (code q).val.1))
        (c.stripNewCenter width (code q).val) (c.stripNewVelocity width (code q).val)
        (c.stripNewFrame width (code q).val) (p.test (code q).val.1)
        (c.stripPiece width q.val.1 q.val.2.val)
        (c.pieceIncidence width gap j normal bias q.val.1 q.val.2.val) True := by
    have hq := hc.stripPiece_chart (gap := gap) ht hp hNk hMp hMg hκ hT hB hwidth hwidth1 hinv hfit
      j normal bias q.val.1 q.val.2.val q.property
    have hq' := gchart_mono hq hN1 le_rfl le_rfl (show 0 < 32 * p.κ ^ 2 by positivity)
      hchartSlack (hB _) id
    exact hq'
  have hwidthOut (key : J) :
      |(c.stripNewFrame width key.val).det| * (4 : ℝ) ^ p.T c.level ≤
        Nk ^ (-(p.nw c.level + Δ * L)) := by
    have hn := hc.representative_unit ht (width := width) key.val.1 key.val.2.1
    have hOld := (hp.narrowness key.val.1).2
    rw [hlevel key] at hOld
    have hOld' : |(p.frame key.val.1).det| * (4 : ℝ) ^ p.T c.level ≤
        Nk ^ (-p.nw c.level + δ₀ * L) := by
      convert hOld using 1 <;> congr 1 <;> ring
    exact composed_strip_width_gain (p.frame key.val.1) (p.T c.level)
      hN1 hκ0 (show 0 ≤ 4 + 6 * p.κ by linarith) hwidth
      ((planePerp_norm _).trans hn) hn (planePerp_inner _) hOld'
      (by convert hfactor using 1 <;> congr 1 <;> ring) hsaving
  have hcount : (Fintype.card I : ℝ) ≤ Nk ^ (Mg + Mr + 4) :=
    hc.usedStripPiece_count ht hp hNk hwidth hκ hinv
  have hmassPieces : ENNReal.ofReal (Nk ^ (-τ)) ≤ ∑ q : I,
      ENNReal.ofReal (ω (p.world (c.old q.val.1))) *
        ((ν (p.world (c.old q.val.1))).prod volume)
          (c.pieceIncidence width gap j normal bias q.val.1 q.val.2.val) :=
    hmass.trans (hc.stripPieces_mass ht hp hwidth normal bias)
  change XOutput (fun _ => W) (fun _ => ω) (fun _ => ν) (fun _ => E) (fun _ => B)
    (fun _ => Nk) L Δ κ₁ m p.r p.T p.nw
    ((2 * Mold + Mr + 8) + (Mg + Mr + 4)) (max Dp (max Dg 1)) τ 0
  apply xOutput_of_coded_strips codeF hcodeF (fun key => p.world key.val.1) outBin
    (fun key => c.stripNewCenter width key.val) (fun key => c.stripNewVelocity width key.val)
    (fun key => c.stripNewFrame width key.val) (fun key => p.test key.val.1)
    (fun b => c.stripPiece width (e.symm b).val.1 (e.symm b).val.2.val)
    (fun b => c.pieceIncidence width gap j normal bias (e.symm b).val.1 (e.symm b).val.2.val)
    (c.stripLists Nk L width j normal bias) hN1 hc.1 hdepth hcount hwidthOut
  · intro b b' hne hw hj
    have hneq : ((e.symm b).val.1, (e.symm b).val.2.val) ≠
        ((e.symm b').val.1, (e.symm b').val.2.val) := by
      intro heq
      exact hne (e.symm.injective (c.usedStripPiece_raw_injective width heq))
    apply hc.stripPieces_disjoint ht hp (width := width) _ _ _ _ hneq
    · exact hw
    · exact congrArg Fin.val hj
  · intro w o
    exact (CoverData.Valid.stripLists_count (c := c) hp j normal bias w o).trans hslack
  · intro b
    exact hcharts (e.symm b)
  · intro b v hv
    exact hc.stripPiece_known ht hp j normal bias hN1 hrj hrjL hwidth hgap hfit
      (e.symm b).val.1 (e.symm b).val.2.val (codeF b) rfl hv
  · exact hmassPieces.trans_eq (Fintype.sum_equiv e _ _ (fun q => by
      simp only [codeF, code, CoverData.stripKey, Function.comp_apply, Equiv.symm_apply_apply]))

end Submission.Obl.k4_finite_positive_mixed_cover_realization
