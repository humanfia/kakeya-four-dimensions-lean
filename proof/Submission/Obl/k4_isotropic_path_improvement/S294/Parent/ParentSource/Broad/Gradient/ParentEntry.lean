-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentEntry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentEntry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentEntry.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreGradientEntry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentLipschitz

/-!
# A renewed original core entry for an independent physical parent

Adapted from o265 session x0946, `Broad/Gradient/CoreGradientEntry.lean`.
Only incidences on a prescribed measurable set of good original lines are used.
The entry law, pure cap and renewal cell laws retain their original normalization.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- **Lipschitz bound on a renewed core entry.** -/
theorem CoreEntryData.parent_lipschitz_of_renewal
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (a : Fin V.count)
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a)
      (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (ii : ↥C.codes × Bool) (hii : (C.raw ii).Nonempty)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (old : Fin p.C) (hγ : p.γ b = p.γ old)
    (P : Poly) (hP : P.totalDegree ≤ 2)
    (hwidth : δ (d.N k) (p.r (p.lev b)) ≤ 1)
    (hFineOld : p.F b ⊆ p.F old)
    (good : Set Line) (hgoodm : MeasurableSet good)
    {M : ℝ} (hM : 0 ≤ M)
    (hparentJets : ∀ z ∈ C.raw ii ∩ Prod.fst ⁻¹' good,
      |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 P)| ≤ K * d.B k (p.γ b) ∧
      |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤
        K * d.B k (p.γ b) ^ 2)
    (hmotion : ∀ z ∈ C.raw ii ∩ Prod.fst ⁻¹' good,
      ∀ z' ∈ C.raw ii ∩ Prod.fst ⁻¹' good, z'.1 = z.1 →
      |MvPolynomial.eval (xp z'.1 z'.2) P - MvPolynomial.eval (xp z.1 z.2) P| ≤
        M * |z'.2 - z.2|)
    {Kc width θrow fraction : ℝ} {qc : ℕ} (hKc : 2 * K ^ (qcore + 7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc ^ qc)⁻¹ ≤ width)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1)
    {δref : ENNReal} (hβ1 : δref⁻¹ * ENNReal.ofReal (8 * fraction) < 1)
    (keep : Set Event) (hkeep : MeasurableSet keep)
    (hbreadth : ∀ (label : Fin 3 → ℤ) (n center : EuclideanSpace ℝ (Fin 2)), ‖n‖ = 1 →
      ((((d.ν k (p.γ old)).prod volume).restrict
          (coreLongRows p b K R (C.raw ii ∩ Prod.fst ⁻¹' good) θrow)).restrict keep)
        {x | renewalCellCode Kc J qc
            (packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center ii.1.1) x) = label ∧
          |inner ℝ n (packetCubeVelocity p b x.1 - center)| ≤ width} ≤
        (δref⁻¹ * ENNReal.ofReal (8 * fraction)) *
          ((((d.ν k (p.γ old)).prod volume).restrict
            (coreLongRows p b K R (C.raw ii ∩ Prod.fst ⁻¹' good) θrow)).restrict keep)
            {x | renewalCellCode Kc J qc
              (packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center ii.1.1) x) = label})
    (hgood : ENNReal.ofReal ((K ^ qcore)⁻¹ / 2) ≤
      V.entryLaw b a (coreLongRows p b K R (C.raw ii ∩ Prod.fst ⁻¹' good) θrow ∩ keep)) :
    ∀ z ∈ C.raw ii ∩ Prod.fst ⁻¹' good, ∀ z' ∈ C.raw ii ∩ Prod.fst ⁻¹' good,
      |MvPolynomial.eval (xp z.1 z.2) P -
          MvPolynomial.eval (xp z'.1 z'.2) P| ≤
        (2 + coreGradientCoeff (2 * K ^ (qcore + 7)) width θrow J / 2) *
            (K ^ 14 * (K ^ 6)⁻¹ * δ (d.N k) (p.r (p.lev b))) +
          M / 2 * coreGradientCoeff (2 * K ^ (qcore + 7)) width θrow J *
            (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
            ((2 : ℝ) ^ p.T (p.lev old))⁻¹ *
            ‖packetBase p old z - packetBase p old z'‖ := by
  classical
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  have hKtwo : 2 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hεpos : 0 < (K ^ 6)⁻¹ := by positivity
  -- the core and its long rows
  let U := C.raw ii ∩ Prod.fst ⁻¹' good
  let Ul := coreLongRows p b K R U θrow
  let Z := packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center ii.1.1)
  let code : Event → (Fin 3 → ℤ) := fun x => renewalCellCode Kc J qc (Z x)
  have hZ : Measurable Z :=
    (((measurable_nativeBase.comp (measurable_packetNativeCubePoint (d.N k) (d.B k) p b)).sub_const
      (C.center ii.1.1)).const_smul (K ^ R))
  have hcode : Measurable code := (measurable_renewalCellCode Kc J qc).comp hZ
  have hUm : MeasurableSet U := (C.measurable ii).1.inter (hgoodm.preimage measurable_fst)
  have hUlm : MeasurableSet Ul := measurableSet_coreLongRows p b K R hUm θrow
  have hUlU : Ul ⊆ U := fun x hx => hx.1
  have hU : ∀ z ∈ U, CoreIncidence (d.N k) (d.B k) p old b K (K ^ 6)⁻¹ R (V.center a)
      (C.center ii.1.1) (C.sheet ii) z := by
    intro z hz
    have hzV := (C.subset ii).2 hz.1
    have hzF := ((V.subset b a).2 hzV).2
    have hc := C.points ii z hz.1
    exact ⟨hzF, hFineOld hzF, V.value b a z hzV, hc.1, hc.2.2⟩
  have hbranch := C.branch ii hii
  -- the renewed law, the norming law and the cell laws
  let ρk := (((d.ν k (p.γ old)).prod volume).restrict Ul).restrict keep
  have hρk (S : Set Event) : ρk S = ((d.ν k (p.γ old)).prod volume) (S ∩ keep ∩ Ul) := by
    simp only [ρk]
    rw [Measure.restrict_apply' hkeep, Measure.restrict_apply' hUlm]
  let ref : ENNReal := d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹)
  let μ₀ := (V.entryLaw b a).restrict (Ul ∩ keep)
  have hμ₀le (S : Set Event) : μ₀ S ≤ ref⁻¹ * ρk S := by
    simp only [μ₀]
    rw [Measure.restrict_apply' (hUlm.inter hkeep), ValueBranchData.entryLaw, Measure.smul_apply,
      smul_eq_mul, Measure.restrict_apply' (V.measurable b a).1, hρk, ← hγ]
    apply mul_le_mul' le_rfl
    apply measure_mono
    intro x hx
    exact ⟨⟨hx.1.1, hx.1.2.2⟩, hx.1.2.1⟩
  have hac : μ₀ ≪ ρk := by
    intro S hS
    have hh := hμ₀le S
    rw [hS, mul_zero] at hh
    exact le_antisymm hh zero_le
  -- the parameters of the renewal
  set A : ℝ := 2 * K ^ (qcore + 7) with hAdef
  have hA : 2 ≤ A := by
    have : (1 : ℝ) ≤ K ^ (qcore + 7) := one_le_pow₀ (by linarith)
    rw [hAdef]; linarith
  have hKc2 : 2 ≤ Kc := hA.trans hKc
  have hmass₀ : ENNReal.ofReal (K ^ 7 / A) ≤ μ₀ univ := by
    have heq : K ^ 7 / A = (K ^ qcore)⁻¹ / 2 := by
      rw [hAdef, pow_add]
      field_simp
    rw [heq]
    simpa only [μ₀, Measure.restrict_apply_univ] using hgood
  have hcap (S : Set Base) (hS : MeasurableSet S) :
      μ₀ (Z ⁻¹' S) ≤ ENNReal.ofReal (K ^ 7) * volume S := by
    have hmap := V.entryLaw_core_cap Q hpure hd hp hHE hHbase hK hmax hpower b hb hr hrL a
      (Ul ∩ keep) (C.center ii.1.1)
    rw [← Measure.map_apply hZ hS]
    simpa only [Measure.smul_apply, smul_eq_mul] using (Measure.le_iff.mp hmap S hS)
  let E : Set Base := closedBall (0 : Base) (1 / 4) ∩
    (renewalCellCode Kc J qc) ⁻¹' {L | ρk {x | code x = L} ≠ 0}
  have hE : MeasurableSet E :=
    measurableSet_closedBall.inter
      ((measurable_renewalCellCode Kc J qc) (DiscreteMeasurableSpace.forall_measurableSet _))
  have hEball : E ⊆ closedBall (0 : Base) (1 / 4) := fun y hy => hy.1
  have hsupp : ∀ᵐ x ∂μ₀, Z x ∈ E := by
    have hnull : ∀ᵐ x ∂ρk, ρk {y | code y = code x} ≠ 0 := by
      have hcount : ρk (⋃ L ∈ {L : Fin 3 → ℤ | ρk {y | code y = L} = 0}, {y | code y = L}) = 0 :=
        (measure_biUnion_null_iff (Set.to_countable _)).mpr (fun L hL => hL)
      rw [ae_iff]
      refine measure_mono_null ?_ hcount
      intro x hx
      simp only [mem_ofPred_eq, not_not] at hx
      exact mem_iUnion₂.mpr ⟨code x, hx, rfl⟩
    have hcore : ∀ᵐ x ∂μ₀, x ∈ Ul := by
      have hh : ∀ᵐ x ∂μ₀, x ∈ Ul ∩ keep := ae_restrict_mem (hUlm.inter hkeep)
      filter_upwards [hh] with x hx using hx.1
    filter_upwards [hac.ae_le hnull, hcore] with x hx hxU
    refine ⟨?_, hx⟩
    rw [mem_closedBall, dist_zero_right]
    exact (hU x (hUlU hxU)).2.2.2.1
  let threshold : (Fin 3 → ℤ) → ENNReal :=
    fun L => (δref⁻¹ * ENNReal.ofReal (8 * fraction)) * ρk {x | code x = L}
  let μc : (Fin 3 → ℤ) → Measure Event := fun L => ρk.restrict {x | code x = L}
  let tests : (Fin 3 → ℤ) → Set Event := fun L => Ul ∩ keep ∩ {x | code x = L}
  have hcodeset (L : Fin 3 → ℤ) : MeasurableSet {x : Event | code x = L} :=
    hcode (measurableSet_singleton L)
  have hstrip : ∀ L, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c' : ℝ,
      μc L ((fun q : Event => packetCubeVelocity p b q.1) ⁻¹'
        Submission.Lib.K4VelocityStrips.affineStrip n c' width) ≤ threshold L := by
    intro L n hn c'
    have hh := hbreadth L n (c' • n) hn
    simp only [μc, threshold]
    rw [Measure.restrict_apply' (hcodeset L)]
    refine le_trans (measure_mono ?_) hh
    intro x hx
    refine ⟨hx.2, ?_⟩
    have hx1 := hx.1
    simp only [mem_preimage, Submission.Lib.K4VelocityStrips.affineStrip, mem_ofPred_eq] at hx1
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one,
      real_inner_comm]
    exact hx1
  have hfinite (L : Fin 3 → ℤ) : ρk {x | code x = L} ≠ ⊤ := by
    rw [hρk]
    refine ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => (hUlU hx.2 : x ∈ U)))
    have hsub : U ⊆ p.F b := fun x hx => ((V.subset b a).2 ((C.subset ii).2 hx.1)).2
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
    refine ne_top_of_le_ne_top ?_ (Broad.prod_le_prior_mul_block
      (fun q (hq : q ∈ p.F b) => ⟨(hF q hq).2.1, (hF q hq).2.2.1⟩))
    obtain ⟨-, -, hν⟩ := hd.weights k
    haveI := hν (p.γ b)
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hmass : ∀ y ∈ E, threshold (renewalCellCode Kc J qc y) <
      μc (renewalCellCode Kc J qc y) (tests (renewalCellCode Kc J qc y)) := by
    intro y hy
    have hne : ρk {x | code x = renewalCellCode Kc J qc y} ≠ 0 := hy.2
    have heq : μc (renewalCellCode Kc J qc y) (tests (renewalCellCode Kc J qc y)) =
        ρk {x | code x = renewalCellCode Kc J qc y} := by
      simp only [μc, tests]
      rw [Measure.restrict_apply' (hcodeset _), hρk, hρk]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [heq]
    calc
      threshold (renewalCellCode Kc J qc y) =
          ρk {x | code x = renewalCellCode Kc J qc y} * (δref⁻¹ * ENNReal.ofReal (8 * fraction)) :=
        mul_comm _ _
      _ < ρk {x | code x = renewalCellCode Kc J qc y} * 1 :=
        ENNReal.mul_lt_mul_right hne (hfinite _) hβ1
      _ = _ := mul_one _
  have htestcode : ∀ L x, x ∈ tests L →
      renewalCellCode Kc J qc (packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center ii.1.1) x) =
        L := fun L x hx => hx.2
  have htestU : ∀ L x, x ∈ tests L → x ∈ U := fun L x hx => hUlU hx.1.1
  have hlong : ∀ L x, x ∈ tests L →
      ENNReal.ofReal θrow ≤ volume (coreRowTimes p b K R U x) := fun L x hx => hx.1.1.2
  have hjetsV : ValueJetBound D J := fun A' hA' g hg => (hjets A' hA' g hg).1
  have hgrad := parent_core_gradient hp hNpos old b hB P hP hwidth hKtwo hκK hεpos le_rfl
    (V.center a) R (C.center ii.1.1) (nativeCoreSign ii.2) (C.extension ii) (C.sheet ii)
    hbranch U hUm hU hM hparentJets hmotion (by omega) hjetsV μ₀ μc tests E hE hEball hKc2 hA hKc hwidthpos
    hwidthfloor (by positivity) hθrow hθrow1 hmass₀ hcap hsupp threshold hstrip hmass
    htestcode htestU hlong
  have hG0 : 0 ≤ coreGradientCoeff A width θrow J := by
    unfold coreGradientCoeff
    have hK0 := coreRow_spec.1
    positivity
  exact parent_core_lipschitz hp hN hNpos old b hB P hP hwidth hKtwo hκK hεpos le_rfl
    (V.center a) R (C.center ii.1.1) (nativeCoreSign ii.2) (C.extension ii) (C.sheet ii)
    hbranch U hU hM hparentJets hG0 hgrad

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
