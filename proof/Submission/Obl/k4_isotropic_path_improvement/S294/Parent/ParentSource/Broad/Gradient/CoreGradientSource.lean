-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.CoreGradientSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/CoreGradientSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/CoreGradientSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreGradientEntry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueCoreRetention

/-!
# The gradient source: Lipschitz old signal on every retained fine core

For every coherent fine core under one old packet, keep the incidences with long rows and
renew strip breadth on their renewal cells (with the ORIGINAL law `(ν ⊗ dt)`). A core is
*good* when its renewed long rows still carry half of its earlier floor in the original entry
law; then the old signal is Lipschitz in old base coordinates on the whole core
(`CoreEntryData.old_signal_lipschitz_of_renewal`).

The retained set is the union of the good cores' retained pieces. It does not depend on the
later law `μ`. A bad core has original mass at most twice its short rows plus its renewal
deletion. So the deleted cores cost at most
`4 K^{3R+28} κ² (θ_row K^{-R} + 27 δ κ²)` times the FULL old reference, for any `μ ≤ ν ⊗ dt`
supported on the retained cores.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

theorem ValueBranchData.entryLaw_apply_of_subset
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (b : Fin p.C) (a : Fin V.count)
    {S : Set Event} (hS : S ⊆ V.outer b a) :
    V.entryLaw b a S = (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹))⁻¹ *
      ((d.ν k (p.γ b)).prod volume) S := by
  rw [ValueBranchData.entryLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (V.measurable b a).1, inter_eq_left.mpr hS]

theorem ennreal_le_two_mul_of_le_add_half {x y : ENNReal} (hx : x ≠ ⊤) (h : x ≤ y + x / 2) :
    x ≤ 2 * y := by
  have hhalf : x / 2 ≠ ⊤ := ENNReal.div_ne_top hx (by norm_num)
  have h' : x / 2 ≤ y := by
    have hh : x / 2 + x / 2 ≤ y + x / 2 := by rw [ENNReal.add_halves]; exact h
    exact (ENNReal.add_le_add_iff_right hhalf).mp hh
  calc
    x = x / 2 + x / 2 := (ENNReal.add_halves x).symm
    _ ≤ y + y := add_le_add h' h'
    _ = 2 * y := (two_mul y).symm

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

/-- **The gradient source.** -/
theorem ValueBranchData.exists_gradient_core_source
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hHterminal : ∀ w, H₀ w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, H w ⊆ broad.residual w)
    (old : Fin p.C) (hold : p.lev old = i) (hactive : F.active old)
    (hmid : p.lev old ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r (p.lev old)))
    {Kc width θrow : ℝ} {qc : ℕ} (hKc : 2 * K ^ (qcore + 7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc ^ qc)⁻¹ ≤ width)
    (hstrip : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ r)
    (hdeep : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞)
    (hβ1 : δref⁻¹ * ENNReal.ofReal (8 * fraction) < 1)
    (μ : Measure Event) (hμ : μ ≤ (d.ν k (p.γ old)).prod volume)
    (hsupport : ∀ᵐ z ∂μ, z ∈ V.coreRetained cores (p.γ old) ∩ p.F old) :
    ∃ keep : Set Event, MeasurableSet keep ∧
      μ univ ≤ (μ.restrict keep) univ +
        ENNReal.ofReal (4 * K ^ (3 * R + 28) * p.κ ^ 2) *
          (ENNReal.ofReal (θrow * (K ^ R)⁻¹) + 27 * (δref * ENNReal.ofReal (p.κ ^ 2))) *
          (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) ∧
      ∀ (v : V.ActiveValue) (ii : ↥(cores v).codes × Bool), p.γ v.1.1 = p.γ old →
        (keep ∩ (V.inner v.1.1 v.1.2 ∩ (cores v).kept ii)).Nonempty →
        ∀ z ∈ (cores v).raw ii, ∀ z' ∈ (cores v).raw ii,
          |MvPolynomial.eval (xp z.1 z.2) (p.R old) / δ (d.N k) (p.r (p.lev old)) -
              MvPolynomial.eval (xp z'.1 z'.2) (p.R old) / δ (d.N k) (p.r (p.lev old))| ≤
            (2 + coreGradientCoeff (2 * K ^ (qcore + 7)) width θrow J / 2) *
                (K ^ 14 * (K ^ 6)⁻¹ *
                  (δ (d.N k) (p.r (p.lev v.1.1)) / δ (d.N k) (p.r (p.lev old)))) +
              4 * p.κ * coreGradientCoeff (2 * K ^ (qcore + 7)) width θrow J *
                (1 + 4 * p.κ + 6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) *
                ‖packetBase p old z - packetBase p old z'‖ := by
  classical
  letI : Fintype V.ActiveValue := Fintype.ofFinite _
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  have hKpos : 0 < K := by linarith
  have hK0 : 0 ≤ K := hKpos.le
  have hKcpos : 0 < Kc := by
    have : (0 : ℝ) < 2 * K ^ (qcore + 7) := by positivity
    linarith
  have hBpos : ∀ w, 0 < d.B k w := by
    have hd₁ := hd
    rcases hd₁ with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D', hformat⟩ := hformat
    intro w
    exact ((hformat k).2.2.2.1 w).2.1
  have hν : ∀ w, IsProbabilityMeasure (d.ν k w) := (hd.weights k).2.2
  -- the cores
  let X := Σ v : V.ActiveValue, ↥(cores v).codes × Bool
  let rel : X → Prop := fun x => p.F x.1.1.1 ⊆ p.F old ∧ p.γ x.1.1.1 = p.γ old
  let Ul : X → Set Event := fun x =>
    coreLongRows p x.1.1.1 K R ((cores x.1).raw x.2) θrow
  have hrawm : ∀ x : X, MeasurableSet ((cores x.1).raw x.2) :=
    fun x => ((cores x.1).measurable x.2).1
  have hUlm : ∀ x : X, MeasurableSet (Ul x) :=
    fun x => measurableSet_coreLongRows p _ K R (hrawm x) θrow
  have hrawsub : ∀ x : X, (cores x.1).raw x.2 ⊆ V.outer x.1.1.1 x.1.1.2 :=
    fun x => ((cores x.1).subset x.2).2
  have hUlH : ∀ x : X, Ul x ⊆ H (p.γ x.1.1.1) ∩ p.F x.1.1.1 :=
    fun x z hz => (V.subset _ _).2 (hrawsub x hz.1)
  let refb : Fin p.C → ENNReal := fun b =>
    d.ν k (p.γ old) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)
  -- the renewal of every relevant core
  have hren : ∀ x : X, ∃ keepx : Set Event, MeasurableSet keepx ∧ (rel x →
      (((d.ν k (p.γ old)).prod volume).restrict (Ul x)) univ ≤
        ((((d.ν k (p.γ old)).prod volume).restrict (Ul x)).restrict keepx) univ +
          δref * (27 * (ENNReal.ofReal (p.κ ^ 2) * refb x.1.1.1)) ∧
      ∀ (label : Fin 3 → ℤ) (n center : EuclideanSpace ℝ (Fin 2)), ‖n‖ = 1 →
        ((((d.ν k (p.γ old)).prod volume).restrict (Ul x)).restrict keepx)
          {z | renewalCellCode Kc J qc (packetLocalCorePoint (d.N k) (d.B k) p x.1.1.1 K R
              ((cores x.1).center x.2.1.1) z) = label ∧
            |Inner.inner ℝ n (packetCubeVelocity p x.1.1.1 z.1 - center)| ≤ width} ≤
          (δref⁻¹ * ENNReal.ofReal (8 * fraction)) *
            ((((d.ν k (p.γ old)).prod volume).restrict (Ul x)).restrict keepx)
              {z | renewalCellCode Kc J qc (packetLocalCorePoint (d.N k) (d.B k) p x.1.1.1 K R
                ((cores x.1).center x.2.1.1) z) = label}) := by
    intro x
    by_cases hx : rel x
    · obtain ⟨keepx, hkm, hbud, hcap⟩ := exists_core_cell_renewal Q hd hp hHbase hHterminal
        broad hHbroad old hold hactive x.1.1.1 x.1.2.1 hmid hstop hx.2 hx.1 hK0 R
        ((cores x.1).center x.2.1.1) hKcpos J qc
        (fun deep hdl => hdeep x.1.1.1 deep x.1.2.1 hdl) hfraction hwidthpos.le hstrip
        (Ul x) (hUlm x) (hUlH x) δref hδ0 hδtop
      exact ⟨keepx, hkm, fun _ => ⟨hbud, hcap⟩⟩
    · exact ⟨univ, MeasurableSet.univ, fun h => absurd h hx⟩
  choose keepf hkeepfm hkeepf using hren
  -- good cores and the retained set
  let good : X → Prop := fun x => rel x ∧
    ENNReal.ofReal ((K ^ qcore)⁻¹ / 2) ≤ V.entryLaw x.1.1.1 x.1.1.2 (Ul x ∩ keepf x)
  let piece : X → Set Event := fun x => V.inner x.1.1.1 x.1.1.2 ∩ (cores x.1).kept x.2
  have hpiecem : ∀ x, MeasurableSet (piece x) :=
    fun x => (V.measurable _ _).2.inter ((cores x.1).measurable x.2).2
  let keep : Set Event := ⋃ x : X, if good x then piece x else ∅
  have hkeepm : MeasurableSet keep := by
    apply MeasurableSet.iUnion
    intro x
    split_ifs
    · exact hpiecem x
    · exact MeasurableSet.empty
  refine ⟨keep, hkeepm, ?_, ?_⟩
  · -- the deletion of the bad cores
    let c' : ENNReal := ENNReal.ofReal (θrow * (K ^ R)⁻¹) + 27 * (δref * ENNReal.ofReal (p.κ ^ 2))
    have hbadbound : ∀ x : X, rel x → ¬ good x → μ (piece x) ≤ 2 * (c' * refb x.1.1.1) := by
      intro x hrel hng
      by_cases hkne : ((cores x.1).kept x.2).Nonempty
      swap
      · rw [Set.not_nonempty_iff_eq_empty] at hkne
        have hempty : piece x = ∅ := by
          simp only [piece, hkne, inter_empty]
        rw [hempty, measure_empty]
        exact zero_le
      let b := x.1.1.1
      let ν' : Measure Event := (d.ν k (p.γ old)).prod volume
      let raw := (cores x.1).raw x.2
      have hγb : p.γ b = p.γ old := hrel.2
      have hlev : p.lev b = mid := x.1.2.1
      let ref' : ENNReal := d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹)
      have hrefeq : ref' = refb b := by
        simp only [ref', refb]
        rw [hγb, hlev]
      have hNpos' : 0 < d.N k := hNpos
      have hA0 : d.ν k (p.γ b) (p.A b) ≠ 0 := (hp.assignment_mass_pos hNpos' b).ne'
      have hAtop : d.ν k (p.γ b) (p.A b) ≠ ⊤ := by
        have := hν (p.γ b)
        exact measure_ne_top _ _
      have href0 : ref' ≠ 0 :=
        mul_ne_zero hA0 (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      have hreftop : ref' ≠ ⊤ := ENNReal.mul_ne_top hAtop ENNReal.ofReal_ne_top
      have hconv (S : Set Event) (hS : S ⊆ V.outer b x.1.1.2) :
          ν' S = ref' * V.entryLaw b x.1.1.2 S := by
        rw [V.entryLaw_apply_of_subset b x.1.1.2 hS, ← mul_assoc,
          ENNReal.mul_inv_cancel href0 hreftop, one_mul]
        simp only [ν']
        rw [hγb]
      -- floor and badness, in original units
      have hfloor : ENNReal.ofReal ((K ^ qcore)⁻¹) * ref' ≤ ν' raw := by
        rw [hconv raw (hrawsub x), mul_comm]
        exact mul_le_mul' le_rfl ((cores x.1).original_floor x.2 hkne)
      have hbadlt : ν' (Ul x ∩ keepf x) < ENNReal.ofReal ((K ^ qcore)⁻¹ / 2) * ref' := by
        have hlt : V.entryLaw b x.1.1.2 (Ul x ∩ keepf x) <
            ENNReal.ofReal ((K ^ qcore)⁻¹ / 2) := lt_of_not_ge (fun h => hng ⟨hrel, h⟩)
        rw [hconv _ (fun z hz => hrawsub x hz.1.1), mul_comm (ENNReal.ofReal _) ref']
        exact ENNReal.mul_lt_mul_right href0 hreftop hlt
      have hrawtop : ν' raw ≠ ⊤ := by
        refine ne_top_of_le_ne_top ?_ (measure_mono (hrawsub x))
        refine ne_top_of_le_ne_top ?_ (measure_mono (fun z hz => ((V.subset b _).2 hz).2))
        obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
        refine ne_top_of_le_ne_top ?_ (Broad.prod_le_prior_mul_block
          (fun q (hq : q ∈ p.F b) => ⟨(hF q hq).2.1, (hF q hq).2.2.1⟩))
        haveI := hν (p.γ old)
        exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
      have hhalf : ENNReal.ofReal ((K ^ qcore)⁻¹ / 2) * ref' ≤ ν' raw / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv,
          div_eq_mul_inv, mul_right_comm]
        exact mul_le_mul' hfloor le_rfl
      -- the three parts of the raw core
      have hkpm : MeasurableSet (keepf x) := hkeepfm x
      have hsplit : ν' raw ≤ ν' (raw \ Ul x) + ν' (Ul x \ keepf x) + ν' (Ul x ∩ keepf x) := by
        calc
          ν' raw ≤ ν' ((raw \ Ul x) ∪ (Ul x \ keepf x) ∪ (Ul x ∩ keepf x)) := by
            apply measure_mono
            intro z hz
            by_cases hzU : z ∈ Ul x
            · by_cases hzk : z ∈ keepf x
              · exact Or.inr ⟨hzU, hzk⟩
              · exact Or.inl (Or.inr ⟨hzU, hzk⟩)
            · exact Or.inl (Or.inl ⟨hz, hzU⟩)
          _ ≤ ν' ((raw \ Ul x) ∪ (Ul x \ keepf x)) + ν' (Ul x ∩ keepf x) := measure_union_le _ _
          _ ≤ ν' (raw \ Ul x) + ν' (Ul x \ keepf x) + ν' (Ul x ∩ keepf x) :=
            add_le_add (measure_union_le _ _) le_rfl
      obtain ⟨-, -, hchb⟩ := hp.2.2.2.2.2.2.2 b
      obtain ⟨_, _, _, _, _, _, hAm, _, _, _, hFb, -⟩ := hchb
      have hshort : ν' (raw \ Ul x) ≤
          ENNReal.ofReal (θrow * coreRowStep p b K R) * d.ν k (p.γ old) (p.A b) := by
        have hset : raw \ Ul x = raw ∩ {q | rowVolume raw (coreRowStep p b K R) q <
            ENNReal.ofReal θrow} := by
          ext z
          simp only [Ul, coreLongRows, mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_and, not_le]
          constructor
          · rintro ⟨hz, hz'⟩
            exact ⟨hz, hz' hz⟩
          · rintro ⟨hz, hz'⟩
            exact ⟨hz, fun _ => hz'⟩
        rw [hset]
        have hpos : 0 < coreRowStep p b K R := by unfold coreRowStep; positivity
        exact short_rows_mass_le (d.ν k (p.γ old)) hAm (hrawm x)
          (fun q hq => (hFb q ((V.subset b _).2 (hrawsub x hq)).2).2.1) hpos
      have hpruned : ν' (Ul x \ keepf x) ≤ δref * (27 * (ENNReal.ofReal (p.κ ^ 2) * refb b)) := by
        have hbud := (hkeepf x hrel).1
        rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ,
          Measure.restrict_apply hkpm] at hbud
        have hfin : ν' (Ul x ∩ keepf x) ≠ ⊤ :=
          ne_top_of_le_ne_top hrawtop (measure_mono (fun z hz => hz.1.1))
        have hsum := measure_sdiff_add_inter (μ := ν') (Ul x) hkpm
        rw [← hsum, inter_comm (keepf x) (Ul x)] at hbud
        exact (ENNReal.add_le_add_iff_right hfin).mp (by rwa [add_comm (ν' (Ul x ∩ keepf x))] at hbud)
      have hraw2 : ν' raw ≤ 2 * (ν' (raw \ Ul x) + ν' (Ul x \ keepf x)) := by
        apply ennreal_le_two_mul_of_le_add_half hrawtop
        calc
          ν' raw ≤ ν' (raw \ Ul x) + ν' (Ul x \ keepf x) + ν' (Ul x ∩ keepf x) := hsplit
          _ ≤ ν' (raw \ Ul x) + ν' (Ul x \ keepf x) + ν' raw / 2 :=
            add_le_add le_rfl (hbadlt.le.trans hhalf)
      have hstep : ENNReal.ofReal (θrow * coreRowStep p b K R) * d.ν k (p.γ old) (p.A b) =
          ENNReal.ofReal (θrow * (K ^ R)⁻¹) * refb b := by
        simp only [refb, coreRowStep]
        rw [show θrow * (((2 : ℝ) ^ p.T (p.lev b))⁻¹ * (K ^ R)⁻¹) =
            (θrow * (K ^ R)⁻¹) * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ by ring,
          ENNReal.ofReal_mul (by positivity)]
        ring
      calc
        μ (piece x) ≤ ν' (piece x) := hμ _
        _ ≤ ν' raw := measure_mono (fun z hz => ((cores x.1).subset x.2).1 hz.2)
        _ ≤ 2 * (ν' (raw \ Ul x) + ν' (Ul x \ keepf x)) := hraw2
        _ ≤ 2 * (ENNReal.ofReal (θrow * (K ^ R)⁻¹) * refb b +
            δref * (27 * (ENNReal.ofReal (p.κ ^ 2) * refb b))) := by
          rw [← hstep]
          exact mul_le_mul' le_rfl (add_le_add hshort hpruned)
        _ = 2 * (c' * refb x.1.1.1) := by
          simp only [c']
          ring
    -- every deleted retained incidence lies in a bad core
    have hbad_sub : keepᶜ ≤ᵐ[μ] ⋃ x : X, if (rel x ∧ ¬ good x) then piece x else ∅ := by
      filter_upwards [hsupport] with z hz hznot
      obtain ⟨hzret, hzold⟩ := hz
      obtain ⟨hzres, hzunion⟩ := hzret
      obtain ⟨v, hv⟩ := mem_iUnion.mp hzunion
      by_cases hγv : p.γ v.1.1 = p.γ old
      · rw [ite_eq_left hγv] at hv
        obtain ⟨hzinner, hzkept⟩ := hv
        obtain ⟨ii, hzi⟩ := mem_iUnion.mp hzkept
        have hzbase : z ∈ Q.base (p.γ old) := hHbase _ (V.residual_subset _ hzres)
        have hzfine : z ∈ p.F v.1.1 :=
          ((V.subset v.1.1 v.1.2).2 ((V.subset v.1.1 v.1.2).1 hzinner)).2
        have hrel : rel ⟨v, ii⟩ := ⟨Q.original_ancestor_of_common_incidence hp old v.1.1
          (hmid.trans_eq v.2.1.symm) hγv z hzbase hzold hzfine, hγv⟩
        have hng : ¬ good ⟨v, ii⟩ := by
          intro hg
          apply hznot
          exact mem_iUnion.mpr ⟨⟨v, ii⟩, by rw [ite_eq_left hg]; exact ⟨hzinner, hzi⟩⟩
        exact mem_iUnion.mpr ⟨⟨v, ii⟩, by rw [ite_eq_left ⟨hrel, hng⟩]; exact ⟨hzinner, hzi⟩⟩
      · rw [ite_eq_right hγv] at hv
        exact hv.elim
    -- the count of cores and the local references
    have hcodes : ∀ v : V.ActiveValue,
        (Fintype.card (↥(cores v).codes × Bool) : ENNReal) ≤ ENNReal.ofReal (2 * K ^ (3 * R + 18)) := by
      intro v
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      have hc := (cores v).count_le
      push_cast
      linarith
    have hfine : (∑ b ∈ originalFinePackets p old mid, refb b) ≤
        ENNReal.ofReal (p.κ ^ 2) *
          (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) := by
      have hh := hp.local_reference_sum_le hNpos old mid (originalFinePackets p old mid)
        (fun b hb => (Finset.mem_filter.mp hb).2)
      refine le_trans (le_of_eq ?_) hh
      apply Finset.sum_congr rfl
      intro b hb
      simp only [refb]
      rw [(Finset.mem_filter.mp hb).2.1, mul_comm]
    have hvalues : (∑ v : V.ActiveValue,
        if p.F v.1.1 ⊆ p.F old ∧ p.γ v.1.1 = p.γ old then refb v.1.1 else 0) ≤
        ENNReal.ofReal (K ^ 10) * (ENNReal.ofReal (p.κ ^ 2) *
          (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))) := by
      let g : Fin p.C × Fin V.count → ENNReal := fun ba =>
        if p.lev ba.1 = mid ∧ p.γ ba.1 = p.γ old ∧ p.F ba.1 ⊆ p.F old then refb ba.1 else 0
      calc
        _ ≤ ∑ ba, g ba := by
          apply Finset.sum_le_sum_of_injOn Subtype.val
          · intro v _ v' _ hv
            exact Subtype.val_injective hv
          · exact Finset.subset_univ _
          · intro v _
            by_cases hv : p.F v.1.1 ⊆ p.F old ∧ p.γ v.1.1 = p.γ old
            · simp only [g, ite_eq_left hv, ite_eq_left (show p.lev v.1.1 = mid ∧
                p.γ v.1.1 = p.γ old ∧ p.F v.1.1 ⊆ p.F old from ⟨v.2.1, hv.2, hv.1⟩)]
              exact le_rfl
            · simp only [ite_eq_right hv]
              exact zero_le
          · intros
            exact zero_le
        _ = (V.count : ENNReal) * ∑ b ∈ originalFinePackets p old mid, refb b := by
          rw [Fintype.sum_prod_type]
          simp only [g, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.mul_sum, originalFinePackets, Finset.sum_filter]
          simp only [mul_ite, mul_zero]
        _ ≤ ENNReal.ofReal (K ^ 10) * (ENNReal.ofReal (p.κ ^ 2) *
            (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))) :=
          mul_le_mul' (by simpa only [ENNReal.ofReal_natCast] using
            ENNReal.ofReal_le_ofReal V.count_le) hfine
    have hcompl : μ keepᶜ ≤ ENNReal.ofReal (4 * K ^ (3 * R + 28) * p.κ ^ 2) * c' *
        (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) := by
      calc
        μ keepᶜ ≤ μ (⋃ x : X, if (rel x ∧ ¬ good x) then piece x else ∅) := measure_mono_ae hbad_sub
        _ ≤ ∑ x : X, μ (if (rel x ∧ ¬ good x) then piece x else ∅) := measure_iUnion_fintype_le _ _
        _ ≤ ∑ x : X, if rel x then 2 * (c' * refb x.1.1.1) else 0 := by
          apply Finset.sum_le_sum
          intro x _
          by_cases hbad : rel x ∧ ¬ good x
          · rw [ite_eq_left hbad, ite_eq_left hbad.1]
            exact hbadbound x hbad.1 hbad.2
          · rw [ite_eq_right hbad, measure_empty]
            exact zero_le
        _ = ∑ v : V.ActiveValue, (Fintype.card (↥(cores v).codes × Bool) : ENNReal) *
            (if p.F v.1.1 ⊆ p.F old ∧ p.γ v.1.1 = p.γ old then 2 * (c' * refb v.1.1) else 0) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro v _
          simp only [rel, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ v : V.ActiveValue, ENNReal.ofReal (2 * K ^ (3 * R + 18)) * (2 * c' *
            (if p.F v.1.1 ⊆ p.F old ∧ p.γ v.1.1 = p.γ old then refb v.1.1 else 0)) := by
          apply Finset.sum_le_sum
          intro v _
          refine mul_le_mul' (hcodes v) (le_of_eq ?_)
          split_ifs <;> ring
        _ = ENNReal.ofReal (2 * K ^ (3 * R + 18)) * (2 * c') * ∑ v : V.ActiveValue,
            (if p.F v.1.1 ⊆ p.F old ∧ p.γ v.1.1 = p.γ old then refb v.1.1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ ≤ ENNReal.ofReal (2 * K ^ (3 * R + 18)) * (2 * c') * (ENNReal.ofReal (K ^ 10) *
            (ENNReal.ofReal (p.κ ^ 2) *
              (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)))) :=
          mul_le_mul' le_rfl hvalues
        _ = ENNReal.ofReal (4 * K ^ (3 * R + 28) * p.κ ^ 2) * c' *
            (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) := by
          have hpow : (4 : ℝ) * K ^ (3 * R + 28) * p.κ ^ 2 =
              (2 * K ^ (3 * R + 18)) * 2 * K ^ 10 * p.κ ^ 2 := by
            rw [show 3 * R + 28 = (3 * R + 18) + 10 by ring, pow_add]
            ring
          have h1 : (0 : ℝ) ≤ 2 * K ^ (3 * R + 18) := by positivity
          have h2 : (0 : ℝ) ≤ 2 * K ^ (3 * R + 18) * 2 := by positivity
          have h3 : (0 : ℝ) ≤ 2 * K ^ (3 * R + 18) * 2 * K ^ 10 := by positivity
          have hconst : ENNReal.ofReal (4 * K ^ (3 * R + 28) * p.κ ^ 2) =
              ENNReal.ofReal (2 * K ^ (3 * R + 18)) * 2 * ENNReal.ofReal (K ^ 10) *
                ENNReal.ofReal (p.κ ^ 2) := by
            rw [hpow, ENNReal.ofReal_mul h3, ENNReal.ofReal_mul h2, ENNReal.ofReal_mul h1,
              ENNReal.ofReal_ofNat]
          rw [hconst]
          ring
    calc
      μ univ = μ keep + μ keepᶜ := (measure_add_measure_compl hkeepm).symm
      _ = (μ.restrict keep) univ + μ keepᶜ := by rw [Measure.restrict_apply_univ]
      _ ≤ _ := add_le_add le_rfl hcompl
  · -- the Lipschitz bound on every retained core
    intro v ii hvγ hne z hz z' hz'
    obtain ⟨z₀, hz₀keep, hz₀inner, hz₀kept⟩ := hne
    obtain ⟨⟨v', ii'⟩, hx'⟩ := mem_iUnion.mp hz₀keep
    by_cases hg : good ⟨v', ii'⟩
    · rw [if_pos hg] at hx'
      obtain ⟨hz₀inner', hz₀kept'⟩ := hx'
      have hzbase : z₀ ∈ Q.base (p.γ old) := by
        have hh := hHbase _ ((V.subset v.1.1 v.1.2).2 ((V.subset v.1.1 v.1.2).1 hz₀inner)).1
        rwa [hvγ] at hh
      have hzF : z₀ ∈ p.F v.1.1 :=
        ((V.subset v.1.1 v.1.2).2 ((V.subset v.1.1 v.1.2).1 hz₀inner)).2
      have hzF' : z₀ ∈ p.F v'.1.1 :=
        ((V.subset v'.1.1 v'.1.2).2 ((V.subset v'.1.1 v'.1.2).1 hz₀inner')).2
      have hb : v'.1.1 = v.1.1 := Q.base_packet_unique (p.γ old) z₀ hzbase v'.1.1 v.1.1
        (v'.2.1.trans v.2.1.symm) hg.1.2 hvγ hzF' hzF
      have ha : v'.1.2 = v.1.2 := by
        by_contra hne
        have hdis := V.disjoint v.1.1 hne
        rw [hb] at hz₀inner'
        exact Set.disjoint_left.mp hdis hz₀inner' hz₀inner
      have hv : v' = v := Subtype.ext (Prod.ext hb ha)
      subst hv
      have hii : ii' = ii := by
        by_contra hne
        exact Set.disjoint_left.mp ((cores v').disjoint hne) hz₀kept' hz₀kept
      subst hii
      have hrawne : ((cores v').raw ii').Nonempty := ⟨z, hz⟩
      have hwidth' : δ (d.N k) (p.r (p.lev v'.1.1)) ≤ δ (d.N k) (p.r (p.lev old)) := by
        rw [v'.2.1]
        exact hwidth
      exact CoreEntryData.old_signal_lipschitz_of_renewal V Q hpure hd hp hHE hHbase hK hmax
        hpower hκK v'.1.1 v'.2.1 hr hrL (hBpos _) v'.1.2 (cores v') ii' hrawne hD hjets old
        hg.1.2 hwidth' hg.1.1 hKc hwidthpos hwidthfloor hθrow hθrow1 hβ1 (keepf ⟨v', ii'⟩)
        (hkeepfm _) ((hkeepf _ hg.1).2) hg.2 z hz z' hz'
    · rw [if_neg hg] at hx'
      exact hx'.elim

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
