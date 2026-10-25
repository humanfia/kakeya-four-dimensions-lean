-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/PreparedSourceDomains.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedSourceDomains.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PositiveSourceDomains
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.TrueLayerDomains
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ProjectedLayerDomains

/-! Actual positive common domains of a prepared true and projected layer. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers
open CommonDomain
open scoped ENNReal

noncomputable section

structure PreparedSourcePoint {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) (k : ℕ) (s : ℝ) (L : ProjLayer α)
    (Extra : α × ℝ → Prop) (z : α × ℝ) : Prop where
  time : z.2 ∈ Icc (0 : ℝ) 1
  coefficients : |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ p.K k
  true_label : ∃ i, z.1 ∈ a.B k s i ∧ z.2 ∈ a.block k s i
  projected_label : ∃ i, z.1 ∈ L.C i
  extra : Extra z

structure PreparedDomainData {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) (k : ℕ) (s H q χ m : ℝ) (L : ProjLayer α)
    (ζ : Measure (α × ℝ)) (Extra : α × ℝ → Prop) where
  trueMenus : Fin (a.n k s) → Finset Code
  projectedMenus : Fin L.n → Finset Code
  true_cover : ∀ i l, l ∈ a.B k s i →
    |a.b k l 0| + |a.b k l 1| + |a.b k l 3| + |a.b k l 4| ≤ p.K k →
    ∀ t ∈ a.block k s i, code q χ (PreparedModel.narrow p k s) m (a.b k l) t ∈ trueMenus i
  projected_cover : ∀ i l, l ∈ L.C i → ∀ t ∈ Icc (0 : ℝ) 1,
    code q χ (PreparedModel.narrow p k s) m (a.b k l) t ∈ projectedMenus i
  true_reference : (∑ i, ∑ c ∈ trueMenus i, q * χ * m * (PreparedModel.width p k s) ^ p.d *
    (a.pi k {w : ℝ | ⌊w / χ⌋ = c 1}).toReal) ≤ 237600 * p.K k ^ 5
  projected_reference : (∑ i, ∑ c ∈ projectedMenus i, q * χ * m * (PreparedModel.width p k s) ^ p.d *
    (a.pi k {w : ℝ | ⌊w / χ⌋ = c 1}).toReal) ≤ 360 * H ^ 4 * (a.rho k univ).toReal
  n : ℕ
  positive_n : 0 < n
  code : α × ℝ → Fin n
  decode : Fin n → Code
  measurable_code : Measurable code
  injective_decode : Function.Injective decode
  G : Set (α × ℝ)
  measurable_G : MeasurableSet G
  full_G : ζ Gᶜ = 0
  pointwise : ∀ z ∈ G, PreparedSourcePoint p a k s L Extra z ∧
    decode (code z) = CommonDomain.code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2
  positive_domain : ∀ i, codePieces ζ code i univ ≠ 0
  source_point : ∀ i, ∃ z ∈ G, code z = i

theorem exists_prepared_source_domains {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {R s H La χ q m : ℝ} {k : ℕ} (hatlas : a.AtlasAt p R k s)
    (L : ProjLayer α)
    (hL : L.Good (p.N k) H p.d p.ell La s χ (a.b k) (a.P k) (a.pi k) (a.rho k))
    (hH : 1 ≤ H) (hq : 0 < q) (hqQ : q ≤ a.q k s) (hχ : 0 < χ)
    (hχQ : χ ≤ a.q k s) (hχQg : χ ≤ a.q k s * PreparedModel.narrow p k s)
    (hm : 0 < m) (hmQg : m ≤ a.q k s * PreparedModel.narrow p k s) (hmβ : m ≤ L.β)
    (ζ : Measure (α × ℝ)) (hζ : ζ ≤ a.mu k) (hζpos : ζ univ ≠ 0)
    (hcovered : ∀ᵐ z ∂ζ, z ∈ L.covered)
    (Extra : α × ℝ → Prop) (hExtra : ∀ᵐ z ∂ζ, Extra z) :
    Nonempty (PreparedDomainData p a k s H q χ m L ζ Extra) := by
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hq1 : q ≤ 1 := hqQ.trans (by
    have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := a.T k s)
    simpa [PreparedModel.q] using inv_le_one_of_one_le₀ h)
  haveI : IsProbabilityMeasure (a.pi k) := (hcommon k).2.2.1
  haveI : IsFiniteMeasure (a.rho k) :=
    ⟨lt_of_le_of_lt (a.rho_univ_le p hcommon k) ENNReal.ofReal_lt_top⟩
  obtain ⟨trueMenus, htrue, htrueRef⟩ := true_layer_common_domains p hp a hcommon hatlas
    hq hqQ hχ hχQ hχQg hm hmQg
  obtain ⟨projectedMenus, hprojected, -, hprojectedRef⟩ := projected_layer_real_common_domains
    L (a.b k) (a.P k) (a.pi k) (a.rho k) hL hN hH hχ hq hq1 hm hmβ
  have htime : ∀ᵐ z ∂ζ, z.2 ∈ Icc (0 : ℝ) 1 := by
    have hunit : ∀ᵐ z ∂a.mu k, z ∈ univ ×ˢ Icc (0 : ℝ) 1 := ae_iff.mpr (hcommon k).2.2.2.2.2.1
    have hunitζ : ∀ᵐ z ∂ζ, z ∈ univ ×ˢ Icc (0 : ℝ) 1 := ae_mono hζ hunit
    exact hunitζ.mono fun z hz => hz.2
  have hcoeff : ∀ᵐ z ∂ζ,
      |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ p.K k := by
    haveI : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
    have hb := (Measure.quasiMeasurePreserving_fst (μ := a.nu k) (ν := (volume : Measure ℝ))).ae
      (hcommon k).2.2.2.2.2.2.2.2.1
    exact ae_mono hζ ((Measure.absolutelyContinuous_of_le_smul (hcommon k).2.2.2.1).ae_le hb)
  have hpoints : ∀ᵐ z ∂ζ, PreparedSourcePoint p a k s L Extra z := by
    filter_upwards [htime, hcoeff, ae_mono hζ hatlas.2.2.2.2.2.1, hcovered, hExtra]
      with z ht hb htrue hz hE
    exact ⟨ht, hb, htrue, hz, hE⟩
  let menu : Finset Code := Finset.univ.biUnion trueMenus
  have hmenu : ∀ᵐ z ∂ζ, CommonDomain.code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2 ∈ menu := by
    filter_upwards [hpoints] with z hz
    obtain ⟨i, hi, ht⟩ := hz.true_label
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, htrue i z.1 hi hz.coefficients z.2 ht⟩
  obtain ⟨S, -, n, hn, code, decode, G, hcode, hinj, -, hG, hnull, hgood, hpos, hsource⟩ :=
    positive_source_domains ζ hζpos
      (fun z => CommonDomain.code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2)
      (CommonDomain.measurable_code (a.b k) (hcommon k).1 q χ (PreparedModel.narrow p k s) m)
      menu hmenu (PreparedSourcePoint p a k s L Extra) hpoints
  exact ⟨{ trueMenus := trueMenus
           projectedMenus := projectedMenus
           true_cover := htrue
           projected_cover := hprojected
           true_reference := htrueRef
           projected_reference := hprojectedRef
           n := n
           positive_n := hn
           code := code
           decode := decode
           measurable_code := hcode
           injective_decode := hinj
           G := G
           measurable_G := hG
           full_G := hnull
           pointwise := fun z hz => ⟨(hgood z hz).1, (hgood z hz).2.2⟩
           positive_domain := hpos
           source_point := hsource }⟩

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
