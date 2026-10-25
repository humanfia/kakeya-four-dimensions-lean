-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedComparisonAt.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedTrueFamilies
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedProjectedFamilies
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedFamilyComparison
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.LiteralPartnerMenus

/-! The true/projected comparison at one sample, on the actual original source law. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open CommonDomain
open scoped ENNReal Classical

noncomputable section

def commonNativeCapConstant (K : ℝ) : ℝ := 27000000 * K * (2 * K + 5)

def commonComparisonReference (p : Parameters) (k : ℕ) (s H aTable : ℝ) : ℝ :=
  (aTable / PreparedModel.width p k s) ^ p.d *
    (475200 * p.K k ^ 5 + 360 * H ^ 4 * p.K k)

structure PreparedComparison {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) (k : ℕ) (s H q χ m aTable Fprune Llist ε C Λ : ℝ)
    (L : ProjLayer α) (ζ : Measure (α × ℝ)) (assign : α × ℝ → Fin (a.n k s))
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ) where
  law : Measure (α × ℝ)
  le : law ≤ ζ
  mass_budget : ζ univ ≤ law univ + ENNReal.ofReal (commonComparisonReference p k s H aTable / Fprune) +
    ENNReal.ofReal (C * (6 * commonNativeCapConstant (p.K k)) * Λ ^ (-ε) *
      commonComparisonReference p k s H aTable)
  tru : α × ℝ → Fin (a.n k s) × Bool
  lab : α × ℝ → Fin L.n
  measurable_tru : Measurable tru
  measurable_lab : Measurable lab
  partners : Fin (a.n k s) → Code → Finset (Fin L.n)
  reverse : Fin L.n → Code → Finset (Fin (a.n k s))
  card_partners : ∀ i c, ((partners i c).card : ℝ) ≤ 2 * (Llist * Λ ^ p.d)
  card_reverse : ∀ j c, ((reverse j c).card : ℝ) ≤ Llist * Λ ^ p.d
  source : ∀ᵐ z ∂law, z.2 ∈ Icc (0 : ℝ) 1 ∧
    z.1 ∈ a.B k s (tru z).1 ∧ z.2 ∈ a.block k s (tru z).1 ∧ z.1 ∈ L.C (lab z) ∧
    lab z ∈ partners (tru z).1 (code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2) ∧
    (tru z).1 ∈ reverse (lab z) (code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2) ∧
    tru z = (assign z, nativeBranch p a k s (assign z) z)
  agreement : ∀ᵐ z ∂law, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
    ‖trueCandidate p a k s g q χ (PreparedModel.narrow p k s) m
        (code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2) (tru z) (emb x) -
      projectedCandidate (L.G (lab z)) q (PreparedModel.narrow p k s) m
        (code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2) (emb x)‖ ≤ Λ * aTable

/-- Every positive current source outside the native exception has the actual
original-label comparison. All geometric, mesh and reference fields are
constructed from the prepared model and the native source-family constructor. -/
theorem prepared_comparison_at {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {R s H La q χ m : ℝ} {k : ℕ} (hs : 0 ≤ s) (hatlas : a.AtlasAt p R k s)
    (L : ProjLayer α)
    (hL : L.Good (p.N k) H p.d p.ell La s χ (a.b k) (a.P k) (a.pi k) (a.rho k))
    (hH : 1 ≤ H) (hq : 0 < q) (hqQ : q ≤ a.q k s) (hχ : 0 < χ)
    (hχQ : χ ≤ a.q k s) (hχQg : χ ≤ a.q k s * PreparedModel.narrow p k s)
    (hm : 0 < m) (hmQg : m ≤ a.q k s * PreparedModel.narrow p k s) (hmβ : m ≤ L.β)
    (hqg : q * PreparedModel.narrow p k s ≤ m)
    {aTable Fprune Llist ε C Λ r v S σ : ℝ} (haTable : 0 < aTable)
    (Kchart : NNReal) (hKchart : 4 * (projectedSheetConstant * H ^ 3) ≤ Kchart)
    (hprojerr : 4 * (H * PreparedModel.width p k s) ≤ aTable)
    (E : Set (α × ℝ)) (assign : α × ℝ → Fin (a.n k s))
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
    (hfactory : TrueSourceFactory p a k s q χ m aTable Kchart E assign g)
    (hχeq : χ = p.N k ^ (-v)) (hS : 0 ≤ S) (haMin : p.N k ^ (-S) ≤ aTable)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 24)
    (hδq : (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * q * σ)
    (hδχ : (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * χ * σ)
    (hδm : (2 * p.K k + 1) * p.N k ^ (-r) ≤ 100 * m * σ)
    (hmesh : 2 * (Kchart : ℝ) * (3 * σ) ≤ aTable / 2)
    (hcap : ∀ t : ℝ, 0 ≤ t → t ≤ S → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = z ∧
        ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-t)⌋ = j ∧
        ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * t)) *
        a.pi k {w : ℝ | ⌊w / p.N k ^ (-v)⌋ = v₀})
    (hFprune : 0 < Fprune) (hLlist : 1 ≤ Llist)
    (hLfloor : 14 * commonNativeCapConstant (p.K k) * Fprune ≤ Llist)
    (Match : ComparisonEstimate 4 p.d ε C) (hC : 0 ≤ C)
    (hΛ : C * Llist ^ (1 / ε) ≤ Λ) (hΛ1 : 1 ≤ Λ)
    (ζ : Measure (α × ℝ)) [IsFiniteMeasure ζ] (hζ : ζ ≤ a.mu k) (hζpos : ζ univ ≠ 0)
    (hζE : ζ E = 0) (hcovered : ∀ᵐ z ∂ζ, z ∈ L.covered) :
    Nonempty (PreparedComparison p a k s H q χ m aTable Fprune Llist ε C Λ L ζ assign g) := by
  obtain ⟨D⟩ := exists_prepared_source_domains p hp a hcommon hatlas L hL hH hq hqQ hχ hχQ hχQg
    hm hmQg hmβ ζ hζ hζpos hcovered (fun _ => True) (Filter.Eventually.of_forall fun _ => trivial)
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hQ1 : a.q k s ≤ 1 := by
    have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := a.T k s)
    simpa [PreparedModel.q] using inv_le_one_of_one_le₀ h
  have hg : 0 < PreparedModel.narrow p k s := Real.rpow_pos_of_pos hN _
  have hg1 : PreparedModel.narrow p k s ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos ((by norm_num : (1 : ℝ) ≤ 2).trans (hp.1 k))
    have hell : 0 < p.ell := hp.2.2.2.2.2.2.2.1
    nlinarith only [hell, hs]
  have hresolve := D.resolved hp hq hχ (hχQ.trans hQ1) hg hg1 hm
    (Real.rpow_nonneg hN.le _) hδq hδχ hδm
  choose M hbase hdiam hvolume hnative using fun u =>
    D.exists_native_mesh hp hcommon hζ hq hχ hm hqg hχeq hS hσ hσsmall haTable haMin hresolve hcap u
  obtain ⟨full₁, oldTrue, hTrue, hsource₁, hcanonical₁, hcurrent₁⟩ :=
    D.exists_true_families Kchart E assign g hfactory hζ hζE M hbase
  obtain ⟨full₂, oldProjected, hProjected, hsource₂, hcanonical₂⟩ :=
    D.exists_projected_families hp hL hH hq (hqQ.trans hQ1) hχ hm hqg hmβ Kchart hKchart hprojerr M hbase
  have hsignal : Measurable (fun z : α × ℝ => eval (a.x k z.1 z.2) (a.P k)) := by
    have hb : Measurable (a.b k) := (hcommon k).1
    apply (MvPolynomial.continuous_eval _).measurable.comp
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> dsimp [PreparedModel.x, Submission.Lib.K4ContactNormalization.point] <;> fun_prop
  have hBcap : 0 < commonNativeCapConstant (p.K k) := by
    have hK0 : 0 < p.K k := zero_lt_one.trans_le hK
    unfold commonNativeCapConstant
    positivity
  obtain ⟨ρ, tru, lab, forward, reverse, htru, hlab, htruEq, hlabEq, hρ, hmass, hforward,
      hreverse, hsource, hagreement⟩ :=
    D.compare_families hp hcommon hq hχ hm Kchart M
      (fun z => eval (a.x k z.1 z.2) (a.P k)) hsignal full₁ full₂ oldTrue oldProjected
      hTrue hProjected hsource₁ hsource₂ haTable hBcap hFprune hLlist hLfloor
      (D.palette_ne_zero_of_caps hζ hχeq hS hcap)
      (fun u => by simpa only [hdiam u] using hmesh) hvolume hnative Match hC hΛ hΛ1
  let partners (i : Fin (a.n k s)) (c : Code) := literalMenu D.decode (fun u => forward u i) c
  let rev (j : Fin L.n) (c : Code) := literalMenu D.decode (fun u => reverse u j) c
  have hB : 0 ≤ Llist * Λ ^ p.d := mul_nonneg (zero_le_one.trans hLlist)
    (Real.rpow_nonneg (by linarith only [hΛ1]) _)
  have hbranch : ∀ᵐ z ∂ζ, oldTrue (D.code z) ((full₁ (D.code z)).index z) =
      (assign z, nativeBranch p a k s (assign z) z) := D.ae_of_domains _ hcurrent₁
  have hW₁ : ∀ᵐ z ∂ζ, z ∈ (full₁ (D.code z)).witness ((full₁ (D.code z)).index z) :=
    D.ae_of_domains _ (fun u => (full₁ u).assigned)
  have hW₂ : ∀ᵐ z ∂ζ, z ∈ (full₂ (D.code z)).witness ((full₂ (D.code z)).index z) :=
    D.ae_of_domains _ (fun u => (full₂ u).assigned)
  refine ⟨{ law := ρ
            le := hρ
            mass_budget := hmass
            tru := tru
            lab := lab
            measurable_tru := htru
            measurable_lab := hlab
            partners := partners
            reverse := rev
            card_partners := ?_
            card_reverse := ?_
            source := ?_
            agreement := ?_ }⟩
  · intro i c
    exact literalMenu_card_le D.decode (fun u => forward u i) (mul_nonneg (by norm_num) hB)
      (fun u => hforward u i) c
  · intro j c
    exact literalMenu_card_le D.decode (fun u => reverse u j) hB (fun u => hreverse u j) c
  · filter_upwards [hsource, ae_mono hρ hbranch] with z hz hbr
    obtain ⟨hG, hB, ht, hC, hf, hr⟩ := hz
    have hc := (D.pointwise z hG).2
    refine ⟨(D.pointwise z hG).1.time, hB, ht, hC, ?_, ?_, (htruEq z).trans hbr⟩
    · change lab z ∈ literalMenu D.decode (fun u => forward u (tru z).1)
        (code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2)
      rw [← hc, literalMenu_at_decode D.decode D.injective_decode]
      exact hf
    · change (tru z).1 ∈ literalMenu D.decode (fun u => reverse u (lab z))
        (code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2)
      rw [← hc, literalMenu_at_decode D.decode D.injective_decode]
      exact hr
  · filter_upwards [hagreement, hsource, ae_mono hρ hW₁, ae_mono hρ hW₂] with z hz hsrc hw₁ hw₂
    have hc := (D.pointwise z hsrc.1).2
    have hcanon₁ := hcanonical₁ (D.code z) ((full₁ (D.code z)).index z) ⟨z, hw₁⟩
    have hcanon₂ := hcanonical₂ (D.code z) ((full₂ (D.code z)).index z) ⟨z, hw₂⟩
    rw [hcanon₁, hcanon₂, ← htruEq z, ← hlabEq z, hc] at hz
    exact hz

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
