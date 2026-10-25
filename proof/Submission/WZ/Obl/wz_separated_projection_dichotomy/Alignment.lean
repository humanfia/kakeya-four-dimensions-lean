-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Alignment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentFirst
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentAnisotropic
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentWide
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentScales
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleSlices

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

/-- The finite alignment lemma. Unless the projection gains at some scale,
a strip containing the second factor also traps the third factor and an
orthogonal strip through the origin traps the first factor. -/
theorem strip_alignment {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (F G U : Finset Plane) (H : Finset Triple), H.Nonempty → H ⊆ F ×ˢ (G ×ˢ U) →
        (∀ a ∈ F, ‖a‖ ≤ 4) → (∀ x ∈ G, ‖x‖ ≤ 4) → (∀ b ∈ U, ‖b‖ ≤ 4) →
        ClosedFiniteFrostman δ (δ ^ (-η)) F → ClosedFiniteFrostman δ (δ ^ (-η)) G →
        (∀ x ∈ G, ∀ b ∈ U, 1 / 2 ≤ ‖b - x‖) →
        TripleUniform (δ ^ η) F G U H →
        (∀ a ∈ F, ∃ x b, (a, x, b) ∈ H) → (∀ b ∈ U, ∃ a x, (a, x, b) ∈ H) →
        ∀ (e : Plane) (c w : ℝ), ‖e‖ = 1 → δ ≤ w →
          (∀ x ∈ G, |inner ℝ x (perp e) - c| ≤ w) →
          ((∀ a ∈ F, |inner ℝ a e| ≤ δ ^ (-ε) * w) ∧
            ∀ b ∈ U, |inner ℝ b (perp e) - c| ≤ δ ^ (-ε) * w) ∨
          ProjectionGain δ η ε (↑H : Set Triple) := by
  classical
  let η := alignmentEta ε
  let κ := alignmentKappa ε
  obtain ⟨hκ, hη, hηκ, hκeps, htrans, hrad⟩ := alignment_parameter_bounds hε hε1
  obtain ⟨δ₀, hδ₀, hbudget⟩ := exists_alignment_scale_budget hε hε1
  refine ⟨η, δ₀, hη, hδ₀, ?_⟩
  intro δ hδ hsmall F G U H hHne hH hFnorm hGnorm hUnorm hF hG hsep huni hFon hUon e c w he hδw hstrip
  have hb : AlignmentScaleBudget δ ε η κ := hbudget δ hδ hsmall
  have hw : 0 < w := hδ.trans_le hδw
  obtain ⟨p₀, hp₀⟩ := hHne
  have hpF := (Finset.mem_product.mp (hH hp₀)).1
  have hpG := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp₀)).2).1
  have hpU := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp₀)).2).2
  have hheight : ∀ b ∈ U, |inner ℝ b (perp e) - c| ≤ 8 + w := fun b hb' =>
    strip_height_bound ((perp_norm e).trans he) (hGnorm _ hpG) (hUnorm b hb') (hstrip _ hpG)
  have hεpow : 32 ≤ δ ^ (-ε) := hb.inverse_epsilon hδ hε.le hκ.le
  by_cases hw1 : 1 ≤ w
  · left
    have hlarge : 32 * w ≤ δ ^ (-ε) * w := mul_le_mul_of_nonneg_right hεpow hw.le
    constructor
    · intro a ha
      have hproj : |inner ℝ a e| ≤ 4 :=
        (abs_real_inner_le_norm _ _).trans (by simpa only [he, mul_one] using hFnorm a ha)
      linarith
    · intro b hb'
      have h := hheight b hb'
      linarith
  have hwle : w ≤ 1 := (lt_of_not_ge hw1).le
  obtain ⟨b₀, hb₀, hmax⟩ := U.exists_max_image (fun b => |inner ℝ b (perp e) - c|) ⟨p₀.2.2, hpU⟩
  let t := max w |inner ℝ b₀ (perp e) - c|
  have hwt0 : w ≤ t := le_max_left _ _
  have hδt : δ ≤ t := hδw.trans hwt0
  have ht : 0 < t := hδ.trans_le hδt
  have ht16 : t ≤ 16 := max_le (by linarith) ((hheight b₀ hb₀).trans (by linarith))
  have hUstrip : ∀ b ∈ U, |inner ℝ b (perp e) - c| ≤ t :=
    fun b hb' => (hmax b hb').trans (le_max_right _ _)
  have hκpow : 1 ≤ δ ^ (-κ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hb.scale_le_one (by linarith)
  let h := δ ^ (-κ) * t
  have hh : 0 < h := by dsimp [h]; positivity
  have hth : t ≤ h := by dsimp [h]; nlinarith
  have hfar : ∀ x ∈ G, ∀ b ∈ U, ‖b - x‖ ≤ 8 := by
    intro x hx b hb'
    exact (norm_sub_le _ _).trans (by linarith [hGnorm x hx, hUnorm b hb'])
  by_cases hFstrip : ∀ a ∈ F, |inner ℝ a e| ≤ h
  swap
  · right
    push_neg at hFstrip
    obtain ⟨a, ha, houtside⟩ := hFstrip
    obtain ⟨x, b, hp⟩ := hFon a ha
    have hxG := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).1
    have hbU := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).2
    have hTsub : secondFiber G H a b ⊆ G := Finset.filter_subset _ _
    have hTne : (secondFiber G H a b).Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hxG, hp⟩⟩
    exact alignment_first_gain hb hδ hε hε1 hκ.le hηκ hδt he (hFnorm a ha) hG hTsub hTne
      (huni.secondFiber_dense hH hp)
      (fun x hx => (hstrip x (hTsub hx)).trans hwt0) (hUstrip b hbU)
      (fun x hx => by simpa only [norm_sub_rev] using hfar x (hTsub hx) b hbU)
      houtside.le (fun x hx => (Finset.mem_filter.mp hx).2)
  by_cases htight : t ≤ δ ^ (-ε + κ) * w
  · left
    have hhsmall : h ≤ δ ^ (-ε) * w := by
      calc h ≤ δ ^ (-κ) * (δ ^ (-ε + κ) * w) := mul_le_mul_of_nonneg_left htight (by positivity)
        _ = _ := by rw [← mul_assoc, ← Real.rpow_add hδ]; congr 1; congr 1; ring
    exact ⟨fun a ha => (hFstrip a ha).trans hhsmall,
      fun b hb' => (hUstrip b hb').trans (hth.trans hhsmall)⟩
  right
  have hlarge : δ ^ (-ε + κ) * w < t := lt_of_not_ge htight
  have hwt : w ≤ t / 2 := hb.narrow_relative_width hδ hε.le hw hlarge
  have hpin : |inner ℝ b₀ (perp e) - c| = t := by
    have hlt : w < t := by linarith
    dsimp [t] at hlt ⊢
    by_cases hwheight : w ≤ |inner ℝ b₀ (perp e) - c|
    · exact (max_eq_right hwheight).symm
    · rw [max_eq_left (le_of_not_ge hwheight)] at hlt
      exact (lt_irrefl _ hlt).elim
  obtain ⟨a₀, x₀, hp⟩ := hUon b₀ hb₀
  have ha₀ := (Finset.mem_product.mp (hH hp)).1
  have hx₀ := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).1
  let T : G → Finset Plane := fun x => tripleFiber F H x b₀
  have hT : ∀ x, T x ⊆ F := fun _ => Finset.filter_subset _ _
  have hTne : ∃ x, (T x).Nonempty :=
    ⟨⟨x₀, hx₀⟩, a₀, Finset.mem_filter.mpr ⟨ha₀, hp⟩⟩
  have hdensity : δ ^ η * (G.card : ℝ) * (F.card : ℝ) ≤ ∑ x, ((T x).card : ℝ) :=
    huni.third_row_dense hH hp
  have hQ : ∀ x, ∀ a ∈ T x, (a, (x : Plane), b₀) ∈ (↑H : Set Triple) :=
    fun x a ha => (Finset.mem_filter.mp ha).2
  have hηε : η ≤ ε / 2 := hηκ.trans hκeps.le
  by_cases hh1 : h ≤ 1
  · obtain ⟨hscale, hratio⟩ := hb.anisotropic_radial_scale hδ hε.le hκ.le hw ht hlarge
    have hht : h / t ≤ δ ^ (-κ) := by dsimp [h]; rw [mul_div_cancel_right₀ _ ht.ne']
    exact alignment_anisotropic_gain T hb hδ hε hε1 hη.le hηε hδw hh hh1 ht hth hwt hscale hratio hht
      he hF hG hFnorm hFstrip hstrip hpin (fun x hx => hsep x hx b₀ hb₀)
      (fun x hx => hfar x hx b₀ hb₀) hT hTne hdensity hQ
  · obtain ⟨hscale, hratio⟩ := hb.wide_radial_scale hδ hε.le hw ht16 hlarge
    have htt : 1 / t ≤ δ ^ (-κ) := (div_le_iff₀ ht).mpr (lt_of_not_ge hh1).le
    exact alignment_wide_gain T hb hδ hε hε1 hη.le hηε hδw hscale ht ht16 hwt hratio htt
      ((perp_norm e).trans he) hF hG hFnorm hstrip hpin.ge (fun x hx => hsep x hx b₀ hb₀)
      (fun x hx => hfar x hx b₀ hb₀) hT hTne hdensity hQ

end WangZahlLot.Obl.wz_separated_projection_dichotomy
