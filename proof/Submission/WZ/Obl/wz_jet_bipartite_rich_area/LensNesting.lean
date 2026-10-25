-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.LensNesting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LensSlope
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactCrossing

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set

/-- Oppositely ordered contacts on two upper-curvature curves produce two
crossings of the lower curves, one between each pair of same-row contacts. -/
theorem exists_lens_of_opposite_contacts {f h b₀ b₁ : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hb₀ : ContDiff ℝ 2 b₀) (hb₁ : ContDiff ℝ 2 b₁)
    {x₀ x₁ y₁ y₀ c δ η : ℝ}
    (hx : x₀ < x₁) (hmid : x₁ < y₁) (hy : y₁ < y₀)
    (hcf₀ : ∀ t ∈ uIcc x₀ x₁, c ≤ deriv (deriv f) t-deriv (deriv b₀) t)
    (hcf₁ : ∀ t ∈ uIcc x₀ x₁, c ≤ deriv (deriv f) t-deriv (deriv b₁) t)
    (hch₁ : ∀ t ∈ uIcc y₁ y₀, c ≤ deriv (deriv h) t-deriv (deriv b₁) t)
    (hch₀ : ∀ t ∈ uIcc y₁ y₀, c ≤ deriv (deriv h) t-deriv (deriv b₀) t)
    (hfx₀ : NearContact δ η f b₀ x₀) (hfx₁ : NearContact δ η f b₁ x₁)
    (hhy₁ : NearContact δ η h b₁ y₁) (hhy₀ : NearContact δ η h b₀ y₀)
    (hroomx : 2*δ < c/2*(x₁-x₀)^2-η*(x₁-x₀))
    (hroomy : 2*δ < c/2*(y₀-y₁)^2-η*(y₀-y₁)) :
    ∃ l ∈ Ioo x₀ x₁, ∃ u ∈ Ioo y₁ y₀,
      b₀ l=b₁ l ∧ b₀ u=b₁ u ∧ l<u ∧ u-l<y₀-x₀ := by
  have hxsign := contact_pair_dominance hf hb₀ hb₁ hx hcf₀ hcf₁ hfx₀ hfx₁ hroomx
  have hysign := contact_pair_dominance hh hb₁ hb₀ hy hch₁ hch₀ hhy₁ hhy₀ hroomy
  have hcont : Continuous (fun t => b₀ t-b₁ t) := hb₀.continuous.sub hb₁.continuous
  obtain ⟨l, hl, hel⟩ := intermediate_value_Icc' hx.le hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (b₀ x₁-b₁ x₁) (b₀ x₀-b₁ x₀) from ⟨hxsign.2.le, hxsign.1.le⟩)
  obtain ⟨u, hu, heu⟩ := intermediate_value_Icc hy.le hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (b₀ y₁-b₁ y₁) (b₀ y₀-b₁ y₀) by
      constructor <;> linarith [hysign.1, hysign.2])
  have hxl : x₀<l := lt_of_le_of_ne hl.1 (by intro he; subst l; linarith [hxsign.1])
  have hlx : l<x₁ := lt_of_le_of_ne hl.2 (by intro he; subst l; linarith [hxsign.2])
  have hyu : y₁<u := lt_of_le_of_ne hu.1 (by intro he; subst u; linarith [hysign.1])
  have huy : u<y₀ := lt_of_le_of_ne hu.2 (by intro he; subst u; linarith [hysign.2])
  exact ⟨l, ⟨hxl, hlx⟩, u, ⟨hyu, huy⟩, sub_eq_zero.mp hel,
    sub_eq_zero.mp heu, by linarith, by linarith⟩

/-- If the inner row contact lies in a lens of the upper curves, the new
lower-curve lens contracts by the within-to-cross curvature ratio, down to
the scale set by the slope error. -/
theorem exists_shorter_lens_of_opposite_contacts {f h b₀ b₁ : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hb₀ : ContDiff ℝ 2 b₀) (hb₁ : ContDiff ℝ 2 b₁)
    {L U x₀ x₁ y₁ y₀ c M δ η : ℝ}
    (hc : 0<c) (hLU : L<U) (hyin : y₀ ∈ Icc L U)
    (heqL : f L=h L) (heqU : f U=h U)
    (hwithin : ∀ t ∈ Icc L U, |deriv (deriv f) t-deriv (deriv h) t| ≤ M)
    (hx : x₀<x₁) (hmid : x₁<y₁) (hy : y₁<y₀)
    (hcf₀ : ∀ t ∈ Icc x₀ y₀, c ≤ deriv (deriv f) t-deriv (deriv b₀) t)
    (hcf₁ : ∀ t ∈ Icc x₀ y₀, c ≤ deriv (deriv f) t-deriv (deriv b₁) t)
    (hch₁ : ∀ t ∈ Icc x₀ y₀, c ≤ deriv (deriv h) t-deriv (deriv b₁) t)
    (hch₀ : ∀ t ∈ Icc x₀ y₀, c ≤ deriv (deriv h) t-deriv (deriv b₀) t)
    (hfx₀ : NearContact δ η f b₀ x₀) (hfx₁ : NearContact δ η f b₁ x₁)
    (hhy₁ : NearContact δ η h b₁ y₁) (hhy₀ : NearContact δ η h b₀ y₀)
    (hroomx : 2*δ < c/2*(x₁-x₀)^2-η*(x₁-x₀))
    (hroomy : 2*δ < c/2*(y₀-y₁)^2-η*(y₀-y₁)) :
    ∃ l ∈ Ioo x₀ x₁, ∃ u ∈ Ioo y₁ y₀,
      b₀ l=b₁ l ∧ b₀ u=b₁ u ∧ l<u ∧ c*(u-l)<M*(U-L)+2*η := by
  have hxy : x₀<y₀ := hx.trans (hmid.trans hy)
  have hsubx : uIcc x₀ x₁ ⊆ Icc x₀ y₀ :=
    uIcc_subset_Icc ⟨le_rfl, hxy.le⟩ ⟨hx.le, (hmid.trans hy).le⟩
  have hsuby : uIcc y₁ y₀ ⊆ Icc x₀ y₀ :=
    uIcc_subset_Icc ⟨(hx.trans hmid).le, hy.le⟩ ⟨hxy.le, le_rfl⟩
  obtain ⟨l, hl, u, hu, hel, heu, hlu, hwidth⟩ :=
    exists_lens_of_opposite_contacts hf hh hb₀ hb₁ hx hmid hy
      (fun t ht => hcf₀ t (hsubx ht)) (fun t ht => hcf₁ t (hsubx ht))
      (fun t ht => hch₁ t (hsuby ht)) (fun t ht => hch₀ t (hsuby ht))
      hfx₀ hfx₁ hhy₁ hhy₀ hroomx hroomy
  have hbound := two_slope_contacts_lens_width hh hf hb₀ hLU hyin heqL.symm heqU.symm
    (by simpa only [abs_sub_comm] using hwithin)
    (fun t ht => hcf₀ t (uIcc_subset_Icc ⟨hxy.le, le_rfl⟩ ⟨le_rfl, hxy.le⟩ ht))
    hhy₀.2 hfx₀.2
  rw [abs_of_pos (sub_pos.mpr hxy)] at hbound
  exact ⟨l, hl, u, hu, hel, heu, hlu,
    (mul_lt_mul_of_pos_left hwidth hc).trans_le hbound⟩

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
