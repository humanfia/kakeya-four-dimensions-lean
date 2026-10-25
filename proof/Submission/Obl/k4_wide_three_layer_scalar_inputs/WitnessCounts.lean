import Submission.Obl.k4_wide_three_layer_scalar_inputs.WitnessMenus
import Submission.Obl.k4_wide_three_layer_scalar_inputs.WitnessEntries
import Submission.Obl.k4_wide_three_layer_scalar_inputs.WitnessFreezing
import Submission.Obl.k4_wide_three_layer_scalar_inputs.OffsetCount

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context

open Set MeasureTheory Finset
open Inherited.Native Inherited.Core Inherited.MatchGML2D

noncomputable section

open scoped Classical

variable {α : Type} [MeasurableSpace α] (W : Context α)

/-- The coarse list count is the proved jet count for the earlier heavy
coarse entries on this very key. -/
theorem coarse_candidate_count [IsFiniteMeasure (W.cfg.π W.k)]
    {r vp Rc s₁ Lv Xb B δ A w η R₀ : ℝ}
    (hb : Measurable (W.cfg.b W.k)) (hρμ : W.layers.ρs ≤ W.cfg.μ W.k)
    (hN : 0 < W.cfg.N W.k) (hχ : W.χ = W.cfg.N W.k ^ (-vp)) (hD : 0 < W.D)
    (hXb : 2 * W.cfg.N W.k ^ W.ε ≤ Xb)
    (hdrift : W.ζ + W.χ ≤ W.D / 4)
    (hsmallD : 4 * W.m + W.q * (W.ζ + W.χ) ≤ 4 * W.D)
    (hnull : W.layers.ρs (horizSet (W.cfg.b W.k) W.ζ)ᶜ = 0)
    (hBsh : 8 * (11 * (160 * W.cfg.N W.k ^ W.ε) / W.width 0) ≤ B)
    (key : Fin 3 → ℤ) (hk : key ∈ W.KB)
    (hn : KeyNum (W.cfg.N W.k) (W.cfg.K W.k) W.cfg.d r vp Rc s₁ W.t₀ W.q W.m W.ζ Lv
      (W.width 0) Xb W.K₁ B (W.tolerance 0) (W.tolerance 0) δ W.Mst A w η R₀ key)
    (hcap : ∀ sp, 0 ≤ sp → sp ≤ Rc → JointCapAt (W.cfg.μ W.k) (W.cfg.π W.k)
      (W.cfg.b W.k) (W.cfg.N W.k) (W.cfg.K W.k) W.cfg.d r sp vp) :
    ((W.coarseCandidates key).card : ℝ) ≤ A * (W.Mst / δ) ^ W.cfg.d := by
  have hχp : 0 < W.χ := hχ.symm ▸ Real.rpow_pos_of_pos hN _
  have hm : 0 < W.m := hn.hm
  have hsmall : W.q * (W.ζ + W.χ) ≤ 4 * W.D := by linarith
  have hMst : 0 < W.Mst := hn.hW₁.trans_le hn.hW₁M
  have hδ : 0 < δ := by linarith [hn.hW₁, hn.hW₂, hn.hδW]
  have hA : 0 ≤ A := by linarith [hn.hA1]
  let c := W.coarseCandidates key
  rcases c.eq_empty_or_nonempty with hc | ⟨j₀, hj₀⟩
  · rw [show W.coarseCandidates key = ∅ from hc]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hheavy : ∀ j ∈ c, pieceHeavy W.cfg.comparisonData W.k W.s W.datum W.m W.K₁
      0 j (W.cfg.j W.k W.s W.i) key := by
    intro j hj
    change j ∈ W.coarseCandidates key at hj
    rw [coarseCandidates, if_pos hk, Finset.mem_filter] at hj
    exact hj.2.1
  let J : Finset (W.HeavyPiece 0 key) := c.subtype fun j =>
    pieceHeavy W.cfg.comparisonData W.k W.s W.datum W.m W.K₁ 0 j
      (W.cfg.j W.k W.s W.i) key
  have hJcard : J.card = c.card := by
    exact (Finset.card_subtype _ c).trans
      (congrArg Finset.card (Finset.filter_eq_self.mpr hheavy))
  have hT : W.reference 0 key = W.q * W.cfg.N W.k ^ (-vp) * W.m *
      (W.width 0) ^ W.cfg.d * (W.cfg.π W.k {v | ⌊v / W.cfg.N W.k ^ (-vp)⌋ = key 0}).toReal := by
    unfold reference keyRef
    rw [hχ] <;> rfl
  have hTpos := W.entry_reference_pos hχ (hcap 0 le_rfl hn.hRc0) hρμ hN 0 key
    ⟨j₀, hheavy j₀ hj₀⟩
  have hcount := slot_count hb hρμ hn hcap hT hTpos (measure_ne_top _ _) hnull
    (W.entryLabels 0 key) (W.entryGraph 0 key)
    (W.entryLabels_measurable hb 0 key) (W.entryLabels_disjoint 0 key)
    (W.entry_floor 0 key) hn.hW₁M
    (by simpa only [← hχ] using W.entry_graph hN hχp hD hXb hdrift hsmall 0 key)
    (W.entry_coefficients hN hχp hD hdrift hsmallD hnull 0 hBsh key)
    (blockKeyCoeff (W.cfg.F W.k W.s W.i) W.a W.χ W.m W.q W.t₀ key)
    W.Mst le_rfl J (by
      intro j hj e
      have hcj : j.1 ∈ c := Finset.mem_subtype.mp hj
      change j.1 ∈ W.coarseCandidates key at hcj
      rw [coarseCandidates, if_pos hk, Finset.mem_filter] at hcj
      exact hcj.2.2 e)
  simpa only [hJcard] using hcount

def fineCandidates (γ : W.Coarse) (h : Fin 3) : Finset (W.HeavyPiece h (W.key γ)) :=
  Finset.univ.filter fun j => W.fineValid γ h j.1

def offsetBins (γ : W.Coarse) (h : Fin 3) (Δ : ℝ) : Finset ℤ :=
  (W.fineCandidates γ h).image fun j =>
    ⌊(W.physicalOffset γ h j.1 / W.a) / W.cfg.N W.k ^ (-Δ)⌋

theorem mem_offsetBins (γ : W.Coarse) (h : Fin 3) (Δ : ℝ)
    (j : Fin (W.layers.np h)) (hj : W.fineValid γ h j) :
    ⌊(W.physicalOffset γ h j / W.a) / W.cfg.N W.k ^ (-Δ)⌋ ∈ W.offsetBins γ h Δ := by
  exact Finset.mem_image.mpr ⟨⟨j, hj.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

/-- The fine offset menu is counted from the unchanged earlier marginal
floors, using the supplied full-strip agreement and its short variation. -/
theorem fine_offset_count [IsFiniteMeasure (W.cfg.π W.k)]
    {r vp Rc s₁ Lv Xb B δ A w η R₀ H : ℝ}
    (hb : Measurable (W.cfg.b W.k)) (hρμ : W.layers.ρs ≤ W.cfg.μ W.k)
    (hN : 0 < W.cfg.N W.k) (hχ : W.χ = W.cfg.N W.k ^ (-vp)) (hD : 0 < W.D)
    (hXb : 2 * W.cfg.N W.k ^ W.ε ≤ Xb) (hmD : W.m ≤ W.D)
    (hdrift : W.ζ + W.χ ≤ W.D / 4)
    (hsmallD : 4 * W.m + W.q * (W.ζ + W.χ) ≤ 4 * W.D)
    (hnull : W.layers.ρs (horizSet (W.cfg.b W.k) W.ζ)ᶜ = 0)
    (γ : W.Coarse) (h : Fin 3) (Δ : ℝ)
    (hBsh : 8 * (11 * (160 * W.cfg.N W.k ^ W.ε) / W.width h) ≤ B)
    (haA : W.width h ≤ W.a) (hH : 2 * W.cfg.N W.k ^ W.ε + 1 ≤ H)
    (hwide : 98304 * W.E * (W.q + W.m / W.D) ≤ W.width h)
    (hMst : W.Mst ≤ 16 * H * W.a / W.width h)
    (hn : KeyNum (W.cfg.N W.k) (W.cfg.K W.k) W.cfg.d r vp Rc s₁ W.t₀ W.q W.m W.ζ Lv
      (W.width h) Xb W.K₁ B (W.tolerance h) (W.tolerance h) δ W.Mst A w η R₀ (W.key γ))
    (hcap : ∀ sp, 0 ≤ sp → sp ≤ Rc → JointCapAt (W.cfg.μ W.k) (W.cfg.π W.k)
      (W.cfg.b W.k) (W.cfg.N W.k) (W.cfg.K W.k) W.cfg.d r sp vp) :
    ((W.offsetBins γ h Δ).card : ℝ) ≤ A * ((16 * H * W.a / W.width h) / δ) ^ W.cfg.d := by
  have hχp : 0 < W.χ := hχ.symm ▸ Real.rpow_pos_of_pos hN _
  have hsmall : W.q * (W.ζ + W.χ) ≤ 4 * W.D := by linarith [hn.hm]
  have hP : 0 < W.cfg.N W.k ^ W.ε := Real.rpow_pos_of_pos hN _
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hA : 0 ≤ A := by linarith [hn.hA1]
  have hδ : 0 < δ := by linarith [hn.hW₁, hn.hW₂, hn.hδW]
  let J := W.fineCandidates γ h
  rcases J.eq_empty_or_nonempty with hJ | ⟨j₀, hj₀⟩
  · have hJ0 : W.fineCandidates γ h = ∅ := hJ
    rw [offsetBins, hJ0]
    simp only [Finset.image_empty, Finset.card_empty, Nat.cast_zero]
    have ha0 : 0 < W.a := Real.rpow_pos_of_pos hN _
    have hah : 0 < W.width h := hn.ha
    positivity
  have hT : W.reference h (W.key γ) = W.q * W.cfg.N W.k ^ (-vp) * W.m *
      (W.width h) ^ W.cfg.d *
        (W.cfg.π W.k {v | ⌊v / W.cfg.N W.k ^ (-vp)⌋ = W.key γ 0}).toReal := by
    unfold reference keyRef
    rw [hχ] <;> rfl
  have hTpos := W.entry_reference_pos hχ (hcap 0 le_rfl hn.hRc0) hρμ hN h (W.key γ) j₀
  have hfreeze : ∀ j ∈ J, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![W.t₀ + W.q * τ, domY W.χ W.m W.q (W.key γ) τ y]
        (W.layers.G h j.1 - W.layers.G 0 (W.coarseIndex γ)) -
          W.physicalOffset γ h j.1| ≤ W.width h := by
    intro j hj τ hτ y hy
    exact (W.fine_key_freezing hN hχp hD hmD hdrift γ h j.1
      (Finset.mem_filter.mp hj).2 τ hτ y hy).trans hwide
  have hc := count_frozen_sheet_offsets hb hρμ hn hcap hT hTpos (measure_ne_top _ _) hnull
    (W.entryLabels h (W.key γ)) (fun j => W.layers.G h j.1)
    (W.layers.G 0 (W.coarseIndex γ)) (W.datum.degree 0 _)
    (fun j => W.datum.degree h j.1)
    (W.entryLabels_measurable hb h (W.key γ)) (W.entryLabels_disjoint h (W.key γ))
    (W.entry_floor h (W.key γ))
    (by simpa only [entryGraph, ← hχ] using W.entry_graph hN hχp hD hXb hdrift hsmall h (W.key γ))
    (by simpa only [entryGraph, ← hχ] using
      W.entry_coefficients hN hχp hD hdrift hsmallD hnull h hBsh (W.key γ))
    haA hH0 hMst J (fun j => W.physicalOffset γ h j.1)
    (by
      intro j hj
      exact W.fine_offset_bound hN γ h j.1 (Finset.mem_filter.mp hj).2 rfl haA hH
        (hfreeze j hj))
    (by
      intro j hj τ hτ y hy
      rw [← hχ]
      exact (hfreeze j hj τ hτ y hy).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg hN.le _) hH1))
  have hi : ((W.offsetBins γ h Δ).card : ℝ) ≤ J.card := by
    exact_mod_cast Finset.card_image_le
  exact hi.trans hc.1

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context
