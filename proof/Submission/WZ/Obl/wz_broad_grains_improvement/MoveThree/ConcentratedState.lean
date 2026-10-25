-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ConcentratedState.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ThickThin
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalReduction
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainReduction
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainBlocks

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (assignedFiber)
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

/-- The remaining concentration case, after the thick-grain, planiness,
packet, natural-neighborhood, and small-local-coefficient alternatives have
all been resolved. The stability power is uniform in the family. -/
structure ConcentratedGrainData (ω ζ δ ε b ρ c : ℝ) (p : ℕ)
    (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) where
  S : Finset (Fin n)
  Z : Fin n → Set V
  N : ℕ
  y : Fin N → V
  w : Fin N → V
  f : Fin n → Fin N
  a : ℝ
  g : ℝ
  L : ℕ
  z : Fin L → V
  e : Fin L → V ≃ₗᵢ[ℝ] V
  Hg : Fin L → Set V
  γ : Fin L → Fin N
  m : ℝ
  cover : C δ (ε / 4) n x v Y S Z ρ N y w f True
  lower_scale : δ ^ (1 - ω / 100) ≤ ρ
  coefficient_pos : 0 < g
  broad : Broad ω ζ δ (ε / 4) ρ n N v S Z f
  grains : GrainWitnesses δ (ε / 4) n x v S Z ρ N y w f a c 0 g L z e Hg γ m
  thin : a < 2 * δ ^ (1 - b)
  length_stop : δ ^ ζ * (ρ / δ) * N / n ≤ c
  scale_stop : ρ ≤ δ ^ (ω / 100)
  K : ℕ
  packet : Fin L → Fin K
  anchor : Fin K → Fin L
  natural : ∀ j, Hg j ≠ ∅ → grainNear a ρ c z e (anchor (packet j)) j
  disjoint : ∀ k l, k ≠ l → Disjoint (assignedFiber packet Hg k) (assignedFiber packet Hg l)
  Q : Finset (Fin L)
  selected_nonempty : Q.Nonempty
  retained : O (δ ^ (ε / 4 + ε / 80)) * ∑ j, μ (Hg j) ≤ ∑ j ∈ Q, μ (Hg j)
  large : δ ^ (-ζ) < grainCoefficient a ρ c z e Q
  above_stability : 2 * (2 : ℝ) ^ p < grainCoefficient a ρ c z e Q
  balanced : ∀ i ∈ Q, ∀ j ∈ Q,
    (μ (Hg i)).toReal ≤ δ ^ (-(ε / 80)) * (μ (Hg j)).toReal
  stable : ∀ R ⊆ Q, (Q.card : ℝ) ≤ 2 * R.card →
    grainCoefficient a ρ c z e Q ≤ 2 ^ p * grainCoefficient a ρ c z e R

/-- All reductions through the stable large-coefficient case, with one
uniform choice of errors and cutoff. -/
theorem gain_terminal_or_concentrated_grains {σ ω ζ ε : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (b κ θ d₀ : ℝ) (p : ℕ),
      0 < b ∧ b ≤ ε / 384 ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε / 4 ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ 0 < p ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ ρ c, J ω ζ δ h ρ c n x v Y 2 →
      Gain σ ω κ (b * ω / 2) δ n Y ∨ J ω ζ δ ε ρ c n x v Y 3 ∨
        Nonempty (ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y) := by
  let b := ε / 384
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  obtain ⟨κ₁, θ₁, d₁, hκ₁, hθ₁, hd₁, hd₁small, Hthin⟩ :=
    gain_or_thin_state hσ hσhalf hω hE hb hb1
  obtain ⟨κ₂, θ₂, d₂, hκ₂, hθ₂, hθ₂ε, hd₂, hd₂small, Hpacket⟩ :=
    gain_or_natural_packet_grains hσ hσhalf hω hE hb hb1 (by positivity : 0 < ε / 4)
      (by dsimp [b]; linarith : b ≤ (ε / 4) / 96)
  obtain ⟨p, d₃, hp, hd₃, Hstable⟩ := stable_grain_reduction (ζ := ζ) hε hε1
  obtain ⟨d₄, hd₄, Hlarge⟩ := exists_rpow_cutoff hζ
    (by positivity : 0 < (2 * (2 : ℝ) ^ p)⁻¹)
  refine ⟨b, min κ₁ κ₂, min θ₁ θ₂, min d₁ (min d₂ (min d₃ d₄)), p,
    hb, le_rfl, lt_min hκ₁ hκ₂, lt_min hθ₁ hθ₂,
    (min_le_right _ _).trans hθ₂ε, lt_min hd₁ (lt_min hd₂ (lt_min hd₃ hd₄)),
    (min_le_left _ _).trans hd₁small, hp, ?_⟩
  intro δ h hδ hδd hh hhθ n x v Y hA ρ c hJ
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hδd₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₄ := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ1 : δ ≤ 1 := hδd₁.trans (hd₁small.trans (by norm_num))
  have hhθ₁ := hhθ.trans (min_le_left _ _)
  have hhθ₂ := hhθ.trans (min_le_right _ _)
  have hκ : 0 ≤ min κ₁ κ₂ := (lt_min hκ₁ hκ₂).le
  rcases Hthin δ h hδ hδd₁ hh hhθ₁ n x v Y hA ζ ρ c 2 hJ with hgain | hthin
  · exact Or.inl (gain_bound_mono hδ hδ1 hκ (min_le_left _ _) le_rfl hgain)
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρlow, hg, hB, hH, hat, hstop⟩ := Jt_iff.mp hthin
  obtain ⟨L, z, e, Hg, γ, m, hG⟩ := hH
  rcases Hpacket δ h hδ hδd₂ hh hhθ₂ n x v Y hA ζ ρ a c g N L S Z y w f z e Hg γ m
      hC hB hG with hgain | hpacket
  · exact Or.inl (gain_bound_mono hδ hδ1 hκ (min_le_right _ _) le_rfl hgain)
  obtain ⟨Z', H', K, q, r, -, -, hC', hB', hG', hnear, hdisj⟩ := hpacket
  rcases Hstable δ hδ hδd₃ ω (ε / 4) ρ a c g n N L x v Y S Z' y w f z e H' γ m
      le_rfl (admissible_mono hδ hδ1 (hhθ₂.trans hθ₂ε) hA) hC' hρlow hB' hG'
      (hstop.1 (by decide)) (hstop.2.1 le_rfl) with hterminal | hlarge
  · exact Or.inr (Or.inl hterminal)
  obtain ⟨Q, hQ, hkeep, hlargeQ, hbal, hstable⟩ := hlarge
  have hconst : 2 * (2 : ℝ) ^ p ≤ δ ^ (-ζ) := by
    have h := inv_anti₀ (Real.rpow_pos_of_pos hδ ζ) (Hlarge δ hδ hδd₄)
    simpa only [inv_inv, Real.rpow_neg hδ.le] using h
  exact Or.inr (Or.inr ⟨{
    S := S, Z := Z', N := N, y := y, w := w, f := f, a := a, g := g,
    L := L, z := z, e := e, Hg := H', γ := γ, m := m,
    cover := hC', lower_scale := hρlow, coefficient_pos := hg, broad := hB',
    grains := hG', thin := hat, length_stop := hstop.1 (by decide), scale_stop := hstop.2.1 le_rfl,
    K := K, packet := q, anchor := r, natural := hnear, disjoint := hdisj,
    Q := Q, selected_nonempty := hQ, retained := hkeep, large := hlargeQ,
    above_stability := hconst.trans_lt hlargeQ, balanced := hbal, stable := hstable }⟩)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
