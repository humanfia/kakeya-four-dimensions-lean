-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketReduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketReduction.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Planiness

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (assignedFiber geometricPacketOverlap boxAxis)
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

/-- The normalized angular scale is positive, at most one, and wide enough
for the short dimension of the original grain. -/
theorem grainPlaneScale_bounds {δ b a ρ c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b)
    (ha : 0 < a) (hac : a ≤ ρ * c) (hρc : ρ * c ≤ c) :
    0 < grainPlaneScale δ b a ρ c ∧ grainPlaneScale δ b a ρ c ≤ 1 ∧
      a ≤ grainPlaneScale δ b a ρ c * c := by
  have hrc : 0 < ρ * c := ha.trans_le hac
  have hc : 0 < c := hrc.trans_le hρc
  have hp : 1 ≤ δ ^ (-b) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hb)
  refine ⟨by unfold grainPlaneScale; positivity, min_le_left _ _, ?_⟩
  unfold grainPlaneScale
  rw [min_mul_of_nonneg _ _ hc.le]
  refine le_min (by simpa using hac.trans hρc) ?_
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hrc).mpr
  nlinarith [mul_le_mul_of_nonneg_left hρc ha.le,
    mul_le_mul_of_nonneg_right hp (mul_nonneg ha.le hc.le)]

/-- Steps 2 and 3 of Move 3 with uniform parameters: gain, or a refinement
into geometrically confined packets with disjoint packet shadings. The exact
frozen cover and grain witnesses survive at the requested error. -/
theorem gain_or_packet_grains {σ ω b ε : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hb : 0 < b) (hb1 : b ≤ 1) (hε : 0 < ε) :
    ∃ κ θ d₀ : ℝ, 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ (ζ ρ a c g : ℝ) (N L : ℕ) (S : Finset (Fin n)) (Z : Fin n → Set V)
        (y w : Fin N → V) (f : Fin n → Fin N) (z : Fin L → V)
        (e : Fin L → V ≃ₗᵢ[ℝ] V) (Hg : Fin L → Set V) (γ : Fin L → Fin N) (m : ℝ),
      C δ h n x v Y S Z ρ N y w f True → Broad ω ζ δ h ρ n N v S Z f →
      GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m →
      Gain σ ω κ (b * ω / 2) δ n Y ∨
      ∃ (Z' : Fin n → Set V) (H' : Fin L → Set V)
        (K : ℕ) (q : Fin L → Fin K) (ref : Fin K → Fin L),
        (∀ i, Z' i ⊆ Z i) ∧ (∀ j, H' j ⊆ Hg j) ∧
        C δ ε n x v Y S Z' ρ N y w f True ∧ Broad ω ζ δ ε ρ n N v S Z' f ∧
        GrainWitnesses δ ε n x v S Z' ρ N y w f a c 0 g L z e H' γ m ∧
        (∀ k, q (ref k) = k) ∧
        (∀ i j, q i = q j →
          ‖boxAxis (e i) 0 - boxAxis (e j) 0‖ ≤ grainPlaneScale δ b a ρ c / 100 ∧
          1 / 2 ≤ |inner ℝ (boxAxis (e j) 2) (boxAxis (e i) 2)| ∧
          ‖z i - z j‖ ≤ c / 100 ∧
          |inner ℝ (boxAxis (e j) 0) (z i - z j)| ≤ grainPlaneScale δ b a ρ c * c / 100) ∧
        ∀ k l, k ≠ l → Disjoint (assignedFiber q H' k) (assignedFiber q H' l) := by
  obtain ⟨κ, θ, d₁, hκ, hθ, hθε, hd₁, hd₁small, Hp⟩ :=
    gain_or_plane_narrow_grains hσ hσhalf hω hE hb hb1 (by positivity : 0 < ε / 2)
  have hP : (0 : ℝ) < geometricPacketOverlap := by norm_num [geometricPacketOverlap]
  obtain ⟨d₂, hd₂, Hcut⟩ := exists_rpow_cutoff (by positivity : 0 < ε / 2)
    (by positivity : 0 < (geometricPacketOverlap : ℝ)⁻¹ / 2)
  refine ⟨κ, θ, min d₁ d₂, hκ, hθ, hθε.trans (by linarith), lt_min hd₁ hd₂,
    (min_le_left _ _).trans hd₁small, ?_⟩
  intro δ h hδ hδd hh hhθ n x v Y hA ζ ρ a c g N L S Z y w f z e Hg γ m hC hB hG
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hδd₂ := hδd.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := (hδd₁.trans hd₁small).trans (by norm_num)
  rcases Hp δ h hδ hδd₁ hh hhθ n x v Y hA ζ ρ a c g N L S Z y w f z e Hg γ m
    hC hB hG with hgain | hnarrow
  · exact Or.inl hgain
  obtain ⟨h', Z₁, H₁, hhh', hh'ε, hZ₁, hH₁, hC₁, hB₁, hG₁, hnarrow⟩ := hnarrow
  obtain ⟨hs, hs1, has⟩ := grainPlaneScale_bounds hδ hδ1 hb.le
    (hδ.trans_le hG.1) hG.2.1 hG.2.2.1
  have hbudget : δ ^ ε ≤ ((geometricPacketOverlap : ℝ)⁻¹ / 2) * δ ^ h' := by
    calc
      _ ≤ δ ^ (ε / 2 + h') :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (ε / 2) * δ ^ h' := Real.rpow_add hδ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Hcut δ hδ hδd₂) (Real.rpow_nonneg hδ.le _)
  obtain ⟨K, q, ref, H₂, href, hgeom, hH₂, hmass, hdisj, hC₂, hB₂, hG₂⟩ :=
    plane_narrow_grain_packets hδ hδ1 (by linarith : h' ≤ ε) hs hs1 has
      (admissible_mono hδ hδ1 hhh' hA) hC₁ hB₁ hG₁ hnarrow hbudget
  exact Or.inr ⟨fun i => Z₁ i ∩ assignedFiber γ H₂ (f i), H₂, K, q, ref,
    fun i => inter_subset_left.trans (hZ₁ i), fun j => (hH₂ j).2.trans (hH₁ j),
    hC₂, hB₂, hG₂, href, hgeom, hdisj⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
