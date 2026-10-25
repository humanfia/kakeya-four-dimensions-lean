-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NaturalReduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NaturalReduction.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketReduction
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketPowers
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalState

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (assignedFiber)
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

/-- The complete natural-neighborhood reduction: gain, or exact frozen
witnesses whose active grains are partitioned into disjointly shaded packets,
each lying in one expanded-plate neighborhood at the natural aspect ratio. -/
theorem gain_or_natural_packet_grains {σ ω b ε : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hb : 0 < b) (hb1 : b ≤ 1) (hε : 0 < ε) (hbε : b ≤ ε / 96) :
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
        (K : ℕ) (q : Fin L → Fin K) (r : Fin K → Fin L),
        (∀ i, Z' i ⊆ Z i) ∧ (∀ j, H' j ⊆ Hg j) ∧
        C δ ε n x v Y S Z' ρ N y w f True ∧ Broad ω ζ δ ε ρ n N v S Z' f ∧
        GrainWitnesses δ ε n x v S Z' ρ N y w f a c 0 g L z e H' γ m ∧
        (∀ j, H' j ≠ ∅ → grainNear a ρ c z e (r (q j)) j) ∧
        ∀ k l, k ≠ l → Disjoint (assignedFiber q H' k) (assignedFiber q H' l) := by
  obtain ⟨κ, θ, d₁, hκ, hθ, hθε, hd₁, hd₁small, Hp⟩ :=
    gain_or_packet_grains hσ hσhalf hω hE hb hb1 (by positivity : 0 < ε / 4)
  obtain ⟨d₂, hd₂, hd₂small, Hpalette⟩ := natural_packet_palette_parameters
    (by positivity : 0 < ε / 2) hb.le (by linarith : b ≤ (ε / 2) / 48)
  obtain ⟨d₃, hd₃, Hhalf⟩ := exists_rpow_cutoff (by positivity : 0 < ε / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨κ, θ, min d₁ (min d₂ d₃), hκ, hθ, hθε.trans (by linarith),
    lt_min hd₁ (lt_min hd₂ hd₃), (min_le_left _ _).trans hd₁small, ?_⟩
  intro δ h hδ hδd hh hhθ n x v Y hA ζ ρ a c g N L S Z y w f z e Hg γ m hC hB hG
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hδd₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := hδd₂.trans hd₂small
  have hhε : h ≤ ε / 4 := hhθ.trans hθε
  rcases Hp δ h hδ hδd₁ hh hhθ n x v Y hA ζ ρ a c g N L S Z y w f z e Hg γ m
    hC hB hG with hgain | hpacket
  · exact Or.inl hgain
  obtain ⟨Z₁, H₁, K, q, ref, hZ₁, hH₁, hC₁, hB₁, hG₁, href, hgeom, hdisj⟩ := hpacket
  have ha : 0 < a := hδ.trans_le hG.1
  have hrc : 0 < ρ * c := ha.trans_le hG.2.1
  have hc : 0 < c := hrc.trans_le hG.2.2.1
  have hρ : 0 < ρ := (mul_pos_iff_of_pos_right hc).mp hrc
  obtain ⟨A₀, hA₀, hAd, hpalette⟩ := Hpalette δ hδ hδd₂
  have hexp : -(ε / 2 / 2) = -(ε / 4) := by ring
  rw [hexp] at hpalette
  let M : ℕ := (128 * A₀ ^ 2 + 1) ^ 6
  have hM : (0 : ℝ) < M := by dsimp [M]; positivity
  have hs := (grainPlaneScale_bounds hδ hδ1 hb.le ha hG.2.1 hG.2.2.1).1
  have hsA : grainPlaneScale δ b a ρ c ≤ A₀ * (a / ρ / c) := by
    calc
      _ ≤ δ ^ (-b) * a / (ρ * c) := min_le_right _ _
      _ = δ ^ (-b) * (a / ρ / c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAd (by positivity)
  have hbudget : δ ^ ε ≤ ((M : ℝ)⁻¹ / 2) * δ ^ (ε / 4) := by
    have hh : (M : ℝ) * δ ^ ε ≤ (1 / 2) * δ ^ (ε / 4) := by
      calc
        _ ≤ δ ^ (-(ε / 4)) * δ ^ ε :=
          mul_le_mul_of_nonneg_right hpalette (Real.rpow_nonneg hδ.le _)
        _ = δ ^ (ε / 2) * δ ^ (ε / 4) := by
          rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Hhalf δ hδ hδd₃)
          (Real.rpow_nonneg hδ.le _)
    have hh' := (le_div_iff₀ hM).mpr (show δ ^ ε * M ≤ (1 / 2) * δ ^ (ε / 4) by nlinarith)
    convert hh' using 1 <;> ring
  obtain ⟨H₂, r, hH₂, hnear, hdisj₂, hC₂, hB₂, hG₂⟩ :=
    natural_packet_state hδ hδ1 (by linarith : ε / 4 ≤ ε) hA₀ hs hsA
      (admissible_mono hδ hδ1 hhε hA) hC₁ hB₁ hG₁ q ref href
      (fun i j hij => ⟨(hgeom i j hij).1, (hgeom i j hij).2.2⟩) hdisj hbudget
  exact Or.inr ⟨fun i => Z₁ i ∩ assignedFiber γ H₂ (f i), H₂, K, q, r,
    fun i => inter_subset_left.trans (hZ₁ i), fun j => (hH₂ j).2.trans (hH₁ j),
    hC₂, hB₂, hG₂, hnear, hdisj₂⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
