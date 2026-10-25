-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FlatFramedStage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FlatFramedStage.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FlatFramedStage.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FramedFilling
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.CoreSteps
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.PerTube

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal Classical

/-- Slab filling retaining the midpoint and the frame relative to a specified
slab normal for each tube. -/
theorem flat_filling_with_frames_and_mass {n N : ℕ} {δ ρ θ L b β h lam e : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hρ : 0 < ρ)
    (hθδ : δ ≤ θ) (hθρ : θ ≤ ρ) (hθ1 : θ ≤ 1)
    (hlam : 0 < lam) (hb : b = 32 * ρ * L)
    (hL3 : 3 * δ ≤ L) (hL : 1 / 2 + δ + L ≤ 1) (hbδ : 2 * δ ≤ b)
    (hρL : 3 * δ + 8 * ρ * (L + 2 * δ) ≤ b / 2)
    (hsmall : δ ^ (-h) * (θ / ρ) ^ β ≤ lam / 8)
    (hnum : δ ^ e * (10 ^ 13 * (ρ / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y Z : Fin n → Set V)
    (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (S : Finset (Fin n)) (f : Fin n → Fin N)
    (hmass : O (768 * lam * δ ^ 2 * n) ≤ ∑ i ∈ S, volume (Z i))
    (hbroad : ∀ (k : Fin N) (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-h) * (r / ρ) ^ β * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i})
    (hangle : ∀ i ∈ S, ∀ j ∈ S, f j = f i → (Z i ∩ Z j).Nonempty →
      min ‖v j - v i‖ ‖v j + v i‖ ≤ 8 * ρ)
    (u : Fin n → V)
    (hflat : ∀ i ∈ S, ∃ (t r : ℝ), ‖u i‖ = 1 ∧
      T δ (x i) (v i) ⊆ {p | |inner ℝ (u i) p - t| ≤ r} ∧
      32 * r ≤ θ ∧ 3 * δ + 8 * r * (L + 2 * δ) ≤ 5 * δ ∧
      ∀ j ∈ S, f j = f i → (Z i ∩ Z j).Nonempty →
        T δ (x j) (v j) ⊆ {p | |inner ℝ (u i) p - t| ≤ r}) :
    ∃ G : Finset (Fin n), G ⊆ S ∧ (lam / 8) * n ≤ (G.card : ℝ) ∧
      (∀ i ∈ G, O (48 * lam * δ ^ 2) ≤ volume (Z i)) ∧
      ∀ i ∈ G, ∃ (g : V ≃ₗᵢ[ℝ] V),
        (∀ p, g p 2 = inner ℝ (v i) p) ∧
        (∀ w, |g w 0| ≤ 2 * (|inner ℝ (u i) w| + |inner ℝ (u i) (v i)| * ‖w‖)) ∧
        T δ (x i) (v i) ⊆ P (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g ∧
        O (δ ^ e) * volume (P (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g) ≤
          volume (P (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g ∩ ⋃ j, Y j) := by
  have hδle : δ ≤ 1 := by linarith
  have hLpos : 0 < L := by linarith
  have hZT : ∀ i, Z i ⊆ T δ (x i) (v i) := fun i => (hZY i).trans (hYT i)
  have hmass' : O (384 * lam * δ ^ 2 * n + 384 * lam * δ ^ 2 * n) ≤
      ∑ i ∈ S, volume (Z i) := by
    convert hmass using 1 <;> congr 1 <;> ring
  obtain ⟨G2, Z2, hG2, hZ2m, hZ2Z, hmass2, hreg⟩ :=
    WangZahlLot.Obl.wz_flat_cluster_slab_filling.regularize hδ hδle hlam.le hLpos
      (by positivity : 0 ≤ 384 * lam * δ ^ 2 * n) x v hv S Z hZm hZT hmass'
  let D := WangZahlLot.Obl.wz_flat_cluster_slab_filling.survivors S G2 f Z Z2 (lam / 4)
  let G := G2.filter fun i => O (48 * lam * δ ^ 2) ≤ volume (Z2 i ∩ D i)
  have hG : G ⊆ S := (Finset.filter_subset _ _).trans hG2
  have hZB (i : Fin n) : volume (Z i) ≤ O (384 * δ ^ 2) :=
    (measure_mono (hZT i)).trans
      (WangZahlLot.Obl.wz_flat_cluster_slab_filling.tube_volume_le hδ hδle (x i) (v i) (hv i))
  have hZ2B (i : Fin n) : volume (Z2 i) ≤ O (384 * δ ^ 2) :=
    (measure_mono (hZ2Z i)).trans (hZB i)
  have hmany := WangZahlLot.Obl.wz_flat_cluster_slab_filling.survive_heavy
    (by positivity : 0 ≤ lam / 4) (by positivity : 0 < 384 * δ ^ 2)
    (by positivity : 0 ≤ 48 * lam * δ ^ 2) S G2 f Z Z2 hZm hZ2m
    (fun i _ => hZB i) (fun i _ => hZ2B i) hmass2
  have hcard : (lam / 8) * n ≤ (G.card : ℝ) := by
    change 384 * lam * δ ^ 2 * n / 2 - (lam / 4) * (384 * δ ^ 2) * n -
      n * (48 * lam * δ ^ 2) ≤ (384 * δ ^ 2) * (G.card : ℝ) at hmany
    have hs : (384 * δ ^ 2) * ((lam / 8) * n) ≤ (384 * δ ^ 2) * (G.card : ℝ) := by
      nlinarith only [hmany]
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 384 * δ ^ 2)).mp hs
  refine ⟨G, hG, hcard, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.trans
      (measure_mono (Set.inter_subset_left.trans (hZ2Z i)))
  intro i hi
  have hiS := hG hi
  obtain ⟨t, r, hu, hslab, hr32, hr, hcompat⟩ := hflat i hiS
  have hDm : MeasurableSet (D i) :=
    WangZahlLot.Obl.wz_flat_cluster_slab_filling.survivors_measurable S G2 f Z Z2
      hZm hZ2m (lam / 4) i
  have hvu := WangZahlLot.Obl.wz_flat_cluster_slab_filling.slab_inner_dir hδ hslab
  obtain ⟨g, hg₂, hg₀⟩ := WangZahlLot.Obl.wz_flat_cluster_slab_filling.adapted_frame
    hu (hv i) (by linarith : |inner ℝ (u i) (v i)| ≤ 1 / 2)
  refine ⟨g, hg₂, hg₀,
    WangZahlLot.Obl.wz_flat_cluster_slab_filling.tube_subset_box hδ (hv i) hbδ (by linarith) hg₂, ?_⟩
  apply slab_filling_in_frame hδ hδ1 hρ (hδ.trans_le hθδ) hθ1
    (by positivity) (Real.rpow_nonneg hδ.le e) hb hL3 hL hr32 hr hρL
    x v Y Z2 hv hYm hYT hZ2m (fun j => (hZ2Z j).trans (hZY j)) i (u i) g hg₂ hg₀ hslab
    (Z2 i ∩ D i) ((hZ2m i).inter hDm) ((Set.inter_subset_left.trans (hZ2Z i)).trans (hZT i))
    (Finset.mem_filter.mp hi).2 ?_ hnum
  intro p hp
  have hpZi : p ∈ Z i := hZ2Z i hp.1
  obtain ⟨j, hj, hji, hpj, hanglelo⟩ :=
    WangZahlLot.Obl.wz_flat_cluster_slab_filling.crossing_exists S G2 f v Z Z2 hG2 hZ2Z
      hbroad hθδ hθρ (by positivity : 0 < lam / 4)
      (by convert hsmall using 1 <;> ring) i hiS (hv i) p hpZi hp.2
  have hmeet : (Z i ∩ Z j).Nonempty := ⟨p, hpZi, hZ2Z j hpj⟩
  exact ⟨j, hpj, hcompat j (hG2 hj) hji hmeet, hanglelo,
    hangle i hiS j (hG2 hj) hji hmeet, hreg j p hpj⟩

/-- The frame-only interface is retained for existing callers. -/
theorem flat_filling_with_frames {n N : ℕ} {δ ρ θ L b β h lam e : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hρ : 0 < ρ)
    (hθδ : δ ≤ θ) (hθρ : θ ≤ ρ) (hθ1 : θ ≤ 1)
    (hlam : 0 < lam) (hb : b = 32 * ρ * L)
    (hL3 : 3 * δ ≤ L) (hL : 1 / 2 + δ + L ≤ 1) (hbδ : 2 * δ ≤ b)
    (hρL : 3 * δ + 8 * ρ * (L + 2 * δ) ≤ b / 2)
    (hsmall : δ ^ (-h) * (θ / ρ) ^ β ≤ lam / 8)
    (hnum : δ ^ e * (10 ^ 13 * (ρ / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y Z : Fin n → Set V)
    (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (S : Finset (Fin n)) (f : Fin n → Fin N)
    (hmass : O (768 * lam * δ ^ 2 * n) ≤ ∑ i ∈ S, volume (Z i))
    (hbroad : ∀ (k : Fin N) (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-h) * (r / ρ) ^ β * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i})
    (hangle : ∀ i ∈ S, ∀ j ∈ S, f j = f i → (Z i ∩ Z j).Nonempty →
      min ‖v j - v i‖ ‖v j + v i‖ ≤ 8 * ρ)
    (u : Fin n → V)
    (hflat : ∀ i ∈ S, ∃ (t r : ℝ), ‖u i‖ = 1 ∧
      T δ (x i) (v i) ⊆ {p | |inner ℝ (u i) p - t| ≤ r} ∧
      32 * r ≤ θ ∧ 3 * δ + 8 * r * (L + 2 * δ) ≤ 5 * δ ∧
      ∀ j ∈ S, f j = f i → (Z i ∩ Z j).Nonempty →
        T δ (x j) (v j) ⊆ {p | |inner ℝ (u i) p - t| ≤ r}) :
    ∃ G : Finset (Fin n), G ⊆ S ∧ (lam / 8) * n ≤ (G.card : ℝ) ∧
      ∀ i ∈ G, ∃ (g : V ≃ₗᵢ[ℝ] V),
        (∀ p, g p 2 = inner ℝ (v i) p) ∧
        (∀ w, |g w 0| ≤ 2 * (|inner ℝ (u i) w| + |inner ℝ (u i) (v i)| * ‖w‖)) ∧
        T δ (x i) (v i) ⊆ P (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g ∧
        O (δ ^ e) * volume (P (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g) ≤
          volume (P (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g ∩ ⋃ j, Y j) := by
  obtain ⟨G, hGS, hcard, _, H⟩ := flat_filling_with_frames_and_mass
    hδ hδ1 hρ hθδ hθρ hθ1 hlam hb hL3 hL hbδ hρL hsmall hnum
    x v Y Z hv hYm hYT hZm hZY S f hmass hbroad hangle u hflat
  exact ⟨G, hGS, hcard, H⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
