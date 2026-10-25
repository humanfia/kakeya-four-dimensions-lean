-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PrismFamilyMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PrismFamilyMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismPacketMass
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketMassSum

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyEstimate BodyConvexCount BodyPacking)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (body_convex_count_restrict)
open WangZahlLot.Obl.wz_separated_cover_refinement
  (enumerate enumerate_mem enumerate_injective enumerate_sum)

noncomputable section

/-- The sharp estimate summed over common-dimension packet prisms. Shadings
need only have total density; the explicit duplication budget pays for
sparse pieces before applying the individual body estimate. -/
theorem sharp_prism_family_mass {σ ω : ℝ} (hbody : BodyEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (n : ℕ) (U : Fin n → Set V) (x : Fin n → V) (a b r w m p : ℝ),
      (n : ℝ) ≤ d ^ (-100 : ℝ) →
      0 < a → a ≤ b → b ≤ 4 → 0 < r → d ≤ r / 4 → 0 < w →
      d ≤ r / (8192 * a) → 1 ≤ m → 1 ≤ p →
      (∀ i, IsCompact (U i)) → (∀ i, Convex ℝ (U i)) →
      (∀ i, ball (x i) r ⊆ U i) →
      (∀ i, ∃ q ∈ U i, ∃ q' ∈ U i, (1 / 4 : ℝ) ≤ dist q q') →
      (∀ i, μ (U i) = O w) → BodyConvexCount U w m → BodyPacking U w p →
      ∀ (ι : Type) [Fintype ι] (Z : ι → Fin n → Set V) (S : ι → Finset (Fin n))
        (z : ι → V) (e : ι → V ≃ₗᵢ[ℝ] V) (V₀ : Set V) (lam C L : ℝ),
      0 < lam → 0 ≤ L → μ V₀ ≠ ⊤ →
      (∀ j i, MeasurableSet (Z j i)) → (∀ j i, Z j i ⊆ U i) →
      (∀ j i, Z j i ⊆ V₀) → (∀ j i, i ∉ S j → Z j i = ∅) →
      (∀ j i, i ∈ S j → U i ⊆ P a b 4 (z j) (e j)) →
      O (lam * n * w) ≤ ∑ j, ∑ i, μ (Z j i) →
      (∑ j, ((S j).card : ℝ)) ≤ C * n → 2 * d ^ η * C ≤ lam →
      (∀ q ∈ V₀, ((Finset.univ.filter fun j => ∃ i, q ∈ Z j i).card : ℝ) ≤ L) →
      O ((A / 2) * d ^ ε * (r / (8192 * a)) ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) *
        (w / (4 * a * b)) ^ (σ / 2) * lam * n * w) ≤ O L * μ V₀ := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hsmall, H⟩ := sharp_prism_packet_mass hbody ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hsmall, ?_⟩
  intro d hd hdd n U x a b r w m p hnmax ha hab hb hr hdr hw hdB hm hp
    hcompact hconvex hball hlong hvolume hcount hpack ι inst Z S z e V₀ lam C L
    hlam hL hVfin hZm hZU hZV hZS hbox hmass hdup hbudget hover
  let K := A * d ^ ε * (r / (8192 * a)) ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) *
    (w / (4 * a * b)) ^ (σ / 2)
  let M j := (∑ i, μ (Z j i)).toReal
  let count j : ℝ := (S j).card
  let Y j := ⋃ i, Z j i
  have hbpos := ha.trans_le hab
  have hmpos := zero_lt_one.trans_le hm
  have hppos := zero_lt_one.trans_le hp
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hZfin j i : μ (Z j i) ≠ ⊤ := ne_top_of_le_ne_top hVfin (measure_mono (hZV j i))
  have hYfin j : μ (Y j) ≠ ⊤ := ne_top_of_le_ne_top hVfin
    (measure_mono (iUnion_subset fun i => hZV j i))
  have hpacket j : K * M j ≤ (μ (Y j)).toReal + K * (d ^ η * w) * count j := by
    let f := enumerate (S j)
    have hf : Function.Injective f := enumerate_injective (S j)
    have hSn : (S j).card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ (S j)
    have hh := H d hd hdd (S j).card (U ∘ f) (Z j ∘ f) (x ∘ f) a b r w m p
      ((Nat.cast_le.mpr hSn).trans hnmax) ha hab hb hr hdr hw hdB hm hp
      (fun i => hcompact (f i)) (fun i => hconvex (f i)) (fun i => hball (f i))
      (fun i => hlong (f i)) (fun i => hvolume (f i)) (fun i => hZm j (f i))
      (fun i => hZU j (f i)) (body_convex_count_restrict hw.le hcount f hf)
      (packing_restrict hw.le hpack f hf) (z j) (e j)
      (fun i => hbox j (f i) (enumerate_mem (S j) i))
    have hsum : ∑ i, μ (Z j (f i)) = ∑ i, μ (Z j i) := by
      dsimp only [f]
      rw [enumerate_sum (S j) (fun i => μ (Z j i))]
      exact Finset.sum_subset (Finset.subset_univ _)
        (by intro i _ hi; simp only [hZS j i hi, μ, measure_empty])
    have hmono : (μ (⋃ i, Z j (f i))).toReal ≤ (μ (Y j)).toReal :=
      ENNReal.toReal_mono (hYfin j)
        (measure_mono (iUnion_subset fun i => subset_iUnion (Z j) (f i)))
    change K * (∑ i, μ (Z j (f i))).toReal ≤
      (μ (⋃ i, Z j (f i))).toReal + K * d ^ η * w * (S j).card at hh
    rw [hsum] at hh
    exact hh.trans (by simpa only [M, count, mul_assoc] using add_le_add hmono (le_refl (K * d ^ η * w * (S j).card)))
  have hsumfin : (∑ j, ∑ i, μ (Z j i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.sum_ne_top.mpr (fun i _ => hZfin j i))
  have hmassR : (lam * w) * n ≤ ∑ j, M j := by
    have hh := ENNReal.toReal_mono hsumfin hmass
    rw [ENNReal.toReal_sum (fun j _ => ENNReal.sum_ne_top.mpr (fun i _ => hZfin j i)),
      ENNReal.toReal_ofReal (by positivity)] at hh
    convert hh using 1 <;> ring
  have hh := packet_mass_sum Y V₀ M count hK (by positivity : 0 ≤ d ^ η * w)
    (Nat.cast_nonneg n) hL (fun j => MeasurableSet.iUnion (hZm j))
    (fun j => iUnion_subset fun i => hZV j i) hVfin hpacket hmassR hdup
    (by nlinarith [mul_le_mul_of_nonneg_right hbudget hw.le])
    (by simpa only [Y, Set.mem_iUnion] using hover)
  convert hh using 1 <;> dsimp only [K, O] <;> congr 1 <;> ring

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
