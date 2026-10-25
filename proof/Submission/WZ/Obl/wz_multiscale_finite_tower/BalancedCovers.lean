-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.BalancedCovers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.PhysicalAlternative
import Submission.WZ.Obl.wz_multiscale_finite_tower.DenseRestriction
import Submission.WZ.Obl.wz_multiscale_finite_tower.IndexTransport
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Balance
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Reindex

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound doubled)

/-- Whole, occupied groups in a physical cover. Their cardinalities are balanced;
the fine relative slab estimate retains its original denominator. -/
structure BalancedPhysicalCover (d r s ζ C ω H B : ℝ) (n : ℕ) (x v : Fin n → Space) where
  radius : ℝ
  radius_pos : 0 < radius
  scale_lower : r * (s / r) ^ (1 - ω / 100) ≤ C * radius
  scale_upper : radius ≤ C * (r * (s / r) ^ (ω / 100))
  selected : Finset (Fin n)
  retained : H * n ≤ selected.card
  card : ℕ
  card_pos : 0 < card
  position : Fin card → Space
  direction : Fin card → Space
  unit : ∀ k, ‖direction k‖ = 1
  assign : Fin n → Fin card
  representative : Fin card → Fin n
  representative_mem : ∀ k, representative k ∈ selected
  representative_assign : ∀ k, assign (representative k) = k
  balanced : ∀ k l, ((selected.filter (fun i => assign i = k)).card : ℝ) ≤
    B * (selected.filter (fun i => assign i = l)).card
  containment : ∀ i ∈ selected, Tube s (x i) (v i) ⊆ doubled radius (position (assign i)) (direction (assign i))
  count : ConvexCount radius (d ^ (-ζ)) (fun _ => True) (fun k => Tube radius (position k) (direction k))
  slab : ∀ k, SlabBound (doubled radius (position k) (direction k)) (d ^ (-ζ))
    (fun i => i ∈ selected ∧ assign i = k) (fun i => Tube s (x i) (v i))

theorem balance_physical_cover {d r s θ ζ C ω H B : ℝ} {y w : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (F : PhysicalFrame d r s θ y w n x v Y)
    (P : PhysicalCover d r s ζ C ω y w n x v Y)
    (hd : 0 < d) (hr : 0 < r) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 < C)
    (hH : 0 < H) (hB : 1 < B) (q : ℕ) (hq : 0 < q) (hnq : (n : ℝ) < B ^ q)
    (hbudget : H * q ≤ d ^ (θ + ζ) / 56) :
    Nonempty (BalancedPhysicalCover d r s ζ C ω H B n x v) := by
  classical
  obtain ⟨S, Z, ρ, N, y', w', f, hZ, hmass, hlo, hhi, hw, hsub, hK, _, hslab⟩ := P
  have hρ : 0 < ρ := by
    have hp : 0 < r * (s / r) ^ (1 - ω / 100) := mul_pos hr (Real.rpow_pos_of_pos (div_pos hs hr) _)
    exact (mul_pos_iff_of_pos_left hC).mp (hp.trans_le hlo)
  have hSret : (d ^ (θ + ζ) / 56) * n ≤ S.card := by
    have hh := retained_subset_cardinality hs (Real.rpow_nonneg hd.le ζ) S F.2.2.1
      (fun i hi => (measure_mono ((hZ i).2.trans (F.2.1 i).2.2.2)).trans
        (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hs.le hs1 _ _ (F.2.1 i).1)) hmass
    simpa only [Real.rpow_add hd, mul_comm (d ^ ζ) (d ^ θ)] using hh
  obtain ⟨S', hS'S, hcard, hwhole, hbal⟩ :=
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.balance_whole_fibres hq hB hnq S f (fun _ => 1)
  have hcard' : (S.card : ℝ) ≤ q * S'.card := by
    have hh : (S.card : ENNReal) ≤ (q : ENNReal) * S'.card := by simpa using hcard
    exact_mod_cast hh
  have hretain : H * n ≤ S'.card := by
    have hh := ((mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg n)).trans hSret).trans hcard'
    apply (mul_le_mul_iff_left₀ (Nat.cast_pos.mpr hq : (0 : ℝ) < q)).mp
    nlinarith only [hh]
  have hS' : S'.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos hH (Nat.cast_pos.mpr F.1)).trans_le hretain))
  obtain ⟨M, b, g, rep, hM, hb, hrep, hbg, hpred⟩ :=
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.reindex_whole_fibres S S' hS'S hS' f hwhole
  have hrg (k : Fin M) : g (rep k) = k := hb ((hbg _ (hrep k).1).trans (hrep k).2)
  have hfilter (k : Fin M) : S'.filter (fun i => g i = k) = S'.filter (fun i => f i = f (rep k)) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, he⟩
      exact ⟨hi, (hbg i hi).symm.trans ((congrArg b he).trans (hrep k).2.symm)⟩
    · rintro ⟨hi, he⟩
      exact ⟨hi, hb ((hbg i hi).trans (he.trans (hrep k).2))⟩
  refine ⟨⟨ρ, hρ, hlo, hhi, S', hretain, M, hM, y' ∘ b, w' ∘ b,
    (fun k => (hw (b k)).1), g, rep, (fun k => (hrep k).1), hrg, ?_, ?_, ?_, ?_⟩⟩
  · intro k l
    rw [hfilter k, hfilter l]
    exact hbal (rep k) (hrep k).1 (rep l) (hrep l).1
  · intro i hi
    simpa only [Function.comp_apply, hbg i hi] using hsub i (hS'S hi)
  · simpa only [Function.comp_def] using convexCount_reindex hK b hb (fun _ _ => trivial)
  · intro k
    have hp : (fun i => i ∈ S' ∧ g i = k) = (fun i => i ∈ S ∧ f i = b k) :=
      funext fun i => propext (hpred k i)
    simpa only [Function.comp_apply, hp] using hslab (b k)

end WangZahlLot.Obl.wz_multiscale_finite_tower
