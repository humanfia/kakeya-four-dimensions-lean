-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrowingAngularPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrowingAngularPackets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, GrowingAngularPackets.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_move_two_long_grains_gain.Core
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketPower

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement)

/-- Dense packets at a point of high overlap must grow in angular scale
whenever the original directions have a cubic local cap count. -/
theorem dense_packet_scale_growth_of_bound {n : ℕ} (v : Fin n → V)
    (K W : Finset (Fin n)) (u : V) {C δ ρ θ β q₀ t : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ)
    (hδθ : δ ≤ θ) (hβ : 0 ≤ β) (ht : 0 ≤ t)
    (hbudget : 16 * C * δ ^ (q₀ - β - 3 * t) ≤ 1)
    (hcount : ∀ R, ρ ≤ R →
      ((K.filter (fun i => pd (v i) u ≤ R)).card : ℝ) ≤ C * (R / ρ) ^ 3)
    (hWK : W ⊆ K) (hhigh : δ ^ (-q₀) < K.card)
    (hlarge : ((K.card : ℝ) / 2) * θ ^ β ≤ W.card)
    (hcap : ∀ i ∈ W, pd (v i) u ≤ 2 * θ) : δ ^ (-t) * ρ ≤ θ := by
  classical
  by_contra hsmall
  have hθsmall : θ < δ ^ (-t) * ρ := lt_of_not_ge hsmall
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hp : 1 ≤ δ ^ (-t) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hR : ρ ≤ 2 * δ ^ (-t) * ρ := by nlinarith
  have hWcount : (W.card : ℝ) ≤ 8 * C * δ ^ (-3 * t) := by
    have hsub : W ⊆ K.filter (fun i => pd (v i) u ≤ 2 * δ ^ (-t) * ρ) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨hWK hi, (hcap i hi).trans (by linarith)⟩
    calc
      _ ≤ ((K.filter (fun i => pd (v i) u ≤ 2 * δ ^ (-t) * ρ)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ C * ((2 * δ ^ (-t) * ρ) / ρ) ^ 3 := hcount _ hR
      _ = 8 * C * δ ^ (-3 * t) := by
        rw [mul_div_cancel_right₀ _ hρ.ne', mul_pow,
          ← Real.rpow_natCast (δ ^ (-t)) 3, ← Real.rpow_mul hδ.le]
        norm_num
        rw [show t * 3 = 3 * t by ring]
        ring
  have hlower : δ ^ (β - q₀) / 2 < (W.card : ℝ) := by
    calc
      _ = (δ ^ (-q₀) / 2) * δ ^ β := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hδ]
        congr 2
        ring
      _ < ((K.card : ℝ) / 2) * δ ^ β :=
        mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hδ β)
      _ ≤ ((K.card : ℝ) / 2) * θ ^ β := by gcongr
      _ ≤ _ := hlarge
  have hupper : 8 * C * δ ^ (-3 * t) ≤ δ ^ (β - q₀) / 2 := by
    calc
      _ = (16 * C * δ ^ (q₀ - β - 3 * t)) * (δ ^ (β - q₀) / 2) := by
        calc
          _ = 8 * C * δ ^ ((q₀ - β - 3 * t) + (β - q₀)) := by congr 2 <;> ring
          _ = _ := by rw [Real.rpow_add hδ]; ring
      _ ≤ 1 * (δ ^ (β - q₀) / 2) := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = _ := one_mul _
  exact (hlower.trans_le (hWcount.trans hupper)).false

/-- Measurable growing packets under an abstract cap-count bound. This can
be applied directly inside a normalized grain block; no fraction of the
ambient fine incidence count is required. -/
theorem measurable_growing_packets_of_cap_count {C β q₀ t τ : ℝ}
    (hC : 0 < C) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 0 < t)
    (hmargin : 0 < q₀ - β - 3 * t) (hτ : 0 < τ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ ρ : ℝ,
      0 < δ → δ ≤ d₀ → 0 < ρ →
      ∀ (n : ℕ) (v : Fin n → V) (H : Fin n → Set V),
        0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, MeasurableSet (H i)) →
        0 < ∑ i, μ (H i) →
        (∀ p ∈ ⋃ i, H i, δ ^ (-q₀) < q n {i | p ∈ H i}) →
        (∀ p u R, ρ ≤ R → q n {i | p ∈ H i ∧ pd (v i) u ≤ R} ≤ C * (R / ρ) ^ 3) →
        ∃ (θ : ℝ) (D : Fin n → Set V)
          (P : V → Finset (Finset (Fin n))) (center : V → Finset (Fin n) → Fin n),
          δ ≤ θ ∧ θ ≤ 1 ∧ δ ^ (-t) * ρ ≤ θ ∧
          PacketRefinement β δ θ v H D P center ∧
          O (δ ^ τ) * ∑ i, μ (H i) ≤ ∑ i, μ (D i) := by
  classical
  obtain ⟨d₁, hd₁, Hsmall⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    hmargin (K := 1 / (16 * C)) (by positivity)
  obtain ⟨d₂, hd₂, hd₂1, Hselect⟩ :=
    WangZahlLot.Obl.wz_broad_grains_initialization.measurable_angular_packets_power hβ hβ1 hτ
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, (min_le_right _ _).trans hd₂1, ?_⟩
  intro δ ρ hδ hδd hρ n v H hn hv hHm hpos hhigh hcount
  have hδ1 : δ ≤ 1 := ((hδd.trans (min_le_right _ _)).trans hd₂1).trans (by norm_num)
  obtain ⟨θ, D, P, center, hδθ, hθ1, hpacket, hmass⟩ :=
    Hselect δ hδ (hδd.trans (min_le_right _ _)) n v H hn hv hHm
  refine ⟨θ, D, P, center, hδθ, hθ1, ?_, hpacket, hmass⟩
  have hDpos : 0 < ∑ i, μ (D i) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ τ)).ne' hpos.ne').trans_le hmass
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
    (f := fun _ => (0 : ENNReal)) (g := fun i => μ (D i)) (by simpa using hDpos)
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hi.ne'
  have hiU : i ∈ (P p).biUnion id := by
    change i ∈ ((P p).biUnion id : Set (Fin n))
    rw [(hpacket.2.2.2 p).2.1]
    exact hp
  obtain ⟨W, hW, _⟩ := Finset.mem_biUnion.mp hiU
  let K := {i : Fin n | p ∈ H i}.toFinset
  have hWsub : W ⊆ K := by
    intro j hj
    have hjU : j ∈ ((P p).biUnion id : Set (Fin n)) := Finset.mem_biUnion.mpr ⟨W, hW, hj⟩
    rw [(hpacket.2.2.2 p).2.1] at hjU
    exact Set.mem_toFinset.mpr ((hpacket.1 j).2 hjU)
  have hKh : δ ^ (-q₀) < (K.card : ℝ) := by
    simpa only [K, q, Set.ncard_eq_toFinset_card'] using
      hhigh p (mem_iUnion.mpr ⟨i, (hpacket.1 i).2 hp⟩)
  have hlarge : ((K.card : ℝ) / 2) * θ ^ β ≤ W.card := by
    simpa only [K, Set.ncard_eq_toFinset_card'] using ((hpacket.2.2.2 p).2.2 W hW).2.2.1
  apply dense_packet_scale_growth_of_bound v K W (v (center p W))
    hC hδ hδ1 hρ hδθ hβ.le ht.le ?_ ?_ hWsub hKh hlarge
    ((hpacket.2.2.2 p).2.2 W hW).2.1
  · have Hsmall' := Hsmall δ hδ (hδd.trans (min_le_left _ _))
    have HH := (le_div_iff₀ (by positivity : 0 < 16 * C)).mp Hsmall'
    nlinarith
  · intro R hR
    have hfilter : K.filter (fun i => pd (v i) (v (center p W)) ≤ R) =
        {i : Fin n | p ∈ H i ∧ pd (v i) (v (center p W)) ≤ R}.toFinset := by
      ext i
      simp [K]
    rw [hfilter]
    simpa only [q, Set.ncard_eq_toFinset_card'] using hcount p (v (center p W)) R hR

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
