-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.RawCoverPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.FibrePackets
import Submission.WZ.Obl.wz_coarse_grains_assembly.DenseFibres
import Submission.WZ.Obl.wz_coarse_grains_assembly.FibreSize
import Submission.WZ.Obl.wz_coarse_grains_assembly.SmallLength
import Submission.WZ.Obl.wz_coarse_grains_assembly.Double

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- The packet data attached to one original coarse index. -/
def FibrePacketProperty (ω ζ δ e ρ c : ℝ) {n N : ℕ}
    (x v : Fin n → V) (Z : Fin n → Set V) (S : Finset (Fin n))
    (f : Fin n → Fin N) (y w : Fin N → V) (k : Fin N) (W : Fin n → Set V) (m : ℝ) : Prop :=
  (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
  (∀ i p, p ∈ W i → i ∈ S ∧ f i = k) ∧
  O (δ ^ e) * (∑ i ∈ S.filter (fun i => f i = k), μ (Z i)) ≤ ∑ i, μ (W i) ∧
  (∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
    q n {i | p ∈ W i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-e) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ W i}) ∧
  (∀ p, (∃ i, p ∈ W i) → q n {i | p ∈ W i} ∈ Set.Icc m (2 * m)) ∧
  Nonempty (GrainPacket δ e ρ c x v W (y k) (w k))

/-- Dense fibres admit packets at one common length, before coarse
separation and common-multiplicity selection. -/
theorem raw_cover_packets {ω ζ δ θ e ε η d₀ ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hTG : TubePacketStatement (ω * ζ / 100) (ζ / 2) e η d₀)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδd : δ ≤ d₀) (hδρ : δ ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hsmall : 2 * δ ^ (4 * θ) ≤ δ ^ (2 * θ)) (hdensity : 4 * θ ≤ η)
    (hloss : 2 * δ ^ (-θ) ≤ δ ^ (-η)) (htwo : 2 ≤ δ ^ (-η))
    (hlength : e + θ ≤ ζ / 2) (herror : e + θ ≤ ε)
    (hwidth : 16 * δ ≤ δ ^ (1 - ζ / 2))
    (hn : 0 < n) (hgeom : ∀ i, ‖v i‖ = 1 ∧ Y i ⊆ T δ (x i) (v i))
    (hX : X δ n x v) (hfinite : ∀ i, μ (Z i) ≠ ⊤)
    (hmassY : O (δ ^ θ * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hC : C δ θ n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ θ ρ n N v S Z f)
    (hregime : δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n) :
    ∃ (c : ℝ) (B : Finset (Fin N)) (W : Fin N → Fin n → Set V) (m : Fin N → ℝ),
      0 < c ∧ c ≤ 1 ∧ 16 * δ ≤ (2 * ρ) * c ∧ B.Nonempty ∧
      δ ^ ε * (ρ / δ) * N / n ≤ c ∧
      (∀ k ∈ B, FibrePacketProperty ω ζ δ e (2 * ρ) c x v Z S f y w k (W k) (m k)) ∧
      (∀ k ∈ B, 0 < ∑ i, μ (W k i)) ∧
      O (δ ^ e) * (∑ i ∈ S, μ (Z i)) ≤ 2 * ∑ k ∈ B, ∑ i, μ (W k i) := by
  classical
  have hρ : 0 < ρ := hδ.trans_le hδρ
  obtain ⟨D, hD, hmax, havg⟩ := maximum_cover_fibre hδ hn hmassY hC
  let c := δ ^ e * (2 * ρ / δ) / D
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨hclo, hdesired⟩ := small_radius_prescribed_length hδ hδ1 hρ hn hD havg hregime hlength herror
  have hwide : 16 * δ ≤ (2 * ρ) * c := by
    have hh := (div_le_iff₀ (show 0 < 2 * ρ by positivity)).mp hclo
    dsimp only [c]
    nlinarith
  obtain ⟨B, hB, hBmass, hBdense⟩ := dense_cover_fibres hδ hn hsmall hfinite hmassY hC
  have hbr' : Broad ω ζ δ η (2 * ρ) n N v S Z f :=
    broad_enlarge hδ hω hω1 hζ hζ1 hρ (by linarith) le_rfl hloss htwo hbr
  have hdense (k : Fin N) (hk : k ∈ B) :
      O (δ ^ η * (S.filter (fun i => f i = k)).card * δ ^ 2) ≤
        ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) := by
    apply le_trans (ENNReal.ofReal_le_ofReal _) (hBdense k hk).2
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hdensity)
        (Nat.cast_nonneg _)) (sq_nonneg δ)
  have Hk := fun (k : Fin N) (hk : k ∈ B) => cover_fibre_packet hTG hδ hδd
    (by linarith : δ ≤ 2 * ρ) (by linarith : 2 * ρ ≤ 1) hgeom hX hC hbr' k
    (hBdense k hk).1 (hdense k hk)
  have hc1 : c ≤ 1 := by
    obtain ⟨k, hk⟩ := hB
    have hh : 4 * δ ^ e * (2 * ρ / δ) ≤ D := (Hk k hk).1.trans (hmax k)
    have hh' : c ≤ 1 / 4 := by
      dsimp only [c]
      rw [div_le_iff₀ hD]
      linarith
    linarith
  have hupper (k : Fin N) (hk : k ∈ B) :
      c ≤ δ ^ e * (2 * ρ / δ) / (S.filter (fun i => f i = k)).card := by
    have hcard : (0 : ℝ) < (S.filter (fun i => f i = k)).card :=
      Nat.cast_pos.mpr (hBdense k hk).1.card_pos
    exact div_le_div_of_nonneg_left (by positivity) hcard (hmax k)
  have hexists : ∀ k : Fin N, ∃ (Wk : Fin n → Set V) (mk : ℝ),
      k ∈ B → FibrePacketProperty ω ζ δ e (2 * ρ) c x v Z S f y w k Wk mk := by
    intro k
    by_cases hk : k ∈ B
    · obtain ⟨Wk, mk, hdata⟩ := (Hk k hk).2 c hclo (hupper k hk)
      exact ⟨Wk, mk, fun _ => hdata⟩
    · exact ⟨fun _ => ∅, 0, fun hh => False.elim (hk hh)⟩
  choose W m hdata using hexists
  have hpositive (k : Fin N) (hk : k ∈ B) : 0 < ∑ i, μ (W k i) := by
    have hcard : (0 : ℝ) < (S.filter (fun i => f i = k)).card :=
      Nat.cast_pos.mpr (hBdense k hk).1.card_pos
    have hmass : 0 < ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) (hBdense k hk).2
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ e))) (ne_of_gt hmass)))
      (hdata k hk).2.2.1
  refine ⟨c, B, W, m, hc, hc1, hwide, hB, hdesired, hdata, hpositive, ?_⟩
  calc
    _ ≤ O (δ ^ e) * (2 * ∑ k ∈ B, ∑ i ∈ S.filter (fun i => f i = k), μ (Z i)) :=
      mul_le_mul' le_rfl hBmass
    _ = 2 * ∑ k ∈ B, O (δ ^ e) * (∑ i ∈ S.filter (fun i => f i = k), μ (Z i)) := by
      rw [mul_left_comm, Finset.mul_sum]
    _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum (fun k hk => (hdata k hk).2.2.1))

end WangZahlLot.Obl.wz_coarse_grains_assembly
