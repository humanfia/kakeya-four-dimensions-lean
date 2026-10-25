-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.SmallQuantitative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.UniformPackets
import Submission.WZ.Obl.wz_coarse_grains_assembly.DoubleSelection
import Submission.WZ.Obl.wz_coarse_grains_assembly.RetainedCoarse
import Submission.WZ.Obl.wz_coarse_grains_assembly.SelectedPackets

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- The small-radius assembly with all parameter losses explicit. The only
geometric construction used is the single-tube packet theorem. -/
theorem small_radius_quantitative {ω ζ δ θ e ε η d₀ ρ : ℝ} {n N K : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hTG : TubePacketStatement (ω * ζ / 100) (ζ / 2) e η d₀)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hε : 0 < ε) (hθ : 0 < θ) (hθε : θ ≤ ε / 12)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδd : δ ≤ d₀) (hδρ : δ ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hsmall : 2 * δ ^ (4 * θ) ≤ δ ^ (2 * θ)) (hdensity : 4 * θ ≤ η)
    (hloss : 2 * δ ^ (-θ) ≤ δ ^ (-η)) (htwo : 2 ≤ δ ^ (-η))
    (hlength : e + θ ≤ ζ / 2) (herror : e + θ ≤ ε)
    (hwidth : 16 * δ ≤ δ ^ (1 - ζ / 2))
    (hlevel : 4 * δ ^ (-e) ≤ δ ^ (-ε))
    (h56 : 56 ≤ δ ^ (-(ε / 4))) (hcontain : 10 ^ 15 ≤ δ ^ (-ε))
    (hK : 0 < K) (color : ℕ → Fin K)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
      color a = color b → (a : ℝ) ≤ 2 * b)
    (hbudget : (8 * (K : ℝ) * (10 ^ 40 + 1)) * δ ^ (ε / 2) ≤ δ ^ (θ + e))
    (hn : 0 < n) (hgeom : ∀ i, ‖v i‖ = 1 ∧ Y i ⊆ T δ (x i) (v i))
    (hX : X δ n x v) (hfinite : ∀ i, μ (Z i) ≠ ⊤)
    (hmassY : O (δ ^ θ * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hC : C δ θ n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ θ ρ n N v S Z f)
    (hregime : δ / ρ ≤ δ ^ ζ * (ρ / δ) * N / n) :
    ∃ (S' : Finset (Fin n)) (Z' : Fin n → Set V) (N' : ℕ)
      (y' w' : Fin N' → V) (f' : Fin n → Fin N') (c g : ℝ),
      C δ ε n x v Y S' Z' (2 * ρ) N' y' w' f' True ∧
      0 < g ∧ Broad ω ζ δ ε (2 * ρ) n N' v S' Z' f' ∧
      H δ ε n x v S' Z' (2 * ρ) N' y' w' f' (16 * δ) c 0 g ∧
      δ ^ ε * (ρ / δ) * N / n ≤ c := by
  classical
  have hρ : 0 < ρ := hδ.trans_le hδρ
  obtain ⟨c, B, W, m, hc, hc1, hwide, hB, hdesired, hraw, hpos, hrawmass⟩ :=
    raw_cover_packets hTG hω hω1 hζ hζ1 hδ hδ1 hδd hδρ hρhalf hsmall hdensity
      hloss htwo hlength herror hwidth hn hgeom hX hfinite hmassY hC hbr hregime
  obtain ⟨A₀, M, U, hA₀B, hA₀, hM, hU, hUmass, hUpos⟩ :=
    uniform_cover_packets hδ hδ1 (by positivity : 0 < 2 * ρ) hc.le
      (by linarith : e ≤ ε) hlevel hK color hcolor B hB W m hraw hpos
  obtain ⟨A, hAA₀, hA, hAmass, hAX⟩ := doubled_distinct_selection hρ hρhalf y w
    hC.2.2.1 hC.2.2.2.2.2.2.2.1 A₀ (fun k => ∑ i, μ (U k i)) hUpos
  have hdata (k : Fin N) (hk : k ∈ A) := hU k (hAA₀ hk)
  let loss : ℝ := 8 * (K : ℝ) * (10 ^ 40 + 1)
  have hlosspos : 0 < loss := by dsimp [loss]; positivity
  have hcoef : O loss = (8 * K * (10 ^ 40 + 1) : ENNReal) := by
    norm_num [loss, O, ENNReal.ofReal_mul]
  have hmass : O (δ ^ (θ + e)) * (∑ i, μ (Y i)) ≤
      O loss * ∑ k ∈ A, ∑ i, μ (U k i) := by
    calc
      _ = O (δ ^ e) * (O (δ ^ θ) * ∑ i, μ (Y i)) := by
        dsimp only [O]
        rw [show θ + e = e + θ by ring, Real.rpow_add hδ,
          ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le e), mul_assoc]
      _ ≤ O (δ ^ e) * ∑ i ∈ S, μ (Z i) := mul_le_mul' le_rfl hC.2.1
      _ ≤ 2 * ∑ k ∈ B, ∑ i, μ (W k i) := hrawmass
      _ ≤ 2 * ((4 * K : ENNReal) * ∑ k ∈ A₀, ∑ i, μ (U k i)) :=
        mul_le_mul' le_rfl hUmass
      _ ≤ 2 * ((4 * K : ENNReal) *
          (((10 ^ 40 + 1 : ℕ) : ENNReal) * ∑ k ∈ A, ∑ i, μ (U k i))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hAmass)
      _ = _ := by rw [hcoef]; push_cast; ring
  have hret : O (δ ^ (ε / 2)) * ∑ i, μ (Y i) ≤ ∑ k ∈ A, ∑ i, μ (U k i) := by
    apply (ENNReal.mul_le_mul_iff_right
      (a := O loss) (ne_of_gt (ENNReal.ofReal_pos.mpr hlosspos)) ENNReal.ofReal_ne_top).mp
    calc
      O loss * (O (δ ^ (ε / 2)) * ∑ i, μ (Y i)) =
          O (loss * δ ^ (ε / 2)) * ∑ i, μ (Y i) := by
        dsimp only [O]
        rw [ENNReal.ofReal_mul hlosspos.le, mul_assoc]
      _ ≤ O (δ ^ (θ + e)) * ∑ i, μ (Y i) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl
      _ ≤ _ := hmass
  let Z' (i : Fin n) : Set V := if f i ∈ A then U (f i) i else ∅
  have hZ' (i : Fin n) : MeasurableSet (Z' i) ∧ Z' i ⊆ Z i := by
    dsimp only [Z']
    split_ifs with hi
    · exact (hdata _ hi).1 i
    · exact ⟨MeasurableSet.empty, Set.empty_subset _⟩
  have hsupport : ∀ k ∈ A, ∀ i p, p ∈ U k i → i ∈ S ∧ f i = k :=
    fun k hk => (hdata k hk).2.1
  have hsum : (∑ k ∈ A, ∑ i, μ (U k i)) =
      ∑ i ∈ S.filter (fun i => f i ∈ A), μ (Z' i) := by
    rw [sum_selected_packets S f A U hsupport]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Z']
    rw [ite_eq_left (Finset.mem_filter.mp hi).2]
  have hret' : O (δ ^ (ε / 2)) * ∑ i, μ (Y i) ≤
      ∑ i ∈ S.filter (fun i => f i ∈ A), μ (Z' i) := by rwa [← hsum]
  have hcount := retained_coarse_budget hδ hδ1 hθ hθε h56 hn (fun i => (hgeom i).1)
    (fun i => (hZ' i).2.trans ((hC.1 i).2.1.trans (hgeom i).2)) hmassY hC A hret'
  have hfinalret : O (δ ^ ε) * ∑ i, μ (Y i) ≤
      ∑ i ∈ S.filter (fun i => f i ∈ A), μ (Z' i) :=
    (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : ε / 2 ≤ ε))) le_rfl).trans hret'
  have hcover := cover_restrict_refined hδ hδ1 (by linarith : θ ≤ ε)
    (by linarith : ρ ≤ 2 * ρ) hC A hA Z' hZ' hfinalret hcount hAX (by
      intro i hi hiA
      exact (selected_doubled_multiplicity hδ hδρ hρhalf y w hC.2.2.1 A hAX
        (x i) (v i) (hgeom i).1).trans hcontain)
  have hmask : (fun i => if f i ∈ A then Z' i else ∅) = Z' := by
    funext i
    dsimp only [Z']
    split_ifs <;> rfl
  rw [hmask] at hcover
  obtain ⟨g, hg, hbroad, hgrains⟩ := assemble_selected_packets S f A hA U y w hδ hwide
    (by nlinarith : (2 * ρ) * c ≤ c) hc1 hsupport
    (fun k hk => (hdata k hk).2.2.1)
    (m := (M : ℝ)) (by
      intro k hk p hp
      rw [(hdata k hk).2.2.2.1 p hp]
      exact ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) M]⟩)
    (fun k hk => (hdata k hk).2.2.2.2)
  exact ⟨S.filter (fun i => f i ∈ A), Z', A.card,
    (fun k => y (rIdx A k)), (fun k => w (rIdx A k)), rFib A hA f,
    c, g, hcover, hg, hbroad, hgrains, hdesired⟩

end WangZahlLot.Obl.wz_coarse_grains_assembly
